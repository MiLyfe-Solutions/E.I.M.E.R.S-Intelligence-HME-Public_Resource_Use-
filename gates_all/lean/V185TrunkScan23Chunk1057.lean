import V185TrunkScan23Chunk1056

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6258168 : List Nat := [2, 1, 2, 1, 1, 5, 2, 1, 2, 6]
def baseStart_6258168 : Nat := 118140960795 + 6258168 * 2 ^ 59
def prefixEnd_6258168 : Nat := 4983230072969 + 3 ^ 40 * 6258168 * 2
def baseEnd_6258168 : Nat := 1071149400195525374206405

theorem tailTrace_6258168 : CollatzResearch.WordTrace tailWord_6258168 prefixEnd_6258168 1071149400195525374206405 := by
  unfold tailWord_6258168
  simp only [CollatzResearch.WordTrace]
  refine ⟨114127069395866810423599579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152169425861155747231466105 114127069395866810423599579)
  ·
    refine ⟨171190604093800215635399369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114127069395866810423599579 171190604093800215635399369)
    ·
      refine ⟨128392953070350161726549527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171190604093800215635399369 128392953070350161726549527)
      ·
        refine ⟨192589429605525242589824291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128392953070350161726549527 192589429605525242589824291)
        ·
          refine ⟨288884144408287863884736437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192589429605525242589824291 288884144408287863884736437)
          ·
            refine ⟨27082888538276987239194041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 288884144408287863884736437 27082888538276987239194041)
            ·
              refine ⟨20312166403707740429395531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27082888538276987239194041 20312166403707740429395531)
              ·
                refine ⟨30468249605561610644093297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20312166403707740429395531 30468249605561610644093297)
                ·
                  refine ⟨22851187204171207983069973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30468249605561610644093297 22851187204171207983069973)
                  ·
                    refine ⟨1071149400195525374206405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22851187204171207983069973 1071149400195525374206405)
                    ·
                      rfl

theorem cell23_6258168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 2, 6].length) (baseStart_6258168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258168 prefixEnd_6258168 := by exact prefixLift 6258168
  have htrace : WordTrace (prefixWord ++ tailWord_6258168) baseStart_6258168 baseEnd_6258168 := by
    simpa [prefixWord, tailWord_6258168, baseEnd_6258168] using wordTrace_append hprefix tailTrace_6258168
  have hstable : (prefixWord ++ tailWord_6258168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258168).length < 2 ^ (prefixWord ++ tailWord_6258168).sum := by decide
  have hdescent : baseEnd_6258168 < baseStart_6258168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258175 : List Nat := [1, 1, 2, 2, 1, 2, 2, 5, 1, 4, 2]
def baseStart_6258175 : Nat := 118140960795 + 6258175 * 2 ^ 59
def prefixEnd_6258175 : Nat := 4983230072969 + 3 ^ 40 * 6258175 * 2
def baseEnd_6258175 : Nat := 3213451794951157595231683

theorem tailTrace_6258175 : CollatzResearch.WordTrace tailWord_6258175 prefixEnd_6258175 3213451794951157595231683 := by
  unfold tailWord_6258175
  simp only [CollatzResearch.WordTrace]
  refine ⟨228254394102708261042703979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152169596068472174028469319 228254394102708261042703979)
  ·
    refine ⟨342381591154062391564055969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228254394102708261042703979 342381591154062391564055969)
    ·
      refine ⟨256786193365546793673041977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342381591154062391564055969 256786193365546793673041977)
      ·
        refine ⟨192589645024160095254781483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256786193365546793673041977 192589645024160095254781483)
        ·
          refine ⟨288884467536240142882172225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192589645024160095254781483 288884467536240142882172225)
          ·
            refine ⟨216663350652180107161629169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288884467536240142882172225 216663350652180107161629169)
            ·
              refine ⟨162497512989135080371221877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216663350652180107161629169 162497512989135080371221877)
              ·
                refine ⟨15234141842731413784802051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162497512989135080371221877 15234141842731413784802051)
                ·
                  refine ⟨22851212764097120677203077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15234141842731413784802051 22851212764097120677203077)
                  ·
                    refine ⟨4284602393268210126975577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22851212764097120677203077 4284602393268210126975577)
                    ·
                      refine ⟨3213451794951157595231683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4284602393268210126975577 3213451794951157595231683)
                      ·
                        rfl

theorem cell23_6258175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 4, 2].length) (baseStart_6258175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258175 prefixEnd_6258175 := by exact prefixLift 6258175
  have htrace : WordTrace (prefixWord ++ tailWord_6258175) baseStart_6258175 baseEnd_6258175 := by
    simpa [prefixWord, tailWord_6258175, baseEnd_6258175] using wordTrace_append hprefix tailTrace_6258175
  have hstable : (prefixWord ++ tailWord_6258175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258175).length < 2 ^ (prefixWord ++ tailWord_6258175).sum := by decide
  have hdescent : baseEnd_6258175 < baseStart_6258175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258245 : List Nat := [1, 3, 1, 1, 1, 4, 4, 1, 2, 5]
def baseStart_6258245 : Nat := 118140960795 + 6258245 * 2 ^ 59
def prefixEnd_6258245 : Nat := 4983230072969 + 3 ^ 40 * 6258245 * 2
def baseEnd_6258245 : Nat := 1071162579532324107118787

theorem tailTrace_6258245 : CollatzResearch.WordTrace tailWord_6258245 prefixEnd_6258245 1071162579532324107118787 := by
  unfold tailWord_6258245
  simp only [CollatzResearch.WordTrace]
  refine ⟨228256947212454662997752189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152171298141636441998501459 228256947212454662997752189)
  ·
    refine ⟨85596355204670498624157071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228256947212454662997752189 85596355204670498624157071)
    ·
      refine ⟨128394532807005747936235607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85596355204670498624157071 128394532807005747936235607)
      ·
        refine ⟨192591799210508621904353411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128394532807005747936235607 192591799210508621904353411)
        ·
          refine ⟨288887698815762932856530117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192591799210508621904353411 288887698815762932856530117)
          ·
            refine ⟨54166443527955549910599397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 288887698815762932856530117 54166443527955549910599397)
            ·
              refine ⟨10156208161491665608237387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54166443527955549910599397 10156208161491665608237387)
              ·
                refine ⟨15234312242237498412356081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10156208161491665608237387 15234312242237498412356081)
                ·
                  refine ⟨11425734181678123809267061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15234312242237498412356081 11425734181678123809267061)
                  ·
                    refine ⟨1071162579532324107118787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11425734181678123809267061 1071162579532324107118787)
                    ·
                      rfl

theorem cell23_6258245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 5].length) (baseStart_6258245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258245 prefixEnd_6258245 := by exact prefixLift 6258245
  have htrace : WordTrace (prefixWord ++ tailWord_6258245) baseStart_6258245 baseEnd_6258245 := by
    simpa [prefixWord, tailWord_6258245, baseEnd_6258245] using wordTrace_append hprefix tailTrace_6258245
  have hstable : (prefixWord ++ tailWord_6258245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258245).length < 2 ^ (prefixWord ++ tailWord_6258245).sum := by decide
  have hdescent : baseEnd_6258245 < baseStart_6258245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258265 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 3, 6, 2]
def baseStart_6258265 : Nat := 118140960795 + 6258265 * 2 ^ 59
def prefixEnd_6258265 : Nat := 4983230072969 + 3 ^ 40 * 6258265 * 2
def baseEnd_6258265 : Nat := 3213498008210062243106269

theorem tailTrace_6258265 : CollatzResearch.WordTrace tailWord_6258265 prefixEnd_6258265 3213498008210062243106269 := by
  unfold tailWord_6258265
  simp only [CollatzResearch.WordTrace]
  refine ⟨228257676672382206413480249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152171784448254804275653499 228257676672382206413480249)
  ·
    refine ⟨171193257504286654810110187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228257676672382206413480249 171193257504286654810110187)
    ·
      refine ⟨256789886256429982215165281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171193257504286654810110187 256789886256429982215165281)
      ·
        refine ⟨192592414692322486661373961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256789886256429982215165281 192592414692322486661373961)
        ·
          refine ⟨144444311019241864996030471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192592414692322486661373961 144444311019241864996030471)
          ·
            refine ⟨216666466528862797494045707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144444311019241864996030471 216666466528862797494045707)
            ·
              refine ⟨324999699793294196241068561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216666466528862797494045707 324999699793294196241068561)
              ·
                refine ⟨243749774844970647180801421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 324999699793294196241068561 243749774844970647180801421)
                ·
                  refine ⟨91406165566863992692800533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 243749774844970647180801421 91406165566863992692800533)
                  ·
                    refine ⟨4284664010946749657475025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 91406165566863992692800533 4284664010946749657475025)
                    ·
                      refine ⟨3213498008210062243106269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4284664010946749657475025 3213498008210062243106269)
                      ·
                        rfl

theorem cell23_6258265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 6, 2].length) (baseStart_6258265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258265 prefixEnd_6258265 := by exact prefixLift 6258265
  have htrace : WordTrace (prefixWord ++ tailWord_6258265) baseStart_6258265 baseEnd_6258265 := by
    simpa [prefixWord, tailWord_6258265, baseEnd_6258265] using wordTrace_append hprefix tailTrace_6258265
  have hstable : (prefixWord ++ tailWord_6258265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258265).length < 2 ^ (prefixWord ++ tailWord_6258265).sum := by decide
  have hdescent : baseEnd_6258265 < baseStart_6258265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258282 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 1, 6, 2]
def baseStart_6258282 : Nat := 118140960795 + 6258282 * 2 ^ 59
def prefixEnd_6258282 : Nat := 4983230072969 + 3 ^ 40 * 6258282 * 2
def baseEnd_6258282 : Nat := 3213506737381188676593691

theorem tailTrace_6258282 : CollatzResearch.WordTrace tailWord_6258282 prefixEnd_6258282 3213506737381188676593691 := by
  unfold tailWord_6258282
  simp only [CollatzResearch.WordTrace]
  refine ⟨57064574178330154579212275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152172197808880412211232733 57064574178330154579212275)
  ·
    refine ⟨85596861267495231868818413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57064574178330154579212275 85596861267495231868818413)
    ·
      refine ⟨32098822975310711950806905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85596861267495231868818413 32098822975310711950806905)
      ·
        refine ⟨24074117231483033963105179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32098822975310711950806905 24074117231483033963105179)
        ·
          refine ⟨36111175847224550944657769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24074117231483033963105179 36111175847224550944657769)
          ·
            refine ⟨27083381885418413208493327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36111175847224550944657769 27083381885418413208493327)
            ·
              refine ⟨40625072828127619812739991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27083381885418413208493327 40625072828127619812739991)
              ·
                refine ⟨60937609242191429719109987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40625072828127619812739991 60937609242191429719109987)
                ·
                  refine ⟨91406413863287144578664981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60937609242191429719109987 91406413863287144578664981)
                  ·
                    refine ⟨4284675649841584902124921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 91406413863287144578664981 4284675649841584902124921)
                    ·
                      refine ⟨3213506737381188676593691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4284675649841584902124921 3213506737381188676593691)
                      ·
                        rfl

theorem cell23_6258282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_6258282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258282 prefixEnd_6258282 := by exact prefixLift 6258282
  have htrace : WordTrace (prefixWord ++ tailWord_6258282) baseStart_6258282 baseEnd_6258282 := by
    simpa [prefixWord, tailWord_6258282, baseEnd_6258282] using wordTrace_append hprefix tailTrace_6258282
  have hstable : (prefixWord ++ tailWord_6258282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258282).length < 2 ^ (prefixWord ++ tailWord_6258282).sum := by decide
  have hdescent : baseEnd_6258282 < baseStart_6258282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258309 : List Nat := [1, 3, 1, 1, 4, 1, 4, 3, 1, 4]
def baseStart_6258309 : Nat := 118140960795 + 6258309 * 2 ^ 59
def prefixEnd_6258309 : Nat := 4983230072969 + 3 ^ 40 * 6258309 * 2
def baseEnd_6258309 : Nat := 1071173533786286690318689

theorem tailTrace_6258309 : CollatzResearch.WordTrace tailWord_6258309 prefixEnd_6258309 1071173533786286690318689 := by
  unfold tailWord_6258309
  simp only [CollatzResearch.WordTrace]
  refine ⟨228259281484222801928081981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152172854322815201285387987 228259281484222801928081981)
  ·
    refine ⟨85597230556583550723030743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228259281484222801928081981 85597230556583550723030743)
    ·
      refine ⟨128395845834875326084546115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85597230556583550723030743 128395845834875326084546115)
      ·
        refine ⟨192593768752312989126819173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128395845834875326084546115 192593768752312989126819173)
        ·
          refine ⟨36111331641058685461278595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192593768752312989126819173 36111331641058685461278595)
          ·
            refine ⟨54166997461588028191917893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36111331641058685461278595 54166997461588028191917893)
            ·
              refine ⟨10156312024047755285984605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54166997461588028191917893 10156312024047755285984605)
              ·
                refine ⟨3808617009017908232244227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10156312024047755285984605 3808617009017908232244227)
                ·
                  refine ⟨5712925513526862348366341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3808617009017908232244227 5712925513526862348366341)
                  ·
                    refine ⟨1071173533786286690318689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5712925513526862348366341 1071173533786286690318689)
                    ·
                      rfl

theorem cell23_6258309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 3, 1, 4].length) (baseStart_6258309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258309 prefixEnd_6258309 := by exact prefixLift 6258309
  have htrace : WordTrace (prefixWord ++ tailWord_6258309) baseStart_6258309 baseEnd_6258309 := by
    simpa [prefixWord, tailWord_6258309, baseEnd_6258309] using wordTrace_append hprefix tailTrace_6258309
  have hstable : (prefixWord ++ tailWord_6258309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258309).length < 2 ^ (prefixWord ++ tailWord_6258309).sum := by decide
  have hdescent : baseEnd_6258309 < baseStart_6258309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258322 : List Nat := [3, 2, 3, 1, 3, 1, 1, 1, 8]
def baseStart_6258322 : Nat := 118140960795 + 6258322 * 2 ^ 59
def prefixEnd_6258322 : Nat := 4983230072969 + 3 ^ 40 * 6258322 * 2
def baseEnd_6258322 : Nat := 357058586289707613343723

theorem tailTrace_6258322 : CollatzResearch.WordTrace tailWord_6258322 prefixEnd_6258322 357058586289707613343723 := by
  unfold tailWord_6258322
  simp only [CollatzResearch.WordTrace]
  refine ⟨57064938908293926287076305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152173170422117136765536813 57064938908293926287076305)
  ·
    refine ⟨42798704181220444715307229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57064938908293926287076305 42798704181220444715307229)
    ·
      refine ⟨16049514067957666768240211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42798704181220444715307229 16049514067957666768240211)
      ·
        refine ⟨24074271101936500152360317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16049514067957666768240211 24074271101936500152360317)
        ·
          refine ⟨9027851663226187557135119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24074271101936500152360317 9027851663226187557135119)
          ·
            refine ⟨13541777494839281335702679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9027851663226187557135119 13541777494839281335702679)
            ·
              refine ⟨20312666242258922003554019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13541777494839281335702679 20312666242258922003554019)
              ·
                refine ⟨30468999363388383005331029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20312666242258922003554019 30468999363388383005331029)
                ·
                  refine ⟨357058586289707613343723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30468999363388383005331029 357058586289707613343723)
                  ·
                    rfl

theorem cell23_6258322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 8].length) (baseStart_6258322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258322 prefixEnd_6258322 := by exact prefixLift 6258322
  have htrace : WordTrace (prefixWord ++ tailWord_6258322) baseStart_6258322 baseEnd_6258322 := by
    simpa [prefixWord, tailWord_6258322, baseEnd_6258322] using wordTrace_append hprefix tailTrace_6258322
  have hstable : (prefixWord ++ tailWord_6258322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258322).length < 2 ^ (prefixWord ++ tailWord_6258322).sum := by decide
  have hdescent : baseEnd_6258322 < baseStart_6258322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258349 : List Nat := [1, 5, 2, 1, 1, 1, 1, 4, 3, 1, 3]
def baseStart_6258349 : Nat := 118140960795 + 6258349 * 2 ^ 59
def prefixEnd_6258349 : Nat := 4983230072969 + 3 ^ 40 * 6258349 * 2
def baseEnd_6258349 : Nat := 3213541140585039914455883

theorem tailTrace_6258349 : CollatzResearch.WordTrace tailWord_6258349 prefixEnd_6258349 3213541140585039914455883 := by
  unfold tailWord_6258349
  simp only [CollatzResearch.WordTrace]
  refine ⟨228260740404077888759538101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152173826936051925839692067 228260740404077888759538101)
  ·
    refine ⟨21399444412882302071206697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 228260740404077888759538101 21399444412882302071206697)
    ·
      refine ⟨16049583309661726553405023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21399444412882302071206697 16049583309661726553405023)
      ·
        refine ⟨24074374964492589830107535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16049583309661726553405023 24074374964492589830107535)
        ·
          refine ⟨36111562446738884745161303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24074374964492589830107535 36111562446738884745161303)
          ·
            refine ⟨54167343670108327117741955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36111562446738884745161303 54167343670108327117741955)
            ·
              refine ⟨81251015505162490676612933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54167343670108327117741955 81251015505162490676612933)
              ·
                refine ⟨15234565407217967001864925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81251015505162490676612933 15234565407217967001864925)
                ·
                  refine ⟨5712962027706737625699347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15234565407217967001864925 5712962027706737625699347)
                  ·
                    refine ⟨8569443041560106438549021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5712962027706737625699347 8569443041560106438549021)
                    ·
                      refine ⟨3213541140585039914455883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8569443041560106438549021 3213541140585039914455883)
                      ·
                        rfl

theorem cell23_6258349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_6258349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258349 prefixEnd_6258349 := by exact prefixLift 6258349
  have htrace : WordTrace (prefixWord ++ tailWord_6258349) baseStart_6258349 baseEnd_6258349 := by
    simpa [prefixWord, tailWord_6258349, baseEnd_6258349] using wordTrace_append hprefix tailTrace_6258349
  have hstable : (prefixWord ++ tailWord_6258349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258349).length < 2 ^ (prefixWord ++ tailWord_6258349).sum := by decide
  have hdescent : baseEnd_6258349 < baseStart_6258349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258365 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 3, 6]
def baseStart_6258365 : Nat := 118140960795 + 6258365 * 2 ^ 59
def prefixEnd_6258365 : Nat := 4983230072969 + 3 ^ 40 * 6258365 * 2
def baseEnd_6258365 : Nat := 1071183118758503950618603

theorem tailTrace_6258365 : CollatzResearch.WordTrace tailWord_6258365 prefixEnd_6258365 1071183118758503950618603 := by
  unfold tailWord_6258365
  simp only [CollatzResearch.WordTrace]
  refine ⟨228261323972019923492120549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152174215981346615661413699 228261323972019923492120549)
  ·
    refine ⟨42798998244753735654772603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228261323972019923492120549 42798998244753735654772603)
    ·
      refine ⟨64198497367130603482158905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42798998244753735654772603 64198497367130603482158905)
      ·
        refine ⟨48148873025347952611619179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64198497367130603482158905 48148873025347952611619179)
        ·
          refine ⟨72223309538021928917428769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48148873025347952611619179 72223309538021928917428769)
          ·
            refine ⟨54167482153516446688071577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72223309538021928917428769 54167482153516446688071577)
            ·
              refine ⟨40625611615137335016053683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54167482153516446688071577 40625611615137335016053683)
              ·
                refine ⟨60938417422706002524080525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40625611615137335016053683 60938417422706002524080525)
                ·
                  refine ⟨22851906533514750946530197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60938417422706002524080525 22851906533514750946530197)
                  ·
                    refine ⟨1071183118758503950618603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22851906533514750946530197 1071183118758503950618603)
                    ·
                      rfl

theorem cell23_6258365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_6258365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258365 prefixEnd_6258365 := by exact prefixLift 6258365
  have htrace : WordTrace (prefixWord ++ tailWord_6258365) baseStart_6258365 baseEnd_6258365 := by
    simpa [prefixWord, tailWord_6258365, baseEnd_6258365] using wordTrace_append hprefix tailTrace_6258365
  have hstable : (prefixWord ++ tailWord_6258365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258365).length < 2 ^ (prefixWord ++ tailWord_6258365).sum := by decide
  have hdescent : baseEnd_6258365 < baseStart_6258365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258382 : List Nat := [4, 1, 1, 1, 3, 1, 1, 3, 4, 4]
def baseStart_6258382 : Nat := 118140960795 + 6258382 * 2 ^ 59
def prefixEnd_6258382 : Nat := 4983230072969 + 3 ^ 40 * 6258382 * 2
def baseEnd_6258382 : Nat := 1071186028482212761781077

theorem tailTrace_6258382 : CollatzResearch.WordTrace tailWord_6258382 prefixEnd_6258382 1071186028482212761781077 := by
  unfold tailWord_6258382
  simp only [CollatzResearch.WordTrace]
  refine ⟨28532743001619791924436175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152174629341972223596992933 28532743001619791924436175)
  ·
    refine ⟨42799114502429687886654263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28532743001619791924436175 42799114502429687886654263)
    ·
      refine ⟨64198671753644531829981395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42799114502429687886654263 64198671753644531829981395)
      ·
        refine ⟨96298007630466797744972093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64198671753644531829981395 96298007630466797744972093)
        ·
          refine ⟨36111752861425049154364535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96298007630466797744972093 36111752861425049154364535)
          ·
            refine ⟨54167629292137573731546803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36111752861425049154364535 54167629292137573731546803)
            ·
              refine ⟨81251443938206360597320205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54167629292137573731546803 81251443938206360597320205)
              ·
                refine ⟨30469291476827385223995077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81251443938206360597320205 30469291476827385223995077)
                ·
                  refine ⟨5712992151905134729499077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30469291476827385223995077 5712992151905134729499077)
                  ·
                    refine ⟨1071186028482212761781077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5712992151905134729499077 1071186028482212761781077)
                    ·
                      rfl

theorem cell23_6258382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_6258382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258382 prefixEnd_6258382 := by exact prefixLift 6258382
  have htrace : WordTrace (prefixWord ++ tailWord_6258382) baseStart_6258382 baseEnd_6258382 := by
    simpa [prefixWord, tailWord_6258382, baseEnd_6258382] using wordTrace_append hprefix tailTrace_6258382
  have hstable : (prefixWord ++ tailWord_6258382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258382).length < 2 ^ (prefixWord ++ tailWord_6258382).sum := by decide
  have hdescent : baseEnd_6258382 < baseStart_6258382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258385 : List Nat := [1, 2, 2, 1, 2, 4, 1, 2, 1, 1, 6]
def baseStart_6258385 : Nat := 118140960795 + 6258385 * 2 ^ 59
def prefixEnd_6258385 : Nat := 4983230072969 + 3 ^ 40 * 6258385 * 2
def baseEnd_6258385 : Nat := 3213559625888601773605717

theorem tailTrace_6258385 : CollatzResearch.WordTrace tailWord_6258385 prefixEnd_6258385 3213559625888601773605717 := by
  unfold tailWord_6258385
  simp only [CollatzResearch.WordTrace]
  refine ⟨228262053431947466907848609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152174702287964977938565739 228262053431947466907848609)
  ·
    refine ⟨171196540073960600180886457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228262053431947466907848609 171196540073960600180886457)
    ·
      refine ⟨128397405055470450135664843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171196540073960600180886457 128397405055470450135664843)
      ·
        refine ⟨192596107583205675203497265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128397405055470450135664843 192596107583205675203497265)
        ·
          refine ⟨144447080687404256402622949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192596107583205675203497265 144447080687404256402622949)
          ·
            refine ⟨27083827628888298075491803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144447080687404256402622949 27083827628888298075491803)
            ·
              refine ⟨40625741443332447113237705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27083827628888298075491803 40625741443332447113237705)
              ·
                refine ⟨30469306082499335334928279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40625741443332447113237705 30469306082499335334928279)
                ·
                  refine ⟨45703959123749003002392419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30469306082499335334928279 45703959123749003002392419)
                  ·
                    refine ⟨68555938685623504503588629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45703959123749003002392419 68555938685623504503588629)
                    ·
                      refine ⟨3213559625888601773605717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68555938685623504503588629 3213559625888601773605717)
                      ·
                        rfl

theorem cell23_6258385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_6258385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258385 prefixEnd_6258385 := by exact prefixLift 6258385
  have htrace : WordTrace (prefixWord ++ tailWord_6258385) baseStart_6258385 baseEnd_6258385 := by
    simpa [prefixWord, tailWord_6258385, baseEnd_6258385] using wordTrace_append hprefix tailTrace_6258385
  have hstable : (prefixWord ++ tailWord_6258385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258385).length < 2 ^ (prefixWord ++ tailWord_6258385).sum := by decide
  have hdescent : baseEnd_6258385 < baseStart_6258385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258390 : List Nat := [5, 2, 1, 3, 2, 1, 2, 1, 6]
def baseStart_6258390 : Nat := 118140960795 + 6258390 * 2 ^ 59
def prefixEnd_6258390 : Nat := 4983230072969 + 3 ^ 40 * 6258390 * 2
def baseEnd_6258390 : Nat := 357062465921319361560355

theorem tailTrace_6258390 : CollatzResearch.WordTrace tailWord_6258390 prefixEnd_6258390 357062465921319361560355 := by
  unfold tailWord_6258390
  simp only [CollatzResearch.WordTrace]
  refine ⟨14266389737308084547611289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152174823864619568507853749 14266389737308084547611289)
  ·
    refine ⟨10699792302981063410708467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14266389737308084547611289 10699792302981063410708467)
    ·
      refine ⟨16049688454471595116062701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10699792302981063410708467 16049688454471595116062701)
      ·
        refine ⟨6018633170426848168523513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16049688454471595116062701 6018633170426848168523513)
        ·
          refine ⟨4513974877820136126392635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6018633170426848168523513 4513974877820136126392635)
          ·
            refine ⟨6770962316730204189588953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4513974877820136126392635 6770962316730204189588953)
            ·
              refine ⟨5078221737547653142191715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6770962316730204189588953 5078221737547653142191715)
              ·
                refine ⟨7617332606321479713287573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5078221737547653142191715 7617332606321479713287573)
                ·
                  refine ⟨357062465921319361560355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7617332606321479713287573 357062465921319361560355)
                  ·
                    rfl

theorem cell23_6258390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_6258390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258390 prefixEnd_6258390 := by exact prefixLift 6258390
  have htrace : WordTrace (prefixWord ++ tailWord_6258390) baseStart_6258390 baseEnd_6258390 := by
    simpa [prefixWord, tailWord_6258390, baseEnd_6258390] using wordTrace_append hprefix tailTrace_6258390
  have hstable : (prefixWord ++ tailWord_6258390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258390).length < 2 ^ (prefixWord ++ tailWord_6258390).sum := by decide
  have hdescent : baseEnd_6258390 < baseStart_6258390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258392 : List Nat := [2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3]
def baseStart_6258392 : Nat := 118140960795 + 6258392 * 2 ^ 59
def prefixEnd_6258392 : Nat := 4983230072969 + 3 ^ 40 * 6258392 * 2
def baseEnd_6258392 : Nat := 3213563220253183246218185

theorem tailTrace_6258392 : CollatzResearch.WordTrace tailWord_6258392 prefixEnd_6258392 3213563220253183246218185 := by
  unfold tailWord_6258392
  simp only [CollatzResearch.WordTrace]
  refine ⟨114131154371461053551676715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152174872495281404735568953 114131154371461053551676715)
  ·
    refine ⟨171196731557191580327515073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114131154371461053551676715 171196731557191580327515073)
    ·
      refine ⟨128397548667893685245636305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171196731557191580327515073 128397548667893685245636305)
      ·
        refine ⟨96298161500920263934227229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128397548667893685245636305 96298161500920263934227229)
        ·
          refine ⟨36111810562845098975335211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96298161500920263934227229 36111810562845098975335211)
          ·
            refine ⟨54167715844267648463002817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36111810562845098975335211 54167715844267648463002817)
            ·
              refine ⟨40625786883200736347252113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54167715844267648463002817 40625786883200736347252113)
              ·
                refine ⟨30469340162400552260439085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40625786883200736347252113 30469340162400552260439085)
                ·
                  refine ⟨11426002560900207097664657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30469340162400552260439085 11426002560900207097664657)
                  ·
                    refine ⟨8569501920675155323248493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11426002560900207097664657 8569501920675155323248493)
                    ·
                      refine ⟨3213563220253183246218185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8569501920675155323248493 3213563220253183246218185)
                      ·
                        rfl

theorem cell23_6258392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_6258392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258392 prefixEnd_6258392 := by exact prefixLift 6258392
  have htrace : WordTrace (prefixWord ++ tailWord_6258392) baseStart_6258392 baseEnd_6258392 := by
    simpa [prefixWord, tailWord_6258392, baseEnd_6258392] using wordTrace_append hprefix tailTrace_6258392
  have hstable : (prefixWord ++ tailWord_6258392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258392).length < 2 ^ (prefixWord ++ tailWord_6258392).sum := by decide
  have hdescent : baseEnd_6258392 < baseStart_6258392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258435 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 5]
def baseStart_6258435 : Nat := 118140960795 + 6258435 * 2 ^ 59
def prefixEnd_6258435 : Nat := 4983230072969 + 3 ^ 40 * 6258435 * 2
def baseEnd_6258435 : Nat := 3213585299921326577980487

theorem tailTrace_6258435 : CollatzResearch.WordTrace tailWord_6258435 prefixEnd_6258435 3213585299921326577980487 := by
  unfold tailWord_6258435
  simp only [CollatzResearch.WordTrace]
  refine ⟨228263877081766325447168759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152175918054510883631445839 228263877081766325447168759)
  ·
    refine ⟨342395815622649488170753139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228263877081766325447168759 342395815622649488170753139)
    ·
      refine ⟨513593723433974232256129709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342395815622649488170753139 513593723433974232256129709)
      ·
        refine ⟨192597646287740337096048641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 513593723433974232256129709 192597646287740337096048641)
        ·
          refine ⟨144448234715805252822036481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192597646287740337096048641 144448234715805252822036481)
          ·
            refine ⟨108336176036853939616527361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144448234715805252822036481 108336176036853939616527361)
            ·
              refine ⟨81252132027640454712395521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108336176036853939616527361 81252132027640454712395521)
              ·
                refine ⟨60939099020730341034296641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81252132027640454712395521 60939099020730341034296641)
                ·
                  refine ⟨45704324265547755775722481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60939099020730341034296641 45704324265547755775722481)
                  ·
                    refine ⟨34278243199160816831791861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45704324265547755775722481 34278243199160816831791861)
                    ·
                      refine ⟨3213585299921326577980487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34278243199160816831791861 3213585299921326577980487)
                      ·
                        rfl

theorem cell23_6258435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_6258435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258435 prefixEnd_6258435 := by exact prefixLift 6258435
  have htrace : WordTrace (prefixWord ++ tailWord_6258435) baseStart_6258435 baseEnd_6258435 := by
    simpa [prefixWord, tailWord_6258435, baseEnd_6258435] using wordTrace_append hprefix tailTrace_6258435
  have hstable : (prefixWord ++ tailWord_6258435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258435).length < 2 ^ (prefixWord ++ tailWord_6258435).sum := by decide
  have hdescent : baseEnd_6258435 < baseStart_6258435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258466 : List Nat := [3, 3, 1, 1, 2, 1, 2, 4, 1, 3, 2]
def baseStart_6258466 : Nat := 118140960795 + 6258466 * 2 ^ 59
def prefixEnd_6258466 : Nat := 4983230072969 + 3 ^ 40 * 6258466 * 2
def baseEnd_6258466 : Nat := 3213601217821615956692845

theorem tailTrace_6258466 : CollatzResearch.WordTrace tailWord_6258466 prefixEnd_6258466 3213601217821615956692845 := by
  unfold tailWord_6258466
  simp only [CollatzResearch.WordTrace]
  refine ⟨57066251936163504435386813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152176671829769345161031501 57066251936163504435386813)
  ·
    refine ⟨21399844476061314163270055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57066251936163504435386813 21399844476061314163270055)
    ·
      refine ⟨32099766714091971244905083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21399844476061314163270055 32099766714091971244905083)
      ·
        refine ⟨48149650071137956867357625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32099766714091971244905083 48149650071137956867357625)
        ·
          refine ⟨36112237553353467650518219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48149650071137956867357625 36112237553353467650518219)
          ·
            refine ⟨54168356330030201475777329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36112237553353467650518219 54168356330030201475777329)
            ·
              refine ⟨40626267247522651106832997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54168356330030201475777329 40626267247522651106832997)
              ·
                refine ⟨7617425108910497082531187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40626267247522651106832997 7617425108910497082531187)
                ·
                  refine ⟨11426137663365745623796781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7617425108910497082531187 11426137663365745623796781)
                  ·
                    refine ⟨4284801623762154608923793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11426137663365745623796781 4284801623762154608923793)
                    ·
                      refine ⟨3213601217821615956692845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4284801623762154608923793 3213601217821615956692845)
                      ·
                        rfl

theorem cell23_6258466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_6258466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258466 prefixEnd_6258466 := by exact prefixLift 6258466
  have htrace : WordTrace (prefixWord ++ tailWord_6258466) baseStart_6258466 baseEnd_6258466 := by
    simpa [prefixWord, tailWord_6258466, baseEnd_6258466] using wordTrace_append hprefix tailTrace_6258466
  have hstable : (prefixWord ++ tailWord_6258466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258466).length < 2 ^ (prefixWord ++ tailWord_6258466).sum := by decide
  have hdescent : baseEnd_6258466 < baseStart_6258466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258479 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 6, 2, 2]
def baseStart_6258479 : Nat := 118140960795 + 6258479 * 2 ^ 59
def prefixEnd_6258479 : Nat := 4983230072969 + 3 ^ 40 * 6258479 * 2
def baseEnd_6258479 : Nat := 3213607893070124405830285

theorem tailTrace_6258479 : CollatzResearch.WordTrace tailWord_6258479 prefixEnd_6258479 3213607893070124405830285 := by
  unfold tailWord_6258479
  simp only [CollatzResearch.WordTrace]
  refine ⟨228265481893606920961770491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152176987929071280641180327 228265481893606920961770491)
  ·
    refine ⟨342398222840410381442655737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228265481893606920961770491 342398222840410381442655737)
    ·
      refine ⟨256798667130307786081991803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342398222840410381442655737 256798667130307786081991803)
      ·
        refine ⟨385198000695461679122987705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256798667130307786081991803 385198000695461679122987705)
        ·
          refine ⟨288898500521596259342240779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385198000695461679122987705 288898500521596259342240779)
          ·
            refine ⟨433347750782394389013361169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288898500521596259342240779 433347750782394389013361169)
            ·
              refine ⟨325010813086795791760020877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 433347750782394389013361169 325010813086795791760020877)
              ·
                refine ⟨121879054907548421910007829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 325010813086795791760020877 121879054907548421910007829)
                ·
                  refine ⟨5713080698791332277031617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 121879054907548421910007829 5713080698791332277031617)
                  ·
                    refine ⟨4284810524093499207773713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5713080698791332277031617 4284810524093499207773713)
                    ·
                      refine ⟨3213607893070124405830285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4284810524093499207773713 3213607893070124405830285)
                      ·
                        rfl

theorem cell23_6258479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 6, 2, 2].length) (baseStart_6258479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258479 prefixEnd_6258479 := by exact prefixLift 6258479
  have htrace : WordTrace (prefixWord ++ tailWord_6258479) baseStart_6258479 baseEnd_6258479 := by
    simpa [prefixWord, tailWord_6258479, baseEnd_6258479] using wordTrace_append hprefix tailTrace_6258479
  have hstable : (prefixWord ++ tailWord_6258479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258479).length < 2 ^ (prefixWord ++ tailWord_6258479).sum := by decide
  have hdescent : baseEnd_6258479 < baseStart_6258479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258492 : List Nat := [2, 2, 2, 2, 1, 1, 3, 2, 2, 2, 4]
def baseStart_6258492 : Nat := 118140960795 + 6258492 * 2 ^ 59
def prefixEnd_6258492 : Nat := 4983230072969 + 3 ^ 40 * 6258492 * 2
def baseEnd_6258492 : Nat := 3213614568318632854967725

theorem tailTrace_6258492 : CollatzResearch.WordTrace tailWord_6258492 prefixEnd_6258492 3213614568318632854967725 := by
  unfold tailWord_6258492
  simp only [CollatzResearch.WordTrace]
  refine ⟨114132978021279912090996865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152177304028373216121329153 114132978021279912090996865)
  ·
    refine ⟨85599733515959934068247649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114132978021279912090996865 85599733515959934068247649)
    ·
      refine ⟨64199800136969950551185737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85599733515959934068247649 64199800136969950551185737)
      ·
        refine ⟨48149850102727462913389303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64199800136969950551185737 48149850102727462913389303)
        ·
          refine ⟨72224775154091194370083955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48149850102727462913389303 72224775154091194370083955)
          ·
            refine ⟨108337162731136791555125933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72224775154091194370083955 108337162731136791555125933)
            ·
              refine ⟨40626436024176296833172225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108337162731136791555125933 40626436024176296833172225)
              ·
                refine ⟨30469827018132222624879169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40626436024176296833172225 30469827018132222624879169)
                ·
                  refine ⟨22852370263599166968659377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30469827018132222624879169 22852370263599166968659377)
                  ·
                    refine ⟨17139277697699375226494533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22852370263599166968659377 17139277697699375226494533)
                    ·
                      refine ⟨3213614568318632854967725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17139277697699375226494533 3213614568318632854967725)
                      ·
                        rfl

theorem cell23_6258492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_6258492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258492 prefixEnd_6258492 := by exact prefixLift 6258492
  have htrace : WordTrace (prefixWord ++ tailWord_6258492) baseStart_6258492 baseEnd_6258492 := by
    simpa [prefixWord, tailWord_6258492, baseEnd_6258492] using wordTrace_append hprefix tailTrace_6258492
  have hstable : (prefixWord ++ tailWord_6258492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258492).length < 2 ^ (prefixWord ++ tailWord_6258492).sum := by decide
  have hdescent : baseEnd_6258492 < baseStart_6258492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258549 : List Nat := [1, 3, 4, 1, 1, 1, 3, 2, 2, 5]
def baseStart_6258549 : Nat := 118140960795 + 6258549 * 2 ^ 59
def prefixEnd_6258549 : Nat := 4983230072969 + 3 ^ 40 * 6258549 * 2
def baseEnd_6258549 : Nat := 1071214612238646377318321

theorem tailTrace_6258549 : CollatzResearch.WordTrace tailWord_6258549 prefixEnd_6258549 1071214612238646377318321 := by
  unfold tailWord_6258549
  simp only [CollatzResearch.WordTrace]
  refine ⟨228268035003353322916818701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152178690002235548611212467 228268035003353322916818701)
  ·
    refine ⟨85600513126257496093807013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228268035003353322916818701 85600513126257496093807013)
    ·
      refine ⟨16050096211173280517588815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85600513126257496093807013 16050096211173280517588815)
      ·
        refine ⟨24075144316759920776383223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16050096211173280517588815 24075144316759920776383223)
        ·
          refine ⟨36112716475139881164574835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24075144316759920776383223 36112716475139881164574835)
          ·
            refine ⟨54169074712709821746862253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36112716475139881164574835 54169074712709821746862253)
            ·
              refine ⟨20313403017266183155073345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54169074712709821746862253 20313403017266183155073345)
              ·
                refine ⟨15235052262949637366305009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20313403017266183155073345 15235052262949637366305009)
                ·
                  refine ⟨11426289197212228024728757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15235052262949637366305009 11426289197212228024728757)
                  ·
                    refine ⟨1071214612238646377318321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11426289197212228024728757 1071214612238646377318321)
                    ·
                      rfl

theorem cell23_6258549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_6258549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258549 prefixEnd_6258549 := by exact prefixLift 6258549
  have htrace : WordTrace (prefixWord ++ tailWord_6258549) baseStart_6258549 baseEnd_6258549 := by
    simpa [prefixWord, tailWord_6258549, baseEnd_6258549] using wordTrace_append hprefix tailTrace_6258549
  have hstable : (prefixWord ++ tailWord_6258549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258549).length < 2 ^ (prefixWord ++ tailWord_6258549).sum := by decide
  have hdescent : baseEnd_6258549 < baseStart_6258549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258569 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 1, 6, 2]
def baseStart_6258569 : Nat := 118140960795 + 6258569 * 2 ^ 59
def prefixEnd_6258569 : Nat := 4983230072969 + 3 ^ 40 * 6258569 * 2
def baseEnd_6258569 : Nat := 3213654106329029053704871

theorem tailTrace_6258569 : CollatzResearch.WordTrace tailWord_6258569 prefixEnd_6258569 3213654106329029053704871 := by
  unfold tailWord_6258569
  simp only [CollatzResearch.WordTrace]
  refine ⟨228268764463280866332546761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152179176308853910888364507 228268764463280866332546761)
  ·
    refine ⟨171201573347460649749410071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228268764463280866332546761 171201573347460649749410071)
    ·
      refine ⟨256802360021190974624115107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171201573347460649749410071 256802360021190974624115107)
      ·
        refine ⟨385203540031786461936172661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256802360021190974624115107 385203540031786461936172661)
        ·
          refine ⟨36112831877979980806516187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 385203540031786461936172661 36112831877979980806516187)
          ·
            refine ⟨54169247816969971209774281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36112831877979980806516187 54169247816969971209774281)
            ·
              refine ⟨40626935862727478407330711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54169247816969971209774281 40626935862727478407330711)
              ·
                refine ⟨60940403794091217610996067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40626935862727478407330711 60940403794091217610996067)
                ·
                  refine ⟨91410605691136826416494101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60940403794091217610996067 91410605691136826416494101)
                  ·
                    refine ⟨4284872141772038738273161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 91410605691136826416494101 4284872141772038738273161)
                    ·
                      refine ⟨3213654106329029053704871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4284872141772038738273161 3213654106329029053704871)
                      ·
                        rfl

theorem cell23_6258569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 6, 2].length) (baseStart_6258569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258569 prefixEnd_6258569 := by exact prefixLift 6258569
  have htrace : WordTrace (prefixWord ++ tailWord_6258569) baseStart_6258569 baseEnd_6258569 := by
    simpa [prefixWord, tailWord_6258569, baseEnd_6258569] using wordTrace_append hprefix tailTrace_6258569
  have hstable : (prefixWord ++ tailWord_6258569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258569).length < 2 ^ (prefixWord ++ tailWord_6258569).sum := by decide
  have hdescent : baseEnd_6258569 < baseStart_6258569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258586 : List Nat := [3, 1, 1, 4, 2, 2, 2, 1, 2, 1, 4]
def baseStart_6258586 : Nat := 118140960795 + 6258586 * 2 ^ 59
def prefixEnd_6258586 : Nat := 4983230072969 + 3 ^ 40 * 6258586 * 2
def baseEnd_6258586 : Nat := 3213662835500155487192293

theorem tailTrace_6258586 : CollatzResearch.WordTrace tailWord_6258586 prefixEnd_6258586 3213662835500155487192293 := by
  unfold tailWord_6258586
  simp only [CollatzResearch.WordTrace]
  refine ⟨57067346126054819558978903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152179589669479518823943741 57067346126054819558978903)
  ·
    refine ⟨85601019189082229338468355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57067346126054819558978903 85601019189082229338468355)
    ·
      refine ⟨128401528783623344007702533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85601019189082229338468355 128401528783623344007702533)
      ·
        refine ⟨24075286646929377001444225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128401528783623344007702533 24075286646929377001444225)
        ·
          refine ⟨18056464985197032751083169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24075286646929377001444225 18056464985197032751083169)
          ·
            refine ⟨13542348738897774563312377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18056464985197032751083169 13542348738897774563312377)
            ·
              refine ⟨10156761554173330922484283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13542348738897774563312377 10156761554173330922484283)
              ·
                refine ⟨15235142331259996383726425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10156761554173330922484283 15235142331259996383726425)
                ·
                  refine ⟨11426356748444997287794819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15235142331259996383726425 11426356748444997287794819)
                  ·
                    refine ⟨17139535122667495931692229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11426356748444997287794819 17139535122667495931692229)
                    ·
                      refine ⟨3213662835500155487192293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17139535122667495931692229 3213662835500155487192293)
                      ·
                        rfl

theorem cell23_6258586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_6258586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258586 prefixEnd_6258586 := by exact prefixLift 6258586
  have htrace : WordTrace (prefixWord ++ tailWord_6258586) baseStart_6258586 baseEnd_6258586 := by
    simpa [prefixWord, tailWord_6258586, baseEnd_6258586] using wordTrace_append hprefix tailTrace_6258586
  have hstable : (prefixWord ++ tailWord_6258586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258586).length < 2 ^ (prefixWord ++ tailWord_6258586).sum := by decide
  have hdescent : baseEnd_6258586 < baseStart_6258586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258609 : List Nat := [1, 2, 2, 4, 2, 1, 1, 4, 6]
def baseStart_6258609 : Nat := 118140960795 + 6258609 * 2 ^ 59
def prefixEnd_6258609 : Nat := 4983230072969 + 3 ^ 40 * 6258609 * 2
def baseEnd_6258609 : Nat := 357074960617245433022743

theorem tailTrace_6258609 : CollatzResearch.WordTrace tailWord_6258609 prefixEnd_6258609 357074960617245433022743 := by
  unfold tailWord_6258609
  simp only [CollatzResearch.WordTrace]
  refine ⟨228270223383135953164002881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152180148922090635442668587 228270223383135953164002881)
  ·
    refine ⟨171202667537351964873002161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228270223383135953164002881 171202667537351964873002161)
    ·
      refine ⟨128402000653013973654751621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171202667537351964873002161 128402000653013973654751621)
      ·
        refine ⟨24075375122440120060265929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128402000653013973654751621 24075375122440120060265929)
        ·
          refine ⟨18056531341830090045199447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24075375122440120060265929 18056531341830090045199447)
          ·
            refine ⟨27084797012745135067799171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18056531341830090045199447 27084797012745135067799171)
            ·
              refine ⟨40627195519117702601698757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27084797012745135067799171 40627195519117702601698757)
              ·
                refine ⟨7617599159834569237818517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40627195519117702601698757 7617599159834569237818517)
                ·
                  refine ⟨357074960617245433022743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7617599159834569237818517 357074960617245433022743)
                  ·
                    rfl

theorem cell23_6258609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 6].length) (baseStart_6258609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258609 prefixEnd_6258609 := by exact prefixLift 6258609
  have htrace : WordTrace (prefixWord ++ tailWord_6258609) baseStart_6258609 baseEnd_6258609 := by
    simpa [prefixWord, tailWord_6258609, baseEnd_6258609] using wordTrace_append hprefix tailTrace_6258609
  have hstable : (prefixWord ++ tailWord_6258609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258609).length < 2 ^ (prefixWord ++ tailWord_6258609).sum := by decide
  have hdescent : baseEnd_6258609 < baseStart_6258609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258613 : List Nat := [1, 3, 3, 2, 1, 3, 1, 4, 1, 4]
def baseStart_6258613 : Nat := 118140960795 + 6258613 * 2 ^ 59
def prefixEnd_6258613 : Nat := 4983230072969 + 3 ^ 40 * 6258613 * 2
def baseEnd_6258613 : Nat := 1071225566492608960518223

theorem tailTrace_6258613 : CollatzResearch.WordTrace tailWord_6258613 prefixEnd_6258613 1071225566492608960518223 := by
  unfold tailWord_6258613
  simp only [CollatzResearch.WordTrace]
  refine ⟨228270369275121461847148493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152180246183414307898098995 228270369275121461847148493)
  ·
    refine ⟨85601388478170548192680685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228270369275121461847148493 85601388478170548192680685)
    ·
      refine ⟨32100520679313955572255257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85601388478170548192680685 32100520679313955572255257)
      ·
        refine ⟨24075390509485466679191443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32100520679313955572255257 24075390509485466679191443)
        ·
          refine ⟨36113085764228200018787165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24075390509485466679191443 36113085764228200018787165)
          ·
            refine ⟨13542407161585575007045187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36113085764228200018787165 13542407161585575007045187)
            ·
              refine ⟨20313610742378362510567781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13542407161585575007045187 20313610742378362510567781)
              ·
                refine ⟨3808802014195942970731459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20313610742378362510567781 3808802014195942970731459)
                ·
                  refine ⟨5713203021293914456097189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3808802014195942970731459 5713203021293914456097189)
                  ·
                    refine ⟨1071225566492608960518223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5713203021293914456097189 1071225566492608960518223)
                    ·
                      rfl

theorem cell23_6258613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_6258613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258613 prefixEnd_6258613 := by exact prefixLift 6258613
  have htrace : WordTrace (prefixWord ++ tailWord_6258613) baseStart_6258613 baseEnd_6258613 := by
    simpa [prefixWord, tailWord_6258613, baseEnd_6258613] using wordTrace_append hprefix tailTrace_6258613
  have hstable : (prefixWord ++ tailWord_6258613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258613).length < 2 ^ (prefixWord ++ tailWord_6258613).sum := by decide
  have hdescent : baseEnd_6258613 < baseStart_6258613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258636 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 5, 1, 3]
def baseStart_6258636 : Nat := 118140960795 + 6258636 * 2 ^ 59
def prefixEnd_6258636 : Nat := 4983230072969 + 3 ^ 40 * 6258636 * 2
def baseEnd_6258636 : Nat := 3213688509532880291567063

theorem tailTrace_6258636 : CollatzResearch.WordTrace tailWord_6258636 prefixEnd_6258636 3213688509532880291567063 := by
  unfold tailWord_6258636
  simp only [CollatzResearch.WordTrace]
  refine ⟨114135604077019068387617881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152180805436025424516823841 114135604077019068387617881)
  ·
    refine ⟨85601703057764301290713411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114135604077019068387617881 85601703057764301290713411)
    ·
      refine ⟨128402554586646451936070117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85601703057764301290713411 128402554586646451936070117)
      ·
        refine ⟨24075478984996209738013147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128402554586646451936070117 24075478984996209738013147)
        ·
          refine ⟨36113218477494314607019721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24075478984996209738013147 36113218477494314607019721)
          ·
            refine ⟨27084913858120735955264791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36113218477494314607019721 27084913858120735955264791)
            ·
              refine ⟨40627370787181103932897187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27084913858120735955264791 40627370787181103932897187)
              ·
                refine ⟨60941056180771655899345781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40627370787181103932897187 60941056180771655899345781)
                ·
                  refine ⟨5713224016947342740563667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60941056180771655899345781 5713224016947342740563667)
                  ·
                    refine ⟨8569836025421014110845501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5713224016947342740563667 8569836025421014110845501)
                    ·
                      refine ⟨3213688509532880291567063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8569836025421014110845501 3213688509532880291567063)
                      ·
                        rfl

theorem cell23_6258636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_6258636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258636 prefixEnd_6258636 := by exact prefixLift 6258636
  have htrace : WordTrace (prefixWord ++ tailWord_6258636) baseStart_6258636 baseEnd_6258636 := by
    simpa [prefixWord, tailWord_6258636, baseEnd_6258636] using wordTrace_append hprefix tailTrace_6258636
  have hstable : (prefixWord ++ tailWord_6258636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258636).length < 2 ^ (prefixWord ++ tailWord_6258636).sum := by decide
  have hdescent : baseEnd_6258636 < baseStart_6258636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258639 : List Nat := [1, 1, 2, 1, 1, 5, 2, 4, 1, 5]
def baseStart_6258639 : Nat := 118140960795 + 6258639 * 2 ^ 59
def prefixEnd_6258639 : Nat := 4983230072969 + 3 ^ 40 * 6258639 * 2
def baseEnd_6258639 : Nat := 1071230016658281259943183

theorem tailTrace_6258639 : CollatzResearch.WordTrace tailWord_6258639 prefixEnd_6258639 1071230016658281259943183 := by
  unfold tailWord_6258639
  simp only [CollatzResearch.WordTrace]
  refine ⟨228271317573027268287594971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152180878382018178858396647 228271317573027268287594971)
  ·
    refine ⟨342406976359540902431392457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228271317573027268287594971 342406976359540902431392457)
    ·
      refine ⟨256805232269655676823544343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342406976359540902431392457 256805232269655676823544343)
      ·
        refine ⟨385207848404483515235316515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256805232269655676823544343 385207848404483515235316515)
        ·
          refine ⟨577811772606725272852974773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385207848404483515235316515 577811772606725272852974773)
          ·
            refine ⟨54169853681880494329966385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 577811772606725272852974773 54169853681880494329966385)
            ·
              refine ⟨40627390261410370747474789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54169853681880494329966385 40627390261410370747474789)
              ·
                refine ⟨7617635674014444515151523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40627390261410370747474789 7617635674014444515151523)
                ·
                  refine ⟨11426453511021666772727285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7617635674014444515151523 11426453511021666772727285)
                  ·
                    refine ⟨1071230016658281259943183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11426453511021666772727285 1071230016658281259943183)
                    ·
                      rfl

theorem cell23_6258639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 5].length) (baseStart_6258639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258639 prefixEnd_6258639 := by exact prefixLift 6258639
  have htrace : WordTrace (prefixWord ++ tailWord_6258639) baseStart_6258639 baseEnd_6258639 := by
    simpa [prefixWord, tailWord_6258639, baseEnd_6258639] using wordTrace_append hprefix tailTrace_6258639
  have hstable : (prefixWord ++ tailWord_6258639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258639).length < 2 ^ (prefixWord ++ tailWord_6258639).sum := by decide
  have hdescent : baseEnd_6258639 < baseStart_6258639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258670 : List Nat := [4, 1, 2, 1, 3, 1, 2, 4, 1, 1, 3]
def baseStart_6258670 : Nat := 118140960795 + 6258670 * 2 ^ 59
def prefixEnd_6258670 : Nat := 4983230072969 + 3 ^ 40 * 6258670 * 2
def baseEnd_6258670 : Nat := 3213705967875133158541907

theorem tailTrace_6258670 : CollatzResearch.WordTrace tailWord_6258670 prefixEnd_6258670 3213705967875133158541907 := by
  unfold tailWord_6258670
  simp only [CollatzResearch.WordTrace]
  refine ⟨28534056029489370072746683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152181632157276640387982309 28534056029489370072746683)
  ·
    refine ⟨42801084044234055109120025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28534056029489370072746683 42801084044234055109120025)
    ·
      refine ⟨32100813033175541331840019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42801084044234055109120025 32100813033175541331840019)
      ·
        refine ⟨48151219549763311997760029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32100813033175541331840019 48151219549763311997760029)
        ·
          refine ⟨18056707331161241999160011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48151219549763311997760029 18056707331161241999160011)
          ·
            refine ⟨27085060996741862998740017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18056707331161241999160011 27085060996741862998740017)
            ·
              refine ⟨20313795747556397249055013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27085060996741862998740017 20313795747556397249055013)
              ·
                refine ⟨3808836702666824484197815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20313795747556397249055013 3808836702666824484197815)
                ·
                  refine ⟨5713255054000236726296723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3808836702666824484197815 5713255054000236726296723)
                  ·
                    refine ⟨8569882581000355089445085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5713255054000236726296723 8569882581000355089445085)
                    ·
                      refine ⟨3213705967875133158541907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8569882581000355089445085 3213705967875133158541907)
                      ·
                        rfl

theorem cell23_6258670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_6258670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258670 prefixEnd_6258670 := by exact prefixLift 6258670
  have htrace : WordTrace (prefixWord ++ tailWord_6258670) baseStart_6258670 baseEnd_6258670 := by
    simpa [prefixWord, tailWord_6258670, baseEnd_6258670] using wordTrace_append hprefix tailTrace_6258670
  have hstable : (prefixWord ++ tailWord_6258670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258670).length < 2 ^ (prefixWord ++ tailWord_6258670).sum := by decide
  have hdescent : baseEnd_6258670 < baseStart_6258670 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258689 : List Nat := [1, 2, 4, 1, 2, 1, 3, 1, 1, 1, 6]
def baseStart_6258689 : Nat := 118140960795 + 6258689 * 2 ^ 59
def prefixEnd_6258689 : Nat := 4983230072969 + 3 ^ 40 * 6258689 * 2
def baseEnd_6258689 : Nat := 3213715724007568584204319

theorem tailTrace_6258689 : CollatzResearch.WordTrace tailWord_6258689 prefixEnd_6258689 3213715724007568584204319 := by
  unfold tailWord_6258689
  simp only [CollatzResearch.WordTrace]
  refine ⟨228273141222846126826915121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152182094148564084551276747 228273141222846126826915121)
  ·
    refine ⟨171204855917134595120186341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228273141222846126826915121 171204855917134595120186341)
    ·
      refine ⟨32100910484462736585034939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171204855917134595120186341 32100910484462736585034939)
      ·
        refine ⟨48151365726694104877552409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32100910484462736585034939 48151365726694104877552409)
        ·
          refine ⟨36113524295020578658164307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48151365726694104877552409 36113524295020578658164307)
          ·
            refine ⟨54170286442530867987246461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36113524295020578658164307 54170286442530867987246461)
            ·
              refine ⟨20313857415949075495217423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54170286442530867987246461 20313857415949075495217423)
              ·
                refine ⟨30470786123923613242826135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20313857415949075495217423 30470786123923613242826135)
                ·
                  refine ⟨45706179185885419864239203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30470786123923613242826135 45706179185885419864239203)
                  ·
                    refine ⟨68559268778828129796358805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45706179185885419864239203 68559268778828129796358805)
                    ·
                      refine ⟨3213715724007568584204319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68559268778828129796358805 3213715724007568584204319)
                      ·
                        rfl

theorem cell23_6258689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_6258689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258689 prefixEnd_6258689 := by exact prefixLift 6258689
  have htrace : WordTrace (prefixWord ++ tailWord_6258689) baseStart_6258689 baseEnd_6258689 := by
    simpa [prefixWord, tailWord_6258689, baseEnd_6258689] using wordTrace_append hprefix tailTrace_6258689
  have hstable : (prefixWord ++ tailWord_6258689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258689).length < 2 ^ (prefixWord ++ tailWord_6258689).sum := by decide
  have hdescent : baseEnd_6258689 < baseStart_6258689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258693 : List Nat := [1, 3, 1, 1, 2, 4, 2, 2, 3, 2, 2]
def baseStart_6258693 : Nat := 118140960795 + 6258693 * 2 ^ 59
def prefixEnd_6258693 : Nat := 4983230072969 + 3 ^ 40 * 6258693 * 2
def baseEnd_6258693 : Nat := 3213717777930186568554301

theorem tailTrace_6258693 : CollatzResearch.WordTrace tailWord_6258693 prefixEnd_6258693 3213717777930186568554301 := by
  unfold tailWord_6258693
  simp only [CollatzResearch.WordTrace]
  refine ⟨228273287114831635510060733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152182191409887757006707155 228273287114831635510060733)
  ·
    refine ⟨85602482668061863316272775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228273287114831635510060733 85602482668061863316272775)
    ·
      refine ⟨128403724002092794974409163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85602482668061863316272775 128403724002092794974409163)
      ·
        refine ⟨192605586003139192461613745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128403724002092794974409163 192605586003139192461613745)
        ·
          refine ⟨144454189502354394346210309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192605586003139192461613745 144454189502354394346210309)
          ·
            refine ⟨27085160531691448939914433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144454189502354394346210309 27085160531691448939914433)
            ·
              refine ⟨20313870398768586704935825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27085160531691448939914433 20313870398768586704935825)
              ·
                refine ⟨15235402799076440028701869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20313870398768586704935825 15235402799076440028701869)
                ·
                  refine ⟨5713276049653665010763201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15235402799076440028701869 5713276049653665010763201)
                  ·
                    refine ⟨4284957037240248758072401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5713276049653665010763201 4284957037240248758072401)
                    ·
                      refine ⟨3213717777930186568554301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4284957037240248758072401 3213717777930186568554301)
                      ·
                        rfl

theorem cell23_6258693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 3, 2, 2].length) (baseStart_6258693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258693 prefixEnd_6258693 := by exact prefixLift 6258693
  have htrace : WordTrace (prefixWord ++ tailWord_6258693) baseStart_6258693 baseEnd_6258693 := by
    simpa [prefixWord, tailWord_6258693, baseEnd_6258693] using wordTrace_append hprefix tailTrace_6258693
  have hstable : (prefixWord ++ tailWord_6258693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258693).length < 2 ^ (prefixWord ++ tailWord_6258693).sum := by decide
  have hdescent : baseEnd_6258693 < baseStart_6258693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258796 : List Nat := [2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 4]
def baseStart_6258796 : Nat := 118140960795 + 6258796 * 2 ^ 59
def prefixEnd_6258796 : Nat := 4983230072969 + 3 ^ 40 * 6258796 * 2
def baseEnd_6258796 : Nat := 3213770666437599665566327

theorem tailTrace_6258796 : CollatzResearch.WordTrace tailWord_6258796 prefixEnd_6258796 3213770666437599665566327 := by
  unfold tailWord_6258796
  simp only [CollatzResearch.WordTrace]
  refine ⟨114138521916729242050530121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152184695888972322734040161 114138521916729242050530121)
  ·
    refine ⟨85603891437546931537897591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114138521916729242050530121 85603891437546931537897591)
    ·
      refine ⟨128405837156320397306846387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85603891437546931537897591 128405837156320397306846387)
      ·
        refine ⟨192608755734480595960269581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128405837156320397306846387 192608755734480595960269581)
        ·
          refine ⟨72228283400430223485101093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192608755734480595960269581 72228283400430223485101093)
          ·
            refine ⟨13542803137580666903456455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72228283400430223485101093 13542803137580666903456455)
            ·
              refine ⟨20314204706371000355184683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13542803137580666903456455 20314204706371000355184683)
              ·
                refine ⟨30471307059556500532777025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20314204706371000355184683 30471307059556500532777025)
                ·
                  refine ⟨22853480294667375399582769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30471307059556500532777025 22853480294667375399582769)
                  ·
                    refine ⟨17140110221000531549687077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22853480294667375399582769 17140110221000531549687077)
                    ·
                      refine ⟨3213770666437599665566327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17140110221000531549687077 3213770666437599665566327)
                      ·
                        rfl

theorem cell23_6258796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_6258796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258796 prefixEnd_6258796 := by exact prefixLift 6258796
  have htrace : WordTrace (prefixWord ++ tailWord_6258796) baseStart_6258796 baseEnd_6258796 := by
    simpa [prefixWord, tailWord_6258796, baseEnd_6258796] using wordTrace_append hprefix tailTrace_6258796
  have hstable : (prefixWord ++ tailWord_6258796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258796).length < 2 ^ (prefixWord ++ tailWord_6258796).sum := by decide
  have hdescent : baseEnd_6258796 < baseStart_6258796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258800 : List Nat := [2, 1, 1, 1, 5, 2, 2, 3, 2, 2, 2]
def baseStart_6258800 : Nat := 118140960795 + 6258800 * 2 ^ 59
def prefixEnd_6258800 : Nat := 4983230072969 + 3 ^ 40 * 6258800 * 2
def baseEnd_6258800 : Nat := 3213772720360217649916309

theorem tailTrace_6258800 : CollatzResearch.WordTrace tailWord_6258800 prefixEnd_6258800 3213772720360217649916309 := by
  unfold tailWord_6258800
  simp only [CollatzResearch.WordTrace]
  refine ⟨114138594862721996392102927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152184793150295995189470569 114138594862721996392102927)
  ·
    refine ⟨171207892294082994588154391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114138594862721996392102927 171207892294082994588154391)
    ·
      refine ⟨256811838441124491882231587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171207892294082994588154391 256811838441124491882231587)
      ·
        refine ⟨385217757661686737823347381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256811838441124491882231587 385217757661686737823347381)
        ·
          refine ⟨36114164780783131670938817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 385217757661686737823347381 36114164780783131670938817)
          ·
            refine ⟨27085623585587348753204113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36114164780783131670938817 27085623585587348753204113)
            ·
              refine ⟨20314217689190511564903085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27085623585587348753204113 20314217689190511564903085)
              ·
                refine ⟨7617831633446441836838657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20314217689190511564903085 7617831633446441836838657)
                ·
                  refine ⟨5713373725084831377628993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7617831633446441836838657 5713373725084831377628993)
                  ·
                    refine ⟨4285030293813623533221745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5713373725084831377628993 4285030293813623533221745)
                    ·
                      refine ⟨3213772720360217649916309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4285030293813623533221745 3213772720360217649916309)
                      ·
                        rfl

theorem cell23_6258800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 2, 2, 2].length) (baseStart_6258800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258800 prefixEnd_6258800 := by exact prefixLift 6258800
  have htrace : WordTrace (prefixWord ++ tailWord_6258800) baseStart_6258800 baseEnd_6258800 := by
    simpa [prefixWord, tailWord_6258800, baseEnd_6258800] using wordTrace_append hprefix tailTrace_6258800
  have hstable : (prefixWord ++ tailWord_6258800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258800).length < 2 ^ (prefixWord ++ tailWord_6258800).sum := by decide
  have hdescent : baseEnd_6258800 < baseStart_6258800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258806 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 9]
def baseStart_6258806 : Nat := 118140960795 + 6258806 * 2 ^ 59
def prefixEnd_6258806 : Nat := 4983230072969 + 3 ^ 40 * 6258806 * 2
def baseEnd_6258806 : Nat := 357086200138238291826809

theorem tailTrace_6258806 : CollatzResearch.WordTrace tailWord_6258806 prefixEnd_6258806 357086200138238291826809 := by
  unfold tailWord_6258806
  simp only [CollatzResearch.WordTrace]
  refine ⟨14267338035213890988057767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152184939042281503872616181 14267338035213890988057767)
  ·
    refine ⟨21401007052820836482086651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14267338035213890988057767 21401007052820836482086651)
    ·
      refine ⟨32101510579231254723129977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21401007052820836482086651 32101510579231254723129977)
      ·
        refine ⟨24076132934423441042347483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32101510579231254723129977 24076132934423441042347483)
        ·
          refine ⟨36114199401635161563521225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24076132934423441042347483 36114199401635161563521225)
          ·
            refine ⟨27085649551226371172640919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36114199401635161563521225 27085649551226371172640919)
            ·
              refine ⟨40628474326839556758961379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27085649551226371172640919 40628474326839556758961379)
              ·
                refine ⟨60942711490259335138442069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40628474326839556758961379 60942711490259335138442069)
                ·
                  refine ⟨357086200138238291826809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60942711490259335138442069 357086200138238291826809)
                  ·
                    rfl

theorem cell23_6258806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_6258806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258806 prefixEnd_6258806 := by exact prefixLift 6258806
  have htrace : WordTrace (prefixWord ++ tailWord_6258806) baseStart_6258806 baseEnd_6258806 := by
    simpa [prefixWord, tailWord_6258806, baseEnd_6258806] using wordTrace_append hprefix tailTrace_6258806
  have hstable : (prefixWord ++ tailWord_6258806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258806).length < 2 ^ (prefixWord ++ tailWord_6258806).sum := by decide
  have hdescent : baseEnd_6258806 < baseStart_6258806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258859 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 5]
def baseStart_6258859 : Nat := 118140960795 + 6258859 * 2 ^ 59
def prefixEnd_6258859 : Nat := 4983230072969 + 3 ^ 40 * 6258859 * 2
def baseEnd_6258859 : Nat := 3213803015718832919078537

theorem tailTrace_6258859 : CollatzResearch.WordTrace tailWord_6258859 prefixEnd_6258859 3213803015718832919078537 := by
  unfold tailWord_6258859
  simp only [CollatzResearch.WordTrace]
  refine ⟨228279341632230245860603631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152186227754820163907069087 228279341632230245860603631)
  ·
    refine ⟨342419012448345368790905447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228279341632230245860603631 342419012448345368790905447)
    ·
      refine ⟨513628518672518053186358171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342419012448345368790905447 513628518672518053186358171)
      ·
        refine ⟨770442778008777079779537257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513628518672518053186358171 770442778008777079779537257)
        ·
          refine ⟨577832083506582809834652943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 770442778008777079779537257 577832083506582809834652943)
          ·
            refine ⟨866748125259874214751979415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577832083506582809834652943 866748125259874214751979415)
            ·
              refine ⟨1300122187889811322127969123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 866748125259874214751979415 1300122187889811322127969123)
              ·
                refine ⟨1950183281834716983191953685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1300122187889811322127969123 1950183281834716983191953685)
                ·
                  refine ⟨91414841336002358587122829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1950183281834716983191953685 91414841336002358587122829)
                  ·
                    refine ⟨34280565501000884470171061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91414841336002358587122829 34280565501000884470171061)
                    ·
                      refine ⟨3213803015718832919078537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34280565501000884470171061 3213803015718832919078537)
                      ·
                        rfl

theorem cell23_6258859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 5].length) (baseStart_6258859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258859 prefixEnd_6258859 := by exact prefixLift 6258859
  have htrace : WordTrace (prefixWord ++ tailWord_6258859) baseStart_6258859 baseEnd_6258859 := by
    simpa [prefixWord, tailWord_6258859, baseEnd_6258859] using wordTrace_append hprefix tailTrace_6258859
  have hstable : (prefixWord ++ tailWord_6258859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258859).length < 2 ^ (prefixWord ++ tailWord_6258859).sum := by decide
  have hdescent : baseEnd_6258859 < baseStart_6258859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258923 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 5, 1, 3]
def baseStart_6258923 : Nat := 118140960795 + 6258923 * 2 ^ 59
def prefixEnd_6258923 : Nat := 4983230072969 + 3 ^ 40 * 6258923 * 2
def baseEnd_6258923 : Nat := 3213835878480720668678243

theorem tailTrace_6258923 : CollatzResearch.WordTrace tailWord_6258923 prefixEnd_6258923 3213835878480720668678243 := by
  unfold tailWord_6258923
  simp only [CollatzResearch.WordTrace]
  refine ⟨228281675903998384790933423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152187783935998923193955615 228281675903998384790933423)
  ·
    refine ⟨342422513855997577186400135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228281675903998384790933423 342422513855997577186400135)
    ·
      refine ⟨513633770783996365779600203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342422513855997577186400135 513633770783996365779600203)
      ·
        refine ⟨770450656175994548669400305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513633770783996365779600203 770450656175994548669400305)
        ·
          refine ⟨577837992131995911502050229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 770450656175994548669400305 577837992131995911502050229)
          ·
            refine ⟨54172311762374616703317209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 577837992131995911502050229 54172311762374616703317209)
            ·
              refine ⟨40629233821780962527487907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54172311762374616703317209 40629233821780962527487907)
              ·
                refine ⟨60943850732671443791231861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40629233821780962527487907 60943850732671443791231861)
                ·
                  refine ⟨5713486006187947855427987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60943850732671443791231861 5713486006187947855427987)
                  ·
                    refine ⟨8570229009281921783141981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5713486006187947855427987 8570229009281921783141981)
                    ·
                      refine ⟨3213835878480720668678243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8570229009281921783141981 3213835878480720668678243)
                      ·
                        rfl

theorem cell23_6258923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 5, 1, 3].length) (baseStart_6258923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258923 prefixEnd_6258923 := by exact prefixLift 6258923
  have htrace : WordTrace (prefixWord ++ tailWord_6258923) baseStart_6258923 baseEnd_6258923 := by
    simpa [prefixWord, tailWord_6258923, baseEnd_6258923] using wordTrace_append hprefix tailTrace_6258923
  have hstable : (prefixWord ++ tailWord_6258923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258923).length < 2 ^ (prefixWord ++ tailWord_6258923).sum := by decide
  have hdescent : baseEnd_6258923 < baseStart_6258923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258951 : List Nat := [1, 1, 4, 5, 1, 2, 2, 2, 1, 4]
def baseStart_6258951 : Nat := 118140960795 + 6258951 * 2 ^ 59
def prefixEnd_6258951 : Nat := 4983230072969 + 3 ^ 40 * 6258951 * 2
def baseEnd_6258951 : Nat := 1071283418646348853042705

theorem tailTrace_6258951 : CollatzResearch.WordTrace tailWord_6258951 prefixEnd_6258951 1071283418646348853042705 := by
  unfold tailWord_6258951
  simp only [CollatzResearch.WordTrace]
  refine ⟨228282697147896945572952707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152188464765264630381968471 228282697147896945572952707)
  ·
    refine ⟨342424045721845418359429061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228282697147896945572952707 342424045721845418359429061)
    ·
      refine ⟨64204508572846015942392949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 342424045721845418359429061 64204508572846015942392949)
      ·
        refine ⟨6019172678704313994599339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64204508572846015942392949 6019172678704313994599339)
        ·
          refine ⟨9028759018056470991899009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6019172678704313994599339 9028759018056470991899009)
          ·
            refine ⟨6771569263542353243924257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9028759018056470991899009 6771569263542353243924257)
            ·
              refine ⟨5078676947656764932943193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6771569263542353243924257 5078676947656764932943193)
              ·
                refine ⟨3809007710742573699707395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5078676947656764932943193 3809007710742573699707395)
                ·
                  refine ⟨5713511566113860549561093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3809007710742573699707395 5713511566113860549561093)
                  ·
                    refine ⟨1071283418646348853042705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5713511566113860549561093 1071283418646348853042705)
                    ·
                      rfl

theorem cell23_6258951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_6258951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258951 prefixEnd_6258951 := by exact prefixLift 6258951
  have htrace : WordTrace (prefixWord ++ tailWord_6258951) baseStart_6258951 baseEnd_6258951 := by
    simpa [prefixWord, tailWord_6258951, baseEnd_6258951] using wordTrace_append hprefix tailTrace_6258951
  have hstable : (prefixWord ++ tailWord_6258951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258951).length < 2 ^ (prefixWord ++ tailWord_6258951).sum := by decide
  have hdescent : baseEnd_6258951 < baseStart_6258951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258956 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 3, 6]
def baseStart_6258956 : Nat := 118140960795 + 6258956 * 2 ^ 59
def prefixEnd_6258956 : Nat := 4983230072969 + 3 ^ 40 * 6258956 * 2
def baseEnd_6258956 : Nat := 1071284274447439679855197

theorem tailTrace_6258956 : CollatzResearch.WordTrace tailWord_6258956 prefixEnd_6258956 1071284274447439679855197 := by
  unfold tailWord_6258956
  simp only [CollatzResearch.WordTrace]
  refine ⟨114141439756439415713442361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152188586341919220951256481 114141439756439415713442361)
  ·
    refine ⟨85606079817329561785081771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114141439756439415713442361 85606079817329561785081771)
    ·
      refine ⟨128409119725994342677622657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85606079817329561785081771 128409119725994342677622657)
      ·
        refine ⟨96306839794495757008216993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128409119725994342677622657 96306839794495757008216993)
        ·
          refine ⟨72230129845871817756162745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96306839794495757008216993 72230129845871817756162745)
          ·
            refine ⟨54172597384403863317122059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72230129845871817756162745 54172597384403863317122059)
            ·
              refine ⟨81258896076605794975683089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54172597384403863317122059 81258896076605794975683089)
              ·
                refine ⟨60944172057454346231762317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81258896076605794975683089 60944172057454346231762317)
                ·
                  refine ⟨22854064521545379836910869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60944172057454346231762317 22854064521545379836910869)
                  ·
                    refine ⟨1071284274447439679855197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22854064521545379836910869 1071284274447439679855197)
                    ·
                      rfl

theorem cell23_6258956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 3, 6].length) (baseStart_6258956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258956 prefixEnd_6258956 := by exact prefixLift 6258956
  have htrace : WordTrace (prefixWord ++ tailWord_6258956) baseStart_6258956 baseEnd_6258956 := by
    simpa [prefixWord, tailWord_6258956, baseEnd_6258956] using wordTrace_append hprefix tailTrace_6258956
  have hstable : (prefixWord ++ tailWord_6258956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258956).length < 2 ^ (prefixWord ++ tailWord_6258956).sum := by decide
  have hdescent : baseEnd_6258956 < baseStart_6258956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258974 : List Nat := [4, 3, 2, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_6258974 : Nat := 118140960795 + 6258974 * 2 ^ 59
def prefixEnd_6258974 : Nat := 4983230072969 + 3 ^ 40 * 6258974 * 2
def baseEnd_6258974 : Nat := 3213862065994099969140509

theorem tailTrace_6258974 : CollatzResearch.WordTrace tailWord_6258974 prefixEnd_6258974 3213862065994099969140509 := by
  unfold tailWord_6258974
  simp only [CollatzResearch.WordTrace]
  refine ⟨28535442003351702562629997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152189024017875747000693317 28535442003351702562629997)
  ·
    refine ⟨10700790751256888460986249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28535442003351702562629997 10700790751256888460986249)
    ·
      refine ⟨8025593063442666345739687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10700790751256888460986249 8025593063442666345739687)
      ·
        refine ⟨12038389595163999518609531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8025593063442666345739687 12038389595163999518609531)
        ·
          refine ⟨18057584392745999277914297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12038389595163999518609531 18057584392745999277914297)
          ·
            refine ⟨13543188294559499458435723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18057584392745999277914297 13543188294559499458435723)
            ·
              refine ⟨20314782441839249187653585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13543188294559499458435723 20314782441839249187653585)
              ·
                refine ⟨15236086831379436890740189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20314782441839249187653585 15236086831379436890740189)
                ·
                  refine ⟨5713532561767288834027571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15236086831379436890740189 5713532561767288834027571)
                  ·
                    refine ⟨8570298842650933251041357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5713532561767288834027571 8570298842650933251041357)
                    ·
                      refine ⟨3213862065994099969140509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8570298842650933251041357 3213862065994099969140509)
                      ·
                        rfl

theorem cell23_6258974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_6258974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258974 prefixEnd_6258974 := by exact prefixLift 6258974
  have htrace : WordTrace (prefixWord ++ tailWord_6258974) baseStart_6258974 baseEnd_6258974 := by
    simpa [prefixWord, tailWord_6258974, baseEnd_6258974] using wordTrace_append hprefix tailTrace_6258974
  have hstable : (prefixWord ++ tailWord_6258974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258974).length < 2 ^ (prefixWord ++ tailWord_6258974).sum := by decide
  have hdescent : baseEnd_6258974 < baseStart_6258974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258984 : List Nat := [2, 1, 5, 1, 3, 2, 1, 1, 2, 3, 2]
def baseStart_6258984 : Nat := 118140960795 + 6258984 * 2 ^ 59
def prefixEnd_6258984 : Nat := 4983230072969 + 3 ^ 40 * 6258984 * 2
def baseEnd_6258984 : Nat := 3213867200800644930015463

theorem tailTrace_6258984 : CollatzResearch.WordTrace tailWord_6258984 prefixEnd_6258984 3213867200800644930015463 := by
  unfold tailWord_6258984
  simp only [CollatzResearch.WordTrace]
  refine ⟨114141950378388696104452003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152189267171184928139269337 114141950378388696104452003)
  ·
    refine ⟨171212925567583044156678005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114141950378388696104452003 171212925567583044156678005)
    ·
      refine ⟨16051211771960910389688563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 171212925567583044156678005 16051211771960910389688563)
      ·
        refine ⟨24076817657941365584532845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16051211771960910389688563 24076817657941365584532845)
        ·
          refine ⟨9028806621728012094199817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24076817657941365584532845 9028806621728012094199817)
          ·
            refine ⟨6771604966296009070649863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9028806621728012094199817 6771604966296009070649863)
            ·
              refine ⟨10157407449444013605974795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6771604966296009070649863 10157407449444013605974795)
              ·
                refine ⟨15236111174166020408962193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10157407449444013605974795 15236111174166020408962193)
                ·
                  refine ⟨11427083380624515306721645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15236111174166020408962193 11427083380624515306721645)
                  ·
                    refine ⟨4285156267734193240020617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11427083380624515306721645 4285156267734193240020617)
                    ·
                      refine ⟨3213867200800644930015463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4285156267734193240020617 3213867200800644930015463)
                      ·
                        rfl

theorem cell23_6258984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_6258984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258984 prefixEnd_6258984 := by exact prefixLift 6258984
  have htrace : WordTrace (prefixWord ++ tailWord_6258984) baseStart_6258984 baseEnd_6258984 := by
    simpa [prefixWord, tailWord_6258984, baseEnd_6258984] using wordTrace_append hprefix tailTrace_6258984
  have hstable : (prefixWord ++ tailWord_6258984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258984).length < 2 ^ (prefixWord ++ tailWord_6258984).sum := by decide
  have hdescent : baseEnd_6258984 < baseStart_6258984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258994 : List Nat := [3, 2, 1, 1, 6, 1, 2, 1, 1, 5]
def baseStart_6258994 : Nat := 118140960795 + 6258994 * 2 ^ 59
def prefixEnd_6258994 : Nat := 4983230072969 + 3 ^ 40 * 6258994 * 2
def baseEnd_6258994 : Nat := 1071290778535729963630139

theorem tailTrace_6258994 : CollatzResearch.WordTrace tailWord_6258994 prefixEnd_6258994 1071290778535729963630139 := by
  unfold tailWord_6258994
  simp only [CollatzResearch.WordTrace]
  refine ⟨57071066371685290979192009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152189510324494109277845357 57071066371685290979192009)
  ·
    refine ⟨42803299778763968234394007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57071066371685290979192009 42803299778763968234394007)
    ·
      refine ⟨64204949668145952351591011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42803299778763968234394007 64204949668145952351591011)
      ·
        refine ⟨96307424502218928527386517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64204949668145952351591011 96307424502218928527386517)
        ·
          refine ⟨4514410523541512274721243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 96307424502218928527386517 4514410523541512274721243)
          ·
            refine ⟨6771615785312268412081865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4514410523541512274721243 6771615785312268412081865)
            ·
              refine ⟨5078711838984201309061399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6771615785312268412081865 5078711838984201309061399)
              ·
                refine ⟨7618067758476301963592099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5078711838984201309061399 7618067758476301963592099)
                ·
                  refine ⟨11427101637714452945388149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7618067758476301963592099 11427101637714452945388149)
                  ·
                    refine ⟨1071290778535729963630139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11427101637714452945388149 1071290778535729963630139)
                    ·
                      rfl

theorem cell23_6258994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_6258994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258994 prefixEnd_6258994 := by exact prefixLift 6258994
  have htrace : WordTrace (prefixWord ++ tailWord_6258994) baseStart_6258994 baseEnd_6258994 := by
    simpa [prefixWord, tailWord_6258994, baseEnd_6258994] using wordTrace_append hprefix tailTrace_6258994
  have hstable : (prefixWord ++ tailWord_6258994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258994).length < 2 ^ (prefixWord ++ tailWord_6258994).sum := by decide
  have hdescent : baseEnd_6258994 < baseStart_6258994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259016 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 1, 9]
def baseStart_6259016 : Nat := 118140960795 + 6259016 * 2 ^ 59
def prefixEnd_6259016 : Nat := 4983230072969 + 3 ^ 40 * 6259016 * 2
def baseEnd_6259016 : Nat := 1071294544060529601605105

theorem tailTrace_6259016 : CollatzResearch.WordTrace tailWord_6259016 prefixEnd_6259016 1071294544060529601605105 := by
  unfold tailWord_6259016
  simp only [CollatzResearch.WordTrace]
  refine ⟨114142533946330730837034451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152190045261774307782712601 114142533946330730837034451)
  ·
    refine ⟨171213800919496096255551677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114142533946330730837034451 171213800919496096255551677)
    ·
      refine ⟨64205175344811036095831879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171213800919496096255551677 64205175344811036095831879)
      ·
        refine ⟨96307763017216554143747819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64205175344811036095831879 96307763017216554143747819)
        ·
          refine ⟨144461644525824831215621729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96307763017216554143747819 144461644525824831215621729)
          ·
            refine ⟨108346233394368623411716297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144461644525824831215621729 108346233394368623411716297)
            ·
              refine ⟨81259675045776467558787223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108346233394368623411716297 81259675045776467558787223)
              ·
                refine ⟨121889512568664701338180835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81259675045776467558787223 121889512568664701338180835)
                ·
                  refine ⟨182834268852997052007271253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121889512568664701338180835 182834268852997052007271253)
                  ·
                    refine ⟨1071294544060529601605105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 182834268852997052007271253 1071294544060529601605105)
                    ·
                      rfl

theorem cell23_6259016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_6259016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259016 prefixEnd_6259016 := by exact prefixLift 6259016
  have htrace : WordTrace (prefixWord ++ tailWord_6259016) baseStart_6259016 baseEnd_6259016 := by
    simpa [prefixWord, tailWord_6259016, baseEnd_6259016] using wordTrace_append hprefix tailTrace_6259016
  have hstable : (prefixWord ++ tailWord_6259016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259016).length < 2 ^ (prefixWord ++ tailWord_6259016).sum := by decide
  have hdescent : baseEnd_6259016 < baseStart_6259016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259023 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 2, 7, 2]
def baseStart_6259023 : Nat := 118140960795 + 6259023 * 2 ^ 59
def prefixEnd_6259023 : Nat := 4983230072969 + 3 ^ 40 * 6259023 * 2
def baseEnd_6259023 : Nat := 3213887226546170277427783

theorem tailTrace_6259023 : CollatzResearch.WordTrace tailWord_6259023 prefixEnd_6259023 3213887226546170277427783 := by
  unfold tailWord_6259023
  simp only [CollatzResearch.WordTrace]
  refine ⟨228285323203636101869573723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152190215469090734579715815 228285323203636101869573723)
  ·
    refine ⟨342427984805454152804360585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228285323203636101869573723 342427984805454152804360585)
    ·
      refine ⟨256820988604090614603270439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342427984805454152804360585 256820988604090614603270439)
      ·
        refine ⟨385231482906135921904905659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256820988604090614603270439 385231482906135921904905659)
        ·
          refine ⟨577847224359203882857358489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385231482906135921904905659 577847224359203882857358489)
          ·
            refine ⟨433385418269402912143018867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 577847224359203882857358489 433385418269402912143018867)
            ·
              refine ⟨650078127404104368214528301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433385418269402912143018867 650078127404104368214528301)
              ·
                refine ⟨243779297776539138080448113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 650078127404104368214528301 243779297776539138080448113)
                ·
                  refine ⟨182834473332404353560336085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243779297776539138080448113 182834473332404353560336085)
                  ·
                    refine ⟨4285182968728227036570377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 182834473332404353560336085 4285182968728227036570377)
                    ·
                      refine ⟨3213887226546170277427783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4285182968728227036570377 3213887226546170277427783)
                      ·
                        rfl

theorem cell23_6259023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 7, 2].length) (baseStart_6259023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259023 prefixEnd_6259023 := by exact prefixLift 6259023
  have htrace : WordTrace (prefixWord ++ tailWord_6259023) baseStart_6259023 baseEnd_6259023 := by
    simpa [prefixWord, tailWord_6259023, baseEnd_6259023] using wordTrace_append hprefix tailTrace_6259023
  have hstable : (prefixWord ++ tailWord_6259023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259023).length < 2 ^ (prefixWord ++ tailWord_6259023).sum := by decide
  have hdescent : baseEnd_6259023 < baseStart_6259023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259127 : List Nat := [1, 1, 3, 1, 3, 3, 4, 2, 5]
def baseStart_6259127 : Nat := 118140960795 + 6259127 * 2 ^ 59
def prefixEnd_6259127 : Nat := 4983230072969 + 3 ^ 40 * 6259127 * 2
def baseEnd_6259127 : Nat := 357104514281581985614145

theorem tailTrace_6259127 : CollatzResearch.WordTrace tailWord_6259127 prefixEnd_6259127 357104514281581985614145 := by
  unfold tailWord_6259127
  simp only [CollatzResearch.WordTrace]
  refine ⟨228289116395259327631359635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152192744263506218420906423 228289116395259327631359635)
  ·
    refine ⟨342433674592888991447039453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228289116395259327631359635 342433674592888991447039453)
    ·
      refine ⟨128412627972333371792639795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342433674592888991447039453 128412627972333371792639795)
      ·
        refine ⟨192618941958500057688959693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128412627972333371792639795 192618941958500057688959693)
        ·
          refine ⟨72232103234437521633359885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192618941958500057688959693 72232103234437521633359885)
          ·
            refine ⟨27087038712914070612509957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72232103234437521633359885 27087038712914070612509957)
            ·
              refine ⟨5078819758671388239845617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27087038712914070612509957 5078819758671388239845617)
              ·
                refine ⟨3809114819003541179884213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5078819758671388239845617 3809114819003541179884213)
                ·
                  refine ⟨357104514281581985614145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3809114819003541179884213 357104514281581985614145)
                  ·
                    rfl

theorem cell23_6259127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 2, 5].length) (baseStart_6259127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259127 prefixEnd_6259127 := by exact prefixLift 6259127
  have htrace : WordTrace (prefixWord ++ tailWord_6259127) baseStart_6259127 baseEnd_6259127 := by
    simpa [prefixWord, tailWord_6259127, baseEnd_6259127] using wordTrace_append hprefix tailTrace_6259127
  have hstable : (prefixWord ++ tailWord_6259127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259127).length < 2 ^ (prefixWord ++ tailWord_6259127).sum := by decide
  have hdescent : baseEnd_6259127 < baseStart_6259127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259157 : List Nat := [1, 3, 2, 3, 1, 4, 1, 1, 2, 5]
def baseStart_6259157 : Nat := 118140960795 + 6259157 * 2 ^ 59
def prefixEnd_6259157 : Nat := 4983230072969 + 3 ^ 40 * 6259157 * 2
def baseEnd_6259157 : Nat := 1071318677651290917717389

theorem tailTrace_6259157 : CollatzResearch.WordTrace tailWord_6259157 prefixEnd_6259157 1071318677651290917717389 := by
  unfold tailWord_6259157
  simp only [CollatzResearch.WordTrace]
  refine ⟨228290210585150642754951725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152193473723433761836634483 228290210585150642754951725)
  ·
    refine ⟨85608828969431491033106897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228290210585150642754951725 85608828969431491033106897)
    ·
      refine ⟨64206621727073618274830173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85608828969431491033106897 64206621727073618274830173)
      ·
        refine ⟨24077483147652606853061315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64206621727073618274830173 24077483147652606853061315)
        ·
          refine ⟨36116224721478910279591973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24077483147652606853061315 36116224721478910279591973)
          ·
            refine ⟨6771792135277295677423495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36116224721478910279591973 6771792135277295677423495)
            ·
              refine ⟨10157688202915943516135243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6771792135277295677423495 10157688202915943516135243)
              ·
                refine ⟨15236532304373915274202865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10157688202915943516135243 15236532304373915274202865)
                ·
                  refine ⟨11427399228280436455652149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15236532304373915274202865 11427399228280436455652149)
                  ·
                    refine ⟨1071318677651290917717389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11427399228280436455652149 1071318677651290917717389)
                    ·
                      rfl

theorem cell23_6259157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_6259157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259157 prefixEnd_6259157 := by exact prefixLift 6259157
  have htrace : WordTrace (prefixWord ++ tailWord_6259157) baseStart_6259157 baseEnd_6259157 := by
    simpa [prefixWord, tailWord_6259157, baseEnd_6259157] using wordTrace_append hprefix tailTrace_6259157
  have hstable : (prefixWord ++ tailWord_6259157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259157).length < 2 ^ (prefixWord ++ tailWord_6259157).sum := by decide
  have hdescent : baseEnd_6259157 < baseStart_6259157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259160 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 3, 6, 2]
def baseStart_6259160 : Nat := 118140960795 + 6259160 * 2 ^ 59
def prefixEnd_6259160 : Nat := 4983230072969 + 3 ^ 40 * 6259160 * 2
def baseEnd_6259160 : Nat := 3213957573395836241414653

theorem tailTrace_6259160 : CollatzResearch.WordTrace tailWord_6259160 prefixEnd_6259160 3213957573395836241414653 := by
  unfold tailWord_6259160
  simp only [CollatzResearch.WordTrace]
  refine ⟨114145160002069887133655467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152193546669426516178207289 114145160002069887133655467)
  ·
    refine ⟨171217740003104830700483201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114145160002069887133655467 171217740003104830700483201)
    ·
      refine ⟨128413305002328623025362401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171217740003104830700483201 128413305002328623025362401)
      ·
        refine ⟨96309978751746467269021801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128413305002328623025362401 96309978751746467269021801)
        ·
          refine ⟨72232484063809850451766351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96309978751746467269021801 72232484063809850451766351)
          ·
            refine ⟨108348726095714775677649527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72232484063809850451766351 108348726095714775677649527)
            ·
              refine ⟨162523089143572163516474291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108348726095714775677649527 162523089143572163516474291)
              ·
                refine ⟨243784633715358245274711437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162523089143572163516474291 243784633715358245274711437)
                ·
                  refine ⟨91419237643259341978016789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 243784633715358245274711437 91419237643259341978016789)
                  ·
                    refine ⟨4285276764527781655219537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 91419237643259341978016789 4285276764527781655219537)
                    ·
                      refine ⟨3213957573395836241414653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4285276764527781655219537 3213957573395836241414653)
                      ·
                        rfl

theorem cell23_6259160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 3, 6, 2].length) (baseStart_6259160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259160 prefixEnd_6259160 := by exact prefixLift 6259160
  have htrace : WordTrace (prefixWord ++ tailWord_6259160) baseStart_6259160 baseEnd_6259160 := by
    simpa [prefixWord, tailWord_6259160, baseEnd_6259160] using wordTrace_append hprefix tailTrace_6259160
  have hstable : (prefixWord ++ tailWord_6259160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259160).length < 2 ^ (prefixWord ++ tailWord_6259160).sum := by decide
  have hdescent : baseEnd_6259160 < baseStart_6259160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259180 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 3]
def baseStart_6259180 : Nat := 118140960795 + 6259180 * 2 ^ 59
def prefixEnd_6259180 : Nat := 4983230072969 + 3 ^ 40 * 6259180 * 2
def baseEnd_6259180 : Nat := 3213967843008926163164561

theorem tailTrace_6259180 : CollatzResearch.WordTrace tailWord_6259180 prefixEnd_6259180 3213967843008926163164561 := by
  unfold tailWord_6259180
  simp only [CollatzResearch.WordTrace]
  refine ⟨114145524732033658841519497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152194032976044878455359329 114145524732033658841519497)
  ·
    refine ⟨85609143549025244131139623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114145524732033658841519497 85609143549025244131139623)
    ·
      refine ⟨128413715323537866196709435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85609143549025244131139623 128413715323537866196709435)
      ·
        refine ⟨192620572985306799295064153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128413715323537866196709435 192620572985306799295064153)
        ·
          refine ⟨144465429738980099471298115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192620572985306799295064153 144465429738980099471298115)
          ·
            refine ⟨216698144608470149206947173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144465429738980099471298115 216698144608470149206947173)
            ·
              refine ⟨40630902114088152976302595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 216698144608470149206947173 40630902114088152976302595)
              ·
                refine ⟨60946353171132229464453893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40630902114088152976302595 60946353171132229464453893)
                ·
                  refine ⟨11427441219587293024585105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60946353171132229464453893 11427441219587293024585105)
                  ·
                    refine ⟨8570580914690469768438829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11427441219587293024585105 8570580914690469768438829)
                    ·
                      refine ⟨3213967843008926163164561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8570580914690469768438829 3213967843008926163164561)
                      ·
                        rfl

theorem cell23_6259180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 3].length) (baseStart_6259180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259180 prefixEnd_6259180 := by exact prefixLift 6259180
  have htrace : WordTrace (prefixWord ++ tailWord_6259180) baseStart_6259180 baseEnd_6259180 := by
    simpa [prefixWord, tailWord_6259180, baseEnd_6259180] using wordTrace_append hprefix tailTrace_6259180
  have hstable : (prefixWord ++ tailWord_6259180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259180).length < 2 ^ (prefixWord ++ tailWord_6259180).sum := by decide
  have hdescent : baseEnd_6259180 < baseStart_6259180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259187 : List Nat := [1, 1, 1, 2, 2, 2, 3, 6, 1, 4]
def baseStart_6259187 : Nat := 118140960795 + 6259187 * 2 ^ 59
def prefixEnd_6259187 : Nat := 4983230072969 + 3 ^ 40 * 6259187 * 2
def baseEnd_6259187 : Nat := 1071323812457835878592343

theorem tailTrace_6259187 : CollatzResearch.WordTrace tailWord_6259187 prefixEnd_6259187 1071323812457835878592343 := by
  unfold tailWord_6259187
  simp only [CollatzResearch.WordTrace]
  refine ⟨228291304775041957878543815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152194203183361305252362543 228291304775041957878543815)
  ·
    refine ⟨342436957162562936817815723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228291304775041957878543815 342436957162562936817815723)
    ·
      refine ⟨513655435743844405226723585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342436957162562936817815723 513655435743844405226723585)
      ·
        refine ⟨385241576807883303920042689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 513655435743844405226723585 385241576807883303920042689)
        ·
          refine ⟨288931182605912477940032017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385241576807883303920042689 288931182605912477940032017)
          ·
            refine ⟨216698386954434358455024013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288931182605912477940032017 216698386954434358455024013)
            ·
              refine ⟨81261895107912884420634005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216698386954434358455024013 81261895107912884420634005)
              ·
                refine ⟨3809151333183416457217219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81261895107912884420634005 3809151333183416457217219)
                ·
                  refine ⟨5713726999775124685825829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3809151333183416457217219 5713726999775124685825829)
                  ·
                    refine ⟨1071323812457835878592343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5713726999775124685825829 1071323812457835878592343)
                    ·
                      rfl

theorem cell23_6259187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6, 1, 4].length) (baseStart_6259187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259187 prefixEnd_6259187 := by exact prefixLift 6259187
  have htrace : WordTrace (prefixWord ++ tailWord_6259187) baseStart_6259187 baseEnd_6259187 := by
    simpa [prefixWord, tailWord_6259187, baseEnd_6259187] using wordTrace_append hprefix tailTrace_6259187
  have hstable : (prefixWord ++ tailWord_6259187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259187).length < 2 ^ (prefixWord ++ tailWord_6259187).sum := by decide
  have hdescent : baseEnd_6259187 < baseStart_6259187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259190 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6]
def baseStart_6259190 : Nat := 118140960795 + 6259190 * 2 ^ 59
def prefixEnd_6259190 : Nat := 4983230072969 + 3 ^ 40 * 6259190 * 2
def baseEnd_6259190 : Nat := 3213972977815471124039515

theorem tailTrace_6259190 : CollatzResearch.WordTrace tailWord_6259190 prefixEnd_6259190 3213972977815471124039515 := by
  unfold tailWord_6259190
  simp only [CollatzResearch.WordTrace]
  refine ⟨14268213387126943086931439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152194276129354059593935349 14268213387126943086931439)
  ·
    refine ⟨21402320080690414630397159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14268213387126943086931439 21402320080690414630397159)
    ·
      refine ⟨32103480121035621945595739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21402320080690414630397159 32103480121035621945595739)
      ·
        refine ⟨48155220181553432918393609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32103480121035621945595739 48155220181553432918393609)
        ·
          refine ⟨36116415136165074688795207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48155220181553432918393609 36116415136165074688795207)
          ·
            refine ⟨54174622704247612033192811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36116415136165074688795207 54174622704247612033192811)
            ·
              refine ⟨81261934056371418049789217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54174622704247612033192811 81261934056371418049789217)
              ·
                refine ⟨60946450542278563537341913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81261934056371418049789217 60946450542278563537341913)
                ·
                  refine ⟨45709837906708922653006435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60946450542278563537341913 45709837906708922653006435)
                  ·
                    refine ⟨68564756860063383979509653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45709837906708922653006435 68564756860063383979509653)
                    ·
                      refine ⟨3213972977815471124039515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68564756860063383979509653 3213972977815471124039515)
                      ·
                        rfl

theorem cell23_6259190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_6259190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259190 prefixEnd_6259190 := by exact prefixLift 6259190
  have htrace : WordTrace (prefixWord ++ tailWord_6259190) baseStart_6259190 baseEnd_6259190 := by
    simpa [prefixWord, tailWord_6259190, baseEnd_6259190] using wordTrace_append hprefix tailTrace_6259190
  have hstable : (prefixWord ++ tailWord_6259190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259190).length < 2 ^ (prefixWord ++ tailWord_6259190).sum := by decide
  have hdescent : baseEnd_6259190 < baseStart_6259190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259203 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 6]
def baseStart_6259203 : Nat := 118140960795 + 6259203 * 2 ^ 59
def prefixEnd_6259203 : Nat := 4983230072969 + 3 ^ 40 * 6259203 * 2
def baseEnd_6259203 : Nat := 3213979653063979573176955

theorem tailTrace_6259203 : CollatzResearch.WordTrace tailWord_6259203 prefixEnd_6259203 3213979653063979573176955 := by
  unfold tailWord_6259203
  simp only [CollatzResearch.WordTrace]
  refine ⟨228291888342983992611126263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152194592228655995074084175 228291888342983992611126263)
  ·
    refine ⟨342437832514475988916689395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228291888342983992611126263 342437832514475988916689395)
    ·
      refine ⟨513656748771713983375034093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342437832514475988916689395 513656748771713983375034093)
      ·
        refine ⟨192621280789392743765637785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 513656748771713983375034093 192621280789392743765637785)
        ·
          refine ⟨144465960592044557824228339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192621280789392743765637785 144465960592044557824228339)
          ·
            refine ⟨216698940888066836736342509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144465960592044557824228339 216698940888066836736342509)
            ·
              refine ⟨81262102833025063776128441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216698940888066836736342509 81262102833025063776128441)
              ·
                refine ⟨60946577124768797832096331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81262102833025063776128441 60946577124768797832096331)
                ·
                  refine ⟨91419865687153196748144497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60946577124768797832096331 91419865687153196748144497)
                  ·
                    refine ⟨68564899265364897561108373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91419865687153196748144497 68564899265364897561108373)
                    ·
                      refine ⟨3213979653063979573176955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68564899265364897561108373 3213979653063979573176955)
                      ·
                        rfl

theorem cell23_6259203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_6259203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259203 prefixEnd_6259203 := by exact prefixLift 6259203
  have htrace : WordTrace (prefixWord ++ tailWord_6259203) baseStart_6259203 baseEnd_6259203 := by
    simpa [prefixWord, tailWord_6259203, baseEnd_6259203] using wordTrace_append hprefix tailTrace_6259203
  have hstable : (prefixWord ++ tailWord_6259203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259203).length < 2 ^ (prefixWord ++ tailWord_6259203).sum := by decide
  have hdescent : baseEnd_6259203 < baseStart_6259203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259210 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 2, 5, 3]
def baseStart_6259210 : Nat := 118140960795 + 6259210 * 2 ^ 59
def prefixEnd_6259210 : Nat := 4983230072969 + 3 ^ 40 * 6259210 * 2
def baseEnd_6259210 : Nat := 3213983247428561045789423

theorem tailTrace_6259210 : CollatzResearch.WordTrace tailWord_6259210 prefixEnd_6259210 3213983247428561045789423 := by
  unfold tailWord_6259210
  simp only [CollatzResearch.WordTrace]
  refine ⟨57073035913489658201657771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152194762435972421871087389 57073035913489658201657771)
  ·
    refine ⟨85609553870234487302486657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57073035913489658201657771 85609553870234487302486657)
    ·
      refine ⟨64207165402675865476864993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85609553870234487302486657 64207165402675865476864993)
      ·
        refine ⟨48155374052006899107648745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64207165402675865476864993 48155374052006899107648745)
        ·
          refine ⟨36116530539005174330736559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48155374052006899107648745 36116530539005174330736559)
          ·
            refine ⟨54174795808507761496104839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36116530539005174330736559 54174795808507761496104839)
            ·
              refine ⟨81262193712761642244157259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54174795808507761496104839 81262193712761642244157259)
              ·
                refine ⟨121893290569142463366235889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81262193712761642244157259 121893290569142463366235889)
                ·
                  refine ⟨91419967926856847524676917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121893290569142463366235889 91419967926856847524676917)
                  ·
                    refine ⟨8570621993142829455438461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91419967926856847524676917 8570621993142829455438461)
                    ·
                      refine ⟨3213983247428561045789423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8570621993142829455438461 3213983247428561045789423)
                      ·
                        rfl

theorem cell23_6259210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_6259210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259210 prefixEnd_6259210 := by exact prefixLift 6259210
  have htrace : WordTrace (prefixWord ++ tailWord_6259210) baseStart_6259210 baseEnd_6259210 := by
    simpa [prefixWord, tailWord_6259210, baseEnd_6259210] using wordTrace_append hprefix tailTrace_6259210
  have hstable : (prefixWord ++ tailWord_6259210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259210).length < 2 ^ (prefixWord ++ tailWord_6259210).sum := by decide
  have hdescent : baseEnd_6259210 < baseStart_6259210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259237 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 4, 3, 2]
def baseStart_6259237 : Nat := 118140960795 + 6259237 * 2 ^ 59
def prefixEnd_6259237 : Nat := 4983230072969 + 3 ^ 40 * 6259237 * 2
def baseEnd_6259237 : Nat := 3213997111406232440151799

theorem tailTrace_6259237 : CollatzResearch.WordTrace tailWord_6259237 prefixEnd_6259237 3213997111406232440151799 := by
  unfold tailWord_6259237
  simp only [CollatzResearch.WordTrace]
  refine ⟨228293128424860816417863965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152195418949907210945242643 228293128424860816417863965)
  ·
    refine ⟨85609923159322806156698987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228293128424860816417863965 85609923159322806156698987)
    ·
      refine ⟨128414884738984209235048481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85609923159322806156698987 128414884738984209235048481)
      ·
        refine ⟨96311163554238156926286361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128414884738984209235048481 96311163554238156926286361)
        ·
          refine ⟨72233372665678617694714771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96311163554238156926286361 72233372665678617694714771)
          ·
            refine ⟨108350058998517926542072157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72233372665678617694714771 108350058998517926542072157)
            ·
              refine ⟨40631272124444222453277059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108350058998517926542072157 40631272124444222453277059)
              ·
                refine ⟨60946908186666333679915589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40631272124444222453277059 60946908186666333679915589)
                ·
                  refine ⟨11427545284999937564984173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60946908186666333679915589 11427545284999937564984173)
                  ·
                    refine ⟨4285329481874976586869065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11427545284999937564984173 4285329481874976586869065)
                    ·
                      refine ⟨3213997111406232440151799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4285329481874976586869065 3213997111406232440151799)
                      ·
                        rfl

theorem cell23_6259237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 3, 2].length) (baseStart_6259237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259237 prefixEnd_6259237 := by exact prefixLift 6259237
  have htrace : WordTrace (prefixWord ++ tailWord_6259237) baseStart_6259237 baseEnd_6259237 := by
    simpa [prefixWord, tailWord_6259237, baseEnd_6259237] using wordTrace_append hprefix tailTrace_6259237
  have hstable : (prefixWord ++ tailWord_6259237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259237).length < 2 ^ (prefixWord ++ tailWord_6259237).sum := by decide
  have hdescent : baseEnd_6259237 < baseStart_6259237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259244 : List Nat := [2, 2, 1, 1, 1, 2, 1, 8, 1, 1, 3]
def baseStart_6259244 : Nat := 118140960795 + 6259244 * 2 ^ 59
def prefixEnd_6259244 : Nat := 4983230072969 + 3 ^ 40 * 6259244 * 2
def baseEnd_6259244 : Nat := 3214000705770813912764267

theorem tailTrace_6259244 : CollatzResearch.WordTrace tailWord_6259244 prefixEnd_6259244 3214000705770813912764267 := by
  unfold tailWord_6259244
  simp only [CollatzResearch.WordTrace]
  refine ⟨114146691867917728306684393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152195589157223637742245857 114146691867917728306684393)
  ·
    refine ⟨85610018900938296230013295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114146691867917728306684393 85610018900938296230013295)
    ·
      refine ⟨128415028351407444345019943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85610018900938296230013295 128415028351407444345019943)
      ·
        refine ⟨192622542527111166517529915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128415028351407444345019943 192622542527111166517529915)
        ·
          refine ⟨288933813790666749776294873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192622542527111166517529915 288933813790666749776294873)
          ·
            refine ⟨216700360343000062332221155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288933813790666749776294873 216700360343000062332221155)
            ·
              refine ⟨325050540514500093498331733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216700360343000062332221155 325050540514500093498331733)
              ·
                refine ⟨3809186021654297970683575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 325050540514500093498331733 3809186021654297970683575)
                ·
                  refine ⟨5713779032481446956025363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3809186021654297970683575 5713779032481446956025363)
                  ·
                    refine ⟨8570668548722170434038045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5713779032481446956025363 8570668548722170434038045)
                    ·
                      refine ⟨3214000705770813912764267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8570668548722170434038045 3214000705770813912764267)
                      ·
                        rfl

theorem cell23_6259244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8, 1, 1, 3].length) (baseStart_6259244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259244 prefixEnd_6259244 := by exact prefixLift 6259244
  have htrace : WordTrace (prefixWord ++ tailWord_6259244) baseStart_6259244 baseEnd_6259244 := by
    simpa [prefixWord, tailWord_6259244, baseEnd_6259244] using wordTrace_append hprefix tailTrace_6259244
  have hstable : (prefixWord ++ tailWord_6259244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259244).length < 2 ^ (prefixWord ++ tailWord_6259244).sum := by decide
  have hdescent : baseEnd_6259244 < baseStart_6259244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259277 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 3, 6]
def baseStart_6259277 : Nat := 118140960795 + 6259277 * 2 ^ 59
def prefixEnd_6259277 : Nat := 4983230072969 + 3 ^ 40 * 6259277 * 2
def baseEnd_6259277 : Nat := 1071339216877470761217205

theorem tailTrace_6259277 : CollatzResearch.WordTrace tailWord_6259277 prefixEnd_6259277 1071339216877470761217205 := by
  unfold tailWord_6259277
  simp only [CollatzResearch.WordTrace]
  refine ⟨228294587344715903249320085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152196391563143935499546723 228294587344715903249320085)
  ·
    refine ⟨10701308781783557964811879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 228294587344715903249320085 10701308781783557964811879)
    ·
      refine ⟨16051963172675336947217819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10701308781783557964811879 16051963172675336947217819)
      ·
        refine ⟨24077944759013005420826729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16051963172675336947217819 24077944759013005420826729)
        ·
          refine ⟨18058458569259754065620047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24077944759013005420826729 18058458569259754065620047)
          ·
            refine ⟨27087687853889631098430071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18058458569259754065620047 27087687853889631098430071)
            ·
              refine ⟨40631531780834446647645107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27087687853889631098430071 40631531780834446647645107)
              ·
                refine ⟨60947297671251669971467661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40631531780834446647645107 60947297671251669971467661)
                ·
                  refine ⟨22855236626719376239300373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60947297671251669971467661 22855236626719376239300373)
                  ·
                    refine ⟨1071339216877470761217205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22855236626719376239300373 1071339216877470761217205)
                    ·
                      rfl

theorem cell23_6259277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_6259277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259277 prefixEnd_6259277 := by exact prefixLift 6259277
  have htrace : WordTrace (prefixWord ++ tailWord_6259277) baseStart_6259277 baseEnd_6259277 := by
    simpa [prefixWord, tailWord_6259277, baseEnd_6259277] using wordTrace_append hprefix tailTrace_6259277
  have hstable : (prefixWord ++ tailWord_6259277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259277).length < 2 ^ (prefixWord ++ tailWord_6259277).sum := by decide
  have hdescent : baseEnd_6259277 < baseStart_6259277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259314 : List Nat := [3, 2, 1, 2, 4, 1, 2, 1, 1, 2, 4]
def baseStart_6259314 : Nat := 118140960795 + 6259314 * 2 ^ 59
def prefixEnd_6259314 : Nat := 4983230072969 + 3 ^ 40 * 6259314 * 2
def baseEnd_6259314 : Nat := 3214036649416628638888945

theorem tailTrace_6259314 : CollatzResearch.WordTrace tailWord_6259314 prefixEnd_6259314 3214036649416628638888945 := by
  unfold tailWord_6259314
  simp only [CollatzResearch.WordTrace]
  refine ⟨57073984211395464642104249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152197291230387905712277997 57073984211395464642104249)
  ·
    refine ⟨42805488158546598481578187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57073984211395464642104249 42805488158546598481578187)
    ·
      refine ⟨64208232237819897722367281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42805488158546598481578187 64208232237819897722367281)
      ·
        refine ⟨48156174178364923291775461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64208232237819897722367281 48156174178364923291775461)
        ·
          refine ⟨9029282658443423117207899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48156174178364923291775461 9029282658443423117207899)
          ·
            refine ⟨13543923987665134675811849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9029282658443423117207899 13543923987665134675811849)
            ·
              refine ⟨10157942990748851006858887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13543923987665134675811849 10157942990748851006858887)
              ·
                refine ⟨15236914486123276510288331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10157942990748851006858887 15236914486123276510288331)
                ·
                  refine ⟨22855371729184914765432497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15236914486123276510288331 22855371729184914765432497)
                  ·
                    refine ⟨17141528796888686074074373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22855371729184914765432497 17141528796888686074074373)
                    ·
                      refine ⟨3214036649416628638888945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17141528796888686074074373 3214036649416628638888945)
                      ·
                        rfl

theorem cell23_6259314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_6259314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259314 prefixEnd_6259314 := by exact prefixLift 6259314
  have htrace : WordTrace (prefixWord ++ tailWord_6259314) baseStart_6259314 baseEnd_6259314 := by
    simpa [prefixWord, tailWord_6259314, baseEnd_6259314] using wordTrace_append hprefix tailTrace_6259314
  have hstable : (prefixWord ++ tailWord_6259314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259314).length < 2 ^ (prefixWord ++ tailWord_6259314).sum := by decide
  have hdescent : baseEnd_6259314 < baseStart_6259314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259318 : List Nat := [5, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2]
def baseStart_6259318 : Nat := 118140960795 + 6259318 * 2 ^ 59
def prefixEnd_6259318 : Nat := 4983230072969 + 3 ^ 40 * 6259318 * 2
def baseEnd_6259318 : Nat := 3214038703339246623238927

theorem tailTrace_6259318 : CollatzResearch.WordTrace tailWord_6259318 prefixEnd_6259318 3214038703339246623238927 := by
  unfold tailWord_6259318
  simp only [CollatzResearch.WordTrace]
  refine ⟨14268505171097960453222663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152197388491711578167708405 14268505171097960453222663)
  ·
    refine ⟨21402757756646940679833995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14268505171097960453222663 21402757756646940679833995)
    ·
      refine ⟨32104136634970411019750993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21402757756646940679833995 32104136634970411019750993)
      ·
        refine ⟨24078102476227808264813245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32104136634970411019750993 24078102476227808264813245)
        ·
          refine ⟨9029288428585428099304967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24078102476227808264813245 9029288428585428099304967)
          ·
            refine ⟨13543932642878142148957451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9029288428585428099304967 13543932642878142148957451)
            ·
              refine ⟨20315898964317213223436177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13543932642878142148957451 20315898964317213223436177)
              ·
                refine ⟨15236924223237909917577133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20315898964317213223436177 15236924223237909917577133)
                ·
                  refine ⟨5713846583714216219091425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15236924223237909917577133 5713846583714216219091425)
                  ·
                    refine ⟨4285384937785662164318569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5713846583714216219091425 4285384937785662164318569)
                    ·
                      refine ⟨3214038703339246623238927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4285384937785662164318569 3214038703339246623238927)
                      ·
                        rfl

theorem cell23_6259318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_6259318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259318 prefixEnd_6259318 := by exact prefixLift 6259318
  have htrace : WordTrace (prefixWord ++ tailWord_6259318) baseStart_6259318 baseEnd_6259318 := by
    simpa [prefixWord, tailWord_6259318, baseEnd_6259318] using wordTrace_append hprefix tailTrace_6259318
  have hstable : (prefixWord ++ tailWord_6259318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259318).length < 2 ^ (prefixWord ++ tailWord_6259318).sum := by decide
  have hdescent : baseEnd_6259318 < baseStart_6259318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259338 : List Nat := [3, 1, 2, 3, 3, 2, 2, 1, 1, 2, 3]
def baseStart_6259338 : Nat := 118140960795 + 6259338 * 2 ^ 59
def prefixEnd_6259338 : Nat := 4983230072969 + 3 ^ 40 * 6259338 * 2
def baseEnd_6259338 : Nat := 3214048972952336544988835

theorem tailTrace_6259338 : CollatzResearch.WordTrace tailWord_6259338 prefixEnd_6259338 3214048972952336544988835 := by
  unfold tailWord_6259338
  simp only [CollatzResearch.WordTrace]
  refine ⟨57074203049373727666822667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152197874798329940444860445 57074203049373727666822667)
  ·
    refine ⟨85611304574060591500234001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57074203049373727666822667 85611304574060591500234001)
    ·
      refine ⟨64208478430545443625175501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85611304574060591500234001 64208478430545443625175501)
      ·
        refine ⟨24078179411454541359440813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64208478430545443625175501 24078179411454541359440813)
        ·
          refine ⟨9029317279295453009790305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24078179411454541359440813 9029317279295453009790305)
          ·
            refine ⟨6771987959471589757342729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9029317279295453009790305 6771987959471589757342729)
            ·
              refine ⟨5078990969603692318007047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6771987959471589757342729 5078990969603692318007047)
              ·
                refine ⟨7618486454405538477010571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5078990969603692318007047 7618486454405538477010571)
                ·
                  refine ⟨11427729681608307715515857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7618486454405538477010571 11427729681608307715515857)
                  ·
                    refine ⟨8570797261206230786636893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11427729681608307715515857 8570797261206230786636893)
                    ·
                      refine ⟨3214048972952336544988835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8570797261206230786636893 3214048972952336544988835)
                      ·
                        rfl

theorem cell23_6259338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_6259338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259338 prefixEnd_6259338 := by exact prefixLift 6259338
  have htrace : WordTrace (prefixWord ++ tailWord_6259338) baseStart_6259338 baseEnd_6259338 := by
    simpa [prefixWord, tailWord_6259338, baseEnd_6259338] using wordTrace_append hprefix tailTrace_6259338
  have hstable : (prefixWord ++ tailWord_6259338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259338).length < 2 ^ (prefixWord ++ tailWord_6259338).sum := by decide
  have hdescent : baseEnd_6259338 < baseStart_6259338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259340 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 1, 5, 4]
def baseStart_6259340 : Nat := 118140960795 + 6259340 * 2 ^ 59
def prefixEnd_6259340 : Nat := 4983230072969 + 3 ^ 40 * 6259340 * 2
def baseEnd_6259340 : Nat := 3214049999913645537163825

theorem tailTrace_6259340 : CollatzResearch.WordTrace tailWord_6259340 prefixEnd_6259340 3214049999913645537163825 := by
  unfold tailWord_6259340
  simp only [CollatzResearch.WordTrace]
  refine ⟨114148442571743832504431737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152197923428991776672575649 114148442571743832504431737)
  ·
    refine ⟨85611331928807874378323803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114148442571743832504431737 85611331928807874378323803)
    ·
      refine ⟨128416997893211811567485705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85611331928807874378323803 128416997893211811567485705)
      ·
        refine ⟨96312748419908858675614279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128416997893211811567485705 96312748419908858675614279)
        ·
          refine ⟨144469122629863288013421419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96312748419908858675614279 144469122629863288013421419)
          ·
            refine ⟨216703683944794932020132129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144469122629863288013421419 216703683944794932020132129)
            ·
              refine ⟨162527762958596199015099097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216703683944794932020132129 162527762958596199015099097)
              ·
                refine ⟨121895822218947149261324323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162527762958596199015099097 121895822218947149261324323)
                ·
                  refine ⟨182843733328420723891986485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121895822218947149261324323 182843733328420723891986485)
                  ·
                    refine ⟨17141599999539442864873733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 182843733328420723891986485 17141599999539442864873733)
                    ·
                      refine ⟨3214049999913645537163825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17141599999539442864873733 3214049999913645537163825)
                      ·
                        rfl

theorem cell23_6259340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_6259340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259340 prefixEnd_6259340 := by exact prefixLift 6259340
  have htrace : WordTrace (prefixWord ++ tailWord_6259340) baseStart_6259340 baseEnd_6259340 := by
    simpa [prefixWord, tailWord_6259340, baseEnd_6259340] using wordTrace_append hprefix tailTrace_6259340
  have hstable : (prefixWord ++ tailWord_6259340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259340).length < 2 ^ (prefixWord ++ tailWord_6259340).sum := by decide
  have hdescent : baseEnd_6259340 < baseStart_6259340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259425 : List Nat := [1, 2, 3, 1, 4, 3, 2, 1, 2, 2, 2]
def baseStart_6259425 : Nat := 118140960795 + 6259425 * 2 ^ 59
def prefixEnd_6259425 : Nat := 4983230072969 + 3 ^ 40 * 6259425 * 2
def baseEnd_6259425 : Nat := 3214093645769277704600935

theorem tailTrace_6259425 : CollatzResearch.WordTrace tailWord_6259425 prefixEnd_6259425 3214093645769277704600935 := by
  unfold tailWord_6259425
  simp only [CollatzResearch.WordTrace]
  refine ⟨228299985348179724525707729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152199990232119816350471819 228299985348179724525707729)
  ·
    refine ⟨171224989011134793394280797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228299985348179724525707729 171224989011134793394280797)
    ·
      refine ⟨64209370879175547522855299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171224989011134793394280797 64209370879175547522855299)
      ·
        refine ⟨96314056318763321284282949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64209370879175547522855299 96314056318763321284282949)
        ·
          refine ⟨18058885559768122740803053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96314056318763321284282949 18058885559768122740803053)
          ·
            refine ⟨6772082084913046027801145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18058885559768122740803053 6772082084913046027801145)
            ·
              refine ⟨5079061563684784520850859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6772082084913046027801145 5079061563684784520850859)
              ·
                refine ⟨7618592345527176781276289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5079061563684784520850859 7618592345527176781276289)
                ·
                  refine ⟨5713944259145382585957217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7618592345527176781276289 5713944259145382585957217)
                  ·
                    refine ⟨4285458194359036939467913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5713944259145382585957217 4285458194359036939467913)
                    ·
                      refine ⟨3214093645769277704600935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4285458194359036939467913 3214093645769277704600935)
                      ·
                        rfl

theorem cell23_6259425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 2, 2, 2].length) (baseStart_6259425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259425 prefixEnd_6259425 := by exact prefixLift 6259425
  have htrace : WordTrace (prefixWord ++ tailWord_6259425) baseStart_6259425 baseEnd_6259425 := by
    simpa [prefixWord, tailWord_6259425, baseEnd_6259425] using wordTrace_append hprefix tailTrace_6259425
  have hstable : (prefixWord ++ tailWord_6259425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259425).length < 2 ^ (prefixWord ++ tailWord_6259425).sum := by decide
  have hdescent : baseEnd_6259425 < baseStart_6259425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259437 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 1, 1, 7]
def baseStart_6259437 : Nat := 118140960795 + 6259437 * 2 ^ 59
def prefixEnd_6259437 : Nat := 4983230072969 + 3 ^ 40 * 6259437 * 2
def baseEnd_6259437 : Nat := 3214099807537131657650879

theorem tailTrace_6259437 : CollatzResearch.WordTrace tailWord_6259437 prefixEnd_6259437 3214099807537131657650879 := by
  unfold tailWord_6259437
  simp only [CollatzResearch.WordTrace]
  refine ⟨228300423024136250575144565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152200282016090833716763043 228300423024136250575144565)
  ·
    refine ⟨21403164658512773491419803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 228300423024136250575144565 21403164658512773491419803)
    ·
      refine ⟨32104746987769160237129705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21403164658512773491419803 32104746987769160237129705)
      ·
        refine ⟨24078560240826870177847279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32104746987769160237129705 24078560240826870177847279)
        ·
          refine ⟨36117840361240305266770919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24078560240826870177847279 36117840361240305266770919)
          ·
            refine ⟨54176760541860457900156379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36117840361240305266770919 54176760541860457900156379)
            ·
              refine ⟨81265140812790686850234569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54176760541860457900156379 81265140812790686850234569)
              ·
                refine ⟨60948855609593015137675927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81265140812790686850234569 60948855609593015137675927)
                ·
                  refine ⟨91423283414389522706513891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60948855609593015137675927 91423283414389522706513891)
                  ·
                    refine ⟨137134925121584284059770837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 91423283414389522706513891 137134925121584284059770837)
                    ·
                      refine ⟨3214099807537131657650879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 137134925121584284059770837 3214099807537131657650879)
                      ·
                        rfl

theorem cell23_6259437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_6259437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259437 prefixEnd_6259437 := by exact prefixLift 6259437
  have htrace : WordTrace (prefixWord ++ tailWord_6259437) baseStart_6259437 baseEnd_6259437 := by
    simpa [prefixWord, tailWord_6259437, baseEnd_6259437] using wordTrace_append hprefix tailTrace_6259437
  have hstable : (prefixWord ++ tailWord_6259437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259437).length < 2 ^ (prefixWord ++ tailWord_6259437).sum := by decide
  have hdescent : baseEnd_6259437 < baseStart_6259437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259454 : List Nat := [4, 2, 2, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_6259454 : Nat := 118140960795 + 6259454 * 2 ^ 59
def prefixEnd_6259454 : Nat := 4983230072969 + 3 ^ 40 * 6259454 * 2
def baseEnd_6259454 : Nat := 3214108536708258091138301

theorem tailTrace_6259454 : CollatzResearch.WordTrace tailWord_6259454 prefixEnd_6259454 3214108536708258091138301 := by
  unfold tailWord_6259454
  simp only [CollatzResearch.WordTrace]
  refine ⟨28537630383134332809814177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152200695376716441652342277 28537630383134332809814177)
  ·
    refine ⟨21403222787350749607360633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28537630383134332809814177 21403222787350749607360633)
    ·
      refine ⟨16052417090513062205520475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21403222787350749607360633 16052417090513062205520475)
      ·
        refine ⟨24078625635769593308280713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16052417090513062205520475 24078625635769593308280713)
        ·
          refine ⟨18058969226827194981210535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24078625635769593308280713 18058969226827194981210535)
          ·
            refine ⟨27088453840240792471815803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18058969226827194981210535 27088453840240792471815803)
            ·
              refine ⟨40632680760361188707723705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27088453840240792471815803 40632680760361188707723705)
              ·
                refine ⟨30474510570270891530792779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40632680760361188707723705 30474510570270891530792779)
                ·
                  refine ⟨45711765855406337296189169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30474510570270891530792779 45711765855406337296189169)
                  ·
                    refine ⟨34283824391554752972141877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45711765855406337296189169 34283824391554752972141877)
                    ·
                      refine ⟨3214108536708258091138301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34283824391554752972141877 3214108536708258091138301)
                      ·
                        rfl

theorem cell23_6259454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_6259454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259454 prefixEnd_6259454 := by exact prefixLift 6259454
  have htrace : WordTrace (prefixWord ++ tailWord_6259454) baseStart_6259454 baseEnd_6259454 := by
    simpa [prefixWord, tailWord_6259454, baseEnd_6259454] using wordTrace_append hprefix tailTrace_6259454
  have hstable : (prefixWord ++ tailWord_6259454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259454).length < 2 ^ (prefixWord ++ tailWord_6259454).sum := by decide
  have hdescent : baseEnd_6259454 < baseStart_6259454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259464 : List Nat := [2, 1, 3, 2, 2, 2, 2, 2, 2, 1, 4]
def baseStart_6259464 : Nat := 118140960795 + 6259464 * 2 ^ 59
def prefixEnd_6259464 : Nat := 4983230072969 + 3 ^ 40 * 6259464 * 2
def baseEnd_6259464 : Nat := 3214113671514803052013255

theorem tailTrace_6259464 : CollatzResearch.WordTrace tailWord_6259464 prefixEnd_6259464 3214113671514803052013255 := by
  unfold tailWord_6259464
  simp only [CollatzResearch.WordTrace]
  refine ⟨114150703897519217093188723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152200938530025622790918297 114150703897519217093188723)
  ·
    refine ⟨171226055846278825639783085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114150703897519217093188723 171226055846278825639783085)
    ·
      refine ⟨64209770942354559614918657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171226055846278825639783085 64209770942354559614918657)
      ·
        refine ⟨48157328206765919711188993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64209770942354559614918657 48157328206765919711188993)
        ·
          refine ⟨36117996155074439783391745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48157328206765919711188993 36117996155074439783391745)
          ·
            refine ⟨27088497116305829837543809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36117996155074439783391745 27088497116305829837543809)
            ·
              refine ⟨20316372837229372378157857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27088497116305829837543809 20316372837229372378157857)
              ·
                refine ⟨15237279627922029283618393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20316372837229372378157857 15237279627922029283618393)
                ·
                  refine ⟨11427959720941521962713795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15237279627922029283618393 11427959720941521962713795)
                  ·
                    refine ⟨17141939581412282944070693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11427959720941521962713795 17141939581412282944070693)
                    ·
                      refine ⟨3214113671514803052013255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17141939581412282944070693 3214113671514803052013255)
                      ·
                        rfl

theorem cell23_6259464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_6259464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259464 prefixEnd_6259464 := by exact prefixLift 6259464
  have htrace : WordTrace (prefixWord ++ tailWord_6259464) baseStart_6259464 baseEnd_6259464 := by
    simpa [prefixWord, tailWord_6259464, baseEnd_6259464] using wordTrace_append hprefix tailTrace_6259464
  have hstable : (prefixWord ++ tailWord_6259464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259464).length < 2 ^ (prefixWord ++ tailWord_6259464).sum := by decide
  have hdescent : baseEnd_6259464 < baseStart_6259464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259467 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 3, 4, 3]
def baseStart_6259467 : Nat := 118140960795 + 6259467 * 2 ^ 59
def prefixEnd_6259467 : Nat := 4983230072969 + 3 ^ 40 * 6259467 * 2
def baseEnd_6259467 : Nat := 3214115211956766540275741

theorem tailTrace_6259467 : CollatzResearch.WordTrace tailWord_6259467 prefixEnd_6259467 3214115211956766540275741 := by
  unfold tailWord_6259467
  simp only [CollatzResearch.WordTrace]
  refine ⟨228301517214027565698736655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152201011476018377132491103 228301517214027565698736655)
  ·
    refine ⟨342452275821041348548104983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228301517214027565698736655 342452275821041348548104983)
    ·
      refine ⟨513678413731562022822157475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342452275821041348548104983 513678413731562022822157475)
      ·
        refine ⟨770517620597343034233236213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513678413731562022822157475 770517620597343034233236213)
        ·
          refine ⟨72236026931000909459365895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 770517620597343034233236213 72236026931000909459365895)
          ·
            refine ⟨108354040396501364189048843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72236026931000909459365895 108354040396501364189048843)
            ·
              refine ⟨162531060594752046283573265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108354040396501364189048843 162531060594752046283573265)
              ·
                refine ⟨121898295446064034712679949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162531060594752046283573265 121898295446064034712679949)
                ·
                  refine ⟨45711860792274013017254981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121898295446064034712679949 45711860792274013017254981)
                  ·
                    refine ⟨8570973898551377440735309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45711860792274013017254981 8570973898551377440735309)
                    ·
                      refine ⟨3214115211956766540275741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8570973898551377440735309 3214115211956766540275741)
                      ·
                        rfl

theorem cell23_6259467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 4, 3].length) (baseStart_6259467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259467 prefixEnd_6259467 := by exact prefixLift 6259467
  have htrace : WordTrace (prefixWord ++ tailWord_6259467) baseStart_6259467 baseEnd_6259467 := by
    simpa [prefixWord, tailWord_6259467, baseEnd_6259467] using wordTrace_append hprefix tailTrace_6259467
  have hstable : (prefixWord ++ tailWord_6259467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259467).length < 2 ^ (prefixWord ++ tailWord_6259467).sum := by decide
  have hdescent : baseEnd_6259467 < baseStart_6259467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259497 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 2, 5, 3]
def baseStart_6259497 : Nat := 118140960795 + 6259497 * 2 ^ 59
def prefixEnd_6259497 : Nat := 4983230072969 + 3 ^ 40 * 6259497 * 2
def baseEnd_6259497 : Nat := 3214130616376401422900603

theorem tailTrace_6259497 : CollatzResearch.WordTrace tailWord_6259497 prefixEnd_6259497 3214130616376401422900603 := by
  unfold tailWord_6259497
  simp only [CollatzResearch.WordTrace]
  refine ⟨228302611403918880822328745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152201740935945920548219163 228302611403918880822328745)
  ·
    refine ⟨171226958552939160616746559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228302611403918880822328745 171226958552939160616746559)
    ·
      refine ⟨256840437829408740925119839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171226958552939160616746559 256840437829408740925119839)
      ·
        refine ⟨385260656744113111387679759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256840437829408740925119839 385260656744113111387679759)
        ·
          refine ⟨577890985116169667081519639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385260656744113111387679759 577890985116169667081519639)
          ·
            refine ⟨866836477674254500622279459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577890985116169667081519639 866836477674254500622279459)
            ·
              refine ⟨1300254716511381750933419189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 866836477674254500622279459 1300254716511381750933419189)
              ·
                refine ⟨121898879672942039150008049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1300254716511381750933419189 121898879672942039150008049)
                ·
                  refine ⟨91424159754706529362506037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121898879672942039150008049 91424159754706529362506037)
                  ·
                    refine ⟨8571014977003737127734941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91424159754706529362506037 8571014977003737127734941)
                    ·
                      refine ⟨3214130616376401422900603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8571014977003737127734941 3214130616376401422900603)
                      ·
                        rfl

theorem cell23_6259497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 5, 3].length) (baseStart_6259497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259497 prefixEnd_6259497 := by exact prefixLift 6259497
  have htrace : WordTrace (prefixWord ++ tailWord_6259497) baseStart_6259497 baseEnd_6259497 := by
    simpa [prefixWord, tailWord_6259497, baseEnd_6259497] using wordTrace_append hprefix tailTrace_6259497
  have hstable : (prefixWord ++ tailWord_6259497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259497).length < 2 ^ (prefixWord ++ tailWord_6259497).sum := by decide
  have hdescent : baseEnd_6259497 < baseStart_6259497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259521 : List Nat := [1, 2, 5, 3, 1, 1, 1, 1, 8]
def baseStart_6259521 : Nat := 118140960795 + 6259521 * 2 ^ 59
def prefixEnd_6259521 : Nat := 4983230072969 + 3 ^ 40 * 6259521 * 2
def baseEnd_6259521 : Nat := 357126993323567703222277

theorem tailTrace_6259521 : CollatzResearch.WordTrace tailWord_6259521 prefixEnd_6259521 357126993323567703222277 := by
  unfold tailWord_6259521
  simp only [CollatzResearch.WordTrace]
  refine ⟨228303486755831932921202417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152202324503887955280801611 228303486755831932921202417)
  ·
    refine ⟨171227615066873949690901813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228303486755831932921202417 171227615066873949690901813)
    ·
      refine ⟨16052588912519432783522045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 171227615066873949690901813 16052588912519432783522045)
      ·
        refine ⟨6019720842194787293820767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16052588912519432783522045 6019720842194787293820767)
        ·
          refine ⟨9029581263292180940731151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6019720842194787293820767 9029581263292180940731151)
          ·
            refine ⟨13544371894938271411096727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9029581263292180940731151 13544371894938271411096727)
            ·
              refine ⟨20316557842407407116645091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13544371894938271411096727 20316557842407407116645091)
              ·
                refine ⟨30474836763611110674967637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20316557842407407116645091 30474836763611110674967637)
                ·
                  refine ⟨357126993323567703222277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30474836763611110674967637 357126993323567703222277)
                  ·
                    rfl

theorem cell23_6259521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 8].length) (baseStart_6259521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259521 prefixEnd_6259521 := by exact prefixLift 6259521
  have htrace : WordTrace (prefixWord ++ tailWord_6259521) baseStart_6259521 baseEnd_6259521 := by
    simpa [prefixWord, tailWord_6259521, baseEnd_6259521] using wordTrace_append hprefix tailTrace_6259521
  have hstable : (prefixWord ++ tailWord_6259521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259521).length < 2 ^ (prefixWord ++ tailWord_6259521).sum := by decide
  have hdescent : baseEnd_6259521 < baseStart_6259521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259548 : List Nat := [2, 2, 4, 2, 1, 1, 2, 2, 3, 1, 3]
def baseStart_6259548 : Nat := 118140960795 + 6259548 * 2 ^ 59
def prefixEnd_6259548 : Nat := 4983230072969 + 3 ^ 40 * 6259548 * 2
def baseEnd_6259548 : Nat := 3214156803889780723362869

theorem tailTrace_6259548 : CollatzResearch.WordTrace tailWord_6259548 prefixEnd_6259548 3214156803889780723362869 := by
  unfold tailWord_6259548
  simp only [CollatzResearch.WordTrace]
  refine ⟨114152235763367058266217649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152202981017822744354956865 114152235763367058266217649)
  ·
    refine ⟨85614176822525293699663237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114152235763367058266217649 85614176822525293699663237)
    ·
      refine ⟨16052658154223492568686857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85614176822525293699663237 16052658154223492568686857)
      ·
        refine ⟨12039493615667619426515143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16052658154223492568686857 12039493615667619426515143)
        ·
          refine ⟨18059240423501429139772715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12039493615667619426515143 18059240423501429139772715)
          ·
            refine ⟨27088860635252143709659073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18059240423501429139772715 27088860635252143709659073)
            ·
              refine ⟨20316645476439107782244305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27088860635252143709659073 20316645476439107782244305)
              ·
                refine ⟨15237484107329330836683229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20316645476439107782244305 15237484107329330836683229)
                ·
                  refine ⟨5714056540248499063756211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15237484107329330836683229 5714056540248499063756211)
                  ·
                    refine ⟨8571084810372748595634317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5714056540248499063756211 8571084810372748595634317)
                    ·
                      refine ⟨3214156803889780723362869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8571084810372748595634317 3214156803889780723362869)
                      ·
                        rfl

theorem cell23_6259548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_6259548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259548 prefixEnd_6259548 := by exact prefixLift 6259548
  have htrace : WordTrace (prefixWord ++ tailWord_6259548) baseStart_6259548 baseEnd_6259548 := by
    simpa [prefixWord, tailWord_6259548, baseEnd_6259548] using wordTrace_append hprefix tailTrace_6259548
  have hstable : (prefixWord ++ tailWord_6259548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259548).length < 2 ^ (prefixWord ++ tailWord_6259548).sum := by decide
  have hdescent : baseEnd_6259548 < baseStart_6259548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259564 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 6, 4]
def baseStart_6259564 : Nat := 118140960795 + 6259564 * 2 ^ 59
def prefixEnd_6259564 : Nat := 4983230072969 + 3 ^ 40 * 6259564 * 2
def baseEnd_6259564 : Nat := 1071388339860084220254265

theorem tailTrace_6259564 : CollatzResearch.WordTrace tailWord_6259564 prefixEnd_6259564 1071388339860084220254265 := by
  unfold tailWord_6259564
  simp only [CollatzResearch.WordTrace]
  refine ⟨114152527547338075632508873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152203370063117434176678497 114152527547338075632508873)
  ·
    refine ⟨85614395660503556724381655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114152527547338075632508873 85614395660503556724381655)
    ·
      refine ⟨128421593490755335086572483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85614395660503556724381655 128421593490755335086572483)
      ·
        refine ⟨192632390236133002629858725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128421593490755335086572483 192632390236133002629858725)
        ·
          refine ⟨36118573169274937993098511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192632390236133002629858725 36118573169274937993098511)
          ·
            refine ⟨54177859753912406989647767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36118573169274937993098511 54177859753912406989647767)
            ·
              refine ⟨81266789630868610484471651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54177859753912406989647767 81266789630868610484471651)
              ·
                refine ⟨121900184446302915726707477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81266789630868610484471651 121900184446302915726707477)
                ·
                  refine ⟨5714071145920449174689413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 121900184446302915726707477 5714071145920449174689413)
                  ·
                    refine ⟨1071388339860084220254265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5714071145920449174689413 1071388339860084220254265)
                    ·
                      rfl

theorem cell23_6259564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 4].length) (baseStart_6259564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259564 prefixEnd_6259564 := by exact prefixLift 6259564
  have htrace : WordTrace (prefixWord ++ tailWord_6259564) baseStart_6259564 baseEnd_6259564 := by
    simpa [prefixWord, tailWord_6259564, baseEnd_6259564] using wordTrace_append hprefix tailTrace_6259564
  have hstable : (prefixWord ++ tailWord_6259564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259564).length < 2 ^ (prefixWord ++ tailWord_6259564).sum := by decide
  have hdescent : baseEnd_6259564 < baseStart_6259564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259571 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 5, 2, 2]
def baseStart_6259571 : Nat := 118140960795 + 6259571 * 2 ^ 59
def prefixEnd_6259571 : Nat := 4983230072969 + 3 ^ 40 * 6259571 * 2
def baseEnd_6259571 : Nat := 3214168613944834133375263

theorem tailTrace_6259571 : CollatzResearch.WordTrace tailWord_6259571 prefixEnd_6259571 3214168613944834133375263 := by
  unfold tailWord_6259571
  simp only [CollatzResearch.WordTrace]
  refine ⟨228305310405650791460522567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152203540270433860973681711 228305310405650791460522567)
  ·
    refine ⟨342457965608476187190783851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228305310405650791460522567 342457965608476187190783851)
    ·
      refine ⟨513686948412714280786175777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342457965608476187190783851 513686948412714280786175777)
      ·
        refine ⟨385265211309535710589631833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 513686948412714280786175777 385265211309535710589631833)
        ·
          refine ⟨288948908482151782942223875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385265211309535710589631833 288948908482151782942223875)
          ·
            refine ⟨433423362723227674413335813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288948908482151782942223875 433423362723227674413335813)
            ·
              refine ⟨81266880510605188952500465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 433423362723227674413335813 81266880510605188952500465)
              ·
                refine ⟨60950160382953891714375349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81266880510605188952500465 60950160382953891714375349)
                ·
                  refine ⟨5714077535901927348222689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60950160382953891714375349 5714077535901927348222689)
                  ·
                    refine ⟨4285558151926445511167017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5714077535901927348222689 4285558151926445511167017)
                    ·
                      refine ⟨3214168613944834133375263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4285558151926445511167017 3214168613944834133375263)
                      ·
                        rfl

theorem cell23_6259571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 5, 2, 2].length) (baseStart_6259571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259571 prefixEnd_6259571 := by exact prefixLift 6259571
  have htrace : WordTrace (prefixWord ++ tailWord_6259571) baseStart_6259571 baseEnd_6259571 := by
    simpa [prefixWord, tailWord_6259571, baseEnd_6259571] using wordTrace_append hprefix tailTrace_6259571
  have hstable : (prefixWord ++ tailWord_6259571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259571).length < 2 ^ (prefixWord ++ tailWord_6259571).sum := by decide
  have hdescent : baseEnd_6259571 < baseStart_6259571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259577 : List Nat := [1, 2, 1, 3, 2, 3, 11]
def baseStart_6259577 : Nat := 118140960795 + 6259577 * 2 ^ 59
def prefixEnd_6259577 : Nat := 4983230072969 + 3 ^ 40 * 6259577 * 2
def baseEnd_6259577 : Nat := 39681132034922976665435

theorem tailTrace_6259577 : CollatzResearch.WordTrace tailWord_6259577 prefixEnd_6259577 39681132034922976665435 := by
  unfold tailWord_6259577
  simp only [CollatzResearch.WordTrace]
  refine ⟨228305529243629054485240985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152203686162419369656827323 228305529243629054485240985)
  ·
    refine ⟨171229146932721790863930739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228305529243629054485240985 171229146932721790863930739)
    ·
      refine ⟨256843720399082686295896109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171229146932721790863930739 256843720399082686295896109)
      ·
        refine ⟨96316395149656007360961041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256843720399082686295896109 96316395149656007360961041)
        ·
          refine ⟨72237296362242005520720781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96316395149656007360961041 72237296362242005520720781)
          ·
            refine ⟨27088986135840752070270293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72237296362242005520720781 27088986135840752070270293)
            ·
              refine ⟨39681132034922976665435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 27088986135840752070270293 39681132034922976665435)
              ·
                rfl

theorem cell23_6259577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 11].length) (baseStart_6259577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259577 prefixEnd_6259577 := by exact prefixLift 6259577
  have htrace : WordTrace (prefixWord ++ tailWord_6259577) baseStart_6259577 baseEnd_6259577 := by
    simpa [prefixWord, tailWord_6259577, baseEnd_6259577] using wordTrace_append hprefix tailTrace_6259577
  have hstable : (prefixWord ++ tailWord_6259577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259577).length < 2 ^ (prefixWord ++ tailWord_6259577).sum := by decide
  have hdescent : baseEnd_6259577 < baseStart_6259577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259582 : List Nat := [4, 2, 3, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_6259582 : Nat := 118140960795 + 6259582 * 2 ^ 59
def prefixEnd_6259582 : Nat := 4983230072969 + 3 ^ 40 * 6259582 * 2
def baseEnd_6259582 : Nat := 3214174262232033590337713

theorem tailTrace_6259582 : CollatzResearch.WordTrace tailWord_6259582 prefixEnd_6259582 3214174262232033590337713 := by
  unfold tailWord_6259582
  simp only [CollatzResearch.WordTrace]
  refine ⟨28538213951076367542396625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152203807739073960226115333 28538213951076367542396625)
  ·
    refine ⟨21403660463307275656797469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28538213951076367542396625 21403660463307275656797469)
    ·
      refine ⟨8026372673740228371299051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21403660463307275656797469 8026372673740228371299051)
      ·
        refine ⟨12039559010610342556948577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8026372673740228371299051 12039559010610342556948577)
        ·
          refine ⟨9029669257957756917711433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12039559010610342556948577 9029669257957756917711433)
          ·
            refine ⟨6772251943468317688283575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9029669257957756917711433 6772251943468317688283575)
            ·
              refine ⟨10158377915202476532425363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6772251943468317688283575 10158377915202476532425363)
              ·
                refine ⟨15237566872803714798638045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10158377915202476532425363 15237566872803714798638045)
                ·
                  refine ⟨5714087577301393049489267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15237566872803714798638045 5714087577301393049489267)
                  ·
                    refine ⟨8571131365952089574233901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5714087577301393049489267 8571131365952089574233901)
                    ·
                      refine ⟨3214174262232033590337713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8571131365952089574233901 3214174262232033590337713)
                      ·
                        rfl

theorem cell23_6259582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_6259582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259582 prefixEnd_6259582 := by exact prefixLift 6259582
  have htrace : WordTrace (prefixWord ++ tailWord_6259582) baseStart_6259582 baseEnd_6259582 := by
    simpa [prefixWord, tailWord_6259582, baseEnd_6259582] using wordTrace_append hprefix tailTrace_6259582
  have hstable : (prefixWord ++ tailWord_6259582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259582).length < 2 ^ (prefixWord ++ tailWord_6259582).sum := by decide
  have hdescent : baseEnd_6259582 < baseStart_6259582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259594 : List Nat := [3, 1, 2, 4, 1, 1, 1, 10]
def baseStart_6259594 : Nat := 118140960795 + 6259594 * 2 ^ 59
def prefixEnd_6259594 : Nat := 4983230072969 + 3 ^ 40 * 6259594 * 2
def baseEnd_6259594 : Nat := 119043719407403242347691

theorem tailTrace_6259594 : CollatzResearch.WordTrace tailWord_6259594 prefixEnd_6259594 119043719407403242347691 := by
  unfold tailWord_6259594
  simp only [CollatzResearch.WordTrace]
  refine ⟨57076537321141866597152459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152204099523044977592406557 57076537321141866597152459)
  ·
    refine ⟨85614805981712799895728689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57076537321141866597152459 85614805981712799895728689)
    ·
      refine ⟨64211104486284599921796517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85614805981712799895728689 64211104486284599921796517)
      ·
        refine ⟨12039582091178362485336847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64211104486284599921796517 12039582091178362485336847)
        ·
          refine ⟨18059373136767543728005271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12039582091178362485336847 18059373136767543728005271)
          ·
            refine ⟨27089059705151315592007907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18059373136767543728005271 27089059705151315592007907)
            ·
              refine ⟨40633589557726973388011861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27089059705151315592007907 40633589557726973388011861)
              ·
                refine ⟨119043719407403242347691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40633589557726973388011861 119043719407403242347691)
                ·
                  rfl

theorem cell23_6259594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 10].length) (baseStart_6259594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259594 prefixEnd_6259594 := by exact prefixLift 6259594
  have htrace : WordTrace (prefixWord ++ tailWord_6259594) baseStart_6259594 baseEnd_6259594 := by
    simpa [prefixWord, tailWord_6259594, baseEnd_6259594] using wordTrace_append hprefix tailTrace_6259594
  have hstable : (prefixWord ++ tailWord_6259594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259594).length < 2 ^ (prefixWord ++ tailWord_6259594).sum := by decide
  have hdescent : baseEnd_6259594 < baseStart_6259594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259627 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 8]
def baseStart_6259627 : Nat := 118140960795 + 6259627 * 2 ^ 59
def prefixEnd_6259627 : Nat := 4983230072969 + 3 ^ 40 * 6259627 * 2
def baseEnd_6259627 : Nat := 3214197368861485914275005

theorem tailTrace_6259627 : CollatzResearch.WordTrace tailWord_6259627 prefixEnd_6259627 3214197368861485914275005 := by
  unfold tailWord_6259627
  simp only [CollatzResearch.WordTrace]
  refine ⟨228307352893447913024561135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152204901928965275349707423 228307352893447913024561135)
  ·
    refine ⟨342461029340171869536841703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228307352893447913024561135 342461029340171869536841703)
    ·
      refine ⟨513691544010257804305262555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342461029340171869536841703 513691544010257804305262555)
      ·
        refine ⟨770537316015386706457893833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513691544010257804305262555 770537316015386706457893833)
        ·
          refine ⟨577902987011540029843420375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 770537316015386706457893833 577902987011540029843420375)
          ·
            refine ⟨866854480517310044765130563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577902987011540029843420375 866854480517310044765130563)
            ·
              refine ⟨1300281720775965067147695845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 866854480517310044765130563 1300281720775965067147695845)
              ·
                refine ⟨243802822645493450090192971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1300281720775965067147695845 243802822645493450090192971)
                ·
                  refine ⟨365704233968240175135289457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243802822645493450090192971 365704233968240175135289457)
                  ·
                    refine ⟨274278175476180131351467093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 365704233968240175135289457 274278175476180131351467093)
                    ·
                      refine ⟨3214197368861485914275005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 274278175476180131351467093 3214197368861485914275005)
                      ·
                        rfl

theorem cell23_6259627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 8].length) (baseStart_6259627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259627 prefixEnd_6259627 := by exact prefixLift 6259627
  have htrace : WordTrace (prefixWord ++ tailWord_6259627) baseStart_6259627 baseEnd_6259627 := by
    simpa [prefixWord, tailWord_6259627, baseEnd_6259627] using wordTrace_append hprefix tailTrace_6259627
  have hstable : (prefixWord ++ tailWord_6259627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259627).length < 2 ^ (prefixWord ++ tailWord_6259627).sum := by decide
  have hdescent : baseEnd_6259627 < baseStart_6259627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259664 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 3]
def baseStart_6259664 : Nat := 118140960795 + 6259664 * 2 ^ 59
def prefixEnd_6259664 : Nat := 4983230072969 + 3 ^ 40 * 6259664 * 2
def baseEnd_6259664 : Nat := 3214216367645702269512335

theorem tailTrace_6259664 : CollatzResearch.WordTrace tailWord_6259664 prefixEnd_6259664 3214216367645702269512335 := by
  unfold tailWord_6259664
  simp only [CollatzResearch.WordTrace]
  refine ⟨114154351197156934171829023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152205801596209245562438697 114154351197156934171829023)
  ·
    refine ⟨171231526795735401257743535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114154351197156934171829023 171231526795735401257743535)
    ·
      refine ⟨256847290193603101886615303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171231526795735401257743535 256847290193603101886615303)
      ·
        refine ⟨385270935290404652829922955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256847290193603101886615303 385270935290404652829922955)
        ·
          refine ⟨577906402935606979244884433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385270935290404652829922955 577906402935606979244884433)
          ·
            refine ⟨433429802201705234433663325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 577906402935606979244884433 433429802201705234433663325)
            ·
              refine ⟨162536175825639462912623747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 433429802201705234433663325 162536175825639462912623747)
              ·
                refine ⟨243804263738459194368935621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162536175825639462912623747 243804263738459194368935621)
                ·
                  refine ⟨45713299450961098944175429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 243804263738459194368935621 45713299450961098944175429)
                  ·
                    refine ⟨8571243647055206052032893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45713299450961098944175429 8571243647055206052032893)
                    ·
                      refine ⟨3214216367645702269512335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8571243647055206052032893 3214216367645702269512335)
                      ·
                        rfl

theorem cell23_6259664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 3].length) (baseStart_6259664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259664 prefixEnd_6259664 := by exact prefixLift 6259664
  have htrace : WordTrace (prefixWord ++ tailWord_6259664) baseStart_6259664 baseEnd_6259664 := by
    simpa [prefixWord, tailWord_6259664, baseEnd_6259664] using wordTrace_append hprefix tailTrace_6259664
  have hstable : (prefixWord ++ tailWord_6259664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259664).length < 2 ^ (prefixWord ++ tailWord_6259664).sum := by decide
  have hdescent : baseEnd_6259664 < baseStart_6259664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259682 : List Nat := [3, 3, 3, 1, 1, 2, 1, 3, 1, 3, 2]
def baseStart_6259682 : Nat := 118140960795 + 6259682 * 2 ^ 59
def prefixEnd_6259682 : Nat := 4983230072969 + 3 ^ 40 * 6259682 * 2
def baseEnd_6259682 : Nat := 3214225610297483199087253

theorem tailTrace_6259682 : CollatzResearch.WordTrace tailWord_6259682 prefixEnd_6259682 3214225610297483199087253 := by
  unfold tailWord_6259682
  simp only [CollatzResearch.WordTrace]
  refine ⟨57077339727062164354453325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152206239272165771611875533 57077339727062164354453325)
  ·
    refine ⟨21404002397648311632919997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57077339727062164354453325 21404002397648311632919997)
    ·
      refine ⟨8026500899118116862344999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21404002397648311632919997 8026500899118116862344999)
      ·
        refine ⟨12039751348677175293517499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8026500899118116862344999 12039751348677175293517499)
        ·
          refine ⟨18059627023015762940276249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12039751348677175293517499 18059627023015762940276249)
          ·
            refine ⟨13544720267261822205207187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18059627023015762940276249 13544720267261822205207187)
            ·
              refine ⟨20317080400892733307810781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13544720267261822205207187 20317080400892733307810781)
              ·
                refine ⟨7618905150334774990429043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20317080400892733307810781 7618905150334774990429043)
                ·
                  refine ⟨11428357725502162485643565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7618905150334774990429043 11428357725502162485643565)
                  ·
                    refine ⟨4285634147063310932116337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11428357725502162485643565 4285634147063310932116337)
                    ·
                      refine ⟨3214225610297483199087253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4285634147063310932116337 3214225610297483199087253)
                      ·
                        rfl

theorem cell23_6259682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_6259682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259682 prefixEnd_6259682 := by exact prefixLift 6259682
  have htrace : WordTrace (prefixWord ++ tailWord_6259682) baseStart_6259682 baseEnd_6259682 := by
    simpa [prefixWord, tailWord_6259682, baseEnd_6259682] using wordTrace_append hprefix tailTrace_6259682
  have hstable : (prefixWord ++ tailWord_6259682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259682).length < 2 ^ (prefixWord ++ tailWord_6259682).sum := by decide
  have hdescent : baseEnd_6259682 < baseStart_6259682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259695 : List Nat := [1, 1, 2, 1, 4, 3, 3, 2, 2, 2, 2]
def baseStart_6259695 : Nat := 118140960795 + 6259695 * 2 ^ 59
def prefixEnd_6259695 : Nat := 4983230072969 + 3 ^ 40 * 6259695 * 2
def baseEnd_6259695 : Nat := 3214232285545991648224693

theorem tailTrace_6259695 : CollatzResearch.WordTrace tailWord_6259695 prefixEnd_6259695 3214232285545991648224693 := by
  unfold tailWord_6259695
  simp only [CollatzResearch.WordTrace]
  refine ⟨228309833057201560638036539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152206555371467707092024359 228309833057201560638036539)
  ·
    refine ⟨342464749585802340957054809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228309833057201560638036539 342464749585802340957054809)
    ·
      refine ⟨256848562189351755717791107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342464749585802340957054809 256848562189351755717791107)
      ·
        refine ⟨385272843284027633576686661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256848562189351755717791107 385272843284027633576686661)
        ·
          refine ⟨72238658115755181295628749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 385272843284027633576686661 72238658115755181295628749)
          ·
            refine ⟨27089496793408192985860781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72238658115755181295628749 27089496793408192985860781)
            ·
              refine ⟨10158561297528072369697793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27089496793408192985860781 10158561297528072369697793)
              ·
                refine ⟨7618920973146054277273345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10158561297528072369697793 7618920973146054277273345)
                ·
                  refine ⟨5714190729859540707955009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7618920973146054277273345 5714190729859540707955009)
                  ·
                    refine ⟨4285643047394655530966257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5714190729859540707955009 4285643047394655530966257)
                    ·
                      refine ⟨3214232285545991648224693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4285643047394655530966257 3214232285545991648224693)
                      ·
                        rfl

theorem cell23_6259695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 2, 2, 2].length) (baseStart_6259695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259695 prefixEnd_6259695 := by exact prefixLift 6259695
  have htrace : WordTrace (prefixWord ++ tailWord_6259695) baseStart_6259695 baseEnd_6259695 := by
    simpa [prefixWord, tailWord_6259695, baseEnd_6259695] using wordTrace_append hprefix tailTrace_6259695
  have hstable : (prefixWord ++ tailWord_6259695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259695).length < 2 ^ (prefixWord ++ tailWord_6259695).sum := by decide
  have hdescent : baseEnd_6259695 < baseStart_6259695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259721 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 2, 5, 2]
def baseStart_6259721 : Nat := 118140960795 + 6259721 * 2 ^ 59
def prefixEnd_6259721 : Nat := 4983230072969 + 3 ^ 40 * 6259721 * 2
def baseEnd_6259721 : Nat := 3214245636043008546499573

theorem tailTrace_6259721 : CollatzResearch.WordTrace tailWord_6259721 prefixEnd_6259721 3214245636043008546499573 := by
  unfold tailWord_6259721
  simp only [CollatzResearch.WordTrace]
  refine ⟨228310781355107367078483017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152207187570071578052322011 228310781355107367078483017)
  ·
    refine ⟨171233086016330525308862263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228310781355107367078483017 171233086016330525308862263)
    ·
      refine ⟨256849629024495787963293395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171233086016330525308862263 256849629024495787963293395)
      ·
        refine ⟨385274443536743681944940093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256849629024495787963293395 385274443536743681944940093)
        ·
          refine ⟨144477916326278880729352535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 385274443536743681944940093 144477916326278880729352535)
          ·
            refine ⟨216716874489418321094028803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144477916326278880729352535 216716874489418321094028803)
            ·
              refine ⟨325075311734127481641043205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216716874489418321094028803 325075311734127481641043205)
              ·
                refine ⟨60951620950148902807695601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 325075311734127481641043205 60951620950148902807695601)
                ·
                  refine ⟨45713715712611677105771701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60951620950148902807695601 45713715712611677105771701)
                  ·
                    refine ⟨4285660848057344728666097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45713715712611677105771701 4285660848057344728666097)
                    ·
                      refine ⟨3214245636043008546499573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4285660848057344728666097 3214245636043008546499573)
                      ·
                        rfl

theorem cell23_6259721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 5, 2].length) (baseStart_6259721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259721 prefixEnd_6259721 := by exact prefixLift 6259721
  have htrace : WordTrace (prefixWord ++ tailWord_6259721) baseStart_6259721 baseEnd_6259721 := by
    simpa [prefixWord, tailWord_6259721, baseEnd_6259721] using wordTrace_append hprefix tailTrace_6259721
  have hstable : (prefixWord ++ tailWord_6259721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259721).length < 2 ^ (prefixWord ++ tailWord_6259721).sum := by decide
  have hdescent : baseEnd_6259721 < baseStart_6259721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259735 : List Nat := [1, 1, 3, 5, 1, 3, 1, 3, 5]
def baseStart_6259735 : Nat := 118140960795 + 6259735 * 2 ^ 59
def prefixEnd_6259735 : Nat := 4983230072969 + 3 ^ 40 * 6259735 * 2
def baseEnd_6259735 : Nat := 357139202752463499080501

theorem tailTrace_6259735 : CollatzResearch.WordTrace tailWord_6259735 prefixEnd_6259735 357139202752463499080501 := by
  unfold tailWord_6259735
  simp only [CollatzResearch.WordTrace]
  refine ⟨228311291977056647469492659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152207527984704431646328439 228311291977056647469492659)
  ·
    refine ⟨342466937965584971204238989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228311291977056647469492659 342466937965584971204238989)
    ·
      refine ⟨128425101737094364201589621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342466937965584971204238989 128425101737094364201589621)
      ·
        refine ⟨12039853287852596643899027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128425101737094364201589621 12039853287852596643899027)
        ·
          refine ⟨18059779931778894965848541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12039853287852596643899027 18059779931778894965848541)
          ·
            refine ⟨6772417474417085612193203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18059779931778894965848541 6772417474417085612193203)
            ·
              refine ⟨10158626211625628418289805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6772417474417085612193203 10158626211625628418289805)
              ·
                refine ⟨3809484829359610656858677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10158626211625628418289805 3809484829359610656858677)
                ·
                  refine ⟨357139202752463499080501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3809484829359610656858677 357139202752463499080501)
                  ·
                    rfl

theorem cell23_6259735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 3, 5].length) (baseStart_6259735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259735 prefixEnd_6259735 := by exact prefixLift 6259735
  have htrace : WordTrace (prefixWord ++ tailWord_6259735) baseStart_6259735 baseEnd_6259735 := by
    simpa [prefixWord, tailWord_6259735, baseEnd_6259735] using wordTrace_append hprefix tailTrace_6259735
  have hstable : (prefixWord ++ tailWord_6259735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259735).length < 2 ^ (prefixWord ++ tailWord_6259735).sum := by decide
  have hdescent : baseEnd_6259735 < baseStart_6259735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259748 : List Nat := [2, 3, 1, 4, 1, 2, 1, 2, 2, 5]
def baseStart_6259748 : Nat := 118140960795 + 6259748 * 2 ^ 59
def prefixEnd_6259748 : Nat := 4983230072969 + 3 ^ 40 * 6259748 * 2
def baseEnd_6259748 : Nat := 1071419833340226646953983

theorem tailTrace_6259748 : CollatzResearch.WordTrace tailWord_6259748 prefixEnd_6259748 1071419833340226646953983 := by
  unfold tailWord_6259748
  simp only [CollatzResearch.WordTrace]
  refine ⟨114155883063004775344857949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152207844084006367126477265 114155883063004775344857949)
  ·
    refine ⟨42808456148626790754321731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114155883063004775344857949 42808456148626790754321731)
    ·
      refine ⟨64212684222940186131482597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42808456148626790754321731 64212684222940186131482597)
      ·
        refine ⟨12039878291801284899652987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64212684222940186131482597 12039878291801284899652987)
        ·
          refine ⟨18059817437701927349479481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12039878291801284899652987 18059817437701927349479481)
          ·
            refine ⟨13544863078276445512109611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18059817437701927349479481 13544863078276445512109611)
            ·
              refine ⟨20317294617414668268164417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13544863078276445512109611 20317294617414668268164417)
              ·
                refine ⟨15237970963061001201123313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20317294617414668268164417 15237970963061001201123313)
                ·
                  refine ⟨11428478222295750900842485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15237970963061001201123313 11428478222295750900842485)
                  ·
                    refine ⟨1071419833340226646953983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11428478222295750900842485 1071419833340226646953983)
                    ·
                      rfl

theorem cell23_6259748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_6259748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259748 prefixEnd_6259748 := by exact prefixLift 6259748
  have htrace : WordTrace (prefixWord ++ tailWord_6259748) baseStart_6259748 baseEnd_6259748 := by
    simpa [prefixWord, tailWord_6259748, baseEnd_6259748] using wordTrace_append hprefix tailTrace_6259748
  have hstable : (prefixWord ++ tailWord_6259748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259748).length < 2 ^ (prefixWord ++ tailWord_6259748).sum := by decide
  have hdescent : baseEnd_6259748 < baseStart_6259748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259845 : List Nat := [1, 3, 1, 1, 6, 1, 1, 1, 1, 5, 2]
def baseStart_6259845 : Nat := 118140960795 + 6259845 * 2 ^ 59
def prefixEnd_6259845 : Nat := 4983230072969 + 3 ^ 40 * 6259845 * 2
def baseEnd_6259845 : Nat := 3214309307644166061349003

theorem tailTrace_6259845 : CollatzResearch.WordTrace tailWord_6259845 prefixEnd_6259845 3214309307644166061349003 := by
  unfold tailWord_6259845
  simp only [CollatzResearch.WordTrace]
  refine ⟨228315304006658136255996989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152210202671105424170664659 228315304006658136255996989)
  ·
    refine ⟨85618239002496801095998871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228315304006658136255996989 85618239002496801095998871)
    ·
      refine ⟨128427358503745201643998307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85618239002496801095998871 128427358503745201643998307)
      ·
        refine ⟨192641037755617802465997461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128427358503745201643998307 192641037755617802465997461)
        ·
          refine ⟨9030048644794584490593631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 192641037755617802465997461 9030048644794584490593631)
          ·
            refine ⟨13545072967191876735890447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9030048644794584490593631 13545072967191876735890447)
            ·
              refine ⟨20317609450787815103835671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13545072967191876735890447 20317609450787815103835671)
              ·
                refine ⟨30476414176181722655753507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20317609450787815103835671 30476414176181722655753507)
                ·
                  refine ⟨45714621264272583983630261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30476414176181722655753507 45714621264272583983630261)
                  ·
                    refine ⟨4285745743525554748465337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45714621264272583983630261 4285745743525554748465337)
                    ·
                      refine ⟨3214309307644166061349003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4285745743525554748465337 3214309307644166061349003)
                      ·
                        rfl

theorem cell23_6259845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 5, 2].length) (baseStart_6259845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259845 prefixEnd_6259845 := by exact prefixLift 6259845
  have htrace : WordTrace (prefixWord ++ tailWord_6259845) baseStart_6259845 baseEnd_6259845 := by
    simpa [prefixWord, tailWord_6259845, baseEnd_6259845] using wordTrace_append hprefix tailTrace_6259845
  have hstable : (prefixWord ++ tailWord_6259845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259845).length < 2 ^ (prefixWord ++ tailWord_6259845).sum := by decide
  have hdescent : baseEnd_6259845 < baseStart_6259845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259895 : List Nat := [1, 1, 3, 1, 4, 1, 4, 2, 1, 2, 3]
def baseStart_6259895 : Nat := 118140960795 + 6259895 * 2 ^ 59
def prefixEnd_6259895 : Nat := 4983230072969 + 3 ^ 40 * 6259895 * 2
def baseEnd_6259895 : Nat := 3214334981676890865723773

theorem tailTrace_6259895 : CollatzResearch.WordTrace tailWord_6259895 prefixEnd_6259895 3214334981676890865723773 := by
  unfold tailWord_6259895
  simp only [CollatzResearch.WordTrace]
  refine ⟨228317127656476994795317139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152211418437651329863544759 228317127656476994795317139)
  ·
    refine ⟨342475691484715492192975709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228317127656476994795317139 342475691484715492192975709)
    ·
      refine ⟨128428384306768309572365891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342475691484715492192975709 128428384306768309572365891)
      ·
        refine ⟨192642576460152464358548837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128428384306768309572365891 192642576460152464358548837)
        ·
          refine ⟨36120483086278587067227907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192642576460152464358548837 36120483086278587067227907)
          ·
            refine ⟨54180724629417880600841861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36120483086278587067227907 54180724629417880600841861)
            ·
              refine ⟨10158885868015852612657849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54180724629417880600841861 10158885868015852612657849)
              ·
                refine ⟨7619164401011889459493387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10158885868015852612657849 7619164401011889459493387)
                ·
                  refine ⟨11428746601517834189240081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7619164401011889459493387 11428746601517834189240081)
                  ·
                    refine ⟨8571559951138375641930061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11428746601517834189240081 8571559951138375641930061)
                    ·
                      refine ⟨3214334981676890865723773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8571559951138375641930061 3214334981676890865723773)
                      ·
                        rfl

theorem cell23_6259895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 2, 3].length) (baseStart_6259895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259895 prefixEnd_6259895 := by exact prefixLift 6259895
  have htrace : WordTrace (prefixWord ++ tailWord_6259895) baseStart_6259895 baseEnd_6259895 := by
    simpa [prefixWord, tailWord_6259895, baseEnd_6259895] using wordTrace_append hprefix tailTrace_6259895
  have hstable : (prefixWord ++ tailWord_6259895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259895).length < 2 ^ (prefixWord ++ tailWord_6259895).sum := by decide
  have hdescent : baseEnd_6259895 < baseStart_6259895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259921 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 4, 2, 5]
def baseStart_6259921 : Nat := 118140960795 + 6259921 * 2 ^ 59
def prefixEnd_6259921 : Nat := 4983230072969 + 3 ^ 40 * 6259921 * 2
def baseEnd_6259921 : Nat := 3214348332173907763998653

theorem tailTrace_6259921 : CollatzResearch.WordTrace tailWord_6259921 prefixEnd_6259921 3214348332173907763998653 := by
  unfold tailWord_6259921
  simp only [CollatzResearch.WordTrace]
  refine ⟨228318075954382801235763617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152212050636255200823842411 228318075954382801235763617)
  ·
    refine ⟨171238556965787100926822713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228318075954382801235763617 171238556965787100926822713)
    ·
      refine ⟨128428917724340325695117035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171238556965787100926822713 128428917724340325695117035)
      ·
        refine ⟨192643376586510488542675553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128428917724340325695117035 192643376586510488542675553)
        ·
          refine ⟨144482532439882866407006665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192643376586510488542675553 144482532439882866407006665)
          ·
            refine ⟨108361899329912149805254999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144482532439882866407006665 108361899329912149805254999)
            ·
              refine ⟨162542848994868224707882499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108361899329912149805254999 162542848994868224707882499)
              ·
                refine ⟨243814273492302337061823749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162542848994868224707882499 243814273492302337061823749)
                ·
                  refine ⟨45715176279806688199091953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 243814273492302337061823749 45715176279806688199091953)
                  ·
                    refine ⟨34286382209855016149318965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45715176279806688199091953 34286382209855016149318965)
                    ·
                      refine ⟨3214348332173907763998653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34286382209855016149318965 3214348332173907763998653)
                      ·
                        rfl

theorem cell23_6259921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_6259921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259921 prefixEnd_6259921 := by exact prefixLift 6259921
  have htrace : WordTrace (prefixWord ++ tailWord_6259921) baseStart_6259921 baseEnd_6259921 := by
    simpa [prefixWord, tailWord_6259921, baseEnd_6259921] using wordTrace_append hprefix tailTrace_6259921
  have hstable : (prefixWord ++ tailWord_6259921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259921).length < 2 ^ (prefixWord ++ tailWord_6259921).sum := by decide
  have hdescent : baseEnd_6259921 < baseStart_6259921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259958 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 4, 6]
def baseStart_6259958 : Nat := 118140960795 + 6259958 * 2 ^ 59
def prefixEnd_6259958 : Nat := 4983230072969 + 3 ^ 40 * 6259958 * 2
def baseEnd_6259958 : Nat := 1071455776986041373078661

theorem tailTrace_6259958 : CollatzResearch.WordTrace tailWord_6259958 prefixEnd_6259958 1071455776986041373078661 := by
  unfold tailWord_6259958
  simp only [CollatzResearch.WordTrace]
  refine ⟨14269964090953047284678783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152212950303499171036573685 14269964090953047284678783)
  ·
    refine ⟨21404946136429570927018175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14269964090953047284678783 21404946136429570927018175)
    ·
      refine ⟨32107419204644356390527263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21404946136429570927018175 32107419204644356390527263)
      ·
        refine ⟨48161128806966534585790895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32107419204644356390527263 48161128806966534585790895)
        ·
          refine ⟨72241693210449801878686343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48161128806966534585790895 72241693210449801878686343)
          ·
            refine ⟨108362539815674702818029515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72241693210449801878686343 108362539815674702818029515)
            ·
              refine ⟨162543809723512054227044273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108362539815674702818029515 162543809723512054227044273)
              ·
                refine ⟨121907857292634040670283205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162543809723512054227044273 121907857292634040670283205)
                ·
                  refine ⟨22857723242368882625678101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121907857292634040670283205 22857723242368882625678101)
                  ·
                    refine ⟨1071455776986041373078661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22857723242368882625678101 1071455776986041373078661)
                    ·
                      rfl

theorem cell23_6259958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_6259958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259958 prefixEnd_6259958 := by exact prefixLift 6259958
  have htrace : WordTrace (prefixWord ++ tailWord_6259958) baseStart_6259958 baseEnd_6259958 := by
    simpa [prefixWord, tailWord_6259958, baseEnd_6259958] using wordTrace_append hprefix tailTrace_6259958
  have hstable : (prefixWord ++ tailWord_6259958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259958).length < 2 ^ (prefixWord ++ tailWord_6259958).sum := by decide
  have hdescent : baseEnd_6259958 < baseStart_6259958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259969 : List Nat := [1, 2, 4, 1, 1, 4, 3, 1, 1, 3, 2]
def baseStart_6259969 : Nat := 118140960795 + 6259969 * 2 ^ 59
def prefixEnd_6259969 : Nat := 4983230072969 + 3 ^ 40 * 6259969 * 2
def baseEnd_6259969 : Nat := 3214372979245323576198433

theorem tailTrace_6259969 : CollatzResearch.WordTrace tailWord_6259969 prefixEnd_6259969 3214372979245323576198433 := by
  unfold tailWord_6259969
  simp only [CollatzResearch.WordTrace]
  refine ⟨228319826658208905433510961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152213217772139270289007307 228319826658208905433510961)
  ·
    refine ⟨171239869993656679075133221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228319826658208905433510961 171239869993656679075133221)
    ·
      refine ⟨32107475623810627326587479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171239869993656679075133221 32107475623810627326587479)
      ·
        refine ⟨48161213435715940989881219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32107475623810627326587479 48161213435715940989881219)
        ·
          refine ⟨72241820153573911484821829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48161213435715940989881219 72241820153573911484821829)
          ·
            refine ⟨13545341278795108403404093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72241820153573911484821829 13545341278795108403404093)
            ·
              refine ⟨5079502979548165651276535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13545341278795108403404093 5079502979548165651276535)
              ·
                refine ⟨7619254469322248476914803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5079502979548165651276535 7619254469322248476914803)
                ·
                  refine ⟨11428881703983372715372205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7619254469322248476914803 11428881703983372715372205)
                  ·
                    refine ⟨4285830638993764768264577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11428881703983372715372205 4285830638993764768264577)
                    ·
                      refine ⟨3214372979245323576198433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4285830638993764768264577 3214372979245323576198433)
                      ·
                        rfl

theorem cell23_6259969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_6259969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259969 prefixEnd_6259969 := by exact prefixLift 6259969
  have htrace : WordTrace (prefixWord ++ tailWord_6259969) baseStart_6259969 baseEnd_6259969 := by
    simpa [prefixWord, tailWord_6259969, baseEnd_6259969] using wordTrace_append hprefix tailTrace_6259969
  have hstable : (prefixWord ++ tailWord_6259969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259969).length < 2 ^ (prefixWord ++ tailWord_6259969).sum := by decide
  have hdescent : baseEnd_6259969 < baseStart_6259969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6259978 : List Nat := [3, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4]
def baseStart_6259978 : Nat := 118140960795 + 6259978 * 2 ^ 59
def prefixEnd_6259978 : Nat := 4983230072969 + 3 ^ 40 * 6259978 * 2
def baseEnd_6259978 : Nat := 3214377600571214040985891

theorem tailTrace_6259978 : CollatzResearch.WordTrace tailWord_6259978 prefixEnd_6259978 3214377600571214040985891 := by
  unfold tailWord_6259978
  simp only [CollatzResearch.WordTrace]
  refine ⟨57080038728794074992647147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152213436610117533313725725 57080038728794074992647147)
  ·
    refine ⟨85620058093191112488970721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57080038728794074992647147 85620058093191112488970721)
    ·
      refine ⟨64215043569893334366728041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85620058093191112488970721 64215043569893334366728041)
      ·
        refine ⟨48161282677420000775046031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64215043569893334366728041 48161282677420000775046031)
        ·
          refine ⟨72241924016130001162569047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48161282677420000775046031 72241924016130001162569047)
          ·
            refine ⟨108362886024195001743853571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72241924016130001162569047 108362886024195001743853571)
            ·
              refine ⟨162544329036292502615780357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108362886024195001743853571 162544329036292502615780357)
              ·
                refine ⟨30477061694304844240458817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162544329036292502615780357 30477061694304844240458817)
                ·
                  refine ⟨22857796270728633180344113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30477061694304844240458817 22857796270728633180344113)
                  ·
                    refine ⟨17143347203046474885258085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22857796270728633180344113 17143347203046474885258085)
                    ·
                      refine ⟨3214377600571214040985891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17143347203046474885258085 3214377600571214040985891)
                      ·
                        rfl

theorem cell23_6259978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_6259978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6259978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6259978 prefixEnd_6259978 := by exact prefixLift 6259978
  have htrace : WordTrace (prefixWord ++ tailWord_6259978) baseStart_6259978 baseEnd_6259978 := by
    simpa [prefixWord, tailWord_6259978, baseEnd_6259978] using wordTrace_append hprefix tailTrace_6259978
  have hstable : (prefixWord ++ tailWord_6259978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6259978).length < 2 ^ (prefixWord ++ tailWord_6259978).sum := by decide
  have hdescent : baseEnd_6259978 < baseStart_6259978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6259978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260122 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 5, 1, 3]
def baseStart_6260122 : Nat := 118140960795 + 6260122 * 2 ^ 59
def prefixEnd_6260122 : Nat := 4983230072969 + 3 ^ 40 * 6260122 * 2
def baseEnd_6260122 : Nat := 3214451541785461477585229

theorem tailTrace_6260122 : CollatzResearch.WordTrace tailWord_6260122 prefixEnd_6260122 3214451541785461477585229 := by
  unfold tailWord_6260122
  simp only [CollatzResearch.WordTrace]
  refine ⟨57081351756663653140957655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152216938017769741709220413 57081351756663653140957655)
  ·
    refine ⟨85622027634995479711436483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57081351756663653140957655 85622027634995479711436483)
    ·
      refine ⟨128433041452493219567154725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85622027634995479711436483 128433041452493219567154725)
      ·
        refine ⟨24081195272342478668841511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128433041452493219567154725 24081195272342478668841511)
        ·
          refine ⟨36121792908513718003262267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24081195272342478668841511 36121792908513718003262267)
          ·
            refine ⟨54182689362770577004893401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36121792908513718003262267 54182689362770577004893401)
            ·
              refine ⟨40637017022077932753670051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54182689362770577004893401 40637017022077932753670051)
              ·
                refine ⟨60955525533116899130505077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40637017022077932753670051 60955525533116899130505077)
                ·
                  refine ⟨5714580518729709293484851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60955525533116899130505077 5714580518729709293484851)
                  ·
                    refine ⟨8571870778094563940227277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5714580518729709293484851 8571870778094563940227277)
                    ·
                      refine ⟨3214451541785461477585229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8571870778094563940227277 3214451541785461477585229)
                      ·
                        rfl

theorem cell23_6260122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_6260122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260122 prefixEnd_6260122 := by exact prefixLift 6260122
  have htrace : WordTrace (prefixWord ++ tailWord_6260122) baseStart_6260122 baseEnd_6260122 := by
    simpa [prefixWord, tailWord_6260122, baseEnd_6260122] using wordTrace_append hprefix tailTrace_6260122
  have hstable : (prefixWord ++ tailWord_6260122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260122).length < 2 ^ (prefixWord ++ tailWord_6260122).sum := by decide
  have hdescent : baseEnd_6260122 < baseStart_6260122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260126 : List Nat := [4, 3, 1, 2, 2, 1, 2, 1, 2, 2, 3]
def baseStart_6260126 : Nat := 118140960795 + 6260126 * 2 ^ 59
def prefixEnd_6260126 : Nat := 4983230072969 + 3 ^ 40 * 6260126 * 2
def baseEnd_6260126 : Nat := 3214453595708079461935211

theorem tailTrace_6260126 : CollatzResearch.WordTrace tailWord_6260126 prefixEnd_6260126 3214453595708079461935211 := by
  unfold tailWord_6260126
  simp only [CollatzResearch.WordTrace]
  refine ⟨28540694114830015155872029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152217035279093414164650821 28540694114830015155872029)
  ·
    refine ⟨10702760293061255683452011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28540694114830015155872029 10702760293061255683452011)
    ·
      refine ⟨16054140439591883525178017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10702760293061255683452011 16054140439591883525178017)
      ·
        refine ⟨12040605329693912643883513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16054140439591883525178017 12040605329693912643883513)
        ·
          refine ⟨9030453997270434482912635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12040605329693912643883513 9030453997270434482912635)
          ·
            refine ⟨13545680995905651724368953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9030453997270434482912635 13545680995905651724368953)
            ·
              refine ⟨10159260746929238793276715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13545680995905651724368953 10159260746929238793276715)
              ·
                refine ⟨15238891120393858189915073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10159260746929238793276715 15238891120393858189915073)
                ·
                  refine ⟨11429168340295393642436305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15238891120393858189915073 11429168340295393642436305)
                  ·
                    refine ⟨8571876255221545231827229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11429168340295393642436305 8571876255221545231827229)
                    ·
                      refine ⟨3214453595708079461935211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8571876255221545231827229 3214453595708079461935211)
                      ·
                        rfl

theorem cell23_6260126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_6260126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260126 prefixEnd_6260126 := by exact prefixLift 6260126
  have htrace : WordTrace (prefixWord ++ tailWord_6260126) baseStart_6260126 baseEnd_6260126 := by
    simpa [prefixWord, tailWord_6260126, baseEnd_6260126] using wordTrace_append hprefix tailTrace_6260126
  have hstable : (prefixWord ++ tailWord_6260126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260126).length < 2 ^ (prefixWord ++ tailWord_6260126).sum := by decide
  have hdescent : baseEnd_6260126 < baseStart_6260126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260149 : List Nat := [1, 3, 3, 2, 2, 1, 2, 2, 2, 3, 2]
def baseStart_6260149 : Nat := 118140960795 + 6260149 * 2 ^ 59
def prefixEnd_6260149 : Nat := 4983230072969 + 3 ^ 40 * 6260149 * 2
def baseEnd_6260149 : Nat := 3214465405763132871947605

theorem tailTrace_6260149 : CollatzResearch.WordTrace tailWord_6260149 prefixEnd_6260149 3214465405763132871947605 := by
  unfold tailWord_6260149
  simp only [CollatzResearch.WordTrace]
  refine ⟨228326391797556796175063501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152217594531704530783375667 228326391797556796175063501)
  ·
    refine ⟨85622396924083798565648813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228326391797556796175063501 85622396924083798565648813)
    ·
      refine ⟨32108398846531424462118305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85622396924083798565648813 32108398846531424462118305)
      ·
        refine ⟨24081299134898568346588729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32108398846531424462118305 24081299134898568346588729)
        ·
          refine ⟨18060974351173926259941547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24081299134898568346588729 18060974351173926259941547)
          ·
            refine ⟨27091461526760889389912321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18060974351173926259941547 27091461526760889389912321)
            ·
              refine ⟨20318596145070667042434241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27091461526760889389912321 20318596145070667042434241)
              ·
                refine ⟨15238947108803000281825681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20318596145070667042434241 15238947108803000281825681)
                ·
                  refine ⟨11429210331602250211369261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15238947108803000281825681 11429210331602250211369261)
                  ·
                    refine ⟨4285953874350843829263473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11429210331602250211369261 4285953874350843829263473)
                    ·
                      refine ⟨3214465405763132871947605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4285953874350843829263473 3214465405763132871947605)
                      ·
                        rfl

theorem cell23_6260149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_6260149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260149 prefixEnd_6260149 := by exact prefixLift 6260149
  have htrace : WordTrace (prefixWord ++ tailWord_6260149) baseStart_6260149 baseEnd_6260149 := by
    simpa [prefixWord, tailWord_6260149, baseEnd_6260149] using wordTrace_append hprefix tailTrace_6260149
  have hstable : (prefixWord ++ tailWord_6260149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260149).length < 2 ^ (prefixWord ++ tailWord_6260149).sum := by decide
  have hdescent : baseEnd_6260149 < baseStart_6260149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260172 : List Nat := [2, 2, 1, 4, 2, 2, 2, 1, 1, 6]
def baseStart_6260172 : Nat := 118140960795 + 6260172 * 2 ^ 59
def prefixEnd_6260172 : Nat := 4983230072969 + 3 ^ 40 * 6260172 * 2
def baseEnd_6260172 : Nat := 1071492405272728760653333

theorem tailTrace_6260172 : CollatzResearch.WordTrace tailWord_6260172 prefixEnd_6260172 1071492405272728760653333 := by
  unfold tailWord_6260172
  simp only [CollatzResearch.WordTrace]
  refine ⟨114163615338236735551575385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152218153784315647402100513 114163615338236735551575385)
  ·
    refine ⟨85622711503677551663681539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114163615338236735551575385 85622711503677551663681539)
    ·
      refine ⟨128434067255516327495522309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85622711503677551663681539 128434067255516327495522309)
      ·
        refine ⟨24081387610409311405410433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128434067255516327495522309 24081387610409311405410433)
        ·
          refine ⟨18061040707806983554057825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24081387610409311405410433 18061040707806983554057825)
          ·
            refine ⟨13545780530855237665543369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18061040707806983554057825 13545780530855237665543369)
            ·
              refine ⟨10159335398141428249157527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13545780530855237665543369 10159335398141428249157527)
              ·
                refine ⟨15239003097212142373736291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10159335398141428249157527 15239003097212142373736291)
                ·
                  refine ⟨22858504645818213560604437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15239003097212142373736291 22858504645818213560604437)
                  ·
                    refine ⟨1071492405272728760653333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22858504645818213560604437 1071492405272728760653333)
                    ·
                      rfl

theorem cell23_6260172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 1, 6].length) (baseStart_6260172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260172 prefixEnd_6260172 := by exact prefixLift 6260172
  have htrace : WordTrace (prefixWord ++ tailWord_6260172) baseStart_6260172 baseEnd_6260172 := by
    simpa [prefixWord, tailWord_6260172, baseEnd_6260172] using wordTrace_append hprefix tailTrace_6260172
  have hstable : (prefixWord ++ tailWord_6260172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260172).length < 2 ^ (prefixWord ++ tailWord_6260172).sum := by decide
  have hdescent : baseEnd_6260172 < baseStart_6260172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260175 : List Nat := [1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 4]
def baseStart_6260175 : Nat := 118140960795 + 6260175 * 2 ^ 59
def prefixEnd_6260175 : Nat := 4983230072969 + 3 ^ 40 * 6260175 * 2
def baseEnd_6260175 : Nat := 3214478756260149770222485

theorem tailTrace_6260175 : CollatzResearch.WordTrace tailWord_6260175 prefixEnd_6260175 3214478756260149770222485 := by
  unfold tailWord_6260175
  simp only [CollatzResearch.WordTrace]
  refine ⟨228327340095462602615509979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152218226730308401743673319 228327340095462602615509979)
  ·
    refine ⟨342491010143193903923264969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228327340095462602615509979 342491010143193903923264969)
    ·
      refine ⟨256868257607395427942448727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342491010143193903923264969 256868257607395427942448727)
      ·
        refine ⟨385302386411093141913673091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256868257607395427942448727 385302386411093141913673091)
        ·
          refine ⟨577953579616639712870509637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385302386411093141913673091 577953579616639712870509637)
          ·
            refine ⟨108366296178119946163220557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 577953579616639712870509637 108366296178119946163220557)
            ·
              refine ⟨40637361066794979811207709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108366296178119946163220557 40637361066794979811207709)
              ·
                refine ⟨15239010400048117429202891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40637361066794979811207709 15239010400048117429202891)
                ·
                  refine ⟨22858515600072176143804337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15239010400048117429202891 22858515600072176143804337)
                  ·
                    refine ⟨17143886700054132107853253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22858515600072176143804337 17143886700054132107853253)
                    ·
                      refine ⟨3214478756260149770222485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17143886700054132107853253 3214478756260149770222485)
                      ·
                        rfl

theorem cell23_6260175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 4].length) (baseStart_6260175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260175 prefixEnd_6260175 := by exact prefixLift 6260175
  have htrace : WordTrace (prefixWord ++ tailWord_6260175) baseStart_6260175 baseEnd_6260175 := by
    simpa [prefixWord, tailWord_6260175, baseEnd_6260175] using wordTrace_append hprefix tailTrace_6260175
  have hstable : (prefixWord ++ tailWord_6260175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260175).length < 2 ^ (prefixWord ++ tailWord_6260175).sum := by decide
  have hdescent : baseEnd_6260175 < baseStart_6260175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260199 : List Nat := [1, 1, 5, 2, 1, 3, 1, 3, 1, 2, 3]
def baseStart_6260199 : Nat := 118140960795 + 6260199 * 2 ^ 59
def prefixEnd_6260199 : Nat := 4983230072969 + 3 ^ 40 * 6260199 * 2
def baseEnd_6260199 : Nat := 3214491079795857676322375

theorem tailTrace_6260199 : CollatzResearch.WordTrace tailWord_6260199 prefixEnd_6260199 3214491079795857676322375 := by
  unfold tailWord_6260199
  simp only [CollatzResearch.WordTrace]
  refine ⟨228328215447375654714383651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152218810298250436476255767 228328215447375654714383651)
  ·
    refine ⟨342492323171063482071575477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228328215447375654714383651 342492323171063482071575477)
    ·
      refine ⟨32108655297287201444210201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 342492323171063482071575477 32108655297287201444210201)
      ·
        refine ⟨24081491472965401083157651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32108655297287201444210201 24081491472965401083157651)
        ·
          refine ⟨36122237209448101624736477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24081491472965401083157651 36122237209448101624736477)
          ·
            refine ⟨13545838953543038109276179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36122237209448101624736477 13545838953543038109276179)
            ·
              refine ⟨20318758430314557163914269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13545838953543038109276179 20318758430314557163914269)
              ·
                refine ⟨7619534411367958936467851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20318758430314557163914269 7619534411367958936467851)
                ·
                  refine ⟨11429301617051938404701777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7619534411367958936467851 11429301617051938404701777)
                  ·
                    refine ⟨8571976212788953803526333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11429301617051938404701777 8571976212788953803526333)
                    ·
                      refine ⟨3214491079795857676322375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8571976212788953803526333 3214491079795857676322375)
                      ·
                        rfl

theorem cell23_6260199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_6260199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260199 prefixEnd_6260199 := by exact prefixLift 6260199
  have htrace : WordTrace (prefixWord ++ tailWord_6260199) baseStart_6260199 baseEnd_6260199 := by
    simpa [prefixWord, tailWord_6260199, baseEnd_6260199] using wordTrace_append hprefix tailTrace_6260199
  have hstable : (prefixWord ++ tailWord_6260199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260199).length < 2 ^ (prefixWord ++ tailWord_6260199).sum := by decide
  have hdescent : baseEnd_6260199 < baseStart_6260199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260213 : List Nat := [1, 3, 5, 1, 1, 2, 2, 1, 3, 2, 2]
def baseStart_6260213 : Nat := 118140960795 + 6260213 * 2 ^ 59
def prefixEnd_6260213 : Nat := 4983230072969 + 3 ^ 40 * 6260213 * 2
def baseEnd_6260213 : Nat := 3214498268525020621547311

theorem tailTrace_6260213 : CollatzResearch.WordTrace tailWord_6260213 prefixEnd_6260213 3214498268525020621547311 := by
  unfold tailWord_6260213
  simp only [CollatzResearch.WordTrace]
  refine ⟨228328726069324935105393293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152219150712883290070262195 228328726069324935105393293)
  ·
    refine ⟨85623272275996850664522485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228328726069324935105393293 85623272275996850664522485)
    ·
      refine ⟨8027181775874704749798983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85623272275996850664522485 8027181775874704749798983)
      ·
        refine ⟨12040772663812057124698475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8027181775874704749798983 12040772663812057124698475)
        ·
          refine ⟨18061158995718085687047713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12040772663812057124698475 18061158995718085687047713)
          ·
            refine ⟨13545869246788564265285785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18061158995718085687047713 13545869246788564265285785)
            ·
              refine ⟨10159401935091423198964339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13545869246788564265285785 10159401935091423198964339)
              ·
                refine ⟨15239102902637134798446509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10159401935091423198964339 15239102902637134798446509)
                ·
                  refine ⟨5714663588488925549417441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15239102902637134798446509 5714663588488925549417441)
                  ·
                    refine ⟨4285997691366694162063081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5714663588488925549417441 4285997691366694162063081)
                    ·
                      refine ⟨3214498268525020621547311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4285997691366694162063081 3214498268525020621547311)
                      ·
                        rfl

theorem cell23_6260213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_6260213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260213 prefixEnd_6260213 := by exact prefixLift 6260213
  have htrace : WordTrace (prefixWord ++ tailWord_6260213) baseStart_6260213 baseEnd_6260213 := by
    simpa [prefixWord, tailWord_6260213, baseEnd_6260213] using wordTrace_append hprefix tailTrace_6260213
  have hstable : (prefixWord ++ tailWord_6260213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260213).length < 2 ^ (prefixWord ++ tailWord_6260213).sum := by decide
  have hdescent : baseEnd_6260213 < baseStart_6260213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260226 : List Nat := [3, 4, 1, 2, 1, 3, 1, 1, 1, 2, 4]
def baseStart_6260226 : Nat := 118140960795 + 6260226 * 2 ^ 59
def prefixEnd_6260226 : Nat := 4983230072969 + 3 ^ 40 * 6260226 * 2
def baseEnd_6260226 : Nat := 3214504943773529070684751

theorem tailTrace_6260226 : CollatzResearch.WordTrace tailWord_6260226 prefixEnd_6260226 3214504943773529070684751 := by
  unfold tailWord_6260226
  simp only [CollatzResearch.WordTrace]
  refine ⟨57082300054569459581404133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152219466812185225550411021 57082300054569459581404133)
  ·
    refine ⟨10702931260231773671513275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57082300054569459581404133 10702931260231773671513275)
    ·
      refine ⟨16054396890347660507269913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10702931260231773671513275 16054396890347660507269913)
      ·
        refine ⟨12040797667760745380452435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16054396890347660507269913 12040797667760745380452435)
        ·
          refine ⟨18061196501641118070678653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12040797667760745380452435 18061196501641118070678653)
          ·
            refine ⟨6772948688115419276504495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18061196501641118070678653 6772948688115419276504495)
            ·
              refine ⟨10159423032173128914756743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6772948688115419276504495 10159423032173128914756743)
              ·
                refine ⟨15239134548259693372135115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10159423032173128914756743 15239134548259693372135115)
                ·
                  refine ⟨22858701822389540058202673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15239134548259693372135115 22858701822389540058202673)
                  ·
                    refine ⟨17144026366792155043652005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22858701822389540058202673 17144026366792155043652005)
                    ·
                      refine ⟨3214504943773529070684751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17144026366792155043652005 3214504943773529070684751)
                      ·
                        rfl

theorem cell23_6260226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_6260226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260226 prefixEnd_6260226 := by exact prefixLift 6260226
  have htrace : WordTrace (prefixWord ++ tailWord_6260226) baseStart_6260226 baseEnd_6260226 := by
    simpa [prefixWord, tailWord_6260226, baseEnd_6260226] using wordTrace_append hprefix tailTrace_6260226
  have hstable : (prefixWord ++ tailWord_6260226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260226).length < 2 ^ (prefixWord ++ tailWord_6260226).sum := by decide
  have hdescent : baseEnd_6260226 < baseStart_6260226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260230 : List Nat := [6, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_6260230 : Nat := 118140960795 + 6260230 * 2 ^ 59
def prefixEnd_6260230 : Nat := 4983230072969 + 3 ^ 40 * 6260230 * 2
def baseEnd_6260230 : Nat := 3214506997696147055034733

theorem tailTrace_6260230 : CollatzResearch.WordTrace tailWord_6260230 prefixEnd_6260230 3214506997696147055034733 := by
  unfold tailWord_6260230
  simp only [CollatzResearch.WordTrace]
  refine ⟨7135292065945729594023817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 152219564073508898005841429 7135292065945729594023817)
  ·
    refine ⟨5351469049459297195517863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7135292065945729594023817 5351469049459297195517863)
    ·
      refine ⟨8027203574188945793276795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5351469049459297195517863 8027203574188945793276795)
      ·
        refine ⟨12040805361283418689915193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8027203574188945793276795 12040805361283418689915193)
        ·
          refine ⟨9030604020962564017436395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12040805361283418689915193 9030604020962564017436395)
          ·
            refine ⟨13545906031443846026154593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9030604020962564017436395 13545906031443846026154593)
            ·
              refine ⟨10159429523582884519615945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13545906031443846026154593 10159429523582884519615945)
              ·
                refine ⟨7619572142687163389711959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10159429523582884519615945 7619572142687163389711959)
                ·
                  refine ⟨11429358214030745084567939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7619572142687163389711959 11429358214030745084567939)
                  ·
                    refine ⟨17144037321046117626851909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11429358214030745084567939 17144037321046117626851909)
                    ·
                      refine ⟨3214506997696147055034733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17144037321046117626851909 3214506997696147055034733)
                      ·
                        rfl

theorem cell23_6260230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_6260230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260230 prefixEnd_6260230 := by exact prefixLift 6260230
  have htrace : WordTrace (prefixWord ++ tailWord_6260230) baseStart_6260230 baseEnd_6260230 := by
    simpa [prefixWord, tailWord_6260230, baseEnd_6260230] using wordTrace_append hprefix tailTrace_6260230
  have hstable : (prefixWord ++ tailWord_6260230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260230).length < 2 ^ (prefixWord ++ tailWord_6260230).sum := by decide
  have hdescent : baseEnd_6260230 < baseStart_6260230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260255 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 5]
def baseStart_6260255 : Nat := 118140960795 + 6260255 * 2 ^ 59
def prefixEnd_6260255 : Nat := 4983230072969 + 3 ^ 40 * 6260255 * 2
def baseEnd_6260255 : Nat := 3214519834712509457222117

theorem tailTrace_6260255 : CollatzResearch.WordTrace tailWord_6260255 prefixEnd_6260255 3214519834712509457222117 := by
  unfold tailWord_6260255
  simp only [CollatzResearch.WordTrace]
  refine ⟨228330257935172776278422219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152220171956781850852281479 228330257935172776278422219)
  ·
    refine ⟨342495386902759164417633329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228330257935172776278422219 342495386902759164417633329)
    ·
      refine ⟨256871540177069373313224997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342495386902759164417633329 256871540177069373313224997)
      ·
        refine ⟨48163413783200507496229687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 256871540177069373313224997 48163413783200507496229687)
        ·
          refine ⟨72245120674800761244344531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48163413783200507496229687 72245120674800761244344531)
          ·
            refine ⟨108367681012201141866516797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72245120674800761244344531 108367681012201141866516797)
            ·
              refine ⟨40637880379575428199943799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108367681012201141866516797 40637880379575428199943799)
              ·
                refine ⟨60956820569363142299915699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40637880379575428199943799 60956820569363142299915699)
                ·
                  refine ⟨91435230854044713449873549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60956820569363142299915699 91435230854044713449873549)
                  ·
                    refine ⟨34288211570266767543702581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91435230854044713449873549 34288211570266767543702581)
                    ·
                      refine ⟨3214519834712509457222117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34288211570266767543702581 3214519834712509457222117)
                      ·
                        rfl

theorem cell23_6260255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_6260255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260255 prefixEnd_6260255 := by exact prefixLift 6260255
  have htrace : WordTrace (prefixWord ++ tailWord_6260255) baseStart_6260255 baseEnd_6260255 := by
    simpa [prefixWord, tailWord_6260255, baseEnd_6260255] using wordTrace_append hprefix tailTrace_6260255
  have hstable : (prefixWord ++ tailWord_6260255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260255).length < 2 ^ (prefixWord ++ tailWord_6260255).sum := by decide
  have hdescent : baseEnd_6260255 < baseStart_6260255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260256 : List Nat := [2, 1, 1, 6, 1, 1, 2, 3, 1, 3, 2]
def baseStart_6260256 : Nat := 118140960795 + 6260256 * 2 ^ 59
def prefixEnd_6260256 : Nat := 4983230072969 + 3 ^ 40 * 6260256 * 2
def baseEnd_6260256 : Nat := 3214520348193163953309613

theorem tailTrace_6260256 : CollatzResearch.WordTrace tailWord_6260256 prefixEnd_6260256 3214520348193163953309613 := by
  unfold tailWord_6260256
  simp only [CollatzResearch.WordTrace]
  refine ⟨114165147204084576724604311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152220196272112768966139081 114165147204084576724604311)
  ·
    refine ⟨171247720806126865086906467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114165147204084576724604311 171247720806126865086906467)
    ·
      refine ⟨256871581209190297630359701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171247720806126865086906467 256871581209190297630359701)
      ·
        refine ⟨12040855369180795201423111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 256871581209190297630359701 12040855369180795201423111)
        ·
          refine ⟨18061283053771192802134667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12040855369180795201423111 18061283053771192802134667)
          ·
            refine ⟨27091924580656789203202001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18061283053771192802134667 27091924580656789203202001)
            ·
              refine ⟨20318943435492591902401501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27091924580656789203202001 20318943435492591902401501)
              ·
                refine ⟨7619603788309721963400563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20318943435492591902401501 7619603788309721963400563)
                ·
                  refine ⟨11429405682464582945100845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7619603788309721963400563 11429405682464582945100845)
                  ·
                    refine ⟨4286027130924218604412817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11429405682464582945100845 4286027130924218604412817)
                    ·
                      refine ⟨3214520348193163953309613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4286027130924218604412817 3214520348193163953309613)
                      ·
                        rfl

theorem cell23_6260256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_6260256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260256 prefixEnd_6260256 := by exact prefixLift 6260256
  have htrace : WordTrace (prefixWord ++ tailWord_6260256) baseStart_6260256 baseEnd_6260256 := by
    simpa [prefixWord, tailWord_6260256, baseEnd_6260256] using wordTrace_append hprefix tailTrace_6260256
  have hstable : (prefixWord ++ tailWord_6260256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260256).length < 2 ^ (prefixWord ++ tailWord_6260256).sum := by decide
  have hdescent : baseEnd_6260256 < baseStart_6260256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260302 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3]
def baseStart_6260302 : Nat := 118140960795 + 6260302 * 2 ^ 59
def prefixEnd_6260302 : Nat := 4983230072969 + 3 ^ 40 * 6260302 * 2
def baseEnd_6260302 : Nat := 3214543968303270773334401

theorem tailTrace_6260302 : CollatzResearch.WordTrace tailWord_6260302 prefixEnd_6260302 3214543968303270773334401 := by
  unfold tailWord_6260302
  simp only [CollatzResearch.WordTrace]
  refine ⟨28541496520750312913172895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152221314777335002203588773 28541496520750312913172895)
  ·
    refine ⟨42812244781125469369759343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28541496520750312913172895 42812244781125469369759343)
    ·
      refine ⟨64218367171688204054639015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42812244781125469369759343 64218367171688204054639015)
      ·
        refine ⟨96327550757532306081958523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64218367171688204054639015 96327550757532306081958523)
        ·
          refine ⟨144491326136298459122937785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96327550757532306081958523 144491326136298459122937785)
          ·
            refine ⟨108368494602223844342203339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144491326136298459122937785 108368494602223844342203339)
            ·
              refine ⟨162552741903335766513305009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108368494602223844342203339 162552741903335766513305009)
              ·
                refine ⟨121914556427501824884978757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162552741903335766513305009 121914556427501824884978757)
                ·
                  refine ⟨22858979330156592165933517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121914556427501824884978757 22858979330156592165933517)
                  ·
                    refine ⟨8572117248808722062225069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22858979330156592165933517 8572117248808722062225069)
                    ·
                      refine ⟨3214543968303270773334401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8572117248808722062225069 3214543968303270773334401)
                      ·
                        rfl

theorem cell23_6260302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_6260302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260302 prefixEnd_6260302 := by exact prefixLift 6260302
  have htrace : WordTrace (prefixWord ++ tailWord_6260302) baseStart_6260302 baseEnd_6260302 := by
    simpa [prefixWord, tailWord_6260302, baseEnd_6260302] using wordTrace_append hprefix tailTrace_6260302
  have hstable : (prefixWord ++ tailWord_6260302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260302).length < 2 ^ (prefixWord ++ tailWord_6260302).sum := by decide
  have hdescent : baseEnd_6260302 < baseStart_6260302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260335 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 2, 8]
def baseStart_6260335 : Nat := 118140960795 + 6260335 * 2 ^ 59
def prefixEnd_6260335 : Nat := 4983230072969 + 3 ^ 40 * 6260335 * 2
def baseEnd_6260335 : Nat := 1071520304388289714740583

theorem tailTrace_6260335 : CollatzResearch.WordTrace tailWord_6260335 prefixEnd_6260335 1071520304388289714740583 := by
  unfold tailWord_6260335
  simp only [CollatzResearch.WordTrace]
  refine ⟨228333175774882949941334459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152222117183255299960889639 228333175774882949941334459)
  ·
    refine ⟨342499763662324424912001689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228333175774882949941334459 342499763662324424912001689)
    ·
      refine ⟨256874822746743318684001267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342499763662324424912001689 256874822746743318684001267)
      ·
        refine ⟨385312234120114978026001901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256874822746743318684001267 385312234120114978026001901)
        ·
          refine ⟨144492087795043116759750713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 385312234120114978026001901 144492087795043116759750713)
          ·
            refine ⟨108369065846282337569813035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144492087795043116759750713 108369065846282337569813035)
            ·
              refine ⟨162553598769423506354719553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108369065846282337569813035 162553598769423506354719553)
              ·
                refine ⟨121915199077067629766039665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162553598769423506354719553 121915199077067629766039665)
                ·
                  refine ⟨91436399307800722324529749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121915199077067629766039665 91436399307800722324529749)
                  ·
                    refine ⟨1071520304388289714740583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 91436399307800722324529749 1071520304388289714740583)
                    ·
                      rfl

theorem cell23_6260335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 8].length) (baseStart_6260335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260335 prefixEnd_6260335 := by exact prefixLift 6260335
  have htrace : WordTrace (prefixWord ++ tailWord_6260335) baseStart_6260335 baseEnd_6260335 := by
    simpa [prefixWord, tailWord_6260335, baseEnd_6260335] using wordTrace_append hprefix tailTrace_6260335
  have hstable : (prefixWord ++ tailWord_6260335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260335).length < 2 ^ (prefixWord ++ tailWord_6260335).sum := by decide
  have hdescent : baseEnd_6260335 < baseStart_6260335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260356 : List Nat := [2, 3, 2, 1, 4, 2, 1, 1, 2, 5]
def baseStart_6260356 : Nat := 118140960795 + 6260356 * 2 ^ 59
def prefixEnd_6260356 : Nat := 4983230072969 + 3 ^ 40 * 6260356 * 2
def baseEnd_6260356 : Nat := 1071523898752871187353051

theorem tailTrace_6260356 : CollatzResearch.WordTrace tailWord_6260356 prefixEnd_6260356 1071523898752871187353051 := by
  unfold tailWord_6260356
  simp only [CollatzResearch.WordTrace]
  refine ⟨114166970853903435263924461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152222627805204580351899281 114166970853903435263924461)
  ·
    refine ⟨42812614070213788223971673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114166970853903435263924461 42812614070213788223971673)
    ·
      refine ⟨32109460552660341167978755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42812614070213788223971673 32109460552660341167978755)
      ·
        refine ⟨48164190828990511751968133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32109460552660341167978755 48164190828990511751968133)
        ·
          refine ⟨9030785780435720953494025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48164190828990511751968133 9030785780435720953494025)
          ·
            refine ⟨6773089335326790715120519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9030785780435720953494025 6773089335326790715120519)
            ·
              refine ⟨10159634002990186072680779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6773089335326790715120519 10159634002990186072680779)
              ·
                refine ⟨15239451004485279109021169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10159634002990186072680779 15239451004485279109021169)
                ·
                  refine ⟨11429588253363959331765877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15239451004485279109021169 11429588253363959331765877)
                  ·
                    refine ⟨1071523898752871187353051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11429588253363959331765877 1071523898752871187353051)
                    ·
                      rfl

theorem cell23_6260356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_6260356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260356 prefixEnd_6260356 := by exact prefixLift 6260356
  have htrace : WordTrace (prefixWord ++ tailWord_6260356) baseStart_6260356 baseEnd_6260356 := by
    simpa [prefixWord, tailWord_6260356, baseEnd_6260356] using wordTrace_append hprefix tailTrace_6260356
  have hstable : (prefixWord ++ tailWord_6260356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260356).length < 2 ^ (prefixWord ++ tailWord_6260356).sum := by decide
  have hdescent : baseEnd_6260356 < baseStart_6260356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260359 : List Nat := [1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 4]
def baseStart_6260359 : Nat := 118140960795 + 6260359 * 2 ^ 59
def prefixEnd_6260359 : Nat := 4983230072969 + 3 ^ 40 * 6260359 * 2
def baseEnd_6260359 : Nat := 3214573236700577050321639

theorem tailTrace_6260359 : CollatzResearch.WordTrace tailWord_6260359 prefixEnd_6260359 3214573236700577050321639 := by
  unfold tailWord_6260359
  simp only [CollatzResearch.WordTrace]
  refine ⟨228334051126796002040208131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152222700751197334693472087 228334051126796002040208131)
  ·
    refine ⟨342501076690194003060312197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228334051126796002040208131 342501076690194003060312197)
    ·
      refine ⟨64218951879411375573808537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 342501076690194003060312197 64218951879411375573808537)
      ·
        refine ⟨48164213909558531680356403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64218951879411375573808537 48164213909558531680356403)
        ·
          refine ⟨72246320864337797520534605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48164213909558531680356403 72246320864337797520534605)
          ·
            refine ⟨27092370324126674070200477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72246320864337797520534605 27092370324126674070200477)
            ·
              refine ⟨10159638871547502776325179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27092370324126674070200477 10159638871547502776325179)
              ·
                refine ⟨15239458307321254164487769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10159638871547502776325179 15239458307321254164487769)
                ·
                  refine ⟨11429593730490940623365827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15239458307321254164487769 11429593730490940623365827)
                  ·
                    refine ⟨17144390595736410935048741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11429593730490940623365827 17144390595736410935048741)
                    ·
                      refine ⟨3214573236700577050321639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17144390595736410935048741 3214573236700577050321639)
                      ·
                        rfl

theorem cell23_6260359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_6260359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260359 prefixEnd_6260359 := by exact prefixLift 6260359
  have htrace : WordTrace (prefixWord ++ tailWord_6260359) baseStart_6260359 baseEnd_6260359 := by
    simpa [prefixWord, tailWord_6260359, baseEnd_6260359] using wordTrace_append hprefix tailTrace_6260359
  have hstable : (prefixWord ++ tailWord_6260359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260359).length < 2 ^ (prefixWord ++ tailWord_6260359).sum := by decide
  have hdescent : baseEnd_6260359 < baseStart_6260359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260399 : List Nat := [1, 1, 2, 1, 2, 4, 5, 1, 6]
def baseStart_6260399 : Nat := 118140960795 + 6260399 * 2 ^ 59
def prefixEnd_6260399 : Nat := 4983230072969 + 3 ^ 40 * 6260399 * 2
def baseEnd_6260399 : Nat := 357177086214084099313495

theorem tailTrace_6260399 : CollatzResearch.WordTrace tailWord_6260399 prefixEnd_6260399 357177086214084099313495 := by
  unfold tailWord_6260399
  simp only [CollatzResearch.WordTrace]
  refine ⟨228335510046651088871664251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152223673364434059247776167 228335510046651088871664251)
  ·
    refine ⟨342503265069976633307496377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228335510046651088871664251 342503265069976633307496377)
    ·
      refine ⟨256877448802482474980622283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342503265069976633307496377 256877448802482474980622283)
      ·
        refine ⟨385316173203723712470933425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256877448802482474980622283 385316173203723712470933425)
        ·
          refine ⟨288987129902792784353200069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385316173203723712470933425 288987129902792784353200069)
          ·
            refine ⟨54185086856773647066225013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 288987129902792784353200069 54185086856773647066225013)
            ·
              refine ⟨5079851892822529412458595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54185086856773647066225013 5079851892822529412458595)
              ·
                refine ⟨7619777839233794118687893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5079851892822529412458595 7619777839233794118687893)
                ·
                  refine ⟨357177086214084099313495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7619777839233794118687893 357177086214084099313495)
                  ·
                    rfl

theorem cell23_6260399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 6].length) (baseStart_6260399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260399 prefixEnd_6260399 := by exact prefixLift 6260399
  have htrace : WordTrace (prefixWord ++ tailWord_6260399) baseStart_6260399 baseEnd_6260399 := by
    simpa [prefixWord, tailWord_6260399, baseEnd_6260399] using wordTrace_append hprefix tailTrace_6260399
  have hstable : (prefixWord ++ tailWord_6260399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260399).length < 2 ^ (prefixWord ++ tailWord_6260399).sum := by decide
  have hdescent : baseEnd_6260399 < baseStart_6260399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260419 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 8, 3, 2]
def baseStart_6260419 : Nat := 118140960795 + 6260419 * 2 ^ 59
def prefixEnd_6260419 : Nat := 4983230072969 + 3 ^ 40 * 6260419 * 2
def baseEnd_6260419 : Nat := 3214604045539846815571363

theorem tailTrace_6260419 : CollatzResearch.WordTrace tailWord_6260419 prefixEnd_6260419 3214604045539846815571363 := by
  unfold tailWord_6260419
  simp only [CollatzResearch.WordTrace]
  refine ⟨228336239506578632287392311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152224159671052421524928207 228336239506578632287392311)
  ·
    refine ⟨342504359259867948431088467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228336239506578632287392311 342504359259867948431088467)
    ·
      refine ⟨513756538889801922646632701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342504359259867948431088467 513756538889801922646632701)
      ·
        refine ⟨192658702083675720992487263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 513756538889801922646632701 192658702083675720992487263)
        ·
          refine ⟨288988053125513581488730895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192658702083675720992487263 288988053125513581488730895)
          ·
            refine ⟨433482079688270372233096343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288988053125513581488730895 433482079688270372233096343)
            ·
              refine ⟨650223119532405558349644515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433482079688270372233096343 650223119532405558349644515)
              ·
                refine ⟨975334679298608337524466773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 650223119532405558349644515 975334679298608337524466773)
                ·
                  refine ⟨11429703273030566455364845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 975334679298608337524466773 11429703273030566455364845)
                  ·
                    refine ⟨4286138727386462420761817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11429703273030566455364845 4286138727386462420761817)
                    ·
                      refine ⟨3214604045539846815571363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4286138727386462420761817 3214604045539846815571363)
                      ·
                        rfl

theorem cell23_6260419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 3, 2].length) (baseStart_6260419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260419 prefixEnd_6260419 := by exact prefixLift 6260419
  have htrace : WordTrace (prefixWord ++ tailWord_6260419) baseStart_6260419 baseEnd_6260419 := by
    simpa [prefixWord, tailWord_6260419, baseEnd_6260419] using wordTrace_append hprefix tailTrace_6260419
  have hstable : (prefixWord ++ tailWord_6260419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260419).length < 2 ^ (prefixWord ++ tailWord_6260419).sum := by decide
  have hdescent : baseEnd_6260419 < baseStart_6260419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260510 : List Nat := [4, 3, 2, 2, 1, 1, 2, 1, 1, 6]
def baseStart_6260510 : Nat := 118140960795 + 6260510 * 2 ^ 59
def prefixEnd_6260510 : Nat := 4983230072969 + 3 ^ 40 * 6260510 * 2
def baseEnd_6260510 : Nat := 1071550257426468653177815

theorem tailTrace_6260510 : CollatzResearch.WordTrace tailWord_6260510 prefixEnd_6260510 1071550257426468653177815 := by
  unfold tailWord_6260510
  simp only [CollatzResearch.WordTrace]
  refine ⟨28542444818656119353619373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152226372366165969885969989 28542444818656119353619373)
  ·
    refine ⟨10703416806996044757607265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28542444818656119353619373 10703416806996044757607265)
    ·
      refine ⟨8027562605247033568205449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10703416806996044757607265 8027562605247033568205449)
      ·
        refine ⟨6020671953935275176154087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8027562605247033568205449 6020671953935275176154087)
        ·
          refine ⟨9031007930902912764231131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6020671953935275176154087 9031007930902912764231131)
          ·
            refine ⟨13546511896354369146346697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9031007930902912764231131 13546511896354369146346697)
            ·
              refine ⟨10159883922265776859760023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13546511896354369146346697 10159883922265776859760023)
              ·
                refine ⟨15239825883398665289640035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10159883922265776859760023 15239825883398665289640035)
                ·
                  refine ⟨22859738825097997934460053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15239825883398665289640035 22859738825097997934460053)
                  ·
                    refine ⟨1071550257426468653177815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22859738825097997934460053 1071550257426468653177815)
                    ·
                      rfl

theorem cell23_6260510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_6260510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260510 prefixEnd_6260510 := by exact prefixLift 6260510
  have htrace : WordTrace (prefixWord ++ tailWord_6260510) baseStart_6260510 baseEnd_6260510 := by
    simpa [prefixWord, tailWord_6260510, baseEnd_6260510] using wordTrace_append hprefix tailTrace_6260510
  have hstable : (prefixWord ++ tailWord_6260510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260510).length < 2 ^ (prefixWord ++ tailWord_6260510).sum := by decide
  have hdescent : baseEnd_6260510 < baseStart_6260510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260516 : List Nat := [2, 3, 1, 3, 2, 1, 1, 3, 1, 3, 3]
def baseStart_6260516 : Nat := 118140960795 + 6260516 * 2 ^ 59
def prefixEnd_6260516 : Nat := 4983230072969 + 3 ^ 40 * 6260516 * 2
def baseEnd_6260516 : Nat := 3214653853163332936058417

theorem tailTrace_6260516 : CollatzResearch.WordTrace tailWord_6260516 prefixEnd_6260516 3214653853163332936058417 := by
  unfold tailWord_6260516
  simp only [CollatzResearch.WordTrace]
  refine ⟨114169888693613608926836701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152226518258151478569115601 114169888693613608926836701)
  ·
    refine ⟨42813708260105103347563763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114169888693613608926836701 42813708260105103347563763)
    ·
      refine ⟨64220562390157655021345645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42813708260105103347563763 64220562390157655021345645)
      ·
        refine ⟨24082710896309120633004617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64220562390157655021345645 24082710896309120633004617)
        ·
          refine ⟨18062033172231840474753463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24082710896309120633004617 18062033172231840474753463)
          ·
            refine ⟨27093049758347760712130195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18062033172231840474753463 27093049758347760712130195)
            ·
              refine ⟨40639574637521641068195293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27093049758347760712130195 40639574637521641068195293)
              ·
                refine ⟨15239840489070615400573235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40639574637521641068195293 15239840489070615400573235)
                ·
                  refine ⟨22859760733605923100859853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15239840489070615400573235 22859760733605923100859853)
                  ·
                    refine ⟨8572410275102221162822445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22859760733605923100859853 8572410275102221162822445)
                    ·
                      refine ⟨3214653853163332936058417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8572410275102221162822445 3214653853163332936058417)
                      ·
                        rfl

theorem cell23_6260516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_6260516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260516 prefixEnd_6260516 := by exact prefixLift 6260516
  have htrace : WordTrace (prefixWord ++ tailWord_6260516) baseStart_6260516 baseEnd_6260516 := by
    simpa [prefixWord, tailWord_6260516, baseEnd_6260516] using wordTrace_append hprefix tailTrace_6260516
  have hstable : (prefixWord ++ tailWord_6260516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260516).length < 2 ^ (prefixWord ++ tailWord_6260516).sum := by decide
  have hdescent : baseEnd_6260516 < baseStart_6260516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260534 : List Nat := [5, 1, 2, 2, 1, 2, 2, 3, 1, 2, 2]
def baseStart_6260534 : Nat := 118140960795 + 6260534 * 2 ^ 59
def prefixEnd_6260534 : Nat := 4983230072969 + 3 ^ 40 * 6260534 * 2
def baseEnd_6260534 : Nat := 3214663095815113865633335

theorem tailTrace_6260534 : CollatzResearch.WordTrace tailWord_6260534 prefixEnd_6260534 3214663095815113865633335 := by
  unfold tailWord_6260534
  simp only [CollatzResearch.WordTrace]
  refine ⟨14271277118822625432989291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152226955934108004618552437 14271277118822625432989291)
  ·
    refine ⟨21406915678233938149483937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14271277118822625432989291 21406915678233938149483937)
    ·
      refine ⟨16055186758675453612112953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21406915678233938149483937 16055186758675453612112953)
      ·
        refine ⟨12041390069006590209084715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16055186758675453612112953 12041390069006590209084715)
        ·
          refine ⟨18062085103509885313627073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12041390069006590209084715 18062085103509885313627073)
          ·
            refine ⟨13546563827632413985220305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18062085103509885313627073 13546563827632413985220305)
            ·
              refine ⟨10159922870724310488915229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13546563827632413985220305 10159922870724310488915229)
              ·
                refine ⟨3809971076521616433343211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10159922870724310488915229 3809971076521616433343211)
                ·
                  refine ⟨5714956614782424650014817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3809971076521616433343211 5714956614782424650014817)
                  ·
                    refine ⟨4286217461086818487511113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5714956614782424650014817 4286217461086818487511113)
                    ·
                      refine ⟨3214663095815113865633335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4286217461086818487511113 3214663095815113865633335)
                      ·
                        rfl

theorem cell23_6260534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_6260534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260534 prefixEnd_6260534 := by exact prefixLift 6260534
  have htrace : WordTrace (prefixWord ++ tailWord_6260534) baseStart_6260534 baseEnd_6260534 := by
    simpa [prefixWord, tailWord_6260534, baseEnd_6260534] using wordTrace_append hprefix tailTrace_6260534
  have hstable : (prefixWord ++ tailWord_6260534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260534).length < 2 ^ (prefixWord ++ tailWord_6260534).sum := by decide
  have hdescent : baseEnd_6260534 < baseStart_6260534 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260537 : List Nat := [1, 2, 1, 7, 1, 2, 2, 1, 1, 2, 3]
def baseStart_6260537 : Nat := 118140960795 + 6260537 * 2 ^ 59
def prefixEnd_6260537 : Nat := 4983230072969 + 3 ^ 40 * 6260537 * 2
def baseEnd_6260537 : Nat := 3214664636257077353895821

theorem tailTrace_6260537 : CollatzResearch.WordTrace tailWord_6260537 prefixEnd_6260537 3214664636257077353895821 := by
  unfold tailWord_6260537
  simp only [CollatzResearch.WordTrace]
  refine ⟨228340543320151138440187865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152227028880100758960125243 228340543320151138440187865)
  ·
    refine ⟨171255407490113353830140899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228340543320151138440187865 171255407490113353830140899)
    ·
      refine ⟨256883111235170030745211349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171255407490113353830140899 256883111235170030745211349)
      ·
        refine ⟨6020697919574297595590891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 256883111235170030745211349 6020697919574297595590891)
        ·
          refine ⟨9031046879361446393386337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6020697919574297595590891 9031046879361446393386337)
          ·
            refine ⟨6773285159521084795039753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9031046879361446393386337 6773285159521084795039753)
            ·
              refine ⟨5079963869640813596279815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6773285159521084795039753 5079963869640813596279815)
              ·
                refine ⟨7619945804461220394419723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5079963869640813596279815 7619945804461220394419723)
                ·
                  refine ⟨11429918706691830591629585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7619945804461220394419723 11429918706691830591629585)
                  ·
                    refine ⟨8572439030018872943722189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11429918706691830591629585 8572439030018872943722189)
                    ·
                      refine ⟨3214664636257077353895821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8572439030018872943722189 3214664636257077353895821)
                      ·
                        rfl

theorem cell23_6260537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_6260537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260537 prefixEnd_6260537 := by exact prefixLift 6260537
  have htrace : WordTrace (prefixWord ++ tailWord_6260537) baseStart_6260537 baseEnd_6260537 := by
    simpa [prefixWord, tailWord_6260537, baseEnd_6260537] using wordTrace_append hprefix tailTrace_6260537
  have hstable : (prefixWord ++ tailWord_6260537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260537).length < 2 ^ (prefixWord ++ tailWord_6260537).sum := by decide
  have hdescent : baseEnd_6260537 < baseStart_6260537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260569 : List Nat := [1, 2, 1, 2, 2, 3, 1, 3, 2, 2, 4]
def baseStart_6260569 : Nat := 118140960795 + 6260569 * 2 ^ 59
def prefixEnd_6260569 : Nat := 4983230072969 + 3 ^ 40 * 6260569 * 2
def baseEnd_6260569 : Nat := 3214681067638021228695673

theorem tailTrace_6260569 : CollatzResearch.WordTrace tailWord_6260569 prefixEnd_6260569 3214681067638021228695673 := by
  unfold tailWord_6260569
  simp only [CollatzResearch.WordTrace]
  refine ⟨228341710456035207905352761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152227806970690138603568507 228341710456035207905352761)
  ·
    refine ⟨171256282842026405929014571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228341710456035207905352761 171256282842026405929014571)
    ·
      refine ⟨256884424263039608893521857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171256282842026405929014571 256884424263039608893521857)
      ·
        refine ⟨192663318197279706670141393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256884424263039608893521857 192663318197279706670141393)
        ·
          refine ⟨144497488647959780002606045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192663318197279706670141393 144497488647959780002606045)
          ·
            refine ⟨54186558242984917500977267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144497488647959780002606045 54186558242984917500977267)
            ·
              refine ⟨81279837364477376251465901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54186558242984917500977267 81279837364477376251465901)
              ·
                refine ⟨30479939011679016094299713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81279837364477376251465901 30479939011679016094299713)
                ·
                  refine ⟨22859954258759262070724785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30479939011679016094299713 22859954258759262070724785)
                  ·
                    refine ⟨17144965694069446553043589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22859954258759262070724785 17144965694069446553043589)
                    ·
                      refine ⟨3214681067638021228695673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17144965694069446553043589 3214681067638021228695673)
                      ·
                        rfl

theorem cell23_6260569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_6260569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260569 prefixEnd_6260569 := by exact prefixLift 6260569
  have htrace : WordTrace (prefixWord ++ tailWord_6260569) baseStart_6260569 baseEnd_6260569 := by
    simpa [prefixWord, tailWord_6260569, baseEnd_6260569] using wordTrace_append hprefix tailTrace_6260569
  have hstable : (prefixWord ++ tailWord_6260569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260569).length < 2 ^ (prefixWord ++ tailWord_6260569).sum := by decide
  have hdescent : baseEnd_6260569 < baseStart_6260569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260590 : List Nat := [4, 1, 2, 3, 1, 1, 1, 2, 4, 2, 2]
def baseStart_6260590 : Nat := 118140960795 + 6260590 * 2 ^ 59
def prefixEnd_6260590 : Nat := 4983230072969 + 3 ^ 40 * 6260590 * 2
def baseEnd_6260590 : Nat := 3214691850731765646533077

theorem tailTrace_6260590 : CollatzResearch.WordTrace tailWord_6260590 prefixEnd_6260590 3214691850731765646533077 := by
  unfold tailWord_6260590
  simp only [CollatzResearch.WordTrace]
  refine ⟨28542809548619891061483403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152228317592639418994578149 28542809548619891061483403)
  ·
    refine ⟨42814214322929836592225105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28542809548619891061483403 42814214322929836592225105)
    ·
      refine ⟨32110660742197377444168829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42814214322929836592225105 32110660742197377444168829)
      ·
        refine ⟨12041497778324016541563311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32110660742197377444168829 12041497778324016541563311)
        ·
          refine ⟨18062246667486024812344967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12041497778324016541563311 18062246667486024812344967)
          ·
            refine ⟨27093370001229037218517451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18062246667486024812344967 27093370001229037218517451)
            ·
              refine ⟨40640055001843555827776177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27093370001229037218517451 40640055001843555827776177)
              ·
                refine ⟨30480041251382666870832133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40640055001843555827776177 30480041251382666870832133)
                ·
                  refine ⟨5715007734634250038281025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30480041251382666870832133 5715007734634250038281025)
                  ·
                    refine ⟨4286255800975687528710769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5715007734634250038281025 4286255800975687528710769)
                    ·
                      refine ⟨3214691850731765646533077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4286255800975687528710769 3214691850731765646533077)
                      ·
                        rfl

theorem cell23_6260590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_6260590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260590 prefixEnd_6260590 := by exact prefixLift 6260590
  have htrace : WordTrace (prefixWord ++ tailWord_6260590) baseStart_6260590 baseEnd_6260590 := by
    simpa [prefixWord, tailWord_6260590, baseEnd_6260590] using wordTrace_append hprefix tailTrace_6260590
  have hstable : (prefixWord ++ tailWord_6260590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260590).length < 2 ^ (prefixWord ++ tailWord_6260590).sum := by decide
  have hdescent : baseEnd_6260590 < baseStart_6260590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260613 : List Nat := [1, 3, 1, 1, 3, 2, 5, 2, 5]
def baseStart_6260613 : Nat := 118140960795 + 6260613 * 2 ^ 59
def prefixEnd_6260613 : Nat := 4983230072969 + 3 ^ 40 * 6260613 * 2
def baseEnd_6260613 : Nat := 357189295642979895171719

theorem tailTrace_6260613 : CollatzResearch.WordTrace tailWord_6260613 prefixEnd_6260613 357189295642979895171719 := by
  unfold tailWord_6260613
  simp only [CollatzResearch.WordTrace]
  refine ⟨228343315267875803419954493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152228876845250535613302995 228343315267875803419954493)
  ·
    refine ⟨85628743225453426282482935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228343315267875803419954493 85628743225453426282482935)
    ·
      refine ⟨128443114838180139423724403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85628743225453426282482935 128443114838180139423724403)
      ·
        refine ⟨192664672257270209135586605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128443114838180139423724403 192664672257270209135586605)
        ·
          refine ⟨72249252096476328425844977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192664672257270209135586605 72249252096476328425844977)
          ·
            refine ⟨54186939072357246319383733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72249252096476328425844977 54186939072357246319383733)
            ·
              refine ⟨5080025538033491842442225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54186939072357246319383733 5080025538033491842442225)
              ·
                refine ⟨3810019153525118881831669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5080025538033491842442225 3810019153525118881831669)
                ·
                  refine ⟨357189295642979895171719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3810019153525118881831669 357189295642979895171719)
                  ·
                    rfl

theorem cell23_6260613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 2, 5].length) (baseStart_6260613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260613 prefixEnd_6260613 := by exact prefixLift 6260613
  have htrace : WordTrace (prefixWord ++ tailWord_6260613) baseStart_6260613 baseEnd_6260613 := by
    simpa [prefixWord, tailWord_6260613, baseEnd_6260613] using wordTrace_append hprefix tailTrace_6260613
  have hstable : (prefixWord ++ tailWord_6260613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260613).length < 2 ^ (prefixWord ++ tailWord_6260613).sum := by decide
  have hdescent : baseEnd_6260613 < baseStart_6260613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260659 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 6]
def baseStart_6260659 : Nat := 118140960795 + 6260659 * 2 ^ 59
def prefixEnd_6260659 : Nat := 4983230072969 + 3 ^ 40 * 6260659 * 2
def baseEnd_6260659 : Nat := 3214727280896925876570259

theorem tailTrace_6260659 : CollatzResearch.WordTrace tailWord_6260659 prefixEnd_6260659 3214727280896925876570259 := by
  unfold tailWord_6260659
  simp only [CollatzResearch.WordTrace]
  refine ⟨228344993025709153276129031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152229995350472768850752687 228344993025709153276129031)
  ·
    refine ⟨342517489538563729914193547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228344993025709153276129031 342517489538563729914193547)
    ·
      refine ⟨513776234307845594871290321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342517489538563729914193547 513776234307845594871290321)
      ·
        refine ⟨385332175730884196153467741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 513776234307845594871290321 385332175730884196153467741)
        ·
          refine ⟨144499565899081573557550403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 385332175730884196153467741 144499565899081573557550403)
          ·
            refine ⟨216749348848622360336325605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144499565899081573557550403 216749348848622360336325605)
            ·
              refine ⟨40640502909116692563061051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 216749348848622360336325605 40640502909116692563061051)
              ·
                refine ⟨60960754363675038844591577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40640502909116692563061051 60960754363675038844591577)
                ·
                  refine ⟨45720565772756279133443683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60960754363675038844591577 45720565772756279133443683)
                  ·
                    refine ⟨68580848659134418700165525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45720565772756279133443683 68580848659134418700165525)
                    ·
                      refine ⟨3214727280896925876570259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68580848659134418700165525 3214727280896925876570259)
                      ·
                        rfl

theorem cell23_6260659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 6].length) (baseStart_6260659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260659 prefixEnd_6260659 := by exact prefixLift 6260659
  have htrace : WordTrace (prefixWord ++ tailWord_6260659) baseStart_6260659 baseEnd_6260659 := by
    simpa [prefixWord, tailWord_6260659, baseEnd_6260659] using wordTrace_append hprefix tailTrace_6260659
  have hstable : (prefixWord ++ tailWord_6260659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260659).length < 2 ^ (prefixWord ++ tailWord_6260659).sum := by decide
  have hdescent : baseEnd_6260659 < baseStart_6260659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260666 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 4, 2, 3]
def baseStart_6260666 : Nat := 118140960795 + 6260666 * 2 ^ 59
def prefixEnd_6260666 : Nat := 4983230072969 + 3 ^ 40 * 6260666 * 2
def baseEnd_6260666 : Nat := 3214730875261507349182727

theorem tailTrace_6260666 : CollatzResearch.WordTrace tailWord_6260666 prefixEnd_6260666 3214730875261507349182727 := by
  unfold tailWord_6260666
  simp only [CollatzResearch.WordTrace]
  refine ⟨57086312084170948367908463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152230165557789195647755901 57086312084170948367908463)
  ·
    refine ⟨85629468126256422551862695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57086312084170948367908463 85629468126256422551862695)
    ·
      refine ⟨128444202189384633827794043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85629468126256422551862695 128444202189384633827794043)
      ·
        refine ⟨192666303284076950741691065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128444202189384633827794043 192666303284076950741691065)
        ·
          refine ⟨144499727463057713056268299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192666303284076950741691065 144499727463057713056268299)
          ·
            refine ⟨216749591194586569584402449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144499727463057713056268299 216749591194586569584402449)
            ·
              refine ⟨162562193395939927188301837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216749591194586569584402449 162562193395939927188301837)
              ·
                refine ⟨60960822523477472695613189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162562193395939927188301837 60960822523477472695613189)
                ·
                  refine ⟨11430154223152026130427473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60960822523477472695613189 11430154223152026130427473)
                  ·
                    refine ⟨8572615667364019597820605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11430154223152026130427473 8572615667364019597820605)
                    ·
                      refine ⟨3214730875261507349182727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8572615667364019597820605 3214730875261507349182727)
                      ·
                        rfl

theorem cell23_6260666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 4, 2, 3].length) (baseStart_6260666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260666 prefixEnd_6260666 := by exact prefixLift 6260666
  have htrace : WordTrace (prefixWord ++ tailWord_6260666) baseStart_6260666 baseEnd_6260666 := by
    simpa [prefixWord, tailWord_6260666, baseEnd_6260666] using wordTrace_append hprefix tailTrace_6260666
  have hstable : (prefixWord ++ tailWord_6260666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260666).length < 2 ^ (prefixWord ++ tailWord_6260666).sum := by decide
  have hdescent : baseEnd_6260666 < baseStart_6260666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260686 : List Nat := [4, 1, 1, 1, 2, 2, 1, 5, 6]
def baseStart_6260686 : Nat := 118140960795 + 6260686 * 2 ^ 59
def prefixEnd_6260686 : Nat := 4983230072969 + 3 ^ 40 * 6260686 * 2
def baseEnd_6260686 : Nat := 357193460541621918992515

theorem tailTrace_6260686 : CollatzResearch.WordTrace tailWord_6260686 prefixEnd_6260686 357193460541621918992515 := by
  unfold tailWord_6260686
  simp only [CollatzResearch.WordTrace]
  refine ⟨28543247224576417110920239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152230651864407557924907941 28543247224576417110920239)
  ·
    refine ⟨42814870836864625666380359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28543247224576417110920239 42814870836864625666380359)
    ·
      refine ⟨64222306255296938499570539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42814870836864625666380359 64222306255296938499570539)
      ·
        refine ⟨96333459382945407749355809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64222306255296938499570539 96333459382945407749355809)
        ·
          refine ⟨72250094537209055812016857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96333459382945407749355809 72250094537209055812016857)
          ·
            refine ⟨54187570902906791859012643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72250094537209055812016857 54187570902906791859012643)
            ·
              refine ⟨81281356354360187788518965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54187570902906791859012643 81281356354360187788518965)
              ·
                refine ⟨7620127158221267605173653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81281356354360187788518965 7620127158221267605173653)
                ·
                  refine ⟨357193460541621918992515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7620127158221267605173653 357193460541621918992515)
                  ·
                    rfl

theorem cell23_6260686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 6].length) (baseStart_6260686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260686 prefixEnd_6260686 := by exact prefixLift 6260686
  have htrace : WordTrace (prefixWord ++ tailWord_6260686) baseStart_6260686 baseEnd_6260686 := by
    simpa [prefixWord, tailWord_6260686, baseEnd_6260686] using wordTrace_append hprefix tailTrace_6260686
  have hstable : (prefixWord ++ tailWord_6260686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260686).length < 2 ^ (prefixWord ++ tailWord_6260686).sum := by decide
  have hdescent : baseEnd_6260686 < baseStart_6260686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260689 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 3, 2, 6]
def baseStart_6260689 : Nat := 118140960795 + 6260689 * 2 ^ 59
def prefixEnd_6260689 : Nat := 4983230072969 + 3 ^ 40 * 6260689 * 2
def baseEnd_6260689 : Nat := 3214742685316560759195121

theorem tailTrace_6260689 : CollatzResearch.WordTrace tailWord_6260689 prefixEnd_6260689 3214742685316560759195121 := by
  unfold tailWord_6260689
  simp only [CollatzResearch.WordTrace]
  refine ⟨228346087215600468399721121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152230724810400312266480747 228346087215600468399721121)
  ·
    refine ⟨171259565411700351299790841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228346087215600468399721121 171259565411700351299790841)
    ·
      refine ⟨128444674058775263474843131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171259565411700351299790841 128444674058775263474843131)
      ·
        refine ⟨192667011088162895212264697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128444674058775263474843131 192667011088162895212264697)
        ·
          refine ⟨144500258316122171409198523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192667011088162895212264697 144500258316122171409198523)
          ·
            refine ⟨216750387474183257113797785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144500258316122171409198523 216750387474183257113797785)
            ·
              refine ⟨162562790605637442835348339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216750387474183257113797785 162562790605637442835348339)
              ·
                refine ⟨243844185908456164253022509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162562790605637442835348339 243844185908456164253022509)
                ·
                  refine ⟨91441569715671061594883441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 243844185908456164253022509 91441569715671061594883441)
                  ·
                    refine ⟨68581177286753296196162581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91441569715671061594883441 68581177286753296196162581)
                    ·
                      refine ⟨3214742685316560759195121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68581177286753296196162581 3214742685316560759195121)
                      ·
                        rfl

theorem cell23_6260689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_6260689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260689 prefixEnd_6260689 := by exact prefixLift 6260689
  have htrace : WordTrace (prefixWord ++ tailWord_6260689) baseStart_6260689 baseEnd_6260689 := by
    simpa [prefixWord, tailWord_6260689, baseEnd_6260689] using wordTrace_append hprefix tailTrace_6260689
  have hstable : (prefixWord ++ tailWord_6260689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260689).length < 2 ^ (prefixWord ++ tailWord_6260689).sum := by decide
  have hdescent : baseEnd_6260689 < baseStart_6260689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260690 : List Nat := [3, 2, 2, 3, 2, 1, 1, 2, 3, 4]
def baseStart_6260690 : Nat := 118140960795 + 6260690 * 2 ^ 59
def prefixEnd_6260690 : Nat := 4983230072969 + 3 ^ 40 * 6260690 * 2
def baseEnd_6260690 : Nat := 1071581066265738418427539

theorem tailTrace_6260690 : CollatzResearch.WordTrace tailWord_6260690 prefixEnd_6260690 1071581066265738418427539 := by
  unfold tailWord_6260690
  simp only [CollatzResearch.WordTrace]
  refine ⟨57086530922149211392626881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152230749125731230380338349 57086530922149211392626881)
  ·
    refine ⟨42814898191611908544470161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57086530922149211392626881 42814898191611908544470161)
    ·
      refine ⟨32111173643708931408352621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42814898191611908544470161 32111173643708931408352621)
      ·
        refine ⟨12041690116390849278132233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32111173643708931408352621 12041690116390849278132233)
        ·
          refine ⟨9031267587293136958599175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12041690116390849278132233 9031267587293136958599175)
          ·
            refine ⟨13546901380939705437898763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9031267587293136958599175 13546901380939705437898763)
            ·
              refine ⟨20320352071409558156848145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13546901380939705437898763 20320352071409558156848145)
              ·
                refine ⟨15240264053557168617636109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20320352071409558156848145 15240264053557168617636109)
                ·
                  refine ⟨5715099020083938231613541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15240264053557168617636109 5715099020083938231613541)
                  ·
                    refine ⟨1071581066265738418427539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5715099020083938231613541 1071581066265738418427539)
                    ·
                      rfl

theorem cell23_6260690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_6260690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260690 prefixEnd_6260690 := by exact prefixLift 6260690
  have htrace : WordTrace (prefixWord ++ tailWord_6260690) baseStart_6260690 baseEnd_6260690 := by
    simpa [prefixWord, tailWord_6260690, baseEnd_6260690] using wordTrace_append hprefix tailTrace_6260690
  have hstable : (prefixWord ++ tailWord_6260690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260690).length < 2 ^ (prefixWord ++ tailWord_6260690).sum := by decide
  have hdescent : baseEnd_6260690 < baseStart_6260690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260723 : List Nat := [1, 1, 1, 2, 2, 2, 1, 6, 2, 3, 2]
def baseStart_6260723 : Nat := 118140960795 + 6260723 * 2 ^ 59
def prefixEnd_6260723 : Nat := 4983230072969 + 3 ^ 40 * 6260723 * 2
def baseEnd_6260723 : Nat := 3214760143658813626169965

theorem tailTrace_6260723 : CollatzResearch.WordTrace tailWord_6260723 prefixEnd_6260723 3214760143658813626169965 := by
  unfold tailWord_6260723
  simp only [CollatzResearch.WordTrace]
  refine ⟨228347327297477292206458823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152231551531651528137639215 228347327297477292206458823)
  ·
    refine ⟨342520990946215938309688235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228347327297477292206458823 342520990946215938309688235)
    ·
      refine ⟨513781486419323907464532353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342520990946215938309688235 513781486419323907464532353)
      ·
        refine ⟨385336114814492930598399265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 513781486419323907464532353 385336114814492930598399265)
        ·
          refine ⟨289002086110869697948799449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385336114814492930598399265 289002086110869697948799449)
          ·
            refine ⟨216751564583152273461599587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289002086110869697948799449 216751564583152273461599587)
            ·
              refine ⟨325127346874728410192399381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216751564583152273461599587 325127346874728410192399381)
              ·
                refine ⟨15240344384752894227768721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 325127346874728410192399381 15240344384752894227768721)
                ·
                  refine ⟨11430258288564670670826541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15240344384752894227768721 11430258288564670670826541)
                  ·
                    refine ⟨4286346858211751501559953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11430258288564670670826541 4286346858211751501559953)
                    ·
                      refine ⟨3214760143658813626169965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4286346858211751501559953 3214760143658813626169965)
                      ·
                        rfl

theorem cell23_6260723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 3, 2].length) (baseStart_6260723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260723 prefixEnd_6260723 := by exact prefixLift 6260723
  have htrace : WordTrace (prefixWord ++ tailWord_6260723) baseStart_6260723 baseEnd_6260723 := by
    simpa [prefixWord, tailWord_6260723, baseEnd_6260723] using wordTrace_append hprefix tailTrace_6260723
  have hstable : (prefixWord ++ tailWord_6260723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260723).length < 2 ^ (prefixWord ++ tailWord_6260723).sum := by decide
  have hdescent : baseEnd_6260723 < baseStart_6260723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260736 : List Nat := [2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 4]
def baseStart_6260736 : Nat := 118140960795 + 6260736 * 2 ^ 59
def prefixEnd_6260736 : Nat := 4983230072969 + 3 ^ 40 * 6260736 * 2
def baseEnd_6260736 : Nat := 3214766818907322075307405

theorem tailTrace_6260736 : CollatzResearch.WordTrace tailWord_6260736 prefixEnd_6260736 3214766818907322075307405 := by
  unfold tailWord_6260736
  simp only [CollatzResearch.WordTrace]
  refine ⟨114173900723215097713341031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152231867630953463617788041 114173900723215097713341031)
  ·
    refine ⟨171260851084822646570011547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114173900723215097713341031 171260851084822646570011547)
    ·
      refine ⟨256891276627233969855017321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171260851084822646570011547 256891276627233969855017321)
      ·
        refine ⟨192668457470425477391262991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256891276627233969855017321 192668457470425477391262991)
        ·
          refine ⟨289002686205638216086894487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192668457470425477391262991 289002686205638216086894487)
          ·
            refine ⟨433504029308457324130341731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289002686205638216086894487 433504029308457324130341731)
            ·
              refine ⟨650256043962685986195512597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433504029308457324130341731 650256043962685986195512597)
              ·
                refine ⟨30480752060750905602914653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 650256043962685986195512597 30480752060750905602914653)
                ·
                  refine ⟨11430282022781589601092995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30480752060750905602914653 11430282022781589601092995)
                  ·
                    refine ⟨17145423034172384401639493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11430282022781589601092995 17145423034172384401639493)
                    ·
                      refine ⟨3214766818907322075307405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17145423034172384401639493 3214766818907322075307405)
                      ·
                        rfl

theorem cell23_6260736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_6260736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260736 prefixEnd_6260736 := by exact prefixLift 6260736
  have htrace : WordTrace (prefixWord ++ tailWord_6260736) baseStart_6260736 baseEnd_6260736 := by
    simpa [prefixWord, tailWord_6260736, baseEnd_6260736] using wordTrace_append hprefix tailTrace_6260736
  have hstable : (prefixWord ++ tailWord_6260736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260736).length < 2 ^ (prefixWord ++ tailWord_6260736).sum := by decide
  have hdescent : baseEnd_6260736 < baseStart_6260736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260764 : List Nat := [2, 2, 3, 1, 3, 3, 1, 3, 1, 1, 3]
def baseStart_6260764 : Nat := 118140960795 + 6260764 * 2 ^ 59
def prefixEnd_6260764 : Nat := 4983230072969 + 3 ^ 40 * 6260764 * 2
def baseEnd_6260764 : Nat := 3214781196365647965757277

theorem tailTrace_6260764 : CollatzResearch.WordTrace tailWord_6260764 prefixEnd_6260764 3214781196365647965757277 := by
  unfold tailWord_6260764
  simp only [CollatzResearch.WordTrace]
  refine ⟨114174411345164378104350673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152232548460219170805800897 114174411345164378104350673)
  ·
    refine ⟨85630808508873283578263005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114174411345164378104350673 85630808508873283578263005)
    ·
      refine ⟨32111553190827481341848627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85630808508873283578263005 32111553190827481341848627)
      ·
        refine ⟨48167329786241222012772941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32111553190827481341848627 48167329786241222012772941)
        ·
          refine ⟨18062748669840458254789853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48167329786241222012772941 18062748669840458254789853)
          ·
            refine ⟨6773530751190171845546195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18062748669840458254789853 6773530751190171845546195)
            ·
              refine ⟨10160296126785257768319293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6773530751190171845546195 10160296126785257768319293)
              ·
                refine ⟨3810111047544471663119735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10160296126785257768319293 3810111047544471663119735)
                ·
                  refine ⟨5715166571316707494679603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3810111047544471663119735 5715166571316707494679603)
                  ·
                    refine ⟨8572749856975061242019405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5715166571316707494679603 8572749856975061242019405)
                    ·
                      refine ⟨3214781196365647965757277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8572749856975061242019405 3214781196365647965757277)
                      ·
                        rfl

theorem cell23_6260764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_6260764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260764 prefixEnd_6260764 := by exact prefixLift 6260764
  have htrace : WordTrace (prefixWord ++ tailWord_6260764) baseStart_6260764 baseEnd_6260764 := by
    simpa [prefixWord, tailWord_6260764, baseEnd_6260764] using wordTrace_append hprefix tailTrace_6260764
  have hstable : (prefixWord ++ tailWord_6260764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260764).length < 2 ^ (prefixWord ++ tailWord_6260764).sum := by decide
  have hdescent : baseEnd_6260764 < baseStart_6260764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260773 : List Nat := [1, 3, 1, 2, 2, 4, 2, 1, 1, 1, 5]
def baseStart_6260773 : Nat := 118140960795 + 6260773 * 2 ^ 59
def prefixEnd_6260773 : Nat := 4983230072969 + 3 ^ 40 * 6260773 * 2
def baseEnd_6260773 : Nat := 3214785817691538430544735

theorem tailTrace_6260773 : CollatzResearch.WordTrace tailWord_6260773 prefixEnd_6260773 3214785817691538430544735 := by
  unfold tailWord_6260773
  simp only [CollatzResearch.WordTrace]
  refine ⟨228349150947296150745778973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152232767298197433830519315 228349150947296150745778973)
  ·
    refine ⟨85630931605236056529667115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228349150947296150745778973 85630931605236056529667115)
    ·
      refine ⟨128446397407854084794500673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85630931605236056529667115 128446397407854084794500673)
      ·
        refine ⟨96334798055890563595875505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128446397407854084794500673 96334798055890563595875505)
        ·
          refine ⟨72251098541917922696906629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96334798055890563595875505 72251098541917922696906629)
          ·
            refine ⟨13547080976609610505669993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72251098541917922696906629 13547080976609610505669993)
            ·
              refine ⟨10160310732457207879252495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13547080976609610505669993 10160310732457207879252495)
              ·
                refine ⟨15240466098685811818878743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10160310732457207879252495 15240466098685811818878743)
                ·
                  refine ⟨22860699148028717728318115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15240466098685811818878743 22860699148028717728318115)
                  ·
                    refine ⟨34291048722043076592477173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22860699148028717728318115 34291048722043076592477173)
                    ·
                      refine ⟨3214785817691538430544735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34291048722043076592477173 3214785817691538430544735)
                      ·
                        rfl

theorem cell23_6260773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_6260773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260773 prefixEnd_6260773 := by exact prefixLift 6260773
  have htrace : WordTrace (prefixWord ++ tailWord_6260773) baseStart_6260773 baseEnd_6260773 := by
    simpa [prefixWord, tailWord_6260773, baseEnd_6260773] using wordTrace_append hprefix tailTrace_6260773
  have hstable : (prefixWord ++ tailWord_6260773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260773).length < 2 ^ (prefixWord ++ tailWord_6260773).sum := by decide
  have hdescent : baseEnd_6260773 < baseStart_6260773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260787 : List Nat := [1, 1, 1, 2, 4, 1, 2, 6, 1, 2, 2]
def baseStart_6260787 : Nat := 118140960795 + 6260787 * 2 ^ 59
def prefixEnd_6260787 : Nat := 4983230072969 + 3 ^ 40 * 6260787 * 2
def baseEnd_6260787 : Nat := 3214793006420701375769671

theorem tailTrace_6260787 : CollatzResearch.WordTrace tailWord_6260787 prefixEnd_6260787 3214793006420701375769671 := by
  unfold tailWord_6260787
  simp only [CollatzResearch.WordTrace]
  refine ⟨228349661569245431136788615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152233107712830287424525743 228349661569245431136788615)
  ·
    refine ⟨342524492353868146705182923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228349661569245431136788615 342524492353868146705182923)
    ·
      refine ⟨513786738530802220057774385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342524492353868146705182923 513786738530802220057774385)
      ·
        refine ⟨385340053898101665043330789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 513786738530802220057774385 385340053898101665043330789)
        ·
          refine ⟨72251260105894062195624523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 385340053898101665043330789 72251260105894062195624523)
          ·
            refine ⟨108376890158841093293436785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72251260105894062195624523 108376890158841093293436785)
            ·
              refine ⟨81282667619130819970077589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108376890158841093293436785 81282667619130819970077589)
              ·
                refine ⟨3810125044646757186097387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81282667619130819970077589 3810125044646757186097387)
                ·
                  refine ⟨5715187566970135779146081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3810125044646757186097387 5715187566970135779146081)
                  ·
                    refine ⟨4286390675227601834359561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5715187566970135779146081 4286390675227601834359561)
                    ·
                      refine ⟨3214793006420701375769671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4286390675227601834359561 3214793006420701375769671)
                      ·
                        rfl

theorem cell23_6260787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 6, 1, 2, 2].length) (baseStart_6260787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260787 prefixEnd_6260787 := by exact prefixLift 6260787
  have htrace : WordTrace (prefixWord ++ tailWord_6260787) baseStart_6260787 baseEnd_6260787 := by
    simpa [prefixWord, tailWord_6260787, baseEnd_6260787] using wordTrace_append hprefix tailTrace_6260787
  have hstable : (prefixWord ++ tailWord_6260787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260787).length < 2 ^ (prefixWord ++ tailWord_6260787).sum := by decide
  have hdescent : baseEnd_6260787 < baseStart_6260787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260790 : List Nat := [5, 1, 2, 1, 1, 1, 2, 2, 3, 2, 3]
def baseStart_6260790 : Nat := 118140960795 + 6260790 * 2 ^ 59
def prefixEnd_6260790 : Nat := 4983230072969 + 3 ^ 40 * 6260790 * 2
def baseEnd_6260790 : Nat := 3214794546862664864032157

theorem tailTrace_6260790 : CollatzResearch.WordTrace tailWord_6260790 prefixEnd_6260790 3214794546862664864032157 := by
  unfold tailWord_6260790
  simp only [CollatzResearch.WordTrace]
  refine ⟨14271860686764660165571739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152233180658823041766098549 14271860686764660165571739)
  ·
    refine ⟨21407791030146990248357609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14271860686764660165571739 21407791030146990248357609)
    ·
      refine ⟨16055843272610242686268207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21407791030146990248357609 16055843272610242686268207)
      ·
        refine ⟨24083764908915364029402311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16055843272610242686268207 24083764908915364029402311)
        ·
          refine ⟨36125647363373046044103467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24083764908915364029402311 36125647363373046044103467)
          ·
            refine ⟨54188471045059569066155201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36125647363373046044103467 54188471045059569066155201)
            ·
              refine ⟨40641353283794676799616401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54188471045059569066155201 40641353283794676799616401)
              ·
                refine ⟨30481014962846007599712301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40641353283794676799616401 30481014962846007599712301)
                ·
                  refine ⟨11430380611067252849892113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30481014962846007599712301 11430380611067252849892113)
                  ·
                    refine ⟨8572785458300439637419085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11430380611067252849892113 8572785458300439637419085)
                    ·
                      refine ⟨3214794546862664864032157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8572785458300439637419085 3214794546862664864032157)
                      ·
                        rfl

theorem cell23_6260790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_6260790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260790 prefixEnd_6260790 := by exact prefixLift 6260790
  have htrace : WordTrace (prefixWord ++ tailWord_6260790) baseStart_6260790 baseEnd_6260790 := by
    simpa [prefixWord, tailWord_6260790, baseEnd_6260790] using wordTrace_append hprefix tailTrace_6260790
  have hstable : (prefixWord ++ tailWord_6260790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260790).length < 2 ^ (prefixWord ++ tailWord_6260790).sum := by decide
  have hdescent : baseEnd_6260790 < baseStart_6260790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260793 : List Nat := [1, 2, 1, 5, 3, 1, 2, 8]
def baseStart_6260793 : Nat := 118140960795 + 6260793 * 2 ^ 59
def prefixEnd_6260793 : Nat := 4983230072969 + 3 ^ 40 * 6260793 * 2
def baseEnd_6260793 : Nat := 119066521752023272307209

theorem tailTrace_6260793 : CollatzResearch.WordTrace tailWord_6260793 prefixEnd_6260793 119066521752023272307209 := by
  unfold tailWord_6260793
  simp only [CollatzResearch.WordTrace]
  refine ⟨228349880407223694161507033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152233253604815796107671355 228349880407223694161507033)
  ·
    refine ⟨171262410305417770621130275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228349880407223694161507033 171262410305417770621130275)
    ·
      refine ⟨256893615458126655931695413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171262410305417770621130275 256893615458126655931695413)
      ·
        refine ⟨24083776449199373993596445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 256893615458126655931695413 24083776449199373993596445)
        ·
          refine ⟨9031416168449765247598667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24083776449199373993596445 9031416168449765247598667)
          ·
            refine ⟨13547124252674647871398001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9031416168449765247598667 13547124252674647871398001)
            ·
              refine ⟨10160343189505985903548501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13547124252674647871398001 10160343189505985903548501)
              ·
                refine ⟨119066521752023272307209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10160343189505985903548501 119066521752023272307209)
                ·
                  rfl

theorem cell23_6260793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 8].length) (baseStart_6260793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260793 prefixEnd_6260793 := by exact prefixLift 6260793
  have htrace : WordTrace (prefixWord ++ tailWord_6260793) baseStart_6260793 baseEnd_6260793 := by
    simpa [prefixWord, tailWord_6260793, baseEnd_6260793] using wordTrace_append hprefix tailTrace_6260793
  have hstable : (prefixWord ++ tailWord_6260793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260793).length < 2 ^ (prefixWord ++ tailWord_6260793).sum := by decide
  have hdescent : baseEnd_6260793 < baseStart_6260793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260796 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 2, 2, 6]
def baseStart_6260796 : Nat := 118140960795 + 6260796 * 2 ^ 59
def prefixEnd_6260796 : Nat := 4983230072969 + 3 ^ 40 * 6260796 * 2
def baseEnd_6260796 : Nat := 3214797627746591840557129

theorem tailTrace_6260796 : CollatzResearch.WordTrace tailWord_6260796 prefixEnd_6260796 3214797627746591840557129 := by
  unfold tailWord_6260796
  simp only [CollatzResearch.WordTrace]
  refine ⟨114174994913106412836933121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152233326550808550449244161 114174994913106412836933121)
  ·
    refine ⟨85631246184829809627699841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114174994913106412836933121 85631246184829809627699841)
    ·
      refine ⟨64223434638622357220774881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85631246184829809627699841 64223434638622357220774881)
      ·
        refine ⟨48167575978966767915581161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64223434638622357220774881 48167575978966767915581161)
        ·
          refine ⟨36125681984225075936685871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48167575978966767915581161 36125681984225075936685871)
          ·
            refine ⟨54188522976337613905028807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36125681984225075936685871 54188522976337613905028807)
            ·
              refine ⟨81282784464506420857543211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54188522976337613905028807 81282784464506420857543211)
              ·
                refine ⟨121924176696759631286314817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81282784464506420857543211 121924176696759631286314817)
                ·
                  refine ⟨91443132522569723464736113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121924176696759631286314817 91443132522569723464736113)
                  ·
                    refine ⟨68582349391927292598552085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91443132522569723464736113 68582349391927292598552085)
                    ·
                      refine ⟨3214797627746591840557129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68582349391927292598552085 3214797627746591840557129)
                      ·
                        rfl

theorem cell23_6260796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_6260796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260796 prefixEnd_6260796 := by exact prefixLift 6260796
  have htrace : WordTrace (prefixWord ++ tailWord_6260796) baseStart_6260796 baseEnd_6260796 := by
    simpa [prefixWord, tailWord_6260796, baseEnd_6260796] using wordTrace_append hprefix tailTrace_6260796
  have hstable : (prefixWord ++ tailWord_6260796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260796).length < 2 ^ (prefixWord ++ tailWord_6260796).sum := by decide
  have hdescent : baseEnd_6260796 < baseStart_6260796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260803 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 6, 1, 3]
def baseStart_6260803 : Nat := 118140960795 + 6260803 * 2 ^ 59
def prefixEnd_6260803 : Nat := 4983230072969 + 3 ^ 40 * 6260803 * 2
def baseEnd_6260803 : Nat := 3214801222111173313169597

theorem tailTrace_6260803 : CollatzResearch.WordTrace tailWord_6260803 prefixEnd_6260803 3214801222111173313169597 := by
  unfold tailWord_6260803
  simp only [CollatzResearch.WordTrace]
  refine ⟨228350245137187465869371063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152233496758124977246247375 228350245137187465869371063)
  ·
    refine ⟨342525367705781198804056595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228350245137187465869371063 342525367705781198804056595)
    ·
      refine ⟨513788051558671798206084893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342525367705781198804056595 513788051558671798206084893)
      ·
        refine ⟨192670519334501924327281835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 513788051558671798206084893 192670519334501924327281835)
        ·
          refine ⟨289005779001752886490922753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192670519334501924327281835 289005779001752886490922753)
          ·
            refine ⟨216754334251314664868192065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289005779001752886490922753 216754334251314664868192065)
            ·
              refine ⟨162565750688485998651144049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216754334251314664868192065 162565750688485998651144049)
              ·
                refine ⟨121924313016364498988358037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162565750688485998651144049 121924313016364498988358037)
                ·
                  refine ⟨5715202172642085890079283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 121924313016364498988358037 5715202172642085890079283)
                  ·
                    refine ⟨8572803258963128835118925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5715202172642085890079283 8572803258963128835118925)
                    ·
                      refine ⟨3214801222111173313169597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8572803258963128835118925 3214801222111173313169597)
                      ·
                        rfl

theorem cell23_6260803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 6, 1, 3].length) (baseStart_6260803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260803 prefixEnd_6260803 := by exact prefixLift 6260803
  have htrace : WordTrace (prefixWord ++ tailWord_6260803) baseStart_6260803 baseEnd_6260803 := by
    simpa [prefixWord, tailWord_6260803, baseEnd_6260803] using wordTrace_append hprefix tailTrace_6260803
  have hstable : (prefixWord ++ tailWord_6260803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260803).length < 2 ^ (prefixWord ++ tailWord_6260803).sum := by decide
  have hdescent : baseEnd_6260803 < baseStart_6260803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260837 : List Nat := [1, 3, 1, 3, 2, 3, 2, 2, 2, 1, 3]
def baseStart_6260837 : Nat := 118140960795 + 6260837 * 2 ^ 59
def prefixEnd_6260837 : Nat := 4983230072969 + 3 ^ 40 * 6260837 * 2
def baseEnd_6260837 : Nat := 3214818680453426180144441

theorem tailTrace_6260837 : CollatzResearch.WordTrace tailWord_6260837 prefixEnd_6260837 3214818680453426180144441 := by
  unfold tailWord_6260837
  simp only [CollatzResearch.WordTrace]
  refine ⟨228351485219064289676108765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152234323479376193117405843 228351485219064289676108765)
  ·
    refine ⟨85631806957149108628540787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228351485219064289676108765 85631806957149108628540787)
    ·
      refine ⟨128447710435723662942811181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85631806957149108628540787 128447710435723662942811181)
      ·
        refine ⟨48167891413396373603554193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128447710435723662942811181 48167891413396373603554193)
        ·
          refine ⟨36125918560047280202665645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48167891413396373603554193 36125918560047280202665645)
          ·
            refine ⟨13547219460017730075999617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36125918560047280202665645 13547219460017730075999617)
            ·
              refine ⟨10160414595013297556999713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13547219460017730075999617 10160414595013297556999713)
              ·
                refine ⟨7620310946259973167749785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10160414595013297556999713 7620310946259973167749785)
                ·
                  refine ⟨5715233209694979875812339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7620310946259973167749785 5715233209694979875812339)
                  ·
                    refine ⟨8572849814542469813718509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5715233209694979875812339 8572849814542469813718509)
                    ·
                      refine ⟨3214818680453426180144441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8572849814542469813718509 3214818680453426180144441)
                      ·
                        rfl

theorem cell23_6260837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_6260837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260837 prefixEnd_6260837 := by exact prefixLift 6260837
  have htrace : WordTrace (prefixWord ++ tailWord_6260837) baseStart_6260837 baseEnd_6260837 := by
    simpa [prefixWord, tailWord_6260837, baseEnd_6260837] using wordTrace_append hprefix tailTrace_6260837
  have hstable : (prefixWord ++ tailWord_6260837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260837).length < 2 ^ (prefixWord ++ tailWord_6260837).sum := by decide
  have hdescent : baseEnd_6260837 < baseStart_6260837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260860 : List Nat := [2, 2, 2, 1, 1, 4, 1, 3, 1, 4, 2]
def baseStart_6260860 : Nat := 118140960795 + 6260860 * 2 ^ 59
def prefixEnd_6260860 : Nat := 4983230072969 + 3 ^ 40 * 6260860 * 2
def baseEnd_6260860 : Nat := 3214830490508479590156835

theorem tailTrace_6260860 : CollatzResearch.WordTrace tailWord_6260860 prefixEnd_6260860 3214830490508479590156835 := by
  unfold tailWord_6260860
  simp only [CollatzResearch.WordTrace]
  refine ⟨114176162048990482302098017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152234882731987309736130689 114176162048990482302098017)
  ·
    refine ⟨85632121536742861726573513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114176162048990482302098017 85632121536742861726573513)
    ·
      refine ⟨64224091152557146294930135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85632121536742861726573513 64224091152557146294930135)
      ·
        refine ⟨96336136728835719442395203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64224091152557146294930135 96336136728835719442395203)
        ·
          refine ⟨144504205093253579163592805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96336136728835719442395203 144504205093253579163592805)
          ·
            refine ⟨27094538454985046093173651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144504205093253579163592805 27094538454985046093173651)
            ·
              refine ⟨40641807682477569139760477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27094538454985046093173651 40641807682477569139760477)
              ·
                refine ⟨15240677880929088427410179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40641807682477569139760477 15240677880929088427410179)
                ·
                  refine ⟨22861016821393632641115269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15240677880929088427410179 22861016821393632641115269)
                  ·
                    refine ⟨4286440654011306120209113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22861016821393632641115269 4286440654011306120209113)
                    ·
                      refine ⟨3214830490508479590156835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4286440654011306120209113 3214830490508479590156835)
                      ·
                        rfl

theorem cell23_6260860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 1, 4, 2].length) (baseStart_6260860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260860 prefixEnd_6260860 := by exact prefixLift 6260860
  have htrace : WordTrace (prefixWord ++ tailWord_6260860) baseStart_6260860 baseEnd_6260860 := by
    simpa [prefixWord, tailWord_6260860, baseEnd_6260860] using wordTrace_append hprefix tailTrace_6260860
  have hstable : (prefixWord ++ tailWord_6260860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260860).length < 2 ^ (prefixWord ++ tailWord_6260860).sum := by decide
  have hdescent : baseEnd_6260860 < baseStart_6260860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260876 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 3, 2, 7]
def baseStart_6260876 : Nat := 118140960795 + 6260876 * 2 ^ 59
def prefixEnd_6260876 : Nat := 4983230072969 + 3 ^ 40 * 6260876 * 2
def baseEnd_6260876 : Nat := 3214838706198951527556761

theorem tailTrace_6260876 : CollatzResearch.WordTrace tailWord_6260876 prefixEnd_6260876 3214838706198951527556761 := by
  unfold tailWord_6260876
  simp only [CollatzResearch.WordTrace]
  refine ⟨114176453832961499668389241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152235271777281999557852321 114176453832961499668389241)
  ·
    refine ⟨85632340374721124751291931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114176453832961499668389241 85632340374721124751291931)
    ·
      refine ⟨128448510562081687126937897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85632340374721124751291931 128448510562081687126937897)
      ·
        refine ⟨96336382921561265345203423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128448510562081687126937897 96336382921561265345203423)
        ·
          refine ⟨144504574382341898017805135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96336382921561265345203423 144504574382341898017805135)
          ·
            refine ⟨216756861573512847026707703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144504574382341898017805135 216756861573512847026707703)
            ·
              refine ⟨325135292360269270540061555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216756861573512847026707703 325135292360269270540061555)
              ·
                refine ⟨487702938540403905810092333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325135292360269270540061555 487702938540403905810092333)
                ·
                  refine ⟨182888601952651464678784625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 487702938540403905810092333 182888601952651464678784625)
                  ·
                    refine ⟨137166451464488598509088469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 182888601952651464678784625 137166451464488598509088469)
                    ·
                      refine ⟨3214838706198951527556761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 137166451464488598509088469 3214838706198951527556761)
                      ·
                        rfl

theorem cell23_6260876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_6260876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260876 prefixEnd_6260876 := by exact prefixLift 6260876
  have htrace : WordTrace (prefixWord ++ tailWord_6260876) baseStart_6260876 baseEnd_6260876 := by
    simpa [prefixWord, tailWord_6260876, baseEnd_6260876] using wordTrace_append hprefix tailTrace_6260876
  have hstable : (prefixWord ++ tailWord_6260876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260876).length < 2 ^ (prefixWord ++ tailWord_6260876).sum := by decide
  have hdescent : baseEnd_6260876 < baseStart_6260876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260900 : List Nat := [2, 3, 1, 2, 4, 1, 2, 1, 7]
def baseStart_6260900 : Nat := 118140960795 + 6260900 * 2 ^ 59
def prefixEnd_6260900 : Nat := 4983230072969 + 3 ^ 40 * 6260900 * 2
def baseEnd_6260900 : Nat := 357205669970517714850739

theorem tailTrace_6260900 : CollatzResearch.WordTrace tailWord_6260900 prefixEnd_6260900 357205669970517714850739 := by
  unfold tailWord_6260900
  simp only [CollatzResearch.WordTrace]
  refine ⟨114176891508918025717826077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152235855345224034290434769 114176891508918025717826077)
  ·
    refine ⟨42816334315844259644184779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114176891508918025717826077 42816334315844259644184779)
    ·
      refine ⟨64224501473766389466277169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42816334315844259644184779 64224501473766389466277169)
      ·
        refine ⟨48168376105324792099707877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64224501473766389466277169 48168376105324792099707877)
        ·
          refine ⟨9031570519748398518695227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48168376105324792099707877 9031570519748398518695227)
          ·
            refine ⟨13547355779622597778042841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9031570519748398518695227 13547355779622597778042841)
            ·
              refine ⟨10160516834716948333532131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13547355779622597778042841 10160516834716948333532131)
              ·
                refine ⟨15240775252075422500298197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10160516834716948333532131 15240775252075422500298197)
                ·
                  refine ⟨357205669970517714850739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15240775252075422500298197 357205669970517714850739)
                  ·
                    rfl

theorem cell23_6260900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 7].length) (baseStart_6260900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260900 prefixEnd_6260900 := by exact prefixLift 6260900
  have htrace : WordTrace (prefixWord ++ tailWord_6260900) baseStart_6260900 baseEnd_6260900 := by
    simpa [prefixWord, tailWord_6260900, baseEnd_6260900] using wordTrace_append hprefix tailTrace_6260900
  have hstable : (prefixWord ++ tailWord_6260900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260900).length < 2 ^ (prefixWord ++ tailWord_6260900).sum := by decide
  have hdescent : baseEnd_6260900 < baseStart_6260900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260933 : List Nat := [1, 3, 1, 1, 1, 1, 6, 1, 1, 3, 4]
def baseStart_6260933 : Nat := 118140960795 + 6260933 * 2 ^ 59
def prefixEnd_6260933 : Nat := 4983230072969 + 3 ^ 40 * 6260933 * 2
def baseEnd_6260933 : Nat := 3214867974596257804543999

theorem tailTrace_6260933 : CollatzResearch.WordTrace tailWord_6260933 prefixEnd_6260933 3214867974596257804543999 := by
  unfold tailWord_6260933
  simp only [CollatzResearch.WordTrace]
  refine ⟨228354986626716498071603453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152236657751144332047735635 228354986626716498071603453)
  ·
    refine ⟨85633119985018686776851295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228354986626716498071603453 85633119985018686776851295)
    ·
      refine ⟨128449679977528030165276943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85633119985018686776851295 128449679977528030165276943)
      ·
        refine ⟨192674519966292045247915415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128449679977528030165276943 192674519966292045247915415)
        ·
          refine ⟨289011779949438067871873123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192674519966292045247915415 289011779949438067871873123)
          ·
            refine ⟨433517669924157101807809685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289011779949438067871873123 433517669924157101807809685)
            ·
              refine ⟨20321140777694864147241079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 433517669924157101807809685 20321140777694864147241079)
              ·
                refine ⟨30481711166542296220861619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20321140777694864147241079 30481711166542296220861619)
                ·
                  refine ⟨45722566749813444331292429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30481711166542296220861619 45722566749813444331292429)
                  ·
                    refine ⟨17145962531180041624234661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45722566749813444331292429 17145962531180041624234661)
                    ·
                      refine ⟨3214867974596257804543999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17145962531180041624234661 3214867974596257804543999)
                      ·
                        rfl

theorem cell23_6260933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_6260933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260933 prefixEnd_6260933 := by exact prefixLift 6260933
  have htrace : WordTrace (prefixWord ++ tailWord_6260933) baseStart_6260933 baseEnd_6260933 := by
    simpa [prefixWord, tailWord_6260933, baseEnd_6260933] using wordTrace_append hprefix tailTrace_6260933
  have hstable : (prefixWord ++ tailWord_6260933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260933).length < 2 ^ (prefixWord ++ tailWord_6260933).sum := by decide
  have hdescent : baseEnd_6260933 < baseStart_6260933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260962 : List Nat := [3, 3, 4, 1, 1, 2, 2, 1, 2, 2, 2]
def baseStart_6260962 : Nat := 118140960795 + 6260962 * 2 ^ 59
def prefixEnd_6260962 : Nat := 4983230072969 + 3 ^ 40 * 6260962 * 2
def baseEnd_6260962 : Nat := 3214882865535238191081367

theorem tailTrace_6260962 : CollatzResearch.WordTrace tailWord_6260962 prefixEnd_6260962 3214882865535238191081367 := by
  unfold tailWord_6260962
  simp only [CollatzResearch.WordTrace]
  refine ⟨57089011085902859006102285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152237362895740957349606093 57089011085902859006102285)
  ·
    refine ⟨21408379157213572127288357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57089011085902859006102285 21408379157213572127288357)
    ·
      refine ⟨4014071091977544773866567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21408379157213572127288357 4014071091977544773866567)
      ·
        refine ⟨6021106637966317160799851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4014071091977544773866567 6021106637966317160799851)
        ·
          refine ⟨9031659956949475741199777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6021106637966317160799851 9031659956949475741199777)
          ·
            refine ⟨6773744967712106805899833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9031659956949475741199777 6773744967712106805899833)
            ·
              refine ⟨5080308725784080104424875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6773744967712106805899833 5080308725784080104424875)
              ·
                refine ⟨7620463088676120156637313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5080308725784080104424875 7620463088676120156637313)
                ·
                  refine ⟨5715347316507090117477985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7620463088676120156637313 5715347316507090117477985)
                  ·
                    refine ⟨4286510487380317588108489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5715347316507090117477985 4286510487380317588108489)
                    ·
                      refine ⟨3214882865535238191081367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4286510487380317588108489 3214882865535238191081367)
                      ·
                        rfl

theorem cell23_6260962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_6260962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260962 prefixEnd_6260962 := by exact prefixLift 6260962
  have htrace : WordTrace (prefixWord ++ tailWord_6260962) baseStart_6260962 baseEnd_6260962 := by
    simpa [prefixWord, tailWord_6260962, baseEnd_6260962] using wordTrace_append hprefix tailTrace_6260962
  have hstable : (prefixWord ++ tailWord_6260962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260962).length < 2 ^ (prefixWord ++ tailWord_6260962).sum := by decide
  have hdescent : baseEnd_6260962 < baseStart_6260962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6260970 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 4, 2, 3]
def baseStart_6260970 : Nat := 118140960795 + 6260970 * 2 ^ 59
def prefixEnd_6260970 : Nat := 4983230072969 + 3 ^ 40 * 6260970 * 2
def baseEnd_6260970 : Nat := 3214886973380474159781329

theorem tailTrace_6260970 : CollatzResearch.WordTrace tailWord_6260970 prefixEnd_6260970 3214886973380474159781329 := by
  unfold tailWord_6260970
  simp only [CollatzResearch.WordTrace]
  refine ⟨57089084031895613347675091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152237557418388302260466909 57089084031895613347675091)
  ·
    refine ⟨85633626047843420021512637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57089084031895613347675091 85633626047843420021512637)
    ·
      refine ⟨32112609767941282508067239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85633626047843420021512637 32112609767941282508067239)
      ·
        refine ⟨48168914651911923762100859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32112609767941282508067239 48168914651911923762100859)
        ·
          refine ⟨72253371977867885643151289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48168914651911923762100859 72253371977867885643151289)
          ·
            refine ⟨54190028983400914232363467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72253371977867885643151289 54190028983400914232363467)
            ·
              refine ⟨81285043475101371348545201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54190028983400914232363467 81285043475101371348545201)
              ·
                refine ⟨60963782606326028511408901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81285043475101371348545201 60963782606326028511408901)
                ·
                  refine ⟨11430709238686130345889169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60963782606326028511408901 11430709238686130345889169)
                  ·
                    refine ⟨8573031929014597759416877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11430709238686130345889169 8573031929014597759416877)
                    ·
                      refine ⟨3214886973380474159781329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8573031929014597759416877 3214886973380474159781329)
                      ·
                        rfl

theorem cell23_6260970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_6260970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6260970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6260970 prefixEnd_6260970 := by exact prefixLift 6260970
  have htrace : WordTrace (prefixWord ++ tailWord_6260970) baseStart_6260970 baseEnd_6260970 := by
    simpa [prefixWord, tailWord_6260970, baseEnd_6260970] using wordTrace_append hprefix tailTrace_6260970
  have hstable : (prefixWord ++ tailWord_6260970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6260970).length < 2 ^ (prefixWord ++ tailWord_6260970).sum := by decide
  have hdescent : baseEnd_6260970 < baseStart_6260970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6260970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261038 : List Nat := [4, 1, 3, 3, 2, 1, 1, 1, 2, 2, 3]
def baseStart_6261038 : Nat := 118140960795 + 6261038 * 2 ^ 59
def prefixEnd_6261038 : Nat := 4983230072969 + 3 ^ 40 * 6261038 * 2
def baseEnd_6261038 : Nat := 3214921890064979893731017

theorem tailTrace_6261038 : CollatzResearch.WordTrace tailWord_6261038 prefixEnd_6261038 3214921890064979893731017 := by
  unfold tailWord_6261038
  simp only [CollatzResearch.WordTrace]
  refine ⟨28544852036417012625521971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152239210860890734002783845 28544852036417012625521971)
  ·
    refine ⟨42817278054625518938282957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28544852036417012625521971 42817278054625518938282957)
    ·
      refine ⟨16056479270484569601856109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42817278054625518938282957 16056479270484569601856109)
      ·
        refine ⟨6021179726431713600696041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16056479270484569601856109 6021179726431713600696041)
        ·
          refine ⟨4515884794823785200522031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6021179726431713600696041 4515884794823785200522031)
          ·
            refine ⟨6773827192235677800783047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4515884794823785200522031 6773827192235677800783047)
            ·
              refine ⟨10160740788353516701174571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6773827192235677800783047 10160740788353516701174571)
              ·
                refine ⟨15241111182530275051761857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10160740788353516701174571 15241111182530275051761857)
                ·
                  refine ⟨11430833386897706288821393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15241111182530275051761857 11430833386897706288821393)
                  ·
                    refine ⟨8573125040173279716616045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11430833386897706288821393 8573125040173279716616045)
                    ·
                      refine ⟨3214921890064979893731017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8573125040173279716616045 3214921890064979893731017)
                      ·
                        rfl

theorem cell23_6261038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_6261038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261038 prefixEnd_6261038 := by exact prefixLift 6261038
  have htrace : WordTrace (prefixWord ++ tailWord_6261038) baseStart_6261038 baseEnd_6261038 := by
    simpa [prefixWord, tailWord_6261038, baseEnd_6261038] using wordTrace_append hprefix tailTrace_6261038
  have hstable : (prefixWord ++ tailWord_6261038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261038).length < 2 ^ (prefixWord ++ tailWord_6261038).sum := by decide
  have hdescent : baseEnd_6261038 < baseStart_6261038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261040 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 1, 8, 2]
def baseStart_6261040 : Nat := 118140960795 + 6261040 * 2 ^ 59
def prefixEnd_6261040 : Nat := 4983230072969 + 3 ^ 40 * 6261040 * 2
def baseEnd_6261040 : Nat := 3214922917026288885906007

theorem tailTrace_6261040 : CollatzResearch.WordTrace tailWord_6261040 prefixEnd_6261040 3214922917026288885906007 := by
  unfold tailWord_6261040
  simp only [CollatzResearch.WordTrace]
  refine ⟨114179444618664427672874287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152239259491552570230499049 114179444618664427672874287)
  ·
    refine ⟨171269166927996641509311431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114179444618664427672874287 171269166927996641509311431)
    ·
      refine ⟨256903750391994962263967147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171269166927996641509311431 256903750391994962263967147)
      ·
        refine ⟨385355625587992443395950721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256903750391994962263967147 385355625587992443395950721)
        ·
          refine ⟨289016719190994332546963041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385355625587992443395950721 289016719190994332546963041)
          ·
            refine ⟨216762539393245749410222281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289016719190994332546963041 216762539393245749410222281)
            ·
              refine ⟨162571904544934312057666711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216762539393245749410222281 162571904544934312057666711)
              ·
                refine ⟨243857856817401468086500067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162571904544934312057666711 243857856817401468086500067)
                ·
                  refine ⟨365786785226102202129750101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243857856817401468086500067 365786785226102202129750101)
                  ·
                    refine ⟨4286563889368385181208009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 365786785226102202129750101 4286563889368385181208009)
                    ·
                      refine ⟨3214922917026288885906007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4286563889368385181208009 3214922917026288885906007)
                      ·
                        rfl

theorem cell23_6261040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 8, 2].length) (baseStart_6261040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261040 prefixEnd_6261040 := by exact prefixLift 6261040
  have htrace : WordTrace (prefixWord ++ tailWord_6261040) baseStart_6261040 baseEnd_6261040 := by
    simpa [prefixWord, tailWord_6261040, baseEnd_6261040] using wordTrace_append hprefix tailTrace_6261040
  have hstable : (prefixWord ++ tailWord_6261040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261040).length < 2 ^ (prefixWord ++ tailWord_6261040).sum := by decide
  have hdescent : baseEnd_6261040 < baseStart_6261040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261044 : List Nat := [2, 5, 1, 1, 1, 3, 1, 1, 1, 5, 2]
def baseStart_6261044 : Nat := 118140960795 + 6261044 * 2 ^ 59
def prefixEnd_6261044 : Nat := 4983230072969 + 3 ^ 40 * 6261044 * 2
def baseEnd_6261044 : Nat := 3214924970948906870255989

theorem tailTrace_6261044 : CollatzResearch.WordTrace tailWord_6261044 prefixEnd_6261044 3214924970948906870255989 := by
  unfold tailWord_6261044
  simp only [CollatzResearch.WordTrace]
  refine ⟨114179517564657182014447093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152239356752876242685929457 114179517564657182014447093)
  ·
    refine ⟨10704329771686610813854415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114179517564657182014447093 10704329771686610813854415)
    ·
      refine ⟨16056494657529916220781623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10704329771686610813854415 16056494657529916220781623)
      ·
        refine ⟨24084741986294874331172435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16056494657529916220781623 24084741986294874331172435)
        ·
          refine ⟨36127112979442311496758653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24084741986294874331172435 36127112979442311496758653)
          ·
            refine ⟨13547667367290866811284495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36127112979442311496758653 13547667367290866811284495)
            ·
              refine ⟨20321501050936300216926743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13547667367290866811284495 20321501050936300216926743)
              ·
                refine ⟨30482251576404450325390115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20321501050936300216926743 30482251576404450325390115)
                ·
                  refine ⟨45723377364606675488085173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30482251576404450325390115 45723377364606675488085173)
                  ·
                    refine ⟨4286566627931875827007985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45723377364606675488085173 4286566627931875827007985)
                    ·
                      refine ⟨3214924970948906870255989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4286566627931875827007985 3214924970948906870255989)
                      ·
                        rfl

theorem cell23_6261044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_6261044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261044 prefixEnd_6261044 := by exact prefixLift 6261044
  have htrace : WordTrace (prefixWord ++ tailWord_6261044) baseStart_6261044 baseEnd_6261044 := by
    simpa [prefixWord, tailWord_6261044, baseEnd_6261044] using wordTrace_append hprefix tailTrace_6261044
  have hstable : (prefixWord ++ tailWord_6261044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261044).length < 2 ^ (prefixWord ++ tailWord_6261044).sum := by decide
  have hdescent : baseEnd_6261044 < baseStart_6261044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261050 : List Nat := [3, 1, 1, 1, 4, 2, 2, 2, 1, 6]
def baseStart_6261050 : Nat := 118140960795 + 6261050 * 2 ^ 59
def prefixEnd_6261050 : Nat := 4983230072969 + 3 ^ 40 * 6261050 * 2
def baseEnd_6261050 : Nat := 1071642683944277948926987

theorem tailTrace_6261050 : CollatzResearch.WordTrace tailWord_6261050 prefixEnd_6261050 1071642683944277948926987 := by
  unfold tailWord_6261050
  simp only [CollatzResearch.WordTrace]
  refine ⟨57089813491823156763403151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152239502644861751369075069 57089813491823156763403151)
  ·
    refine ⟨85634720237734735145104727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57089813491823156763403151 85634720237734735145104727)
    ·
      refine ⟨128452080356602102717657091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85634720237734735145104727 128452080356602102717657091)
      ·
        refine ⟨192678120534903154076485637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128452080356602102717657091 192678120534903154076485637)
        ·
          refine ⟨36127147600294341389341057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192678120534903154076485637 36127147600294341389341057)
          ·
            refine ⟨27095360700220756042005793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36127147600294341389341057 27095360700220756042005793)
            ·
              refine ⟨20321520525165567031504345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27095360700220756042005793 20321520525165567031504345)
              ·
                refine ⟨15241140393874175273628259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20321520525165567031504345 15241140393874175273628259)
                ·
                  refine ⟨22861710590811262910442389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15241140393874175273628259 22861710590811262910442389)
                  ·
                    refine ⟨1071642683944277948926987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22861710590811262910442389 1071642683944277948926987)
                    ·
                      rfl

theorem cell23_6261050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 1, 6].length) (baseStart_6261050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261050 prefixEnd_6261050 := by exact prefixLift 6261050
  have htrace : WordTrace (prefixWord ++ tailWord_6261050) baseStart_6261050 baseEnd_6261050 := by
    simpa [prefixWord, tailWord_6261050, baseEnd_6261050] using wordTrace_append hprefix tailTrace_6261050
  have hstable : (prefixWord ++ tailWord_6261050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261050).length < 2 ^ (prefixWord ++ tailWord_6261050).sum := by decide
  have hdescent : baseEnd_6261050 < baseStart_6261050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261054 : List Nat := [4, 2, 1, 2, 1, 2, 4, 1, 1, 5]
def baseStart_6261054 : Nat := 118140960795 + 6261054 * 2 ^ 59
def prefixEnd_6261054 : Nat := 4983230072969 + 3 ^ 40 * 6261054 * 2
def baseEnd_6261054 : Nat := 1071643368585150610376981

theorem tailTrace_6261054 : CollatzResearch.WordTrace tailWord_6261054 prefixEnd_6261054 1071643368585150610376981 := by
  unfold tailWord_6261054
  simp only [CollatzResearch.WordTrace]
  refine ⟨28544924982409766967094777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152239599906185423824505477 28544924982409766967094777)
  ·
    refine ⟨21408693736807325225321083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28544924982409766967094777 21408693736807325225321083)
    ·
      refine ⟨32113040605210987837981625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21408693736807325225321083 32113040605210987837981625)
      ·
        refine ⟨24084780453908240878486219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32113040605210987837981625 24084780453908240878486219)
        ·
          refine ⟨36127170680862361317729329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24084780453908240878486219 36127170680862361317729329)
          ·
            refine ⟨27095378010646770988296997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36127170680862361317729329 27095378010646770988296997)
            ·
              refine ⟨5080383376996269560305687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27095378010646770988296997 5080383376996269560305687)
              ·
                refine ⟨7620575065494404340458531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5080383376996269560305687 7620575065494404340458531)
                ·
                  refine ⟨11430862598241606510687797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7620575065494404340458531 11430862598241606510687797)
                  ·
                    refine ⟨1071643368585150610376981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11430862598241606510687797 1071643368585150610376981)
                    ·
                      rfl

theorem cell23_6261054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_6261054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261054 prefixEnd_6261054 := by exact prefixLift 6261054
  have htrace : WordTrace (prefixWord ++ tailWord_6261054) baseStart_6261054 baseEnd_6261054 := by
    simpa [prefixWord, tailWord_6261054, baseEnd_6261054] using wordTrace_append hprefix tailTrace_6261054
  have hstable : (prefixWord ++ tailWord_6261054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261054).length < 2 ^ (prefixWord ++ tailWord_6261054).sum := by decide
  have hdescent : baseEnd_6261054 < baseStart_6261054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261063 : List Nat := [1, 1, 4, 1, 2, 2, 12]
def baseStart_6261063 : Nat := 118140960795 + 6261063 * 2 ^ 59
def prefixEnd_6261063 : Nat := 4983230072969 + 3 ^ 40 * 6261063 * 2
def baseEnd_6261063 : Nat := 39690552186189411060721

theorem tailTrace_6261063 : CollatzResearch.WordTrace tailWord_6261063 prefixEnd_6261063 39690552186189411060721 := by
  unfold tailWord_6261063
  simp only [CollatzResearch.WordTrace]
  refine ⟨228359728116245530273835843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152239818744163686849223895 228359728116245530273835843)
  ·
    refine ⟨342539592174368295410753765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228359728116245530273835843 342539592174368295410753765)
    ·
      refine ⟨64226173532694055389516331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 342539592174368295410753765 64226173532694055389516331)
      ·
        refine ⟨96339260299041083084274497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64226173532694055389516331 96339260299041083084274497)
        ·
          refine ⟨72254445224280812313205873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96339260299041083084274497 72254445224280812313205873)
          ·
            refine ⟨54190833918210609234904405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72254445224280812313205873 54190833918210609234904405)
            ·
              refine ⟨39690552186189411060721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 54190833918210609234904405 39690552186189411060721)
              ·
                rfl

theorem cell23_6261063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 12].length) (baseStart_6261063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261063 prefixEnd_6261063 := by exact prefixLift 6261063
  have htrace : WordTrace (prefixWord ++ tailWord_6261063) baseStart_6261063 baseEnd_6261063 := by
    simpa [prefixWord, tailWord_6261063, baseEnd_6261063] using wordTrace_append hprefix tailTrace_6261063
  have hstable : (prefixWord ++ tailWord_6261063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261063).length < 2 ^ (prefixWord ++ tailWord_6261063).sum := by decide
  have hdescent : baseEnd_6261063 < baseStart_6261063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261074 : List Nat := [3, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2]
def baseStart_6261074 : Nat := 118140960795 + 6261074 * 2 ^ 59
def prefixEnd_6261074 : Nat := 4983230072969 + 3 ^ 40 * 6261074 * 2
def baseEnd_6261074 : Nat := 3214940375368541752880851

theorem tailTrace_6261074 : CollatzResearch.WordTrace tailWord_6261074 prefixEnd_6261074 3214940375368541752880851 := by
  unfold tailWord_6261074
  simp only [CollatzResearch.WordTrace]
  refine ⟨57090032329801419788121569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152240086212803786101657517 57090032329801419788121569)
  ·
    refine ⟨42817524247351064841091177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57090032329801419788121569 42817524247351064841091177)
    ·
      refine ⟨32113143185513298630818383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42817524247351064841091177 32113143185513298630818383)
      ·
        refine ⟨48169714778269947946227575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32113143185513298630818383 48169714778269947946227575)
        ·
          refine ⟨72254572167404921919341363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48169714778269947946227575 72254572167404921919341363)
          ·
            refine ⟨108381858251107382879012045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72254572167404921919341363 108381858251107382879012045)
            ·
              refine ⟨40643196844165268579629517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108381858251107382879012045 40643196844165268579629517)
              ·
                refine ⟨15241198816561975717361069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40643196844165268579629517 15241198816561975717361069)
                ·
                  refine ⟨5715449556210740894010401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15241198816561975717361069 5715449556210740894010401)
                  ·
                    refine ⟨4286587167158055670507801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5715449556210740894010401 4286587167158055670507801)
                    ·
                      refine ⟨3214940375368541752880851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4286587167158055670507801 3214940375368541752880851)
                      ·
                        rfl

theorem cell23_6261074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_6261074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261074 prefixEnd_6261074 := by exact prefixLift 6261074
  have htrace : WordTrace (prefixWord ++ tailWord_6261074) baseStart_6261074 baseEnd_6261074 := by
    simpa [prefixWord, tailWord_6261074, baseEnd_6261074] using wordTrace_append hprefix tailTrace_6261074
  have hstable : (prefixWord ++ tailWord_6261074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261074).length < 2 ^ (prefixWord ++ tailWord_6261074).sum := by decide
  have hdescent : baseEnd_6261074 < baseStart_6261074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261077 : List Nat := [1, 3, 2, 2, 4, 1, 1, 2, 1, 1, 5]
def baseStart_6261077 : Nat := 118140960795 + 6261077 * 2 ^ 59
def prefixEnd_6261077 : Nat := 4983230072969 + 3 ^ 40 * 6261077 * 2
def baseEnd_6261077 : Nat := 3214941915810505241143337

theorem tailTrace_6261077 : CollatzResearch.WordTrace tailWord_6261077 prefixEnd_6261077 3214941915810505241143337 := by
  unfold tailWord_6261077
  simp only [CollatzResearch.WordTrace]
  refine ⟨228360238738194810664845485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152240159158796540443230323 228360238738194810664845485)
  ·
    refine ⟨85635089526823053999317057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228360238738194810664845485 85635089526823053999317057)
    ·
      refine ⟨64226317145117290499487793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85635089526823053999317057 64226317145117290499487793)
      ·
        refine ⟨48169737858837967874615845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64226317145117290499487793 48169737858837967874615845)
        ·
          refine ⟨9031825848532118976490471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48169737858837967874615845 9031825848532118976490471)
          ·
            refine ⟨13547738772798178464735707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9031825848532118976490471 13547738772798178464735707)
            ·
              refine ⟨20321608159197267697103561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13547738772798178464735707 20321608159197267697103561)
              ·
                refine ⟨15241206119397950772827671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20321608159197267697103561 15241206119397950772827671)
                ·
                  refine ⟨22861809179096926159241507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15241206119397950772827671 22861809179096926159241507)
                  ·
                    refine ⟨34292713768645389238862261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22861809179096926159241507 34292713768645389238862261)
                    ·
                      refine ⟨3214941915810505241143337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34292713768645389238862261 3214941915810505241143337)
                      ·
                        rfl

theorem cell23_6261077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_6261077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261077 prefixEnd_6261077 := by exact prefixLift 6261077
  have htrace : WordTrace (prefixWord ++ tailWord_6261077) baseStart_6261077 baseEnd_6261077 := by
    simpa [prefixWord, tailWord_6261077, baseEnd_6261077] using wordTrace_append hprefix tailTrace_6261077
  have hstable : (prefixWord ++ tailWord_6261077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261077).length < 2 ^ (prefixWord ++ tailWord_6261077).sum := by decide
  have hdescent : baseEnd_6261077 < baseStart_6261077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261124 : List Nat := [2, 3, 2, 1, 1, 2, 2, 4, 2, 1, 3]
def baseStart_6261124 : Nat := 118140960795 + 6261124 * 2 ^ 59
def prefixEnd_6261124 : Nat := 4983230072969 + 3 ^ 40 * 6261124 * 2
def baseEnd_6261124 : Nat := 3214966049401266557255621

theorem tailTrace_6261124 : CollatzResearch.WordTrace tailWord_6261124 prefixEnd_6261124 3214966049401266557255621 := by
  unfold tailWord_6261124
  simp only [CollatzResearch.WordTrace]
  refine ⟨114180976484512268845903213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152241301979349691794537617 114180976484512268845903213)
  ·
    refine ⟨42817866181692100817213705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114180976484512268845903213 42817866181692100817213705)
    ·
      refine ⟨32113399636269075612910279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42817866181692100817213705 32113399636269075612910279)
      ·
        refine ⟨48170099454403613419365419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32113399636269075612910279 48170099454403613419365419)
        ·
          refine ⟨72255149181605420129048129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48170099454403613419365419 72255149181605420129048129)
          ·
            refine ⟨54191361886204065096786097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72255149181605420129048129 54191361886204065096786097)
            ·
              refine ⟨40643521414653048822589573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54191361886204065096786097 40643521414653048822589573)
              ·
                refine ⟨7620660265247446654235545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40643521414653048822589573 7620660265247446654235545)
                ·
                  refine ⟨5715495198935584990676659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7620660265247446654235545 5715495198935584990676659)
                  ·
                    refine ⟨8573242798403377486014989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5715495198935584990676659 8573242798403377486014989)
                    ·
                      refine ⟨3214966049401266557255621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8573242798403377486014989 3214966049401266557255621)
                      ·
                        rfl

theorem cell23_6261124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_6261124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261124 prefixEnd_6261124 := by exact prefixLift 6261124
  have htrace : WordTrace (prefixWord ++ tailWord_6261124) baseStart_6261124 baseEnd_6261124 := by
    simpa [prefixWord, tailWord_6261124, baseEnd_6261124] using wordTrace_append hprefix tailTrace_6261124
  have hstable : (prefixWord ++ tailWord_6261124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261124).length < 2 ^ (prefixWord ++ tailWord_6261124).sum := by decide
  have hdescent : baseEnd_6261124 < baseStart_6261124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261142 : List Nat := [5, 3, 1, 2, 2, 1, 1, 2, 1, 1, 4]
def baseStart_6261142 : Nat := 118140960795 + 6261142 * 2 ^ 59
def prefixEnd_6261142 : Nat := 4983230072969 + 3 ^ 40 * 6261142 * 2
def baseEnd_6261142 : Nat := 3214975292053047486830539

theorem tailTrace_6261142 : CollatzResearch.WordTrace tailWord_6261142 prefixEnd_6261142 3214975292053047486830539 := by
  unfold tailWord_6261142
  simp only [CollatzResearch.WordTrace]
  refine ⟨14272663092684957922872605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152241739655306217843974453 14272663092684957922872605)
  ·
    refine ⟨5352248659756859221077227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14272663092684957922872605 5352248659756859221077227)
    ·
      refine ⟨8028372989635288831615841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5352248659756859221077227 8028372989635288831615841)
      ·
        refine ⟨6021279742226466623711881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8028372989635288831615841 6021279742226466623711881)
        ·
          refine ⟨4515959806669849967783911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6021279742226466623711881 4515959806669849967783911)
          ·
            refine ⟨6773939710004774951675867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4515959806669849967783911 6773939710004774951675867)
            ·
              refine ⟨10160909565007162427513801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6773939710004774951675867 10160909565007162427513801)
              ·
                refine ⟨7620682173755371820635351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10160909565007162427513801 7620682173755371820635351)
                ·
                  refine ⟨11431023260633057730953027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7620682173755371820635351 11431023260633057730953027)
                  ·
                    refine ⟨17146534890949586596429541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11431023260633057730953027 17146534890949586596429541)
                    ·
                      refine ⟨3214975292053047486830539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17146534890949586596429541 3214975292053047486830539)
                      ·
                        rfl

theorem cell23_6261142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_6261142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261142 prefixEnd_6261142 := by exact prefixLift 6261142
  have htrace : WordTrace (prefixWord ++ tailWord_6261142) baseStart_6261142 baseEnd_6261142 := by
    simpa [prefixWord, tailWord_6261142, baseEnd_6261142] using wordTrace_append hprefix tailTrace_6261142
  have hstable : (prefixWord ++ tailWord_6261142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261142).length < 2 ^ (prefixWord ++ tailWord_6261142).sum := by decide
  have hdescent : baseEnd_6261142 < baseStart_6261142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261181 : List Nat := [1, 4, 1, 2, 2, 2, 1, 4, 2, 2, 2]
def baseStart_6261181 : Nat := 118140960795 + 6261181 * 2 ^ 59
def prefixEnd_6261181 : Nat := 4983230072969 + 3 ^ 40 * 6261181 * 2
def baseEnd_6261181 : Nat := 3214995317798572834242859

theorem tailTrace_6261181 : CollatzResearch.WordTrace tailWord_6261181 prefixEnd_6261181 3214995317798572834242859 := by
  unfold tailWord_6261181
  simp only [CollatzResearch.WordTrace]
  refine ⟨228364031929818036426631397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152242687953212024284420931 228364031929818036426631397)
  ·
    refine ⟨42818255986840881829993387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228364031929818036426631397 42818255986840881829993387)
    ·
      refine ⟨64227383980261322744990081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42818255986840881829993387 64227383980261322744990081)
      ·
        refine ⟨48170537985195992058742561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64227383980261322744990081 48170537985195992058742561)
        ·
          refine ⟨36127903488896994044056921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48170537985195992058742561 36127903488896994044056921)
          ·
            refine ⟨27095927616672745533042691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36127903488896994044056921 27095927616672745533042691)
            ·
              refine ⟨40643891425009118299564037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27095927616672745533042691 40643891425009118299564037)
              ·
                refine ⟨7620729642189209681168257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40643891425009118299564037 7620729642189209681168257)
                ·
                  refine ⟨5715547231641907260876193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7620729642189209681168257 5715547231641907260876193)
                  ·
                    refine ⟨4286660423731430445657145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5715547231641907260876193 4286660423731430445657145)
                    ·
                      refine ⟨3214995317798572834242859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4286660423731430445657145 3214995317798572834242859)
                      ·
                        rfl

theorem cell23_6261181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_6261181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261181 prefixEnd_6261181 := by exact prefixLift 6261181
  have htrace : WordTrace (prefixWord ++ tailWord_6261181) baseStart_6261181 baseEnd_6261181 := by
    simpa [prefixWord, tailWord_6261181, baseEnd_6261181] using wordTrace_append hprefix tailTrace_6261181
  have hstable : (prefixWord ++ tailWord_6261181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261181).length < 2 ^ (prefixWord ++ tailWord_6261181).sum := by decide
  have hdescent : baseEnd_6261181 < baseStart_6261181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261221 : List Nat := [1, 3, 1, 5, 2, 1, 2, 3, 5]
def baseStart_6261221 : Nat := 118140960795 + 6261221 * 2 ^ 59
def prefixEnd_6261221 : Nat := 4983230072969 + 3 ^ 40 * 6261221 * 2
def baseEnd_6261221 : Nat := 357223984113861408638075

theorem tailTrace_6261221 : CollatzResearch.WordTrace tailWord_6261221 prefixEnd_6261221 357223984113861408638075 := by
  unfold tailWord_6261221
  simp only [CollatzResearch.WordTrace]
  refine ⟨228365490849673123258087517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152243660566448748838725011 228365490849673123258087517)
  ·
    refine ⟨85637059068627421221782819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228365490849673123258087517 85637059068627421221782819)
    ·
      refine ⟨128455588602941131832674229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85637059068627421221782819 128455588602941131832674229)
      ·
        refine ⟨12042711431525731109313209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128455588602941131832674229 12042711431525731109313209)
        ·
          refine ⟨9032033573644298331984907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12042711431525731109313209 9032033573644298331984907)
          ·
            refine ⟨13548050360466447497977361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9032033573644298331984907 13548050360466447497977361)
            ·
              refine ⟨10161037770349835623483021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13548050360466447497977361 10161037770349835623483021)
              ·
                refine ⟨3810389163881188358806133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10161037770349835623483021 3810389163881188358806133)
                ·
                  refine ⟨357223984113861408638075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3810389163881188358806133 357223984113861408638075)
                  ·
                    rfl

theorem cell23_6261221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 3, 5].length) (baseStart_6261221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261221 prefixEnd_6261221 := by exact prefixLift 6261221
  have htrace : WordTrace (prefixWord ++ tailWord_6261221) baseStart_6261221 baseEnd_6261221 := by
    simpa [prefixWord, tailWord_6261221, baseEnd_6261221] using wordTrace_append hprefix tailTrace_6261221
  have hstable : (prefixWord ++ tailWord_6261221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261221).length < 2 ^ (prefixWord ++ tailWord_6261221).sum := by decide
  have hdescent : baseEnd_6261221 < baseStart_6261221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261257 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 6, 2, 3]
def baseStart_6261257 : Nat := 118140960795 + 6261257 * 2 ^ 59
def prefixEnd_6261257 : Nat := 4983230072969 + 3 ^ 40 * 6261257 * 2
def baseEnd_6261257 : Nat := 3215034342328314536892509

theorem tailTrace_6261257 : CollatzResearch.WordTrace tailWord_6261257 prefixEnd_6261257 3215034342328314536892509 := by
  unfold tailWord_6261257
  simp only [CollatzResearch.WordTrace]
  refine ⟨228366803877542701406398025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152244535918361800937598683 228366803877542701406398025)
  ·
    refine ⟨171275102908157026054798519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228366803877542701406398025 171275102908157026054798519)
    ·
      refine ⟨256912654362235539082197779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171275102908157026054798519 256912654362235539082197779)
      ·
        refine ⟨385368981543353308623296669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256912654362235539082197779 385368981543353308623296669)
        ·
          refine ⟨144513368078757490733736251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 385368981543353308623296669 144513368078757490733736251)
          ·
            refine ⟨216770052118136236100604377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144513368078757490733736251 216770052118136236100604377)
            ·
              refine ⟨162577539088602177075453283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216770052118136236100604377 162577539088602177075453283)
              ·
                refine ⟨243866308632903265613179925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162577539088602177075453283 243866308632903265613179925)
                ·
                  refine ⟨11431233217167340575617809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 243866308632903265613179925 11431233217167340575617809)
                  ·
                    refine ⟨8573424912875505431713357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11431233217167340575617809 8573424912875505431713357)
                    ·
                      refine ⟨3215034342328314536892509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8573424912875505431713357 3215034342328314536892509)
                      ·
                        rfl

theorem cell23_6261257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 2, 3].length) (baseStart_6261257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261257 prefixEnd_6261257 := by exact prefixLift 6261257
  have htrace : WordTrace (prefixWord ++ tailWord_6261257) baseStart_6261257 baseEnd_6261257 := by
    simpa [prefixWord, tailWord_6261257, baseEnd_6261257] using wordTrace_append hprefix tailTrace_6261257
  have hstable : (prefixWord ++ tailWord_6261257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261257).length < 2 ^ (prefixWord ++ tailWord_6261257).sum := by decide
  have hdescent : baseEnd_6261257 < baseStart_6261257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261277 : List Nat := [1, 4, 2, 2, 1, 2, 1, 2, 8]
def baseStart_6261277 : Nat := 118140960795 + 6261277 * 2 ^ 59
def prefixEnd_6261277 : Nat := 4983230072969 + 3 ^ 40 * 6261277 * 2
def baseEnd_6261277 : Nat := 357227179104600495404713

theorem tailTrace_6261277 : CollatzResearch.WordTrace tailWord_6261277 prefixEnd_6261277 357227179104600495404713 := by
  unfold tailWord_6261277
  simp only [CollatzResearch.WordTrace]
  refine ⟨228367533337470244822126085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152245022224980163214750723 228367533337470244822126085)
  ·
    refine ⟨42818912500775670904148641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228367533337470244822126085 42818912500775670904148641)
    ·
      refine ⟨32114184375581753178111481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42818912500775670904148641 32114184375581753178111481)
      ·
        refine ⟨24085638281686314883583611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32114184375581753178111481 24085638281686314883583611)
        ·
          refine ⟨36128457422529472325375417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24085638281686314883583611 36128457422529472325375417)
          ·
            refine ⟨27096343066897104244031563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36128457422529472325375417 27096343066897104244031563)
            ·
              refine ⟨40644514600345656366047345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27096343066897104244031563 40644514600345656366047345)
              ·
                refine ⟨30483385950259242274535509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40644514600345656366047345 30483385950259242274535509)
                ·
                  refine ⟨357227179104600495404713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30483385950259242274535509 357227179104600495404713)
                  ·
                    rfl

theorem cell23_6261277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 8].length) (baseStart_6261277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261277 prefixEnd_6261277 := by exact prefixLift 6261277
  have htrace : WordTrace (prefixWord ++ tailWord_6261277) baseStart_6261277 baseEnd_6261277 := by
    simpa [prefixWord, tailWord_6261277, baseEnd_6261277] using wordTrace_append hprefix tailTrace_6261277
  have hstable : (prefixWord ++ tailWord_6261277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261277).length < 2 ^ (prefixWord ++ tailWord_6261277).sum := by decide
  have hdescent : baseEnd_6261277 < baseStart_6261277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261344 : List Nat := [2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 4]
def baseStart_6261344 : Nat := 118140960795 + 6261344 * 2 ^ 59
def prefixEnd_6261344 : Nat := 4983230072969 + 3 ^ 40 * 6261344 * 2
def baseEnd_6261344 : Nat := 3215079015145255696504609

theorem tailTrace_6261344 : CollatzResearch.WordTrace tailWord_6261344 prefixEnd_6261344 3215079015145255696504609 := by
  unfold tailWord_6261344
  simp only [CollatzResearch.WordTrace]
  refine ⟨114184988514113757632407543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152246651352151676843210057 114184988514113757632407543)
  ·
    refine ⟨171277482771170636448611315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114184988514113757632407543 171277482771170636448611315)
    ·
      refine ⟨256916224156755954672916973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171277482771170636448611315 256916224156755954672916973)
      ·
        refine ⟨96343584058783483002343865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256916224156755954672916973 96343584058783483002343865)
        ·
          refine ⟨72257688044087612251757899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96343584058783483002343865 72257688044087612251757899)
          ·
            refine ⟨108386532066131418377636849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72257688044087612251757899 108386532066131418377636849)
            ·
              refine ⟨81289899049598563783227637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108386532066131418377636849 81289899049598563783227637)
              ·
                refine ⟨7620928035899865354677591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81289899049598563783227637 7620928035899865354677591)
                ·
                  refine ⟨11431392053849798032016387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7620928035899865354677591 11431392053849798032016387)
                  ·
                    refine ⟨17147088080774697048024581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11431392053849798032016387 17147088080774697048024581)
                    ·
                      refine ⟨3215079015145255696504609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17147088080774697048024581 3215079015145255696504609)
                      ·
                        rfl

theorem cell23_6261344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_6261344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261344 prefixEnd_6261344 := by exact prefixLift 6261344
  have htrace : WordTrace (prefixWord ++ tailWord_6261344) baseStart_6261344 baseEnd_6261344 := by
    simpa [prefixWord, tailWord_6261344, baseEnd_6261344] using wordTrace_append hprefix tailTrace_6261344
  have hstable : (prefixWord ++ tailWord_6261344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261344).length < 2 ^ (prefixWord ++ tailWord_6261344).sum := by decide
  have hdescent : baseEnd_6261344 < baseStart_6261344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261367 : List Nat := [1, 1, 3, 1, 1, 3, 5, 8]
def baseStart_6261367 : Nat := 118140960795 + 6261367 * 2 ^ 59
def prefixEnd_6261367 : Nat := 4983230072969 + 3 ^ 40 * 6261367 * 2
def baseEnd_6261367 : Nat := 119077437970381818759889

theorem tailTrace_6261367 : CollatzResearch.WordTrace tailWord_6261367 prefixEnd_6261367 119077437970381818759889 := by
  unfold tailWord_6261367
  simp only [CollatzResearch.WordTrace]
  refine ⟨228370815907144190192902355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152247210604762793461934903 228370815907144190192902355)
  ·
    refine ⟨342556223860716285289353533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228370815907144190192902355 342556223860716285289353533)
    ·
      refine ⟨128458583947768606983507575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342556223860716285289353533 128458583947768606983507575)
      ·
        refine ⟨192687875921652910475261363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128458583947768606983507575 192687875921652910475261363)
        ·
          refine ⟨289031813882479365712892045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192687875921652910475261363 289031813882479365712892045)
          ·
            refine ⟨108386930205929762142334517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 289031813882479365712892045 108386930205929762142334517)
            ·
              refine ⟨10161274706805915200843861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108386930205929762142334517 10161274706805915200843861)
              ·
                refine ⟨119077437970381818759889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10161274706805915200843861 119077437970381818759889)
                ·
                  rfl

theorem cell23_6261367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 8].length) (baseStart_6261367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261367 prefixEnd_6261367 := by exact prefixLift 6261367
  have htrace : WordTrace (prefixWord ++ tailWord_6261367) baseStart_6261367 baseEnd_6261367 := by
    simpa [prefixWord, tailWord_6261367, baseEnd_6261367] using wordTrace_append hprefix tailTrace_6261367
  have hstable : (prefixWord ++ tailWord_6261367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261367).length < 2 ^ (prefixWord ++ tailWord_6261367).sum := by decide
  have hdescent : baseEnd_6261367 < baseStart_6261367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261411 : List Nat := [1, 1, 1, 4, 1, 1, 2, 6, 2, 1, 3]
def baseStart_6261411 : Nat := 118140960795 + 6261411 * 2 ^ 59
def prefixEnd_6261411 : Nat := 4983230072969 + 3 ^ 40 * 6261411 * 2
def baseEnd_6261411 : Nat := 3215113418349106934366801

theorem tailTrace_6261411 : CollatzResearch.WordTrace tailWord_6261411 prefixEnd_6261411 3215113418349106934366801 := by
  unfold tailWord_6261411
  simp only [CollatzResearch.WordTrace]
  refine ⟨228372420718984785707504087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152248280479323190471669391 228372420718984785707504087)
  ·
    refine ⟨342558631078477178561256131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228372420718984785707504087 342558631078477178561256131)
    ·
      refine ⟨513837946617715767841884197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342558631078477178561256131 513837946617715767841884197)
      ·
        refine ⟨96344614990821706470353287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 513837946617715767841884197 96344614990821706470353287)
        ·
          refine ⟨144516922486232559705529931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96344614990821706470353287 144516922486232559705529931)
          ·
            refine ⟨216775383729348839558294897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144516922486232559705529931 216775383729348839558294897)
            ·
              refine ⟨162581537797011629668721173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216775383729348839558294897 162581537797011629668721173)
              ·
                refine ⟨7621009584234920140721305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 162581537797011629668721173 7621009584234920140721305)
                ·
                  refine ⟨5715757188176190105540979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7621009584234920140721305 5715757188176190105540979)
                  ·
                    refine ⟨8573635782264285158311469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5715757188176190105540979 8573635782264285158311469)
                    ·
                      refine ⟨3215113418349106934366801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8573635782264285158311469 3215113418349106934366801)
                      ·
                        rfl

theorem cell23_6261411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_6261411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261411 prefixEnd_6261411 := by exact prefixLift 6261411
  have htrace : WordTrace (prefixWord ++ tailWord_6261411) baseStart_6261411 baseEnd_6261411 := by
    simpa [prefixWord, tailWord_6261411, baseEnd_6261411] using wordTrace_append hprefix tailTrace_6261411
  have hstable : (prefixWord ++ tailWord_6261411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261411).length < 2 ^ (prefixWord ++ tailWord_6261411).sum := by decide
  have hdescent : baseEnd_6261411 < baseStart_6261411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261425 : List Nat := [1, 2, 2, 6, 2, 1, 1, 1, 1, 2, 4]
def baseStart_6261425 : Nat := 118140960795 + 6261425 * 2 ^ 59
def prefixEnd_6261425 : Nat := 4983230072969 + 3 ^ 40 * 6261425 * 2
def baseEnd_6261425 : Nat := 3215120607078269879591737

theorem tailTrace_6261425 : CollatzResearch.WordTrace tailWord_6261425 prefixEnd_6261425 3215120607078269879591737 := by
  unfold tailWord_6261425
  simp only [CollatzResearch.WordTrace]
  refine ⟨228372931340934066098513729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152248620893956044065675819 228372931340934066098513729)
  ·
    refine ⟨171279698505700549573885297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228372931340934066098513729 171279698505700549573885297)
    ·
      refine ⟨128459773879275412180413973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171279698505700549573885297 128459773879275412180413973)
      ·
        refine ⟨6021551900591034945956905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 128459773879275412180413973 6021551900591034945956905)
        ·
          refine ⟨4516163925443276209467679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6021551900591034945956905 4516163925443276209467679)
          ·
            refine ⟨6774245888164914314201519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4516163925443276209467679 6774245888164914314201519)
            ·
              refine ⟨10161368832247371471302279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6774245888164914314201519 10161368832247371471302279)
              ·
                refine ⟨15242053248371057206953419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10161368832247371471302279 15242053248371057206953419)
                ·
                  refine ⟨22863079872556585810430129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15242053248371057206953419 22863079872556585810430129)
                  ·
                    refine ⟨17147309904417439357822597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22863079872556585810430129 17147309904417439357822597)
                    ·
                      refine ⟨3215120607078269879591737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17147309904417439357822597 3215120607078269879591737)
                      ·
                        rfl

theorem cell23_6261425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_6261425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261425 prefixEnd_6261425 := by exact prefixLift 6261425
  have htrace : WordTrace (prefixWord ++ tailWord_6261425) baseStart_6261425 baseEnd_6261425 := by
    simpa [prefixWord, tailWord_6261425, baseEnd_6261425] using wordTrace_append hprefix tailTrace_6261425
  have hstable : (prefixWord ++ tailWord_6261425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261425).length < 2 ^ (prefixWord ++ tailWord_6261425).sum := by decide
  have hdescent : baseEnd_6261425 < baseStart_6261425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261454 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5]
def baseStart_6261454 : Nat := 118140960795 + 6261454 * 2 ^ 59
def prefixEnd_6261454 : Nat := 4983230072969 + 3 ^ 40 * 6261454 * 2
def baseEnd_6261454 : Nat := 3215135498017250266129103

theorem tailTrace_6261454 : CollatzResearch.WordTrace tailWord_6261454 prefixEnd_6261454 3215135498017250266129103 := by
  unfold tailWord_6261454
  simp only [CollatzResearch.WordTrace]
  refine ⟨28546748632228625506414927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152249326038552669367546277 28546748632228625506414927)
  ·
    refine ⟨42820122948342938259622391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28546748632228625506414927 42820122948342938259622391)
    ·
      refine ⟨64230184422514407389433587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42820122948342938259622391 64230184422514407389433587)
      ·
        refine ⟨96345276633771611084150381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64230184422514407389433587 96345276633771611084150381)
        ·
          refine ⟨36129478737664354156556393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96345276633771611084150381 36129478737664354156556393)
          ·
            refine ⟨27097109053248265617417295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36129478737664354156556393 27097109053248265617417295)
            ·
              refine ⟨40645663579872398426125943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27097109053248265617417295 40645663579872398426125943)
              ·
                refine ⟨60968495369808597639188915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40645663579872398426125943 60968495369808597639188915)
                ·
                  refine ⟨91452743054712896458783373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60968495369808597639188915 91452743054712896458783373)
                  ·
                    refine ⟨34294778645517336172043765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91452743054712896458783373 34294778645517336172043765)
                    ·
                      refine ⟨3215135498017250266129103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34294778645517336172043765 3215135498017250266129103)
                      ·
                        rfl

theorem cell23_6261454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_6261454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261454 prefixEnd_6261454 := by exact prefixLift 6261454
  have htrace : WordTrace (prefixWord ++ tailWord_6261454) baseStart_6261454 baseEnd_6261454 := by
    simpa [prefixWord, tailWord_6261454, baseEnd_6261454] using wordTrace_append hprefix tailTrace_6261454
  have hstable : (prefixWord ++ tailWord_6261454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261454).length < 2 ^ (prefixWord ++ tailWord_6261454).sum := by decide
  have hdescent : baseEnd_6261454 < baseStart_6261454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261484 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 3]
def baseStart_6261484 : Nat := 118140960795 + 6261484 * 2 ^ 59
def prefixEnd_6261484 : Nat := 4983230072969 + 3 ^ 40 * 6261484 * 2
def baseEnd_6261484 : Nat := 3215150902436885148753965

theorem tailTrace_6261484 : CollatzResearch.WordTrace tailWord_6261484 prefixEnd_6261484 3215150902436885148753965 := by
  unfold tailWord_6261484
  simp only [CollatzResearch.WordTrace]
  refine ⟨114187541623860159587455753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152250055498480212783274337 114187541623860159587455753)
  ·
    refine ⟨85640656217895119690591815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114187541623860159587455753 85640656217895119690591815)
    ·
      refine ⟨128460984326842679535887723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85640656217895119690591815 128460984326842679535887723)
      ·
        refine ⟨192691476490264019303831585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128460984326842679535887723 192691476490264019303831585)
        ·
          refine ⟨144518607367698014477873689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192691476490264019303831585 144518607367698014477873689)
          ·
            refine ⟨108388955525773510858405267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144518607367698014477873689 108388955525773510858405267)
            ·
              refine ⟨162583433288660266287607901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108388955525773510858405267 162583433288660266287607901)
              ·
                refine ⟨60968787483247599857852963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162583433288660266287607901 60968787483247599857852963)
                ·
                  refine ⟨91453181224871399786779445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60968787483247599857852963 91453181224871399786779445)
                  ·
                    refine ⟨8573735739831693730010573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91453181224871399786779445 8573735739831693730010573)
                    ·
                      refine ⟨3215150902436885148753965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8573735739831693730010573 3215150902436885148753965)
                      ·
                        rfl

theorem cell23_6261484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 3].length) (baseStart_6261484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261484 prefixEnd_6261484 := by exact prefixLift 6261484
  have htrace : WordTrace (prefixWord ++ tailWord_6261484) baseStart_6261484 baseEnd_6261484 := by
    simpa [prefixWord, tailWord_6261484, baseEnd_6261484] using wordTrace_append hprefix tailTrace_6261484
  have hstable : (prefixWord ++ tailWord_6261484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261484).length < 2 ^ (prefixWord ++ tailWord_6261484).sum := by decide
  have hdescent : baseEnd_6261484 < baseStart_6261484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261485 : List Nat := [1, 5, 1, 2, 1, 1, 3, 3, 2, 2, 2]
def baseStart_6261485 : Nat := 118140960795 + 6261485 * 2 ^ 59
def prefixEnd_6261485 : Nat := 4983230072969 + 3 ^ 40 * 6261485 * 2
def baseEnd_6261485 : Nat := 3215151415917539644841461

theorem tailTrace_6261485 : CollatzResearch.WordTrace tailWord_6261485 prefixEnd_6261485 3215151415917539644841461 := by
  unfold tailWord_6261485
  simp only [CollatzResearch.WordTrace]
  refine ⟨228375119720716696345697909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152250079813811130897131939 228375119720716696345697909)
  ·
    refine ⟨21410167473817190282409179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 228375119720716696345697909 21410167473817190282409179)
    ·
      refine ⟨32115251210725785423613769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21410167473817190282409179 32115251210725785423613769)
      ·
        refine ⟨24086438408044339067710327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32115251210725785423613769 24086438408044339067710327)
        ·
          refine ⟨36129657612066508601565491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24086438408044339067710327 36129657612066508601565491)
          ·
            refine ⟨54194486418099762902348237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36129657612066508601565491 54194486418099762902348237)
            ·
              refine ⟨20322932406787411088380589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54194486418099762902348237 20322932406787411088380589)
              ·
                refine ⟨7621099652545279158142721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20322932406787411088380589 7621099652545279158142721)
                ·
                  refine ⟨5715824739408959368607041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7621099652545279158142721 5715824739408959368607041)
                  ·
                    refine ⟨4286868554556719526455281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5715824739408959368607041 4286868554556719526455281)
                    ·
                      refine ⟨3215151415917539644841461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4286868554556719526455281 3215151415917539644841461)
                      ·
                        rfl

theorem cell23_6261485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_6261485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261485 prefixEnd_6261485 := by exact prefixLift 6261485
  have htrace : WordTrace (prefixWord ++ tailWord_6261485) baseStart_6261485 baseEnd_6261485 := by
    simpa [prefixWord, tailWord_6261485, baseEnd_6261485] using wordTrace_append hprefix tailTrace_6261485
  have hstable : (prefixWord ++ tailWord_6261485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261485).length < 2 ^ (prefixWord ++ tailWord_6261485).sum := by decide
  have hdescent : baseEnd_6261485 < baseStart_6261485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261514 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 3, 2, 5]
def baseStart_6261514 : Nat := 118140960795 + 6261514 * 2 ^ 59
def prefixEnd_6261514 : Nat := 4983230072969 + 3 ^ 40 * 6261514 * 2
def baseEnd_6261514 : Nat := 3215166306856520031378827

theorem tailTrace_6261514 : CollatzResearch.WordTrace tailWord_6261514 prefixEnd_6261514 3215166306856520031378827 := by
  unfold tailWord_6261514
  simp only [CollatzResearch.WordTrace]
  refine ⟨57094044359402908574625899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152250784958407756199002397 57094044359402908574625899)
  ·
    refine ⟨85641066539104362861938849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57094044359402908574625899 85641066539104362861938849)
    ·
      refine ⟨64230799904328272146454137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85641066539104362861938849 64230799904328272146454137)
      ·
        refine ⟨48173099928246204109840603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64230799904328272146454137 48173099928246204109840603)
        ·
          refine ⟨72259649892369306164760905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48173099928246204109840603 72259649892369306164760905)
          ·
            refine ⟨54194737419276979623570679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72259649892369306164760905 54194737419276979623570679)
            ·
              refine ⟨81292106128915469435356019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54194737419276979623570679 81292106128915469435356019)
              ·
                refine ⟨121938159193373204153034029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81292106128915469435356019 121938159193373204153034029)
                ·
                  refine ⟨45726809697514951557387761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121938159193373204153034029 45726809697514951557387761)
                  ·
                    refine ⟨34295107273136213668040821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45726809697514951557387761 34295107273136213668040821)
                    ·
                      refine ⟨3215166306856520031378827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34295107273136213668040821 3215166306856520031378827)
                      ·
                        rfl

theorem cell23_6261514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_6261514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261514 prefixEnd_6261514 := by exact prefixLift 6261514
  have htrace : WordTrace (prefixWord ++ tailWord_6261514) baseStart_6261514 baseEnd_6261514 := by
    simpa [prefixWord, tailWord_6261514, baseEnd_6261514] using wordTrace_append hprefix tailTrace_6261514
  have hstable : (prefixWord ++ tailWord_6261514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261514).length < 2 ^ (prefixWord ++ tailWord_6261514).sum := by decide
  have hdescent : baseEnd_6261514 < baseStart_6261514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261564 : List Nat := [2, 2, 2, 2, 1, 1, 1, 4, 8]
def baseStart_6261564 : Nat := 118140960795 + 6261564 * 2 ^ 59
def prefixEnd_6261564 : Nat := 4983230072969 + 3 ^ 40 * 6261564 * 2
def baseEnd_6261564 : Nat := 357243553432138315083733

theorem tailTrace_6261564 : CollatzResearch.WordTrace tailWord_6261564 prefixEnd_6261564 357243553432138315083733 := by
  unfold tailWord_6261564
  simp only [CollatzResearch.WordTrace]
  refine ⟨114189000543715246418911873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152252000724953661891882497 114189000543715246418911873)
  ·
    refine ⟨85641750407786434814183905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114189000543715246418911873 85641750407786434814183905)
    ·
      refine ⟨64231312805839826110637929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85641750407786434814183905 64231312805839826110637929)
      ·
        refine ⟨48173484604379869582978447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64231312805839826110637929 48173484604379869582978447)
        ·
          refine ⟨72260226906569804374467671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48173484604379869582978447 72260226906569804374467671)
          ·
            refine ⟨108390340359854706561701507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72260226906569804374467671 108390340359854706561701507)
            ·
              refine ⟨162585510539782059842552261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108390340359854706561701507 162585510539782059842552261)
              ·
                refine ⟨30484783226209136220478549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162585510539782059842552261 30484783226209136220478549)
                ·
                  refine ⟨357243553432138315083733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30484783226209136220478549 357243553432138315083733)
                  ·
                    rfl

theorem cell23_6261564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 8].length) (baseStart_6261564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261564 prefixEnd_6261564 := by exact prefixLift 6261564
  have htrace : WordTrace (prefixWord ++ tailWord_6261564) baseStart_6261564 baseEnd_6261564 := by
    simpa [prefixWord, tailWord_6261564, baseEnd_6261564] using wordTrace_append hprefix tailTrace_6261564
  have hstable : (prefixWord ++ tailWord_6261564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261564).length < 2 ^ (prefixWord ++ tailWord_6261564).sum := by decide
  have hdescent : baseEnd_6261564 < baseStart_6261564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261584 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 6]
def baseStart_6261584 : Nat := 118140960795 + 6261584 * 2 ^ 59
def prefixEnd_6261584 : Nat := 4983230072969 + 3 ^ 40 * 6261584 * 2
def baseEnd_6261584 : Nat := 3215202250502334757503505

theorem tailTrace_6261584 : CollatzResearch.WordTrace tailWord_6261584 prefixEnd_6261584 3215202250502334757503505 := by
  unfold tailWord_6261584
  simp only [CollatzResearch.WordTrace]
  refine ⟨114189365273679018126775903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152252487031572024169034537 114189365273679018126775903)
  ·
    refine ⟨171284047910518527190163855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114189365273679018126775903 171284047910518527190163855)
    ·
      refine ⟨256926071865777790785245783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171284047910518527190163855 256926071865777790785245783)
      ·
        refine ⟨385389107798666686177868675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256926071865777790785245783 385389107798666686177868675)
        ·
          refine ⟨578083661698000029266803013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385389107798666686177868675 578083661698000029266803013)
          ·
            refine ⟨108390686568375005487525565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 578083661698000029266803013 108390686568375005487525565)
            ·
              refine ⟨40646507463140627057822087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108390686568375005487525565 40646507463140627057822087)
              ·
                refine ⟨60969761194710940586733131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40646507463140627057822087 60969761194710940586733131)
                ·
                  refine ⟨91454641792066410880099697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60969761194710940586733131 91454641792066410880099697)
                  ·
                    refine ⟨68590981344049808160074773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91454641792066410880099697 68590981344049808160074773)
                    ·
                      refine ⟨3215202250502334757503505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68590981344049808160074773 3215202250502334757503505)
                      ·
                        rfl

theorem cell23_6261584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 6].length) (baseStart_6261584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261584 prefixEnd_6261584 := by exact prefixLift 6261584
  have htrace : WordTrace (prefixWord ++ tailWord_6261584) baseStart_6261584 baseEnd_6261584 := by
    simpa [prefixWord, tailWord_6261584, baseEnd_6261584] using wordTrace_append hprefix tailTrace_6261584
  have hstable : (prefixWord ++ tailWord_6261584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261584).length < 2 ^ (prefixWord ++ tailWord_6261584).sum := by decide
  have hdescent : baseEnd_6261584 < baseStart_6261584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261611 : List Nat := [1, 1, 1, 1, 2, 2, 5, 4, 1, 5]
def baseStart_6261611 : Nat := 118140960795 + 6261611 * 2 ^ 59
def prefixEnd_6261611 : Nat := 4983230072969 + 3 ^ 40 * 6261611 * 2
def baseEnd_6261611 : Nat := 1071738704826668717288627

theorem tailTrace_6261611 : CollatzResearch.WordTrace tailWord_6261611 prefixEnd_6261611 1071738704826668717288627 := by
  unfold tailWord_6261611
  simp only [CollatzResearch.WordTrace]
  refine ⟨228379715318260219864784687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152253143545506813243189791 228379715318260219864784687)
  ·
    refine ⟨342569572977390329797177031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228379715318260219864784687 342569572977390329797177031)
    ·
      refine ⟨513854359466085494695765547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342569572977390329797177031 513854359466085494695765547)
      ·
        refine ⟨770781539199128242043648321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513854359466085494695765547 770781539199128242043648321)
        ·
          refine ⟨578086154399346181532736241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 770781539199128242043648321 578086154399346181532736241)
          ·
            refine ⟨433564615799509636149552181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 578086154399346181532736241 433564615799509636149552181)
            ·
              refine ⟨40646682731204028389020517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 433564615799509636149552181 40646682731204028389020517)
              ·
                refine ⟨7621253012100755322941347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40646682731204028389020517 7621253012100755322941347)
                ·
                  refine ⟨11431879518151132984412021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7621253012100755322941347 11431879518151132984412021)
                  ·
                    refine ⟨1071738704826668717288627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11431879518151132984412021 1071738704826668717288627)
                    ·
                      rfl

theorem cell23_6261611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 5].length) (baseStart_6261611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261611 prefixEnd_6261611 := by exact prefixLift 6261611
  have htrace : WordTrace (prefixWord ++ tailWord_6261611) baseStart_6261611 baseEnd_6261611 := by
    simpa [prefixWord, tailWord_6261611, baseEnd_6261611] using wordTrace_append hprefix tailTrace_6261611
  have hstable : (prefixWord ++ tailWord_6261611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261611).length < 2 ^ (prefixWord ++ tailWord_6261611).sum := by decide
  have hdescent : baseEnd_6261611 < baseStart_6261611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261618 : List Nat := [3, 2, 1, 2, 1, 1, 4, 1, 1, 5, 2]
def baseStart_6261618 : Nat := 118140960795 + 6261618 * 2 ^ 59
def prefixEnd_6261618 : Nat := 4983230072969 + 3 ^ 40 * 6261618 * 2
def baseEnd_6261618 : Nat := 3215219708844587624478349

theorem tailTrace_6261618 : CollatzResearch.WordTrace tailWord_6261618 prefixEnd_6261618 3215219708844587624478349 := by
  unfold tailWord_6261618
  simp only [CollatzResearch.WordTrace]
  refine ⟨57094992657308715015072377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152253313752823240040193005 57094992657308715015072377)
  ·
    refine ⟨42821244492981536261304283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57094992657308715015072377 42821244492981536261304283)
    ·
      refine ⟨64231866739472304391956425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42821244492981536261304283 64231866739472304391956425)
      ·
        refine ⟨48173900054604228293967319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64231866739472304391956425 48173900054604228293967319)
        ·
          refine ⟨72260850081906342440950979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48173900054604228293967319 72260850081906342440950979)
          ·
            refine ⟨108391275122859513661426469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72260850081906342440950979 108391275122859513661426469)
            ·
              refine ⟨20323364085536158811517463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108391275122859513661426469 20323364085536158811517463)
              ·
                refine ⟨30485046128304238217276195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20323364085536158811517463 30485046128304238217276195)
                ·
                  refine ⟨45727569192456357325914293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30485046128304238217276195 45727569192456357325914293)
                  ·
                    refine ⟨4286959611792783499304465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45727569192456357325914293 4286959611792783499304465)
                    ·
                      refine ⟨3215219708844587624478349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4286959611792783499304465 3215219708844587624478349)
                      ·
                        rfl

theorem cell23_6261618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_6261618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261618 prefixEnd_6261618 := by exact prefixLift 6261618
  have htrace : WordTrace (prefixWord ++ tailWord_6261618) baseStart_6261618 baseEnd_6261618 := by
    simpa [prefixWord, tailWord_6261618, baseEnd_6261618] using wordTrace_append hprefix tailTrace_6261618
  have hstable : (prefixWord ++ tailWord_6261618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261618).length < 2 ^ (prefixWord ++ tailWord_6261618).sum := by decide
  have hdescent : baseEnd_6261618 < baseStart_6261618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261642 : List Nat := [3, 1, 2, 4, 1, 3, 1, 1, 3, 1, 3]
def baseStart_6261642 : Nat := 118140960795 + 6261642 * 2 ^ 59
def prefixEnd_6261642 : Nat := 4983230072969 + 3 ^ 40 * 6261642 * 2
def baseEnd_6261642 : Nat := 3215232032380295530578239

theorem tailTrace_6261642 : CollatzResearch.WordTrace tailWord_6261642 prefixEnd_6261642 3215232032380295530578239 := by
  unfold tailWord_6261642
  simp only [CollatzResearch.WordTrace]
  refine ⟨57095211495286978039790795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152253897320765274772775453 57095211495286978039790795)
  ·
    refine ⟨85642817242930467059686193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57095211495286978039790795 85642817242930467059686193)
    ·
      refine ⟨64232112932197850294764645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85642817242930467059686193 64232112932197850294764645)
      ·
        refine ⟨12043521174787096930268371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64232112932197850294764645 12043521174787096930268371)
        ·
          refine ⟨18065281762180645395402557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12043521174787096930268371 18065281762180645395402557)
          ·
            refine ⟨6774480660817742023275959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18065281762180645395402557 6774480660817742023275959)
            ·
              refine ⟨10161720991226613034913939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6774480660817742023275959 10161720991226613034913939)
              ·
                refine ⟨15242581486839919552370909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10161720991226613034913939 15242581486839919552370909)
                ·
                  refine ⟨5715968057564969832139091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15242581486839919552370909 5715968057564969832139091)
                  ·
                    refine ⟨8573952086347454748208637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5715968057564969832139091 8573952086347454748208637)
                    ·
                      refine ⟨3215232032380295530578239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8573952086347454748208637 3215232032380295530578239)
                      ·
                        rfl

theorem cell23_6261642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_6261642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261642 prefixEnd_6261642 := by exact prefixLift 6261642
  have htrace : WordTrace (prefixWord ++ tailWord_6261642) baseStart_6261642 baseEnd_6261642 := by
    simpa [prefixWord, tailWord_6261642, baseEnd_6261642] using wordTrace_append hprefix tailTrace_6261642
  have hstable : (prefixWord ++ tailWord_6261642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261642).length < 2 ^ (prefixWord ++ tailWord_6261642).sum := by decide
  have hdescent : baseEnd_6261642 < baseStart_6261642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261661 : List Nat := [1, 4, 2, 1, 2, 1, 1, 3, 1, 1, 6]
def baseStart_6261661 : Nat := 118140960795 + 6261661 * 2 ^ 59
def prefixEnd_6261661 : Nat := 4983230072969 + 3 ^ 40 * 6261661 * 2
def baseEnd_6261661 : Nat := 3215241788512730956240651

theorem tailTrace_6261661 : CollatzResearch.WordTrace tailWord_6261661 prefixEnd_6261661 3215241788512730956240651 := by
  unfold tailWord_6261661
  simp only [CollatzResearch.WordTrace]
  refine ⟨228381538968079078404104837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152254359312052718936069891 228381538968079078404104837)
  ·
    refine ⟨42821538556514827200769657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228381538968079078404104837 42821538556514827200769657)
    ·
      refine ⟨32116153917386120400577243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42821538556514827200769657 32116153917386120400577243)
      ·
        refine ⟨48174230876079180600865865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32116153917386120400577243 48174230876079180600865865)
        ·
          refine ⟨36130673157059385450649399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48174230876079180600865865 36130673157059385450649399)
          ·
            refine ⟨54196009735589078175974099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36130673157059385450649399 54196009735589078175974099)
            ·
              refine ⟨81294014603383617263961149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54196009735589078175974099 81294014603383617263961149)
              ·
                refine ⟨30485255476268856473985431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81294014603383617263961149 30485255476268856473985431)
                ·
                  refine ⟨45727883214403284710978147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30485255476268856473985431 45727883214403284710978147)
                  ·
                    refine ⟨68591824821604927066467221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45727883214403284710978147 68591824821604927066467221)
                    ·
                      refine ⟨3215241788512730956240651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68591824821604927066467221 3215241788512730956240651)
                      ·
                        rfl

theorem cell23_6261661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_6261661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261661 prefixEnd_6261661 := by exact prefixLift 6261661
  have htrace : WordTrace (prefixWord ++ tailWord_6261661) baseStart_6261661 baseEnd_6261661 := by
    simpa [prefixWord, tailWord_6261661, baseEnd_6261661] using wordTrace_append hprefix tailTrace_6261661
  have hstable : (prefixWord ++ tailWord_6261661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261661).length < 2 ^ (prefixWord ++ tailWord_6261661).sum := by decide
  have hdescent : baseEnd_6261661 < baseStart_6261661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261665 : List Nat := [1, 2, 3, 4, 1, 1, 3, 2, 1, 1, 4]
def baseStart_6261665 : Nat := 118140960795 + 6261665 * 2 ^ 59
def prefixEnd_6261665 : Nat := 4983230072969 + 3 ^ 40 * 6261665 * 2
def baseEnd_6261665 : Nat := 3215243842435348940590633

theorem tailTrace_6261665 : CollatzResearch.WordTrace tailWord_6261665 prefixEnd_6261665 3215243842435348940590633 := by
  unfold tailWord_6261665
  simp only [CollatzResearch.WordTrace]
  refine ⟨228381684860064587087250449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152254456573376391391500299 228381684860064587087250449)
  ·
    refine ⟨171286263645048440315437837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228381684860064587087250449 171286263645048440315437837)
    ·
      refine ⟨64232348866893165118289189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171286263645048440315437837 64232348866893165118289189)
      ·
        refine ⟨12043565412542468459679223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64232348866893165118289189 12043565412542468459679223)
        ·
          refine ⟨18065348118813702689518835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12043565412542468459679223 18065348118813702689518835)
          ·
            refine ⟨27098022178220554034278253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18065348118813702689518835 27098022178220554034278253)
            ·
              refine ⟨10161758316832707762854345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27098022178220554034278253 10161758316832707762854345)
              ·
                refine ⟨7621318737624530822140759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10161758316832707762854345 7621318737624530822140759)
                ·
                  refine ⟨11431978106436796233211139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7621318737624530822140759 11431978106436796233211139)
                  ·
                    refine ⟨17147967159655194349816709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11431978106436796233211139 17147967159655194349816709)
                    ·
                      refine ⟨3215243842435348940590633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17147967159655194349816709 3215243842435348940590633)
                      ·
                        rfl

theorem cell23_6261665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_6261665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261665 prefixEnd_6261665 := by exact prefixLift 6261665
  have htrace : WordTrace (prefixWord ++ tailWord_6261665) baseStart_6261665 baseEnd_6261665 := by
    simpa [prefixWord, tailWord_6261665, baseEnd_6261665] using wordTrace_append hprefix tailTrace_6261665
  have hstable : (prefixWord ++ tailWord_6261665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261665).length < 2 ^ (prefixWord ++ tailWord_6261665).sum := by decide
  have hdescent : baseEnd_6261665 < baseStart_6261665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261668 : List Nat := [2, 3, 1, 2, 1, 2, 3, 1, 3, 2, 3]
def baseStart_6261668 : Nat := 118140960795 + 6261668 * 2 ^ 59
def prefixEnd_6261668 : Nat := 4983230072969 + 3 ^ 40 * 6261668 * 2
def baseEnd_6261668 : Nat := 3215245382877312428853119

theorem tailTrace_6261668 : CollatzResearch.WordTrace tailWord_6261668 prefixEnd_6261668 3215245382877312428853119 := by
  unfold tailWord_6261668
  simp only [CollatzResearch.WordTrace]
  refine ⟨114190897139526859299804829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152254529519369145733073105 114190897139526859299804829)
  ·
    refine ⟨42821586427322572237426811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114190897139526859299804829 42821586427322572237426811)
    ·
      refine ⟨64232379640983858356140217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42821586427322572237426811 64232379640983858356140217)
      ·
        refine ⟨48174284730737893767105163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64232379640983858356140217 48174284730737893767105163)
        ·
          refine ⟨72261427096106840650657745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48174284730737893767105163 72261427096106840650657745)
          ·
            refine ⟨54196070322080130487993309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72261427096106840650657745 54196070322080130487993309)
            ·
              refine ⟨20323526370780048932997491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54196070322080130487993309 20323526370780048932997491)
              ·
                refine ⟨30485289556170073399496237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20323526370780048932997491 30485289556170073399496237)
                ·
                  refine ⟨11431983583563777524811089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30485289556170073399496237 11431983583563777524811089)
                  ·
                    refine ⟨8573987687672833143608317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11431983583563777524811089 8573987687672833143608317)
                    ·
                      refine ⟨3215245382877312428853119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8573987687672833143608317 3215245382877312428853119)
                      ·
                        rfl

theorem cell23_6261668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_6261668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261668 prefixEnd_6261668 := by exact prefixLift 6261668
  have htrace : WordTrace (prefixWord ++ tailWord_6261668) baseStart_6261668 baseEnd_6261668 := by
    simpa [prefixWord, tailWord_6261668, baseEnd_6261668] using wordTrace_append hprefix tailTrace_6261668
  have hstable : (prefixWord ++ tailWord_6261668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261668).length < 2 ^ (prefixWord ++ tailWord_6261668).sum := by decide
  have hdescent : baseEnd_6261668 < baseStart_6261668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261709 : List Nat := [1, 6, 3, 1, 1, 1, 2, 1, 1, 6]
def baseStart_6261709 : Nat := 118140960795 + 6261709 * 2 ^ 59
def prefixEnd_6261709 : Nat := 4983230072969 + 3 ^ 40 * 6261709 * 2
def baseEnd_6261709 : Nat := 1071755478528048922813477

theorem tailTrace_6261709 : CollatzResearch.WordTrace tailWord_6261709 prefixEnd_6261709 1071755478528048922813477 := by
  unfold tailWord_6261709
  simp only [CollatzResearch.WordTrace]
  refine ⟨228383289671905182601852181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152255526447936788401234787 228383289671905182601852181)
  ·
    refine ⟨10705466703370555434461821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 228383289671905182601852181 10705466703370555434461821)
    ·
      refine ⟨4014550013763958287923183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10705466703370555434461821 4014550013763958287923183)
      ·
        refine ⟨6021825020645937431884775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4014550013763958287923183 6021825020645937431884775)
        ·
          refine ⟨9032737530968906147827163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6021825020645937431884775 9032737530968906147827163)
          ·
            refine ⟨13549106296453359221740745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9032737530968906147827163 13549106296453359221740745)
            ·
              refine ⟨10161829722340019416305559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13549106296453359221740745 10161829722340019416305559)
              ·
                refine ⟨15242744583510029124458339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10161829722340019416305559 15242744583510029124458339)
                ·
                  refine ⟨22864116875265043686687509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15242744583510029124458339 22864116875265043686687509)
                  ·
                    refine ⟨1071755478528048922813477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22864116875265043686687509 1071755478528048922813477)
                    ·
                      rfl

theorem cell23_6261709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_6261709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261709 prefixEnd_6261709 := by exact prefixLift 6261709
  have htrace : WordTrace (prefixWord ++ tailWord_6261709) baseStart_6261709 baseEnd_6261709 := by
    simpa [prefixWord, tailWord_6261709, baseEnd_6261709] using wordTrace_append hprefix tailTrace_6261709
  have hstable : (prefixWord ++ tailWord_6261709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261709).length < 2 ^ (prefixWord ++ tailWord_6261709).sum := by decide
  have hdescent : baseEnd_6261709 < baseStart_6261709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261731 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 1, 8]
def baseStart_6261731 : Nat := 118140960795 + 6261731 * 2 ^ 59
def prefixEnd_6261731 : Nat := 4983230072969 + 3 ^ 40 * 6261731 * 2
def baseEnd_6261731 : Nat := 1071759244052848560788443

theorem tailTrace_6261731 : CollatzResearch.WordTrace tailWord_6261731 prefixEnd_6261731 1071759244052848560788443 := by
  unfold tailWord_6261731
  simp only [CollatzResearch.WordTrace]
  refine ⟨228384092077825480359153047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152256061385216986906102031 228384092077825480359153047)
  ·
    refine ⟨342576138116738220538729571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228384092077825480359153047 342576138116738220538729571)
    ·
      refine ⟨513864207175107330808094357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342576138116738220538729571 513864207175107330808094357)
      ·
        refine ⟨24087384711333156131629423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 513864207175107330808094357 24087384711333156131629423)
        ·
          refine ⟨36131077066999734197444135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24087384711333156131629423 36131077066999734197444135)
          ·
            refine ⟨54196615600499601296166203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36131077066999734197444135 54196615600499601296166203)
            ·
              refine ⟨81294923400749401944249305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54196615600499601296166203 81294923400749401944249305)
              ·
                refine ⟨60971192550562051458186979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81294923400749401944249305 60971192550562051458186979)
                ·
                  refine ⟨91456788825843077187280469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60971192550562051458186979 91456788825843077187280469)
                  ·
                    refine ⟨1071759244052848560788443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 91456788825843077187280469 1071759244052848560788443)
                    ·
                      rfl

theorem cell23_6261731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 8].length) (baseStart_6261731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261731 prefixEnd_6261731 := by exact prefixLift 6261731
  have htrace : WordTrace (prefixWord ++ tailWord_6261731) baseStart_6261731 baseEnd_6261731 := by
    simpa [prefixWord, tailWord_6261731, baseEnd_6261731] using wordTrace_append hprefix tailTrace_6261731
  have hstable : (prefixWord ++ tailWord_6261731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261731).length < 2 ^ (prefixWord ++ tailWord_6261731).sum := by decide
  have hdescent : baseEnd_6261731 < baseStart_6261731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261749 : List Nat := [1, 3, 5, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_6261749 : Nat := 118140960795 + 6261749 * 2 ^ 59
def prefixEnd_6261749 : Nat := 4983230072969 + 3 ^ 40 * 6261749 * 2
def baseEnd_6261749 : Nat := 3215286974810326611940247

theorem tailTrace_6261749 : CollatzResearch.WordTrace tailWord_6261749 prefixEnd_6261749 3215286974810326611940247 := by
  unfold tailWord_6261749
  simp only [CollatzResearch.WordTrace]
  refine ⟨228384748591760269433308301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152256499061173512955538867 228384748591760269433308301)
  ·
    refine ⟨85644280721910101037490613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228384748591760269433308301 85644280721910101037490613)
    ·
      refine ⟨8029151317679071972264745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85644280721910101037490613 8029151317679071972264745)
      ·
        refine ⟨6021863488259303979198559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8029151317679071972264745 6021863488259303979198559)
        ·
          refine ⟨9032795232388955968797839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6021863488259303979198559 9032795232388955968797839)
          ·
            refine ⟨13549192848583433953196759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9032795232388955968797839 13549192848583433953196759)
            ·
              refine ⟨20323789272875150929795139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13549192848583433953196759 20323789272875150929795139)
              ·
                refine ⟨30485683909312726394692709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20323789272875150929795139 30485683909312726394692709)
                ·
                  refine ⟨5716065732996136199004883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30485683909312726394692709 5716065732996136199004883)
                  ·
                    refine ⟨8574098599494204298507325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5716065732996136199004883 8574098599494204298507325)
                    ·
                      refine ⟨3215286974810326611940247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8574098599494204298507325 3215286974810326611940247)
                      ·
                        rfl

theorem cell23_6261749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_6261749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261749 prefixEnd_6261749 := by exact prefixLift 6261749
  have htrace : WordTrace (prefixWord ++ tailWord_6261749) baseStart_6261749 baseEnd_6261749 := by
    simpa [prefixWord, tailWord_6261749, baseEnd_6261749] using wordTrace_append hprefix tailTrace_6261749
  have hstable : (prefixWord ++ tailWord_6261749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261749).length < 2 ^ (prefixWord ++ tailWord_6261749).sum := by decide
  have hdescent : baseEnd_6261749 < baseStart_6261749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261768 : List Nat := [2, 1, 3, 2, 1, 3, 2, 1, 2, 2, 4]
def baseStart_6261768 : Nat := 118140960795 + 6261768 * 2 ^ 59
def prefixEnd_6261768 : Nat := 4983230072969 + 3 ^ 40 * 6261768 * 2
def baseEnd_6261768 : Nat := 3215296730942762037602659

theorem tailTrace_6261768 : CollatzResearch.WordTrace tailWord_6261768 prefixEnd_6261768 3215296730942762037602659 := by
  unfold tailWord_6261768
  simp only [CollatzResearch.WordTrace]
  refine ⟨114192720789345717839124979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152256961052460957118833305 114192720789345717839124979)
  ·
    refine ⟨171289081184018576758687469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114192720789345717839124979 171289081184018576758687469)
    ·
      refine ⟨64233405444006966284507801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171289081184018576758687469 64233405444006966284507801)
      ·
        refine ⟨48175054083005224713380851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64233405444006966284507801 48175054083005224713380851)
        ·
          refine ⟨72262581124507837070071277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48175054083005224713380851 72262581124507837070071277)
          ·
            refine ⟨27098467921690438901276729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72262581124507837070071277 27098467921690438901276729)
            ·
              refine ⟨20323850941267829175957547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27098467921690438901276729 20323850941267829175957547)
              ·
                refine ⟨30485776411901743763936321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20323850941267829175957547 30485776411901743763936321)
                ·
                  refine ⟨22864332308926307822952241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30485776411901743763936321 22864332308926307822952241)
                  ·
                    refine ⟨17148249231694730867214181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22864332308926307822952241 17148249231694730867214181)
                    ·
                      refine ⟨3215296730942762037602659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17148249231694730867214181 3215296730942762037602659)
                      ·
                        rfl

theorem cell23_6261768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_6261768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261768 prefixEnd_6261768 := by exact prefixLift 6261768
  have htrace : WordTrace (prefixWord ++ tailWord_6261768) baseStart_6261768 baseEnd_6261768 := by
    simpa [prefixWord, tailWord_6261768, baseEnd_6261768] using wordTrace_append hprefix tailTrace_6261768
  have hstable : (prefixWord ++ tailWord_6261768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261768).length < 2 ^ (prefixWord ++ tailWord_6261768).sum := by decide
  have hdescent : baseEnd_6261768 < baseStart_6261768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261772 : List Nat := [2, 2, 1, 2, 3, 4, 1, 1, 1, 4, 2]
def baseStart_6261772 : Nat := 118140960795 + 6261772 * 2 ^ 59
def prefixEnd_6261772 : Nat := 4983230072969 + 3 ^ 40 * 6261772 * 2
def baseEnd_6261772 : Nat := 3215298784865380021952641

theorem tailTrace_6261772 : CollatzResearch.WordTrace tailWord_6261772 prefixEnd_6261772 3215298784865380021952641 := by
  unfold tailWord_6261772
  simp only [CollatzResearch.WordTrace]
  refine ⟨114192793735338472180697785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152257058313784629574263713 114192793735338472180697785)
  ·
    refine ⟨85644595301503854135523339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114192793735338472180697785 85644595301503854135523339)
    ·
      refine ⟨128466892952255781203285009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85644595301503854135523339 128466892952255781203285009)
      ·
        refine ⟨96350169714191835902463757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128466892952255781203285009 96350169714191835902463757)
        ·
          refine ⟨36131313642821938463423909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96350169714191835902463757 36131313642821938463423909)
          ·
            refine ⟨6774621308029113461891983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36131313642821938463423909 6774621308029113461891983)
            ·
              refine ⟨10161931962043670192837975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6774621308029113461891983 10161931962043670192837975)
              ·
                refine ⟨15242897943065505289256963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10161931962043670192837975 15242897943065505289256963)
                ·
                  refine ⟨22864346914598257933885445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15242897943065505289256963 22864346914598257933885445)
                  ·
                    refine ⟨4287065046487173362603521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22864346914598257933885445 4287065046487173362603521)
                    ·
                      refine ⟨3215298784865380021952641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4287065046487173362603521 3215298784865380021952641)
                      ·
                        rfl

theorem cell23_6261772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 1, 4, 2].length) (baseStart_6261772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261772 prefixEnd_6261772 := by exact prefixLift 6261772
  have htrace : WordTrace (prefixWord ++ tailWord_6261772) baseStart_6261772 baseEnd_6261772 := by
    simpa [prefixWord, tailWord_6261772, baseEnd_6261772] using wordTrace_append hprefix tailTrace_6261772
  have hstable : (prefixWord ++ tailWord_6261772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261772).length < 2 ^ (prefixWord ++ tailWord_6261772).sum := by decide
  have hdescent : baseEnd_6261772 < baseStart_6261772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261795 : List Nat := [1, 1, 1, 4, 3, 2, 3, 3, 5]
def baseStart_6261795 : Nat := 118140960795 + 6261795 * 2 ^ 59
def prefixEnd_6261795 : Nat := 4983230072969 + 3 ^ 40 * 6261795 * 2
def baseEnd_6261795 : Nat := 357256732768937047996115

theorem tailTrace_6261795 : CollatzResearch.WordTrace tailWord_6261795 prefixEnd_6261795 357256732768937047996115 := by
  unfold tailWord_6261795
  simp only [CollatzResearch.WordTrace]
  refine ⟨228386426349593619289482839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152257617566395746192988559 228386426349593619289482839)
  ·
    refine ⟨342579639524390428934224259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228386426349593619289482839 342579639524390428934224259)
    ·
      refine ⟨513869459286585643401336389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342579639524390428934224259 513869459286585643401336389)
      ·
        refine ⟨96350523616234808137750573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 513869459286585643401336389 96350523616234808137750573)
        ·
          refine ⟨36131446356088053051656465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96350523616234808137750573 36131446356088053051656465)
          ·
            refine ⟨27098584767066039788742349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36131446356088053051656465 27098584767066039788742349)
            ·
              refine ⟨10161969287649764920778381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27098584767066039788742349 10161969287649764920778381)
              ·
                refine ⟨3810738482868661845291893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10161969287649764920778381 3810738482868661845291893)
                ·
                  refine ⟨357256732768937047996115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3810738482868661845291893 357256732768937047996115)
                  ·
                    rfl

theorem cell23_6261795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 3, 5].length) (baseStart_6261795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261795 prefixEnd_6261795 := by exact prefixLift 6261795
  have htrace : WordTrace (prefixWord ++ tailWord_6261795) baseStart_6261795 baseEnd_6261795 := by
    simpa [prefixWord, tailWord_6261795, baseEnd_6261795] using wordTrace_append hprefix tailTrace_6261795
  have hstable : (prefixWord ++ tailWord_6261795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261795).length < 2 ^ (prefixWord ++ tailWord_6261795).sum := by decide
  have hdescent : baseEnd_6261795 < baseStart_6261795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261808 : List Nat := [2, 1, 1, 1, 2, 4, 3, 2, 2, 5]
def baseStart_6261808 : Nat := 118140960795 + 6261808 * 2 ^ 59
def prefixEnd_6261808 : Nat := 4983230072969 + 3 ^ 40 * 6261808 * 2
def baseEnd_6261808 : Nat := 1071772423389647293700825

theorem tailTrace_6261808 : CollatzResearch.WordTrace tailWord_6261808 prefixEnd_6261808 1071772423389647293700825 := by
  unfold tailWord_6261808
  simp only [CollatzResearch.WordTrace]
  refine ⟨114193450249273261254853039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152257933665697681673137385 114193450249273261254853039)
  ·
    refine ⟨171290175373909891882279559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114193450249273261254853039 171290175373909891882279559)
    ·
      refine ⟨256935263060864837823419339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171290175373909891882279559 256935263060864837823419339)
      ·
        refine ⟨385402894591297256735129009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256935263060864837823419339 385402894591297256735129009)
        ·
          refine ⟨289052170943472942551346757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385402894591297256735129009 289052170943472942551346757)
          ·
            refine ⟨54197282051901176728377517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 289052170943472942551346757 54197282051901176728377517)
            ·
              refine ⟨20323980769462941273141569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54197282051901176728377517 20323980769462941273141569)
              ·
                refine ⟨15242985577097205954856177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20323980769462941273141569 15242985577097205954856177)
                ·
                  refine ⟨11432239182822904466142133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15242985577097205954856177 11432239182822904466142133)
                  ·
                    refine ⟨1071772423389647293700825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11432239182822904466142133 1071772423389647293700825)
                    ·
                      rfl

theorem cell23_6261808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 2, 5].length) (baseStart_6261808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261808 prefixEnd_6261808 := by exact prefixLift 6261808
  have htrace : WordTrace (prefixWord ++ tailWord_6261808) baseStart_6261808 baseEnd_6261808 := by
    simpa [prefixWord, tailWord_6261808, baseEnd_6261808] using wordTrace_append hprefix tailTrace_6261808
  have hstable : (prefixWord ++ tailWord_6261808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261808).length < 2 ^ (prefixWord ++ tailWord_6261808).sum := by decide
  have hdescent : baseEnd_6261808 < baseStart_6261808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261812 : List Nat := [2, 5, 1, 2, 1, 3, 1, 1, 7]
def baseStart_6261812 : Nat := 118140960795 + 6261812 * 2 ^ 59
def prefixEnd_6261812 : Nat := 4983230072969 + 3 ^ 40 * 6261812 * 2
def baseEnd_6261812 : Nat := 357257702676839985050273

theorem tailTrace_6261812 : CollatzResearch.WordTrace tailWord_6261812 prefixEnd_6261812 357257702676839985050273 := by
  unfold tailWord_6261812
  simp only [CollatzResearch.WordTrace]
  refine ⟨114193523195266015596425845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152258030927021354128567793 114193523195266015596425845)
  ·
    refine ⟨10705642799556188962164923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114193523195266015596425845 10705642799556188962164923)
    ·
      refine ⟨16058464199334283443247385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10705642799556188962164923 16058464199334283443247385)
      ·
        refine ⟨12043848149500712582435539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16058464199334283443247385 12043848149500712582435539)
        ·
          refine ⟨18065772224251068873653309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12043848149500712582435539 18065772224251068873653309)
          ·
            refine ⟨6774664584094150827619991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18065772224251068873653309 6774664584094150827619991)
            ·
              refine ⟨10161996876141226241429987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6774664584094150827619991 10161996876141226241429987)
              ·
                refine ⟨15242995314211839362144981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10161996876141226241429987 15242995314211839362144981)
                ·
                  refine ⟨357257702676839985050273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15242995314211839362144981 357257702676839985050273)
                  ·
                    rfl

theorem cell23_6261812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_6261812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261812 prefixEnd_6261812 := by exact prefixLift 6261812
  have htrace : WordTrace (prefixWord ++ tailWord_6261812) baseStart_6261812 baseEnd_6261812 := by
    simpa [prefixWord, tailWord_6261812, baseEnd_6261812] using wordTrace_append hprefix tailTrace_6261812
  have hstable : (prefixWord ++ tailWord_6261812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261812).length < 2 ^ (prefixWord ++ tailWord_6261812).sum := by decide
  have hdescent : baseEnd_6261812 < baseStart_6261812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261845 : List Nat := [1, 3, 2, 2, 1, 2, 4, 1, 2, 1, 4]
def baseStart_6261845 : Nat := 118140960795 + 6261845 * 2 ^ 59
def prefixEnd_6261845 : Nat := 4983230072969 + 3 ^ 40 * 6261845 * 2
def baseEnd_6261845 : Nat := 3215336268953158236339805

theorem tailTrace_6261845 : CollatzResearch.WordTrace tailWord_6261845 prefixEnd_6261845 3215336268953158236339805 := by
  unfold tailWord_6261845
  simp only [CollatzResearch.WordTrace]
  refine ⟨228388249999412477828802989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152258833332941651885868659 228388249999412477828802989)
  ·
    refine ⟨85645593749779679185801121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228388249999412477828802989 85645593749779679185801121)
    ·
      refine ⟨64234195312334759389350841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85645593749779679185801121 64234195312334759389350841)
      ·
        refine ⟨48175646484251069542013131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64234195312334759389350841 48175646484251069542013131)
        ·
          refine ⟨72263469726376604313019697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48175646484251069542013131 72263469726376604313019697)
          ·
            refine ⟨54197602294782453234764773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72263469726376604313019697 54197602294782453234764773)
            ·
              refine ⟨10162050430271709981518395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54197602294782453234764773 10162050430271709981518395)
              ·
                refine ⟨15243075645407564972277593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10162050430271709981518395 15243075645407564972277593)
                ·
                  refine ⟨11432306734055673729208195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15243075645407564972277593 11432306734055673729208195)
                  ·
                    refine ⟨17148460101083510593812293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11432306734055673729208195 17148460101083510593812293)
                    ·
                      refine ⟨3215336268953158236339805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17148460101083510593812293 3215336268953158236339805)
                      ·
                        rfl

theorem cell23_6261845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_6261845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261845 prefixEnd_6261845 := by exact prefixLift 6261845
  have htrace : WordTrace (prefixWord ++ tailWord_6261845) baseStart_6261845 baseEnd_6261845 := by
    simpa [prefixWord, tailWord_6261845, baseEnd_6261845] using wordTrace_append hprefix tailTrace_6261845
  have hstable : (prefixWord ++ tailWord_6261845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261845).length < 2 ^ (prefixWord ++ tailWord_6261845).sum := by decide
  have hdescent : baseEnd_6261845 < baseStart_6261845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261865 : List Nat := [1, 2, 1, 1, 1, 6, 2, 2, 2, 2, 3]
def baseStart_6261865 : Nat := 118140960795 + 6261865 * 2 ^ 59
def prefixEnd_6261865 : Nat := 4983230072969 + 3 ^ 40 * 6261865 * 2
def baseEnd_6261865 : Nat := 3215346538566248158089713

theorem tailTrace_6261865 : CollatzResearch.WordTrace tailWord_6261865 prefixEnd_6261865 3215346538566248158089713 := by
  unfold tailWord_6261865
  simp only [CollatzResearch.WordTrace]
  refine ⟨228388979459340021244531049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152259319639560014163020699 228388979459340021244531049)
  ·
    refine ⟨171291734594505015933398287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228388979459340021244531049 171291734594505015933398287)
    ·
      refine ⟨256937601891757523900097431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171291734594505015933398287 256937601891757523900097431)
      ·
        refine ⟨385406402837636285850146147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256937601891757523900097431 385406402837636285850146147)
        ·
          refine ⟨578109604256454428775219221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385406402837636285850146147 578109604256454428775219221)
          ·
            refine ⟨27098887699521301348838401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 578109604256454428775219221 27098887699521301348838401)
            ·
              refine ⟨20324165774640976011628801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27098887699521301348838401 20324165774640976011628801)
              ·
                refine ⟨15243124330980732008721601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20324165774640976011628801 15243124330980732008721601)
                ·
                  refine ⟨11432343248235549006541201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15243124330980732008721601 11432343248235549006541201)
                  ·
                    refine ⟨8574257436176661754905901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11432343248235549006541201 8574257436176661754905901)
                    ·
                      refine ⟨3215346538566248158089713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8574257436176661754905901 3215346538566248158089713)
                      ·
                        rfl

theorem cell23_6261865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 2, 3].length) (baseStart_6261865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261865 prefixEnd_6261865 := by exact prefixLift 6261865
  have htrace : WordTrace (prefixWord ++ tailWord_6261865) baseStart_6261865 baseEnd_6261865 := by
    simpa [prefixWord, tailWord_6261865, baseEnd_6261865] using wordTrace_append hprefix tailTrace_6261865
  have hstable : (prefixWord ++ tailWord_6261865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261865).length < 2 ^ (prefixWord ++ tailWord_6261865).sum := by decide
  have hdescent : baseEnd_6261865 < baseStart_6261865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261872 : List Nat := [2, 1, 1, 1, 5, 1, 3, 4, 1, 4]
def baseStart_6261872 : Nat := 118140960795 + 6261872 * 2 ^ 59
def prefixEnd_6261872 : Nat := 4983230072969 + 3 ^ 40 * 6261872 * 2
def baseEnd_6261872 : Nat := 1071783377643609876900727

theorem tailTrace_6261872 : CollatzResearch.WordTrace tailWord_6261872 prefixEnd_6261872 1071783377643609876900727 := by
  unfold tailWord_6261872
  simp only [CollatzResearch.WordTrace]
  refine ⟨114194617385157330720017935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152259489846876440960023913 114194617385157330720017935)
  ·
    refine ⟨171291926077735996080026903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114194617385157330720017935 171291926077735996080026903)
    ·
      refine ⟨256937889116603994120040355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171291926077735996080026903 256937889116603994120040355)
      ·
        refine ⟨385406833674905991180060533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256937889116603994120040355 385406833674905991180060533)
        ·
          refine ⟨36131890657022436673130675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 385406833674905991180060533 36131890657022436673130675)
          ·
            refine ⟨54197835985533655009696013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36131890657022436673130675 54197835985533655009696013)
            ·
              refine ⟨20324188494575120628636005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54197835985533655009696013 20324188494575120628636005)
              ·
                refine ⟨3810785342732835117869251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20324188494575120628636005 3810785342732835117869251)
                ·
                  refine ⟨5716178014099252676803877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3810785342732835117869251 5716178014099252676803877)
                  ·
                    refine ⟨1071783377643609876900727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5716178014099252676803877 1071783377643609876900727)
                    ·
                      rfl

theorem cell23_6261872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 4, 1, 4].length) (baseStart_6261872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261872 prefixEnd_6261872 := by exact prefixLift 6261872
  have htrace : WordTrace (prefixWord ++ tailWord_6261872) baseStart_6261872 baseEnd_6261872 := by
    simpa [prefixWord, tailWord_6261872, baseEnd_6261872] using wordTrace_append hprefix tailTrace_6261872
  have hstable : (prefixWord ++ tailWord_6261872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261872).length < 2 ^ (prefixWord ++ tailWord_6261872).sum := by decide
  have hdescent : baseEnd_6261872 < baseStart_6261872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261919 : List Nat := [1, 1, 2, 6, 3, 1, 1, 2, 6]
def baseStart_6261919 : Nat := 118140960795 + 6261919 * 2 ^ 59
def prefixEnd_6261919 : Nat := 4983230072969 + 3 ^ 40 * 6261919 * 2
def baseEnd_6261919 : Nat := 357263807391287882979385

theorem tailTrace_6261919 : CollatzResearch.WordTrace tailWord_6261919 prefixEnd_6261919 357263807391287882979385 := by
  unfold tailWord_6261919
  simp only [CollatzResearch.WordTrace]
  refine ⟨228390949001144388466996811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152260632667429592311331207 228390949001144388466996811)
  ·
    refine ⟨342586423501716582700495217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228390949001144388466996811 342586423501716582700495217)
    ·
      refine ⟨256939817626287437025371413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342586423501716582700495217 256939817626287437025371413)
      ·
        refine ⟨12044053951232223610564285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 256939817626287437025371413 12044053951232223610564285)
        ·
          refine ⟨4516520231712083853961607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12044053951232223610564285 4516520231712083853961607)
          ·
            refine ⟨6774780347568125780942411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4516520231712083853961607 6774780347568125780942411)
            ·
              refine ⟨10162170521352188671413617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6774780347568125780942411 10162170521352188671413617)
              ·
                refine ⟨7621627891014141503560213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10162170521352188671413617 7621627891014141503560213)
                ·
                  refine ⟨357263807391287882979385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7621627891014141503560213 357263807391287882979385)
                  ·
                    rfl

theorem cell23_6261919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 6].length) (baseStart_6261919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261919 prefixEnd_6261919 := by exact prefixLift 6261919
  have htrace : WordTrace (prefixWord ++ tailWord_6261919) baseStart_6261919 baseEnd_6261919 := by
    simpa [prefixWord, tailWord_6261919, baseEnd_6261919] using wordTrace_append hprefix tailTrace_6261919
  have hstable : (prefixWord ++ tailWord_6261919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261919).length < 2 ^ (prefixWord ++ tailWord_6261919).sum := by decide
  have hdescent : baseEnd_6261919 < baseStart_6261919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6261945 : List Nat := [1, 2, 1, 4, 1, 3, 3, 1, 1, 6]
def baseStart_6261945 : Nat := 118140960795 + 6261945 * 2 ^ 59
def prefixEnd_6261945 : Nat := 4983230072969 + 3 ^ 40 * 6261945 * 2
def baseEnd_6261945 : Nat := 1071795872339535948363115

theorem tailTrace_6261945 : CollatzResearch.WordTrace tailWord_6261945 prefixEnd_6261945 1071795872339535948363115 := by
  unfold tailWord_6261945
  simp only [CollatzResearch.WordTrace]
  refine ⟨228391897299050194907443289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152261264866033463271628859 228391897299050194907443289)
  ·
    refine ⟨171293922974287646180582467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228391897299050194907443289 171293922974287646180582467)
    ·
      refine ⟨256940884461431469270873701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171293922974287646180582467 256940884461431469270873701)
      ·
        refine ⟨48176415836518400488288819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 256940884461431469270873701 48176415836518400488288819)
        ·
          refine ⟨72264623754777600732433229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48176415836518400488288819 72264623754777600732433229)
          ·
            refine ⟨27099233908041600274662461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72264623754777600732433229 27099233908041600274662461)
            ·
              refine ⟨10162212715515600102998423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27099233908041600274662461 10162212715515600102998423)
              ·
                refine ⟨15243319073273400154497635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10162212715515600102998423 15243319073273400154497635)
                ·
                  refine ⟨22864978609910100231746453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15243319073273400154497635 22864978609910100231746453)
                  ·
                    refine ⟨1071795872339535948363115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22864978609910100231746453 1071795872339535948363115)
                    ·
                      rfl

theorem cell23_6261945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 6].length) (baseStart_6261945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6261945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6261945 prefixEnd_6261945 := by exact prefixLift 6261945
  have htrace : WordTrace (prefixWord ++ tailWord_6261945) baseStart_6261945 baseEnd_6261945 := by
    simpa [prefixWord, tailWord_6261945, baseEnd_6261945] using wordTrace_append hprefix tailTrace_6261945
  have hstable : (prefixWord ++ tailWord_6261945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6261945).length < 2 ^ (prefixWord ++ tailWord_6261945).sum := by decide
  have hdescent : baseEnd_6261945 < baseStart_6261945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6261945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262008 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 10]
def baseStart_6262008 : Nat := 118140960795 + 6262008 * 2 ^ 59
def prefixEnd_6262008 : Nat := 4983230072969 + 3 ^ 40 * 6262008 * 2
def baseEnd_6262008 : Nat := 3215419966299841098601555

theorem tailTrace_6262008 : CollatzResearch.WordTrace tailWord_6262008 prefixEnd_6262008 3215419966299841098601555 := by
  unfold tailWord_6262008
  simp only [CollatzResearch.WordTrace]
  refine ⟨114197097548910978333493339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152262796731881304444657785 114197097548910978333493339)
  ·
    refine ⟨171295646323366467500240009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114197097548910978333493339 171295646323366467500240009)
    ·
      refine ⟨128471734742524850625180007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171295646323366467500240009 128471734742524850625180007)
      ·
        refine ⟨192707602113787275937770011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128471734742524850625180007 192707602113787275937770011)
        ·
          refine ⟨289061403170680913906655017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192707602113787275937770011 289061403170680913906655017)
          ·
            refine ⟨216796052378010685429991263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289061403170680913906655017 216796052378010685429991263)
            ·
              refine ⟨325194078567016028144986895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216796052378010685429991263 325194078567016028144986895)
              ·
                refine ⟨487791117850524042217480343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325194078567016028144986895 487791117850524042217480343)
                ·
                  refine ⟨731686676775786063326220515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 487791117850524042217480343 731686676775786063326220515)
                  ·
                    refine ⟨1097530015163679094989330773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 731686676775786063326220515 1097530015163679094989330773)
                    ·
                      refine ⟨3215419966299841098601555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1097530015163679094989330773 3215419966299841098601555)
                      ·
                        rfl

theorem cell23_6262008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_6262008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262008 prefixEnd_6262008 := by exact prefixLift 6262008
  have htrace : WordTrace (prefixWord ++ tailWord_6262008) baseStart_6262008 baseEnd_6262008 := by
    simpa [prefixWord, tailWord_6262008, baseEnd_6262008] using wordTrace_append hprefix tailTrace_6262008
  have hstable : (prefixWord ++ tailWord_6262008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262008).length < 2 ^ (prefixWord ++ tailWord_6262008).sum := by decide
  have hdescent : baseEnd_6262008 < baseStart_6262008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262065 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 9]
def baseStart_6262065 : Nat := 118140960795 + 6262065 * 2 ^ 59
def prefixEnd_6262065 : Nat := 4983230072969 + 3 ^ 40 * 6262065 * 2
def baseEnd_6262065 : Nat := 357272137188571930620977

theorem tailTrace_6262065 : CollatzResearch.WordTrace tailWord_6262065 prefixEnd_6262065 357272137188571930620977 := by
  unfold tailWord_6262065
  simp only [CollatzResearch.WordTrace]
  refine ⟨228396274058615455401811649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152264182705743636934541099 228396274058615455401811649)
  ·
    refine ⟨171297205543961591551358737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228396274058615455401811649 171297205543961591551358737)
    ·
      refine ⟨128472904157971193663519053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171297205543961591551358737 128472904157971193663519053)
      ·
        refine ⟨48177339059239197623819645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128472904157971193663519053 48177339059239197623819645)
        ·
          refine ⟨18066502147214699108932367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48177339059239197623819645 18066502147214699108932367)
          ·
            refine ⟨27099753220822048663398551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18066502147214699108932367 27099753220822048663398551)
            ·
              refine ⟨40649629831233072995097827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27099753220822048663398551 40649629831233072995097827)
              ·
                refine ⟨60974444746849609492646741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40649629831233072995097827 60974444746849609492646741)
                ·
                  refine ⟨357272137188571930620977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60974444746849609492646741 357272137188571930620977)
                  ·
                    rfl

theorem cell23_6262065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 9].length) (baseStart_6262065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262065 prefixEnd_6262065 := by exact prefixLift 6262065
  have htrace : WordTrace (prefixWord ++ tailWord_6262065) baseStart_6262065 baseEnd_6262065 := by
    simpa [prefixWord, tailWord_6262065, baseEnd_6262065] using wordTrace_append hprefix tailTrace_6262065
  have hstable : (prefixWord ++ tailWord_6262065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262065).length < 2 ^ (prefixWord ++ tailWord_6262065).sum := by decide
  have hdescent : baseEnd_6262065 < baseStart_6262065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262092 : List Nat := [2, 2, 1, 3, 2, 2, 1, 2, 2, 3, 3]
def baseStart_6262092 : Nat := 118140960795 + 6262092 * 2 ^ 59
def prefixEnd_6262092 : Nat := 4983230072969 + 3 ^ 40 * 6262092 * 2
def baseEnd_6262092 : Nat := 3215463098674818769951169

theorem tailTrace_6262092 : CollatzResearch.WordTrace tailWord_6262092 prefixEnd_6262092 3215463098674818769951169 := by
  unfold tailWord_6262092
  simp only [CollatzResearch.WordTrace]
  refine ⟨114198629414758819506522265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152264839219678426008696353 114198629414758819506522265)
  ·
    refine ⟨85648972061069114629891699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114198629414758819506522265 85648972061069114629891699)
    ·
      refine ⟨128473458091603671944837549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85648972061069114629891699 128473458091603671944837549)
      ·
        refine ⟨48177546784351376979314081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128473458091603671944837549 48177546784351376979314081)
        ·
          refine ⟨36133160088263532734485561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48177546784351376979314081 36133160088263532734485561)
          ·
            refine ⟨27099870066197649550864171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36133160088263532734485561 27099870066197649550864171)
            ·
              refine ⟨40649805099296474326296257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27099870066197649550864171 40649805099296474326296257)
              ·
                refine ⟨30487353824472355744722193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40649805099296474326296257 30487353824472355744722193)
                ·
                  refine ⟨22865515368354266808541645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30487353824472355744722193 22865515368354266808541645)
                  ·
                    refine ⟨8574568263132850053203117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22865515368354266808541645 8574568263132850053203117)
                    ·
                      refine ⟨3215463098674818769951169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8574568263132850053203117 3215463098674818769951169)
                      ·
                        rfl

theorem cell23_6262092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_6262092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262092 prefixEnd_6262092 := by exact prefixLift 6262092
  have htrace : WordTrace (prefixWord ++ tailWord_6262092) baseStart_6262092 baseEnd_6262092 := by
    simpa [prefixWord, tailWord_6262092, baseEnd_6262092] using wordTrace_append hprefix tailTrace_6262092
  have hstable : (prefixWord ++ tailWord_6262092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262092).length < 2 ^ (prefixWord ++ tailWord_6262092).sum := by decide
  have hdescent : baseEnd_6262092 < baseStart_6262092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262105 : List Nat := [1, 2, 1, 2, 2, 2, 2, 3, 1, 2, 5]
def baseStart_6262105 : Nat := 118140960795 + 6262105 * 2 ^ 59
def prefixEnd_6262105 : Nat := 4983230072969 + 3 ^ 40 * 6262105 * 2
def baseEnd_6262105 : Nat := 3215469773923327219088609

theorem tailTrace_6262105 : CollatzResearch.WordTrace tailWord_6262105 prefixEnd_6262105 3215469773923327219088609 := by
  unfold tailWord_6262105
  simp only [CollatzResearch.WordTrace]
  refine ⟨228397732978470542233267769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152265155318980361488845179 228397732978470542233267769)
  ·
    refine ⟨171298299733852906674950827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228397732978470542233267769 171298299733852906674950827)
    ·
      refine ⟨256947449600779360012426241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171298299733852906674950827 256947449600779360012426241)
      ·
        refine ⟨192710587200584520009319681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256947449600779360012426241 192710587200584520009319681)
        ·
          refine ⟨144532940400438390006989761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192710587200584520009319681 144532940400438390006989761)
          ·
            refine ⟨108399705300328792505242321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144532940400438390006989761 108399705300328792505242321)
            ·
              refine ⟨81299778975246594378931741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108399705300328792505242321 81299778975246594378931741)
              ·
                refine ⟨30487417115717472892099403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81299778975246594378931741 30487417115717472892099403)
                ·
                  refine ⟨45731125673576209338149105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30487417115717472892099403 45731125673576209338149105)
                  ·
                    refine ⟨34298344255182157003611829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45731125673576209338149105 34298344255182157003611829)
                    ·
                      refine ⟨3215469773923327219088609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34298344255182157003611829 3215469773923327219088609)
                      ·
                        rfl

theorem cell23_6262105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_6262105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262105 prefixEnd_6262105 := by exact prefixLift 6262105
  have htrace : WordTrace (prefixWord ++ tailWord_6262105) baseStart_6262105 baseEnd_6262105 := by
    simpa [prefixWord, tailWord_6262105, baseEnd_6262105] using wordTrace_append hprefix tailTrace_6262105
  have hstable : (prefixWord ++ tailWord_6262105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262105).length < 2 ^ (prefixWord ++ tailWord_6262105).sum := by decide
  have hdescent : baseEnd_6262105 < baseStart_6262105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262133 : List Nat := [1, 3, 4, 1, 4, 1, 1, 3, 5]
def baseStart_6262133 : Nat := 118140960795 + 6262133 * 2 ^ 59
def prefixEnd_6262133 : Nat := 4983230072969 + 3 ^ 40 * 6262133 * 2
def baseEnd_6262133 : Nat := 357276016820183678837609

theorem tailTrace_6262133 : CollatzResearch.WordTrace tailWord_6262133 prefixEnd_6262133 357276016820183678837609 := by
  unfold tailWord_6262133
  simp only [CollatzResearch.WordTrace]
  refine ⟨228398754222369103015287053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152265836148246068676858035 228398754222369103015287053)
  ·
    refine ⟨85649532833388413630732645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228398754222369103015287053 85649532833388413630732645)
    ·
      refine ⟨16059287406260327555762371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85649532833388413630732645 16059287406260327555762371)
      ·
        refine ⟨24088931109390491333643557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16059287406260327555762371 24088931109390491333643557)
        ·
          refine ⟨4516674583010717125058167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24088931109390491333643557 4516674583010717125058167)
          ·
            refine ⟨6775011874516075687587251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4516674583010717125058167 6775011874516075687587251)
            ·
              refine ⟨10162517811774113531380877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6775011874516075687587251 10162517811774113531380877)
              ·
                refine ⟨3810944179415292574267829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10162517811774113531380877 3810944179415292574267829)
                ·
                  refine ⟨357276016820183678837609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3810944179415292574267829 357276016820183678837609)
                  ·
                    rfl

theorem cell23_6262133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 3, 5].length) (baseStart_6262133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262133 prefixEnd_6262133 := by exact prefixLift 6262133
  have htrace : WordTrace (prefixWord ++ tailWord_6262133) baseStart_6262133 baseEnd_6262133 := by
    simpa [prefixWord, tailWord_6262133, baseEnd_6262133] using wordTrace_append hprefix tailTrace_6262133
  have hstable : (prefixWord ++ tailWord_6262133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262133).length < 2 ^ (prefixWord ++ tailWord_6262133).sum := by decide
  have hdescent : baseEnd_6262133 < baseStart_6262133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262146 : List Nat := [3, 4, 2, 1, 1, 2, 1, 2, 2, 5]
def baseStart_6262146 : Nat := 118140960795 + 6262146 * 2 ^ 59
def prefixEnd_6262146 : Nat := 4983230072969 + 3 ^ 40 * 6262146 * 2
def baseEnd_6262146 : Nat := 1071830275543387186225307

theorem tailTrace_6262146 : CollatzResearch.WordTrace tailWord_6262146 prefixEnd_6262146 1071830275543387186225307 := by
  unfold tailWord_6262146
  simp only [CollatzResearch.WordTrace]
  refine ⟨57099807092830501558877573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152266152247548004157006861 57099807092830501558877573)
  ·
    refine ⟨10706213829905719042289545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57099807092830501558877573 10706213829905719042289545)
    ·
      refine ⟨8029660372429289281717159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10706213829905719042289545 8029660372429289281717159)
      ·
        refine ⟨12044490558643933922575739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8029660372429289281717159 12044490558643933922575739)
        ·
          refine ⟨18066735837965900883863609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12044490558643933922575739 18066735837965900883863609)
          ·
            refine ⟨13550051878474425662897707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18066735837965900883863609 13550051878474425662897707)
            ·
              refine ⟨20325077817711638494346561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13550051878474425662897707 20325077817711638494346561)
              ·
                refine ⟨15243808363283728870759921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20325077817711638494346561 15243808363283728870759921)
                ·
                  refine ⟨11432856272462796653069941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15243808363283728870759921 11432856272462796653069941)
                  ·
                    refine ⟨1071830275543387186225307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11432856272462796653069941 1071830275543387186225307)
                    ·
                      rfl

theorem cell23_6262146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_6262146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262146 prefixEnd_6262146 := by exact prefixLift 6262146
  have htrace : WordTrace (prefixWord ++ tailWord_6262146) baseStart_6262146 baseEnd_6262146 := by
    simpa [prefixWord, tailWord_6262146, baseEnd_6262146] using wordTrace_append hprefix tailTrace_6262146
  have hstable : (prefixWord ++ tailWord_6262146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262146).length < 2 ^ (prefixWord ++ tailWord_6262146).sum := by decide
  have hdescent : baseEnd_6262146 < baseStart_6262146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262155 : List Nat := [1, 1, 1, 1, 4, 3, 1, 3, 8]
def baseStart_6262155 : Nat := 118140960795 + 6262155 * 2 ^ 59
def prefixEnd_6262155 : Nat := 4983230072969 + 3 ^ 40 * 6262155 * 2
def baseEnd_6262155 : Nat := 357277271995116891495931

theorem tailTrace_6262155 : CollatzResearch.WordTrace tailWord_6262155 prefixEnd_6262155 357277271995116891495931 := by
  unfold tailWord_6262155
  simp only [CollatzResearch.WordTrace]
  refine ⟨228399556628289400772587919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152266371085526267181725279 228399556628289400772587919)
  ·
    refine ⟨342599334942434101158881879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228399556628289400772587919 342599334942434101158881879)
    ·
      refine ⟨513899002413651151738322819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342599334942434101158881879 513899002413651151738322819)
      ·
        refine ⟨770848503620476727607484229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513899002413651151738322819 770848503620476727607484229)
        ·
          refine ⟨144534094428839386426403293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 770848503620476727607484229 144534094428839386426403293)
          ·
            refine ⟨54200285410814769909901235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144534094428839386426403293 54200285410814769909901235)
            ·
              refine ⟨81300428116222154864851853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54200285410814769909901235 81300428116222154864851853)
              ·
                refine ⟨30487660543583308074319445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81300428116222154864851853 30487660543583308074319445)
                ·
                  refine ⟨357277271995116891495931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30487660543583308074319445 357277271995116891495931)
                  ·
                    rfl

theorem cell23_6262155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 8].length) (baseStart_6262155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262155 prefixEnd_6262155 := by exact prefixLift 6262155
  have htrace : WordTrace (prefixWord ++ tailWord_6262155) baseStart_6262155 baseEnd_6262155 := by
    simpa [prefixWord, tailWord_6262155, baseEnd_6262155] using wordTrace_append hprefix tailTrace_6262155
  have hstable : (prefixWord ++ tailWord_6262155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262155).length < 2 ^ (prefixWord ++ tailWord_6262155).sum := by decide
  have hdescent : baseEnd_6262155 < baseStart_6262155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262195 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 7]
def baseStart_6262195 : Nat := 118140960795 + 6262195 * 2 ^ 59
def prefixEnd_6262195 : Nat := 4983230072969 + 3 ^ 40 * 6262195 * 2
def baseEnd_6262195 : Nat := 3215515987182231866963195

theorem tailTrace_6262195 : CollatzResearch.WordTrace tailWord_6262195 prefixEnd_6262195 3215515987182231866963195 := by
  unfold tailWord_6262195
  simp only [CollatzResearch.WordTrace]
  refine ⟨228401015548144487604044039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152267343698762991736029359 228401015548144487604044039)
  ·
    refine ⟨342601523322216731406066059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228401015548144487604044039 342601523322216731406066059)
    ·
      refine ⟨513902284983325097109099089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342601523322216731406066059 513902284983325097109099089)
      ·
        refine ⟨385426713737493822831824317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 513902284983325097109099089 385426713737493822831824317)
        ·
          refine ⟨144535017651560183561934119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 385426713737493822831824317 144535017651560183561934119)
          ·
            refine ⟨216802526477340275342901179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144535017651560183561934119 216802526477340275342901179)
            ·
              refine ⟨325203789716010413014351769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216802526477340275342901179 325203789716010413014351769)
              ·
                refine ⟨243902842287007809760763827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 325203789716010413014351769 243902842287007809760763827)
                ·
                  refine ⟨365854263430511714641145741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243902842287007809760763827 365854263430511714641145741)
                  ·
                    refine ⟨137195348786441892990429653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 365854263430511714641145741 137195348786441892990429653)
                    ·
                      refine ⟨3215515987182231866963195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 137195348786441892990429653 3215515987182231866963195)
                      ·
                        rfl

theorem cell23_6262195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 7].length) (baseStart_6262195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262195 prefixEnd_6262195 := by exact prefixLift 6262195
  have htrace : WordTrace (prefixWord ++ tailWord_6262195) baseStart_6262195 baseEnd_6262195 := by
    simpa [prefixWord, tailWord_6262195, baseEnd_6262195] using wordTrace_append hprefix tailTrace_6262195
  have hstable : (prefixWord ++ tailWord_6262195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262195).length < 2 ^ (prefixWord ++ tailWord_6262195).sum := by decide
  have hdescent : baseEnd_6262195 < baseStart_6262195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262232 : List Nat := [2, 1, 2, 2, 2, 1, 3, 3, 1, 6]
def baseStart_6262232 : Nat := 118140960795 + 6262232 * 2 ^ 59
def prefixEnd_6262232 : Nat := 4983230072969 + 3 ^ 40 * 6262232 * 2
def baseEnd_6262232 : Nat := 1071844995322149407400175

theorem tailTrace_6262232 : CollatzResearch.WordTrace tailWord_6262232 prefixEnd_6262232 1071844995322149407400175 := by
  unfold tailWord_6262232
  simp only [CollatzResearch.WordTrace]
  refine ⟨114201182524505221461570475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152268243366006961948760633 114201182524505221461570475)
  ·
    refine ⟨171301773786757832192355713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114201182524505221461570475 171301773786757832192355713)
    ·
      refine ⟨128476330340068374144266785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171301773786757832192355713 128476330340068374144266785)
      ·
        refine ⟨96357247755051280608200089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128476330340068374144266785 96357247755051280608200089)
        ·
          refine ⟨72267935816288460456150067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96357247755051280608200089 72267935816288460456150067)
          ·
            refine ⟨108401903724432690684225101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72267935816288460456150067 108401903724432690684225101)
            ·
              refine ⟨40650713896662259006584413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108401903724432690684225101 40650713896662259006584413)
              ·
                refine ⟨15244017711248347127469155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40650713896662259006584413 15244017711248347127469155)
                ·
                  refine ⟨22866026566872520691203733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15244017711248347127469155 22866026566872520691203733)
                  ·
                    refine ⟨1071844995322149407400175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22866026566872520691203733 1071844995322149407400175)
                    ·
                      rfl

theorem cell23_6262232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 1, 6].length) (baseStart_6262232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262232 prefixEnd_6262232 := by exact prefixLift 6262232
  have htrace : WordTrace (prefixWord ++ tailWord_6262232) baseStart_6262232 baseEnd_6262232 := by
    simpa [prefixWord, tailWord_6262232, baseEnd_6262232] using wordTrace_append hprefix tailTrace_6262232
  have hstable : (prefixWord ++ tailWord_6262232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262232).length < 2 ^ (prefixWord ++ tailWord_6262232).sum := by decide
  have hdescent : baseEnd_6262232 < baseStart_6262232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262239 : List Nat := [1, 1, 2, 3, 3, 1, 2, 4, 1, 1, 4]
def baseStart_6262239 : Nat := 118140960795 + 6262239 * 2 ^ 59
def prefixEnd_6262239 : Nat := 4983230072969 + 3 ^ 40 * 6262239 * 2
def baseEnd_6262239 : Nat := 3215538580331029694812993

theorem tailTrace_6262239 : CollatzResearch.WordTrace tailWord_6262239 prefixEnd_6262239 3215538580331029694812993 := by
  unfold tailWord_6262239
  simp only [CollatzResearch.WordTrace]
  refine ⟨228402620359985083118645771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152268413573323388745763847 228402620359985083118645771)
  ·
    refine ⟨342603930539977624677968657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228402620359985083118645771 342603930539977624677968657)
    ·
      refine ⟨256952947904983218508476493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342603930539977624677968657 256952947904983218508476493)
      ·
        refine ⟨96357355464368706940678685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256952947904983218508476493 96357355464368706940678685)
        ·
          refine ⟨36134008299138265102754507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96357355464368706940678685 36134008299138265102754507)
          ·
            refine ⟨54201012448707397654131761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36134008299138265102754507 54201012448707397654131761)
            ·
              refine ⟨40650759336530548240598821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54201012448707397654131761 40650759336530548240598821)
              ·
                refine ⟨7622017375599477795112279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40650759336530548240598821 7622017375599477795112279)
                ·
                  refine ⟨11433026063399216692668419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7622017375599477795112279 11433026063399216692668419)
                  ·
                    refine ⟨17149539095098825039002629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11433026063399216692668419 17149539095098825039002629)
                    ·
                      refine ⟨3215538580331029694812993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17149539095098825039002629 3215538580331029694812993)
                      ·
                        rfl

theorem cell23_6262239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_6262239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262239 prefixEnd_6262239 := by exact prefixLift 6262239
  have htrace : WordTrace (prefixWord ++ tailWord_6262239) baseStart_6262239 baseEnd_6262239 := by
    simpa [prefixWord, tailWord_6262239, baseEnd_6262239] using wordTrace_append hprefix tailTrace_6262239
  have hstable : (prefixWord ++ tailWord_6262239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262239).length < 2 ^ (prefixWord ++ tailWord_6262239).sum := by decide
  have hdescent : baseEnd_6262239 < baseStart_6262239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262243 : List Nat := [1, 1, 1, 6, 2, 3, 1, 1, 2, 3, 2]
def baseStart_6262243 : Nat := 118140960795 + 6262243 * 2 ^ 59
def prefixEnd_6262243 : Nat := 4983230072969 + 3 ^ 40 * 6262243 * 2
def baseEnd_6262243 : Nat := 3215540634253647679162975

theorem tailTrace_6262243 : CollatzResearch.WordTrace tailWord_6262243 prefixEnd_6262243 3215540634253647679162975 := by
  unfold tailWord_6262243
  simp only [CollatzResearch.WordTrace]
  refine ⟨228402766251970591801791383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152268510834647061201194255 228402766251970591801791383)
  ·
    refine ⟨342604149377955887702687075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228402766251970591801791383 342604149377955887702687075)
    ·
      refine ⟨513906224066933831554030613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342604149377955887702687075 513906224066933831554030613)
      ·
        refine ⟨24089354253137523354095185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 513906224066933831554030613 24089354253137523354095185)
        ·
          refine ⟨18067015689853142515571389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24089354253137523354095185 18067015689853142515571389)
          ·
            refine ⟨6775130883694928443339271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18067015689853142515571389 6775130883694928443339271)
            ·
              refine ⟨10162696325542392665008907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6775130883694928443339271 10162696325542392665008907)
              ·
                refine ⟨15244044488313588997513361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10162696325542392665008907 15244044488313588997513361)
                ·
                  refine ⟨11433033366235191748135021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15244044488313588997513361 11433033366235191748135021)
                  ·
                    refine ⟨4287387512338196905550633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11433033366235191748135021 4287387512338196905550633)
                    ·
                      refine ⟨3215540634253647679162975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4287387512338196905550633 3215540634253647679162975)
                      ·
                        rfl

theorem cell23_6262243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_6262243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262243 prefixEnd_6262243 := by exact prefixLift 6262243
  have htrace : WordTrace (prefixWord ++ tailWord_6262243) baseStart_6262243 baseEnd_6262243 := by
    simpa [prefixWord, tailWord_6262243, baseEnd_6262243] using wordTrace_append hprefix tailTrace_6262243
  have hstable : (prefixWord ++ tailWord_6262243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262243).length < 2 ^ (prefixWord ++ tailWord_6262243).sum := by decide
  have hdescent : baseEnd_6262243 < baseStart_6262243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262250 : List Nat := [3, 1, 3, 1, 4, 1, 2, 3, 1, 1, 3]
def baseStart_6262250 : Nat := 118140960795 + 6262250 * 2 ^ 59
def prefixEnd_6262250 : Nat := 4983230072969 + 3 ^ 40 * 6262250 * 2
def baseEnd_6262250 : Nat := 3215544228618229151775443

theorem tailTrace_6262250 : CollatzResearch.WordTrace tailWord_6262250 prefixEnd_6262250 3215544228618229151775443 := by
  unfold tailWord_6262250
  simp only [CollatzResearch.WordTrace]
  refine ⟨57100755390736307999324051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152268681041963487998197469 57100755390736307999324051)
  ·
    refine ⟨85651133086104461998986077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57100755390736307999324051 85651133086104461998986077)
    ·
      refine ⟨32119174907289173249619779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85651133086104461998986077 32119174907289173249619779)
      ·
        refine ⟨48178762360933759874429669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32119174907289173249619779 48178762360933759874429669)
        ·
          refine ⟨9033517942675079976455563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48178762360933759874429669 9033517942675079976455563)
          ·
            refine ⟨13550276914012619964683345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9033517942675079976455563 13550276914012619964683345)
            ·
              refine ⟨10162707685509464973512509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13550276914012619964683345 10162707685509464973512509)
              ·
                refine ⟨3811015382066049365067191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10162707685509464973512509 3811015382066049365067191)
                ·
                  refine ⟨5716523073099074047600787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3811015382066049365067191 5716523073099074047600787)
                  ·
                    refine ⟨8574784609648611071401181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5716523073099074047600787 8574784609648611071401181)
                    ·
                      refine ⟨3215544228618229151775443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8574784609648611071401181 3215544228618229151775443)
                      ·
                        rfl

theorem cell23_6262250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_6262250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262250 prefixEnd_6262250 := by exact prefixLift 6262250
  have htrace : WordTrace (prefixWord ++ tailWord_6262250) baseStart_6262250 baseEnd_6262250 := by
    simpa [prefixWord, tailWord_6262250, baseEnd_6262250] using wordTrace_append hprefix tailTrace_6262250
  have hstable : (prefixWord ++ tailWord_6262250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262250).length < 2 ^ (prefixWord ++ tailWord_6262250).sum := by decide
  have hdescent : baseEnd_6262250 < baseStart_6262250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262252 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 4]
def baseStart_6262252 : Nat := 118140960795 + 6262252 * 2 ^ 59
def prefixEnd_6262252 : Nat := 4983230072969 + 3 ^ 40 * 6262252 * 2
def baseEnd_6262252 : Nat := 3215545255579538143950433

theorem tailTrace_6262252 : CollatzResearch.WordTrace tailWord_6262252 prefixEnd_6262252 3215545255579538143950433 := by
  unfold tailWord_6262252
  simp only [CollatzResearch.WordTrace]
  refine ⟨114201547254468993169434505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152268729672625324225912673 114201547254468993169434505)
  ·
    refine ⟨85651160440851744877075879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114201547254468993169434505 85651160440851744877075879)
    ·
      refine ⟨128476740661277617315613819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85651160440851744877075879 128476740661277617315613819)
      ·
        refine ⟨192715110991916425973420729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128476740661277617315613819 192715110991916425973420729)
        ·
          refine ⟨144536333243937319480065547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192715110991916425973420729 144536333243937319480065547)
          ·
            refine ⟨216804499865905979220098321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144536333243937319480065547 216804499865905979220098321)
            ·
              refine ⟨162603374899429484415073741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216804499865905979220098321 162603374899429484415073741)
              ·
                refine ⟨60976265587286056655652653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162603374899429484415073741 60976265587286056655652653)
                ·
                  refine ⟨22866099595232271245869745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60976265587286056655652653 22866099595232271245869745)
                  ·
                    refine ⟨17149574696424203434402309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22866099595232271245869745 17149574696424203434402309)
                    ·
                      refine ⟨3215545255579538143950433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17149574696424203434402309 3215545255579538143950433)
                      ·
                        rfl

theorem cell23_6262252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_6262252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262252 prefixEnd_6262252 := by exact prefixLift 6262252
  have htrace : WordTrace (prefixWord ++ tailWord_6262252) baseStart_6262252 baseEnd_6262252 := by
    simpa [prefixWord, tailWord_6262252, baseEnd_6262252] using wordTrace_append hprefix tailTrace_6262252
  have hstable : (prefixWord ++ tailWord_6262252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262252).length < 2 ^ (prefixWord ++ tailWord_6262252).sum := by decide
  have hdescent : baseEnd_6262252 < baseStart_6262252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262256 : List Nat := [2, 1, 1, 1, 3, 4, 4, 1, 1, 1, 4]
def baseStart_6262256 : Nat := 118140960795 + 6262256 * 2 ^ 59
def prefixEnd_6262256 : Nat := 4983230072969 + 3 ^ 40 * 6262256 * 2
def baseEnd_6262256 : Nat := 3215547309502156128300415

theorem tailTrace_6262256 : CollatzResearch.WordTrace tailWord_6262256 prefixEnd_6262256 3215547309502156128300415 := by
  unfold tailWord_6262256
  simp only [CollatzResearch.WordTrace]
  refine ⟨114201620200461747511007311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152268826933948996681343081 114201620200461747511007311)
  ·
    refine ⟨171302430300692621266510967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114201620200461747511007311 171302430300692621266510967)
    ·
      refine ⟨256953645451038931899766451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171302430300692621266510967 256953645451038931899766451)
      ·
        refine ⟨385430468176558397849649677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256953645451038931899766451 385430468176558397849649677)
        ·
          refine ⟨144536425566209399193618629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 385430468176558397849649677 144536425566209399193618629)
          ·
            refine ⟨27100579793664262348803493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144536425566209399193618629 27100579793664262348803493)
            ·
              refine ⟨5081358711312049190400655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27100579793664262348803493 5081358711312049190400655)
              ·
                refine ⟨7622038066968073785600983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5081358711312049190400655 7622038066968073785600983)
                ·
                  refine ⟨11433057100452110678401475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7622038066968073785600983 11433057100452110678401475)
                  ·
                    refine ⟨17149585650678166017602213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11433057100452110678401475 17149585650678166017602213)
                    ·
                      refine ⟨3215547309502156128300415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17149585650678166017602213 3215547309502156128300415)
                      ·
                        rfl

theorem cell23_6262256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 1, 1, 4].length) (baseStart_6262256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262256 prefixEnd_6262256 := by exact prefixLift 6262256
  have htrace : WordTrace (prefixWord ++ tailWord_6262256) baseStart_6262256 baseEnd_6262256 := by
    simpa [prefixWord, tailWord_6262256, baseEnd_6262256] using wordTrace_append hprefix tailTrace_6262256
  have hstable : (prefixWord ++ tailWord_6262256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262256).length < 2 ^ (prefixWord ++ tailWord_6262256).sum := by decide
  have hdescent : baseEnd_6262256 < baseStart_6262256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262272 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 3]
def baseStart_6262272 : Nat := 118140960795 + 6262272 * 2 ^ 59
def prefixEnd_6262272 : Nat := 4983230072969 + 3 ^ 40 * 6262272 * 2
def baseEnd_6262272 : Nat := 3215555525192628065700341

theorem tailTrace_6262272 : CollatzResearch.WordTrace tailWord_6262272 prefixEnd_6262272 3215555525192628065700341 := by
  unfold tailWord_6262272
  simp only [CollatzResearch.WordTrace]
  refine ⟨114201911984432764877298535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152269215979243686503064713 114201911984432764877298535)
  ·
    refine ⟨171302867976649147315947803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114201911984432764877298535 171302867976649147315947803)
    ·
      refine ⟨256954301964973720973921705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171302867976649147315947803 256954301964973720973921705)
      ·
        refine ⟨192715726473730290730441279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256954301964973720973921705 192715726473730290730441279)
        ·
          refine ⟨289073589710595436095661919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192715726473730290730441279 289073589710595436095661919)
          ·
            refine ⟨433610384565893154143492879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289073589710595436095661919 433610384565893154143492879)
            ·
              refine ⟨650415576848839731215239319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433610384565893154143492879 650415576848839731215239319)
              ·
                refine ⟨975623365273259596822858979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 650415576848839731215239319 975623365273259596822858979)
                ·
                  refine ⟨1463435047909889395234288469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 975623365273259596822858979 1463435047909889395234288469)
                  ·
                    refine ⟨8574814733847008175200909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1463435047909889395234288469 8574814733847008175200909)
                    ·
                      refine ⟨3215555525192628065700341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8574814733847008175200909 3215555525192628065700341)
                      ·
                        rfl

theorem cell23_6262272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 3].length) (baseStart_6262272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262272 prefixEnd_6262272 := by exact prefixLift 6262272
  have htrace : WordTrace (prefixWord ++ tailWord_6262272) baseStart_6262272 baseEnd_6262272 := by
    simpa [prefixWord, tailWord_6262272, baseEnd_6262272] using wordTrace_append hprefix tailTrace_6262272
  have hstable : (prefixWord ++ tailWord_6262272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262272).length < 2 ^ (prefixWord ++ tailWord_6262272).sum := by decide
  have hdescent : baseEnd_6262272 < baseStart_6262272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262276 : List Nat := [2, 3, 2, 3, 2, 1, 1, 2, 1, 1, 5]
def baseStart_6262276 : Nat := 118140960795 + 6262276 * 2 ^ 59
def prefixEnd_6262276 : Nat := 4983230072969 + 3 ^ 40 * 6262276 * 2
def baseEnd_6262276 : Nat := 3215557579115246050050323

theorem tailTrace_6262276 : CollatzResearch.WordTrace tailWord_6262276 prefixEnd_6262276 3215557579115246050050323 := by
  unfold tailWord_6262276
  simp only [CollatzResearch.WordTrace]
  refine ⟨114201984930425519218871341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152269313240567358958495121 114201984930425519218871341)
  ·
    refine ⟨42825744348909569707076753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114201984930425519218871341 42825744348909569707076753)
    ·
      refine ⟨32119308261682177280307565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42825744348909569707076753 32119308261682177280307565)
      ·
        refine ⟨12044740598130816480115337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32119308261682177280307565 12044740598130816480115337)
        ·
          refine ⟨9033555448598112360086503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12044740598130816480115337 9033555448598112360086503)
          ·
            refine ⟨13550333172897168540129755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9033555448598112360086503 13550333172897168540129755)
            ·
              refine ⟨20325499759345752810194633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13550333172897168540129755 20325499759345752810194633)
              ·
                refine ⟨15244124819509314607645975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20325499759345752810194633 15244124819509314607645975)
                ·
                  refine ⟨22866187229263971911468963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15244124819509314607645975 22866187229263971911468963)
                  ·
                    refine ⟨34299280843895957867203445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22866187229263971911468963 34299280843895957867203445)
                    ·
                      refine ⟨3215557579115246050050323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34299280843895957867203445 3215557579115246050050323)
                      ·
                        rfl

theorem cell23_6262276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_6262276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262276 prefixEnd_6262276 := by exact prefixLift 6262276
  have htrace : WordTrace (prefixWord ++ tailWord_6262276) baseStart_6262276 baseEnd_6262276 := by
    simpa [prefixWord, tailWord_6262276, baseEnd_6262276] using wordTrace_append hprefix tailTrace_6262276
  have hstable : (prefixWord ++ tailWord_6262276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262276).length < 2 ^ (prefixWord ++ tailWord_6262276).sum := by decide
  have hdescent : baseEnd_6262276 < baseStart_6262276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262283 : List Nat := [1, 1, 1, 1, 8, 1, 3, 1, 2, 4]
def baseStart_6262283 : Nat := 118140960795 + 6262283 * 2 ^ 59
def prefixEnd_6262283 : Nat := 4983230072969 + 3 ^ 40 * 6262283 * 2
def baseEnd_6262283 : Nat := 1071853724493275840887597

theorem tailTrace_6262283 : CollatzResearch.WordTrace tailWord_6262283 prefixEnd_6262283 1071853724493275840887597 := by
  unfold tailWord_6262283
  simp only [CollatzResearch.WordTrace]
  refine ⟨228404225171825678633247503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152269483447883785755498335 228404225171825678633247503)
  ·
    refine ⟨342606337757738517949871255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228404225171825678633247503 342606337757738517949871255)
    ·
      refine ⟨513909506636607776924806883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342606337757738517949871255 513909506636607776924806883)
      ·
        refine ⟨770864259954911665387210325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513909506636607776924806883 770864259954911665387210325)
        ·
          refine ⟨9033565546346621078756371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 770864259954911665387210325 9033565546346621078756371)
          ·
            refine ⟨13550348319519931618134557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9033565546346621078756371 13550348319519931618134557)
            ·
              refine ⟨5081380619819974356800459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13550348319519931618134557 5081380619819974356800459)
              ·
                refine ⟨7622070929729961535200689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5081380619819974356800459 7622070929729961535200689)
                ·
                  refine ⟨5716553197297471151400517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7622070929729961535200689 5716553197297471151400517)
                  ·
                    refine ⟨1071853724493275840887597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5716553197297471151400517 1071853724493275840887597)
                    ·
                      rfl

theorem cell23_6262283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 2, 4].length) (baseStart_6262283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262283 prefixEnd_6262283 := by exact prefixLift 6262283
  have htrace : WordTrace (prefixWord ++ tailWord_6262283) baseStart_6262283 baseEnd_6262283 := by
    simpa [prefixWord, tailWord_6262283, baseEnd_6262283] using wordTrace_append hprefix tailTrace_6262283
  have hstable : (prefixWord ++ tailWord_6262283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262283).length < 2 ^ (prefixWord ++ tailWord_6262283).sum := by decide
  have hdescent : baseEnd_6262283 < baseStart_6262283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262296 : List Nat := [2, 1, 2, 3, 4, 2, 2, 7]
def baseStart_6262296 : Nat := 118140960795 + 6262296 * 2 ^ 59
def prefixEnd_6262296 : Nat := 4983230072969 + 3 ^ 40 * 6262296 * 2
def baseEnd_6262296 : Nat := 119095105508456887844453

theorem tailTrace_6262296 : CollatzResearch.WordTrace tailWord_6262296 prefixEnd_6262296 119095105508456887844453 := by
  unfold tailWord_6262296
  simp only [CollatzResearch.WordTrace]
  refine ⟨114202349660389290926735371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152269799547185721235647161 114202349660389290926735371)
  ·
    refine ⟨171303524490583936390103057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114202349660389290926735371 171303524490583936390103057)
    ·
      refine ⟨128477643367937952292577293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171303524490583936390103057 128477643367937952292577293)
      ·
        refine ⟨48179116262976732109716485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128477643367937952292577293 48179116262976732109716485)
        ·
          refine ⟨9033584299308137270571841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48179116262976732109716485 9033584299308137270571841)
          ·
            refine ⟨6775188224481102952928881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9033584299308137270571841 6775188224481102952928881)
            ·
              refine ⟨5081391168360827214696661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6775188224481102952928881 5081391168360827214696661)
              ·
                refine ⟨119095105508456887844453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5081391168360827214696661 119095105508456887844453)
                ·
                  rfl

theorem cell23_6262296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 7].length) (baseStart_6262296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262296 prefixEnd_6262296 := by exact prefixLift 6262296
  have htrace : WordTrace (prefixWord ++ tailWord_6262296) baseStart_6262296 baseEnd_6262296 := by
    simpa [prefixWord, tailWord_6262296, baseEnd_6262296] using wordTrace_append hprefix tailTrace_6262296
  have hstable : (prefixWord ++ tailWord_6262296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262296).length < 2 ^ (prefixWord ++ tailWord_6262296).sum := by decide
  have hdescent : baseEnd_6262296 < baseStart_6262296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262306 : List Nat := [3, 3, 1, 1, 1, 1, 3, 2, 4, 1, 3]
def baseStart_6262306 : Nat := 118140960795 + 6262306 * 2 ^ 59
def prefixEnd_6262306 : Nat := 4983230072969 + 3 ^ 40 * 6262306 * 2
def baseEnd_6262306 : Nat := 3215572983534880932675185

theorem tailTrace_6262306 : CollatzResearch.WordTrace tailWord_6262306 prefixEnd_6262306 3215572983534880932675185 := by
  unfold tailWord_6262306
  simp only [CollatzResearch.WordTrace]
  refine ⟨57101266012685588390333693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152270042700494902374223181 57101266012685588390333693)
  ·
    refine ⟨21412974754757095646375135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57101266012685588390333693 21412974754757095646375135)
    ·
      refine ⟨32119462132135643469562703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21412974754757095646375135 32119462132135643469562703)
      ·
        refine ⟨48179193198203465204344055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32119462132135643469562703 48179193198203465204344055)
        ·
          refine ⟨72268789797305197806516083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48179193198203465204344055 72268789797305197806516083)
          ·
            refine ⟨108403184695957796709774125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72268789797305197806516083 108403184695957796709774125)
            ·
              refine ⟨40651194260984173766165297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108403184695957796709774125 40651194260984173766165297)
              ·
                refine ⟨30488395695738130324623973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40651194260984173766165297 30488395695738130324623973)
                ·
                  refine ⟨5716574192950899435866995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30488395695738130324623973 5716574192950899435866995)
                  ·
                    refine ⟨8574861289426349153800493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5716574192950899435866995 8574861289426349153800493)
                    ·
                      refine ⟨3215572983534880932675185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8574861289426349153800493 3215572983534880932675185)
                      ·
                        rfl

theorem cell23_6262306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_6262306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262306 prefixEnd_6262306 := by exact prefixLift 6262306
  have htrace : WordTrace (prefixWord ++ tailWord_6262306) baseStart_6262306 baseEnd_6262306 := by
    simpa [prefixWord, tailWord_6262306, baseEnd_6262306] using wordTrace_append hprefix tailTrace_6262306
  have hstable : (prefixWord ++ tailWord_6262306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262306).length < 2 ^ (prefixWord ++ tailWord_6262306).sum := by decide
  have hdescent : baseEnd_6262306 < baseStart_6262306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262307 : List Nat := [1, 1, 1, 4, 5, 2, 1, 3, 1, 2, 2]
def baseStart_6262307 : Nat := 118140960795 + 6262307 * 2 ^ 59
def prefixEnd_6262307 : Nat := 4983230072969 + 3 ^ 40 * 6262307 * 2
def baseEnd_6262307 : Nat := 3215573497015535428762681

theorem tailTrace_6262307 : CollatzResearch.WordTrace tailWord_6262307 prefixEnd_6262307 3215573497015535428762681 := by
  unfold tailWord_6262307
  simp only [CollatzResearch.WordTrace]
  refine ⟨228405100523738730732121175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152270067015825820488080783 228405100523738730732121175)
  ·
    refine ⟨342607650785608096098181763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228405100523738730732121175 342607650785608096098181763)
    ·
      refine ⟨513911476178412144147272645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342607650785608096098181763 513911476178412144147272645)
      ·
        refine ⟨96358401783452277027613621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 513911476178412144147272645 96358401783452277027613621)
        ·
          refine ⟨9033600167198650971338777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96358401783452277027613621 9033600167198650971338777)
          ·
            refine ⟨6775200125398988228504083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9033600167198650971338777 6775200125398988228504083)
            ·
              refine ⟨10162800188098482342756125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6775200125398988228504083 10162800188098482342756125)
              ·
                refine ⟨3811050070536930878533547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10162800188098482342756125 3811050070536930878533547)
                ·
                  refine ⟨5716575105805396317800321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3811050070536930878533547 5716575105805396317800321)
                  ·
                    refine ⟨4287431329354047238350241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5716575105805396317800321 4287431329354047238350241)
                    ·
                      refine ⟨3215573497015535428762681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4287431329354047238350241 3215573497015535428762681)
                      ·
                        rfl

theorem cell23_6262307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 3, 1, 2, 2].length) (baseStart_6262307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262307 prefixEnd_6262307 := by exact prefixLift 6262307
  have htrace : WordTrace (prefixWord ++ tailWord_6262307) baseStart_6262307 baseEnd_6262307 := by
    simpa [prefixWord, tailWord_6262307, baseEnd_6262307] using wordTrace_append hprefix tailTrace_6262307
  have hstable : (prefixWord ++ tailWord_6262307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262307).length < 2 ^ (prefixWord ++ tailWord_6262307).sum := by decide
  have hdescent : baseEnd_6262307 < baseStart_6262307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262346 : List Nat := [3, 1, 2, 1, 1, 3, 2, 3, 1, 4, 2]
def baseStart_6262346 : Nat := 118140960795 + 6262346 * 2 ^ 59
def prefixEnd_6262346 : Nat := 4983230072969 + 3 ^ 40 * 6262346 * 2
def baseEnd_6262346 : Nat := 3215593522761060776175001

theorem tailTrace_6262346 : CollatzResearch.WordTrace tailWord_6262346 prefixEnd_6262346 3215593522761060776175001 := by
  unfold tailWord_6262346
  simp only [CollatzResearch.WordTrace]
  refine ⟨57101630742649360098197723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152271015313731626928527261 57101630742649360098197723)
  ·
    refine ⟨85652446113974040147296585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57101630742649360098197723 85652446113974040147296585)
    ·
      refine ⟨64239334585480530110472439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85652446113974040147296585 64239334585480530110472439)
      ·
        refine ⟨96359001878220795165708659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64239334585480530110472439 96359001878220795165708659)
        ·
          refine ⟨144538502817331192748562989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96359001878220795165708659 144538502817331192748562989)
          ·
            refine ⟨54201938556499197280711121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144538502817331192748562989 54201938556499197280711121)
            ·
              refine ⟨40651453917374397960533341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54201938556499197280711121 40651453917374397960533341)
              ·
                refine ⟨15244295219015399235200003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40651453917374397960533341 15244295219015399235200003)
                ·
                  refine ⟨22866442828523098852800005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15244295219015399235200003 22866442828523098852800005)
                  ·
                    refine ⟨4287458030348081034900001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22866442828523098852800005 4287458030348081034900001)
                    ·
                      refine ⟨3215593522761060776175001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4287458030348081034900001 3215593522761060776175001)
                      ·
                        rfl

theorem cell23_6262346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 1, 4, 2].length) (baseStart_6262346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262346 prefixEnd_6262346 := by exact prefixLift 6262346
  have htrace : WordTrace (prefixWord ++ tailWord_6262346) baseStart_6262346 baseEnd_6262346 := by
    simpa [prefixWord, tailWord_6262346, baseEnd_6262346] using wordTrace_append hprefix tailTrace_6262346
  have hstable : (prefixWord ++ tailWord_6262346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262346).length < 2 ^ (prefixWord ++ tailWord_6262346).sum := by decide
  have hdescent : baseEnd_6262346 < baseStart_6262346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262352 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 9]
def baseStart_6262352 : Nat := 118140960795 + 6262352 * 2 ^ 59
def prefixEnd_6262352 : Nat := 4983230072969 + 3 ^ 40 * 6262352 * 2
def baseEnd_6262352 : Nat := 357288511516109750299997

theorem tailTrace_6262352 : CollatzResearch.WordTrace tailWord_6262352 prefixEnd_6262352 357288511516109750299997 := by
  unfold tailWord_6262352
  simp only [CollatzResearch.WordTrace]
  refine ⟨114203370904287851708754655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152271161205717135611672873 114203370904287851708754655)
  ·
    refine ⟨171305056356431777563131983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114203370904287851708754655 171305056356431777563131983)
    ·
      refine ⟨256957584534647666344697975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171305056356431777563131983 256957584534647666344697975)
      ·
        refine ⟨385436376801971499517046963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256957584534647666344697975 385436376801971499517046963)
        ·
          refine ⟨578154565202957249275570445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385436376801971499517046963 578154565202957249275570445)
          ·
            refine ⟨216807961951108968478338917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 578154565202957249275570445 216807961951108968478338917)
            ·
              refine ⟨40651492865832931589688547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 216807961951108968478338917 40651492865832931589688547)
              ·
                refine ⟨60977239298749397384532821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40651492865832931589688547 60977239298749397384532821)
                ·
                  refine ⟨357288511516109750299997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60977239298749397384532821 357288511516109750299997)
                  ·
                    rfl

theorem cell23_6262352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 9].length) (baseStart_6262352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262352 prefixEnd_6262352 := by exact prefixLift 6262352
  have htrace : WordTrace (prefixWord ++ tailWord_6262352) baseStart_6262352 baseEnd_6262352 := by
    simpa [prefixWord, tailWord_6262352, baseEnd_6262352] using wordTrace_append hprefix tailTrace_6262352
  have hstable : (prefixWord ++ tailWord_6262352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262352).length < 2 ^ (prefixWord ++ tailWord_6262352).sum := by decide
  have hdescent : baseEnd_6262352 < baseStart_6262352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262420 : List Nat := [2, 4, 2, 2, 2, 1, 2, 3, 5]
def baseStart_6262420 : Nat := 118140960795 + 6262420 * 2 ^ 59
def prefixEnd_6262420 : Nat := 4983230072969 + 3 ^ 40 * 6262420 * 2
def baseEnd_6262420 : Nat := 357292391147721498516629

theorem tailTrace_6262420 : CollatzResearch.WordTrace tailWord_6262420 prefixEnd_6262420 357292391147721498516629 := by
  unfold tailWord_6262420
  simp only [CollatzResearch.WordTrace]
  refine ⟨114204610986164675515492357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152272814648219567353989809 114204610986164675515492357)
  ·
    refine ⟨21413364559905876659154817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114204610986164675515492357 21413364559905876659154817)
    ·
      refine ⟨16060023419929407494366113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21413364559905876659154817 16060023419929407494366113)
      ·
        refine ⟨12045017564947055620774585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16060023419929407494366113 12045017564947055620774585)
        ·
          refine ⟨9033763173710291715580939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12045017564947055620774585 9033763173710291715580939)
          ·
            refine ⟨13550644760565437573371409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9033763173710291715580939 13550644760565437573371409)
            ·
              refine ⟨10162983570424078180028557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13550644760565437573371409 10162983570424078180028557)
              ·
                refine ⟨3811118838909029317510709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10162983570424078180028557 3811118838909029317510709)
                ·
                  refine ⟨357292391147721498516629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3811118838909029317510709 357292391147721498516629)
                  ·
                    rfl

theorem cell23_6262420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_6262420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262420 prefixEnd_6262420 := by exact prefixLift 6262420
  have htrace : WordTrace (prefixWord ++ tailWord_6262420) baseStart_6262420 baseEnd_6262420 := by
    simpa [prefixWord, tailWord_6262420, baseEnd_6262420] using wordTrace_append hprefix tailTrace_6262420
  have hstable : (prefixWord ++ tailWord_6262420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262420).length < 2 ^ (prefixWord ++ tailWord_6262420).sum := by decide
  have hdescent : baseEnd_6262420 < baseStart_6262420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262459 : List Nat := [1, 1, 1, 1, 1, 2, 3, 7, 6]
def baseStart_6262459 : Nat := 118140960795 + 6262459 * 2 ^ 59
def prefixEnd_6262459 : Nat := 4983230072969 + 3 ^ 40 * 6262459 * 2
def baseEnd_6262459 : Nat := 357294616230557648229109

theorem tailTrace_6262459 : CollatzResearch.WordTrace tailWord_6262459 prefixEnd_6262459 357294616230557648229109 := by
  unfold tailWord_6262459
  simp only [CollatzResearch.WordTrace]
  refine ⟨228410644419188060691654431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152273762946125373794436287 228410644419188060691654431)
  ·
    refine ⟨342615966628782091037481647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228410644419188060691654431 342615966628782091037481647)
    ·
      refine ⟨513923949943173136556222471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342615966628782091037481647 513923949943173136556222471)
      ·
        refine ⟨770885924914759704834333707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513923949943173136556222471 770885924914759704834333707)
        ·
          refine ⟨1156328887372139557251500561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 770885924914759704834333707 1156328887372139557251500561)
          ·
            refine ⟨867246665529104667938625421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1156328887372139557251500561 867246665529104667938625421)
            ·
              refine ⟨325217499573414250476984533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 867246665529104667938625421 325217499573414250476984533)
              ·
                refine ⟨7622285146251896495554325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 325217499573414250476984533 7622285146251896495554325)
                ·
                  refine ⟨357294616230557648229109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7622285146251896495554325 357294616230557648229109)
                  ·
                    rfl

theorem cell23_6262459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 6].length) (baseStart_6262459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262459 prefixEnd_6262459 := by exact prefixLift 6262459
  have htrace : WordTrace (prefixWord ++ tailWord_6262459) baseStart_6262459 baseEnd_6262459 := by
    simpa [prefixWord, tailWord_6262459, baseEnd_6262459] using wordTrace_append hprefix tailTrace_6262459
  have hstable : (prefixWord ++ tailWord_6262459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262459).length < 2 ^ (prefixWord ++ tailWord_6262459).sum := by decide
  have hdescent : baseEnd_6262459 < baseStart_6262459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262470 : List Nat := [6, 1, 2, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_6262470 : Nat := 118140960795 + 6262470 * 2 ^ 59
def prefixEnd_6262470 : Nat := 4983230072969 + 3 ^ 40 * 6262470 * 2
def baseEnd_6262470 : Nat := 3215657194362218291024431

theorem tailTrace_6262470 : CollatzResearch.WordTrace tailWord_6262470 prefixEnd_6262470 3215657194362218291024431 := by
  unfold tailWord_6262470
  simp only [CollatzResearch.WordTrace]
  refine ⟨7137845175692131549072027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 152274030414765473046869909 7137845175692131549072027)
  ·
    refine ⟨10706767763538197323608041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7137845175692131549072027 10706767763538197323608041)
    ·
      refine ⟨8030075822653647992706031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10706767763538197323608041 8030075822653647992706031)
      ·
        refine ⟨12045113733980471989059047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8030075822653647992706031 12045113733980471989059047)
        ·
          refine ⟨18067670600970707983588571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12045113733980471989059047 18067670600970707983588571)
          ·
            refine ⟨27101505901456061975382857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18067670600970707983588571 27101505901456061975382857)
            ·
              refine ⟨20326129426092046481537143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27101505901456061975382857 20326129426092046481537143)
              ·
                refine ⟨30489194139138069722305715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20326129426092046481537143 30489194139138069722305715)
                ·
                  refine ⟨45733791208707104583458573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30489194139138069722305715 45733791208707104583458573)
                  ·
                    refine ⟨17150171703265164218796965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45733791208707104583458573 17150171703265164218796965)
                    ·
                      refine ⟨3215657194362218291024431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17150171703265164218796965 3215657194362218291024431)
                      ·
                        rfl

theorem cell23_6262470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_6262470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262470 prefixEnd_6262470 := by exact prefixLift 6262470
  have htrace : WordTrace (prefixWord ++ tailWord_6262470) baseStart_6262470 baseEnd_6262470 := by
    simpa [prefixWord, tailWord_6262470, baseEnd_6262470] using wordTrace_append hprefix tailTrace_6262470
  have hstable : (prefixWord ++ tailWord_6262470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262470).length < 2 ^ (prefixWord ++ tailWord_6262470).sum := by decide
  have hdescent : baseEnd_6262470 < baseStart_6262470 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262497 : List Nat := [1, 2, 3, 1, 5, 1, 3, 2, 1, 4]
def baseStart_6262497 : Nat := 118140960795 + 6262497 * 2 ^ 59
def prefixEnd_6262497 : Nat := 4983230072969 + 3 ^ 40 * 6262497 * 2
def baseEnd_6262497 : Nat := 1071890352779963228462269

theorem tailTrace_6262497 : CollatzResearch.WordTrace tailWord_6262497 prefixEnd_6262497 1071890352779963228462269 := by
  unfold tailWord_6262497
  simp only [CollatzResearch.WordTrace]
  refine ⟨228412030393050393181537745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152274686928700262121025163 228412030393050393181537745)
  ·
    refine ⟨171309022794787794886153309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228412030393050393181537745 171309022794787794886153309)
    ·
      refine ⟨64240883548045423082307491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171309022794787794886153309 64240883548045423082307491)
      ·
        refine ⟨96361325322068134623461237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64240883548045423082307491 96361325322068134623461237)
        ·
          refine ⟨9033874248943887620949491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96361325322068134623461237 9033874248943887620949491)
          ·
            refine ⟨13550811373415831431424237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9033874248943887620949491 13550811373415831431424237)
            ·
              refine ⟨5081554265030936786784089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13550811373415831431424237 5081554265030936786784089)
              ·
                refine ⟨3811165698773202590088067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5081554265030936786784089 3811165698773202590088067)
                ·
                  refine ⟨5716748548159803885132101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3811165698773202590088067 5716748548159803885132101)
                  ·
                    refine ⟨1071890352779963228462269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5716748548159803885132101 1071890352779963228462269)
                    ·
                      rfl

theorem cell23_6262497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_6262497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262497 prefixEnd_6262497 := by exact prefixLift 6262497
  have htrace : WordTrace (prefixWord ++ tailWord_6262497) baseStart_6262497 baseEnd_6262497 := by
    simpa [prefixWord, tailWord_6262497, baseEnd_6262497] using wordTrace_append hprefix tailTrace_6262497
  have hstable : (prefixWord ++ tailWord_6262497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262497).length < 2 ^ (prefixWord ++ tailWord_6262497).sum := by decide
  have hdescent : baseEnd_6262497 < baseStart_6262497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262536 : List Nat := [2, 1, 3, 2, 2, 1, 3, 2, 1, 6]
def baseStart_6262536 : Nat := 118140960795 + 6262536 * 2 ^ 59
def prefixEnd_6262536 : Nat := 4983230072969 + 3 ^ 40 * 6262536 * 2
def baseEnd_6262536 : Nat := 1071897028028471677599709

theorem tailTrace_6262536 : CollatzResearch.WordTrace tailWord_6262536 prefixEnd_6262536 1071897028028471677599709 := by
  unfold tailWord_6262536
  simp only [CollatzResearch.WordTrace]
  refine ⟨114206726419954551421103731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152275635226606068561471641 114206726419954551421103731)
  ·
    refine ⟨171310089629931827131655597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114206726419954551421103731 171310089629931827131655597)
    ·
      refine ⟨64241283611224435174370849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171310089629931827131655597 64241283611224435174370849)
      ·
        refine ⟨48180962708418326380778137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64241283611224435174370849 48180962708418326380778137)
        ·
          refine ⟨36135722031313744785583603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48180962708418326380778137 36135722031313744785583603)
          ·
            refine ⟨54203583046970617178375405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36135722031313744785583603 54203583046970617178375405)
            ·
              refine ⟨20326343642613981441890777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54203583046970617178375405 20326343642613981441890777)
              ·
                refine ⟨15244757731960486081418083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20326343642613981441890777 15244757731960486081418083)
                ·
                  refine ⟨22867136597940729122127125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15244757731960486081418083 22867136597940729122127125)
                  ·
                    refine ⟨1071897028028471677599709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22867136597940729122127125 1071897028028471677599709)
                    ·
                      rfl

theorem cell23_6262536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_6262536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262536 prefixEnd_6262536 := by exact prefixLift 6262536
  have htrace : WordTrace (prefixWord ++ tailWord_6262536) baseStart_6262536 baseEnd_6262536 := by
    simpa [prefixWord, tailWord_6262536, baseEnd_6262536] using wordTrace_append hprefix tailTrace_6262536
  have hstable : (prefixWord ++ tailWord_6262536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262536).length < 2 ^ (prefixWord ++ tailWord_6262536).sum := by decide
  have hdescent : baseEnd_6262536 < baseStart_6262536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262543 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 7, 2, 2]
def baseStart_6262543 : Nat := 118140960795 + 6262543 * 2 ^ 59
def prefixEnd_6262543 : Nat := 4983230072969 + 3 ^ 40 * 6262543 * 2
def baseEnd_6262543 : Nat := 3215694678449996505411595

theorem tailTrace_6262543 : CollatzResearch.WordTrace tailWord_6262543 prefixEnd_6262543 3215694678449996505411595 := by
  unfold tailWord_6262543
  simp only [CollatzResearch.WordTrace]
  refine ⟨228413708150883743037712283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152275805433922495358474855 228413708150883743037712283)
  ·
    refine ⟨342620562226325614556568425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228413708150883743037712283 342620562226325614556568425)
    ·
      refine ⟨256965421669744210917426319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342620562226325614556568425 256965421669744210917426319)
      ·
        refine ⟨385448132504616316376139479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256965421669744210917426319 385448132504616316376139479)
        ·
          refine ⟨578172198756924474564209219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385448132504616316376139479 578172198756924474564209219)
          ·
            refine ⟨867258298135386711846313829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578172198756924474564209219 867258298135386711846313829)
            ·
              refine ⟨162610930900385008471183843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 867258298135386711846313829 162610930900385008471183843)
              ·
                refine ⟨243916396350577512706775765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162610930900385008471183843 243916396350577512706775765)
                ·
                  refine ⟨5716790539466660454065057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 243916396350577512706775765 5716790539466660454065057)
                  ·
                    refine ⟨4287592904599995340548793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5716790539466660454065057 4287592904599995340548793)
                    ·
                      refine ⟨3215694678449996505411595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4287592904599995340548793 3215694678449996505411595)
                      ·
                        rfl

theorem cell23_6262543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 7, 2, 2].length) (baseStart_6262543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262543 prefixEnd_6262543 := by exact prefixLift 6262543
  have htrace : WordTrace (prefixWord ++ tailWord_6262543) baseStart_6262543 baseEnd_6262543 := by
    simpa [prefixWord, tailWord_6262543, baseEnd_6262543] using wordTrace_append hprefix tailTrace_6262543
  have hstable : (prefixWord ++ tailWord_6262543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262543).length < 2 ^ (prefixWord ++ tailWord_6262543).sum := by decide
  have hdescent : baseEnd_6262543 < baseStart_6262543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262548 : List Nat := [2, 4, 4, 1, 1, 2, 2, 2, 1, 4]
def baseStart_6262548 : Nat := 118140960795 + 6262548 * 2 ^ 59
def prefixEnd_6262548 : Nat := 4983230072969 + 3 ^ 40 * 6262548 * 2
def baseEnd_6262548 : Nat := 1071899081951089661949691

theorem tailTrace_6262548 : CollatzResearch.WordTrace tailWord_6262548 prefixEnd_6262548 1071899081951089661949691 := by
  unfold tailWord_6262548
  simp only [CollatzResearch.WordTrace]
  refine ⟨114206945257932814445822149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152275927010577085927762865 114206945257932814445822149)
  ·
    refine ⟨21413802235862402708591653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114206945257932814445822149 21413802235862402708591653)
    ·
      refine ⟨4015087919224200507860935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21413802235862402708591653 4015087919224200507860935)
      ·
        refine ⟨6022631878836300761791403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4015087919224200507860935 6022631878836300761791403)
        ·
          refine ⟨9033947818254451142687105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6022631878836300761791403 9033947818254451142687105)
          ·
            refine ⟨6775460863690838357015329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9033947818254451142687105 6775460863690838357015329)
            ·
              refine ⟨5081595647768128767761497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6775460863690838357015329 5081595647768128767761497)
              ·
                refine ⟨3811196735826096575821123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5081595647768128767761497 3811196735826096575821123)
                ·
                  refine ⟨5716795103739144863731685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3811196735826096575821123 5716795103739144863731685)
                  ·
                    refine ⟨1071899081951089661949691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5716795103739144863731685 1071899081951089661949691)
                    ·
                      rfl

theorem cell23_6262548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_6262548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262548 prefixEnd_6262548 := by exact prefixLift 6262548
  have htrace : WordTrace (prefixWord ++ tailWord_6262548) baseStart_6262548 baseEnd_6262548 := by
    simpa [prefixWord, tailWord_6262548, baseEnd_6262548] using wordTrace_append hprefix tailTrace_6262548
  have hstable : (prefixWord ++ tailWord_6262548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262548).length < 2 ^ (prefixWord ++ tailWord_6262548).sum := by decide
  have hdescent : baseEnd_6262548 < baseStart_6262548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262549 : List Nat := [1, 3, 2, 1, 2, 14]
def baseStart_6262549 : Nat := 118140960795 + 6262549 * 2 ^ 59
def prefixEnd_6262549 : Nat := 4983230072969 + 3 ^ 40 * 6262549 * 2
def baseEnd_6262549 : Nat := 13233324112485281818669

theorem tailTrace_6262549 : CollatzResearch.WordTrace tailWord_6262549 prefixEnd_6262549 13233324112485281818669 := by
  unfold tailWord_6262549
  simp only [CollatzResearch.WordTrace]
  refine ⟨228413926988862006062430701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152275951325908004041620467 228413926988862006062430701)
  ·
    refine ⟨85655222620823252273411513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228413926988862006062430701 85655222620823252273411513)
    ·
      refine ⟨64241416965617439205058635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85655222620823252273411513 64241416965617439205058635)
      ·
        refine ⟨96362125448426158807587953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64241416965617439205058635 96362125448426158807587953)
        ·
          refine ⟨72271594086319619105690965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96362125448426158807587953 72271594086319619105690965)
          ·
            refine ⟨13233324112485281818669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 72271594086319619105690965 13233324112485281818669)
            ·
              rfl

theorem cell23_6262549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 14].length) (baseStart_6262549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262549 prefixEnd_6262549 := by exact prefixLift 6262549
  have htrace : WordTrace (prefixWord ++ tailWord_6262549) baseStart_6262549 baseEnd_6262549 := by
    simpa [prefixWord, tailWord_6262549, baseEnd_6262549] using wordTrace_append hprefix tailTrace_6262549
  have hstable : (prefixWord ++ tailWord_6262549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262549).length < 2 ^ (prefixWord ++ tailWord_6262549).sum := by decide
  have hdescent : baseEnd_6262549 < baseStart_6262549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262554 : List Nat := [3, 1, 1, 3, 2, 4, 2, 2, 1, 1, 3]
def baseStart_6262554 : Nat := 118140960795 + 6262554 * 2 ^ 59
def prefixEnd_6262554 : Nat := 4983230072969 + 3 ^ 40 * 6262554 * 2
def baseEnd_6262554 : Nat := 3215700326737195962374045

theorem tailTrace_6262554 : CollatzResearch.WordTrace tailWord_6262554 prefixEnd_6262554 3215700326737195962374045 := by
  unfold tailWord_6262554
  simp only [CollatzResearch.WordTrace]
  refine ⟨57103527338460972979090679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152276072902562594610908477 57103527338460972979090679)
  ·
    refine ⟨85655291007691459468636019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57103527338460972979090679 85655291007691459468636019)
    ·
      refine ⟨128482936511537189202954029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85655291007691459468636019 128482936511537189202954029)
      ·
        refine ⟨48181101191826445951107761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128482936511537189202954029 48181101191826445951107761)
        ·
          refine ⟨36135825893869834463330821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48181101191826445951107761 36135825893869834463330821)
          ·
            refine ⟨6775467355100593961874529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36135825893869834463330821 6775467355100593961874529)
            ·
              refine ⟨5081600516325445471405897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6775467355100593961874529 5081600516325445471405897)
              ·
                refine ⟨3811200387244084103554423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5081600516325445471405897 3811200387244084103554423)
                ·
                  refine ⟨5716800580866126155331635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3811200387244084103554423 5716800580866126155331635)
                  ·
                    refine ⟨8575200871299189232997453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5716800580866126155331635 8575200871299189232997453)
                    ·
                      refine ⟨3215700326737195962374045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8575200871299189232997453 3215700326737195962374045)
                      ·
                        rfl

theorem cell23_6262554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_6262554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262554 prefixEnd_6262554 := by exact prefixLift 6262554
  have htrace : WordTrace (prefixWord ++ tailWord_6262554) baseStart_6262554 baseEnd_6262554 := by
    simpa [prefixWord, tailWord_6262554, baseEnd_6262554] using wordTrace_append hprefix tailTrace_6262554
  have hstable : (prefixWord ++ tailWord_6262554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262554).length < 2 ^ (prefixWord ++ tailWord_6262554).sum := by decide
  have hdescent : baseEnd_6262554 < baseStart_6262554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262556 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 3, 2, 4]
def baseStart_6262556 : Nat := 118140960795 + 6262556 * 2 ^ 59
def prefixEnd_6262556 : Nat := 4983230072969 + 3 ^ 40 * 6262556 * 2
def baseEnd_6262556 : Nat := 3215701353698504954549035

theorem tailTrace_6262556 : CollatzResearch.WordTrace tailWord_6262556 prefixEnd_6262556 3215701353698504954549035 := by
  unfold tailWord_6262556
  simp only [CollatzResearch.WordTrace]
  refine ⟨114207091149918323128967761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152276121533224430838623681 114207091149918323128967761)
  ·
    refine ⟨85655318362438742346725821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114207091149918323128967761 85655318362438742346725821)
    ·
      refine ⟨32120744385914528380022183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85655318362438742346725821 32120744385914528380022183)
      ·
        refine ⟨48181116578871792570033275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32120744385914528380022183 48181116578871792570033275)
        ·
          refine ⟨72271674868307688855049913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48181116578871792570033275 72271674868307688855049913)
          ·
            refine ⟨54203756151230766641287435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72271674868307688855049913 54203756151230766641287435)
            ·
              refine ⟨81305634226846149961931153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54203756151230766641287435 81305634226846149961931153)
              ·
                refine ⟨60979225670134612471448365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81305634226846149961931153 60979225670134612471448365)
                ·
                  refine ⟨22867209626300479676793137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60979225670134612471448365 22867209626300479676793137)
                  ·
                    refine ⟨17150407219725359757594853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22867209626300479676793137 17150407219725359757594853)
                    ·
                      refine ⟨3215701353698504954549035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17150407219725359757594853 3215701353698504954549035)
                      ·
                        rfl

theorem cell23_6262556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_6262556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262556 prefixEnd_6262556 := by exact prefixLift 6262556
  have htrace : WordTrace (prefixWord ++ tailWord_6262556) baseStart_6262556 baseEnd_6262556 := by
    simpa [prefixWord, tailWord_6262556, baseEnd_6262556] using wordTrace_append hprefix tailTrace_6262556
  have hstable : (prefixWord ++ tailWord_6262556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262556).length < 2 ^ (prefixWord ++ tailWord_6262556).sum := by decide
  have hdescent : baseEnd_6262556 < baseStart_6262556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262560 : List Nat := [2, 1, 1, 5, 1, 1, 2, 3, 3, 2, 2]
def baseStart_6262560 : Nat := 118140960795 + 6262560 * 2 ^ 59
def prefixEnd_6262560 : Nat := 4983230072969 + 3 ^ 40 * 6262560 * 2
def baseEnd_6262560 : Nat := 3215703407621122938899017

theorem tailTrace_6262560 : CollatzResearch.WordTrace tailWord_6262560 prefixEnd_6262560 3215703407621122938899017 := by
  unfold tailWord_6262560
  simp only [CollatzResearch.WordTrace]
  refine ⟨114207164095911077470540567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152276218794548103294054089 114207164095911077470540567)
  ·
    refine ⟨171310746143866616205810851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114207164095911077470540567 171310746143866616205810851)
    ·
      refine ⟨256966119215799924308716277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171310746143866616205810851 256966119215799924308716277)
      ·
        refine ⟨24090573676481242903942151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 256966119215799924308716277 24090573676481242903942151)
        ·
          refine ⟨36135860514721864355913227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24090573676481242903942151 36135860514721864355913227)
          ·
            refine ⟨54203790772082796533869841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36135860514721864355913227 54203790772082796533869841)
            ·
              refine ⟨40652843079062097400402381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54203790772082796533869841 40652843079062097400402381)
              ·
                refine ⟨15244816154648286525150893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40652843079062097400402381 15244816154648286525150893)
                ·
                  refine ⟨5716806057993107446931585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15244816154648286525150893 5716806057993107446931585)
                  ·
                    refine ⟨4287604543494830585198689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5716806057993107446931585 4287604543494830585198689)
                    ·
                      refine ⟨3215703407621122938899017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4287604543494830585198689 3215703407621122938899017)
                      ·
                        rfl

theorem cell23_6262560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_6262560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262560 prefixEnd_6262560 := by exact prefixLift 6262560
  have htrace : WordTrace (prefixWord ++ tailWord_6262560) baseStart_6262560 baseEnd_6262560 := by
    simpa [prefixWord, tailWord_6262560, baseEnd_6262560] using wordTrace_append hprefix tailTrace_6262560
  have hstable : (prefixWord ++ tailWord_6262560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262560).length < 2 ^ (prefixWord ++ tailWord_6262560).sum := by decide
  have hdescent : baseEnd_6262560 < baseStart_6262560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262580 : List Nat := [2, 5, 1, 1, 2, 1, 2, 1, 3, 2, 3]
def baseStart_6262580 : Nat := 118140960795 + 6262580 * 2 ^ 59
def prefixEnd_6262580 : Nat := 4983230072969 + 3 ^ 40 * 6262580 * 2
def baseEnd_6262580 : Nat := 3215713677234212860648925

theorem tailTrace_6262580 : CollatzResearch.WordTrace tailWord_6262580 prefixEnd_6262580 3215713677234212860648925 := by
  unfold tailWord_6262580
  simp only [CollatzResearch.WordTrace]
  refine ⟨114207528825874849178404597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152276705101166465571206129 114207528825874849178404597)
  ·
    refine ⟨10706955827425767110475431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114207528825874849178404597 10706955827425767110475431)
    ·
      refine ⟨16060433741138650665713147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10706955827425767110475431 16060433741138650665713147)
      ·
        refine ⟨24090650611707975998569721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16060433741138650665713147 24090650611707975998569721)
        ·
          refine ⟨18067987958780981998927291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24090650611707975998569721 18067987958780981998927291)
          ·
            refine ⟨27101981938171472998390937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18067987958780981998927291 27101981938171472998390937)
            ·
              refine ⟨20326486453628604748793203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27101981938171472998390937 20326486453628604748793203)
              ·
                refine ⟨30489729680442907123189805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20326486453628604748793203 30489729680442907123189805)
                ·
                  refine ⟨11433648630166090171196177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30489729680442907123189805 11433648630166090171196177)
                  ·
                    refine ⟨8575236472624567628397133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11433648630166090171196177 8575236472624567628397133)
                    ·
                      refine ⟨3215713677234212860648925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8575236472624567628397133 3215713677234212860648925)
                      ·
                        rfl

theorem cell23_6262580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_6262580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262580 prefixEnd_6262580 := by exact prefixLift 6262580
  have htrace : WordTrace (prefixWord ++ tailWord_6262580) baseStart_6262580 baseEnd_6262580 := by
    simpa [prefixWord, tailWord_6262580, baseEnd_6262580] using wordTrace_append hprefix tailTrace_6262580
  have hstable : (prefixWord ++ tailWord_6262580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262580).length < 2 ^ (prefixWord ++ tailWord_6262580).sum := by decide
  have hdescent : baseEnd_6262580 < baseStart_6262580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262610 : List Nat := [3, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3]
def baseStart_6262610 : Nat := 118140960795 + 6262610 * 2 ^ 59
def prefixEnd_6262610 : Nat := 4983230072969 + 3 ^ 40 * 6262610 * 2
def baseEnd_6262610 : Nat := 3215729081653847743273787

theorem tailTrace_6262610 : CollatzResearch.WordTrace tailWord_6262610 prefixEnd_6262610 3215729081653847743273787 := by
  unfold tailWord_6262610
  simp only [CollatzResearch.WordTrace]
  refine ⟨57104037960410253370100321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152277434561094008986934189 57104037960410253370100321)
  ·
    refine ⟨42828028470307690027575241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57104037960410253370100321 42828028470307690027575241)
    ·
      refine ⟨32121021352730767520681431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42828028470307690027575241 32121021352730767520681431)
      ·
        refine ⟨48181532029096151281022147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32121021352730767520681431 48181532029096151281022147)
        ·
          refine ⟨72272298043644226921533221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48181532029096151281022147 72272298043644226921533221)
          ·
            refine ⟨13551055883183292547787479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72272298043644226921533221 13551055883183292547787479)
            ·
              refine ⟨20326583824774938821681219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13551055883183292547787479 20326583824774938821681219)
              ·
                refine ⟨30489875737162408232521829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20326583824774938821681219 30489875737162408232521829)
                ·
                  refine ⟨5716851700717951543597843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30489875737162408232521829 5716851700717951543597843)
                  ·
                    refine ⟨8575277551076927315396765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5716851700717951543597843 8575277551076927315396765)
                    ·
                      refine ⟨3215729081653847743273787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8575277551076927315396765 3215729081653847743273787)
                      ·
                        rfl

theorem cell23_6262610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_6262610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262610 prefixEnd_6262610 := by exact prefixLift 6262610
  have htrace : WordTrace (prefixWord ++ tailWord_6262610) baseStart_6262610 baseEnd_6262610 := by
    simpa [prefixWord, tailWord_6262610, baseEnd_6262610] using wordTrace_append hprefix tailTrace_6262610
  have hstable : (prefixWord ++ tailWord_6262610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262610).length < 2 ^ (prefixWord ++ tailWord_6262610).sum := by decide
  have hdescent : baseEnd_6262610 < baseStart_6262610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262627 : List Nat := [1, 1, 1, 5, 5, 1, 1, 1, 1, 3, 3]
def baseStart_6262627 : Nat := 118140960795 + 6262627 * 2 ^ 59
def prefixEnd_6262627 : Nat := 4983230072969 + 3 ^ 40 * 6262627 * 2
def baseEnd_6262627 : Nat := 3215737810824974176761209

theorem tailTrace_6262627 : CollatzResearch.WordTrace tailWord_6262627 prefixEnd_6262627 3215737810824974176761209 := by
  unfold tailWord_6262627
  simp only [CollatzResearch.WordTrace]
  refine ⟨228416771882579425383770135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152277847921719616922513423 228416771882579425383770135)
  ·
    refine ⟨342625157823869138075655203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228416771882579425383770135 342625157823869138075655203)
    ·
      refine ⟨513937736735803707113482805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342625157823869138075655203 513937736735803707113482805)
      ·
        refine ⟨48181662818981597541889013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 513937736735803707113482805 48181662818981597541889013)
        ·
          refine ⟨4517030889279524769552095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48181662818981597541889013 4517030889279524769552095)
          ·
            refine ⟨6775546333919287154328143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4517030889279524769552095 6775546333919287154328143)
            ·
              refine ⟨10163319500878930731492215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6775546333919287154328143 10163319500878930731492215)
              ·
                refine ⟨15244979251318396097238323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10163319500878930731492215 15244979251318396097238323)
                ·
                  refine ⟨22867468876977594145857485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15244979251318396097238323 22867468876977594145857485)
                  ·
                    refine ⟨8575300828866597804696557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22867468876977594145857485 8575300828866597804696557)
                    ·
                      refine ⟨3215737810824974176761209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8575300828866597804696557 3215737810824974176761209)
                      ·
                        rfl

theorem cell23_6262627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_6262627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262627 prefixEnd_6262627 := by exact prefixLift 6262627
  have htrace : WordTrace (prefixWord ++ tailWord_6262627) baseStart_6262627 baseEnd_6262627 := by
    simpa [prefixWord, tailWord_6262627, baseEnd_6262627] using wordTrace_append hprefix tailTrace_6262627
  have hstable : (prefixWord ++ tailWord_6262627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262627).length < 2 ^ (prefixWord ++ tailWord_6262627).sum := by decide
  have hdescent : baseEnd_6262627 < baseStart_6262627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262650 : List Nat := [3, 1, 1, 1, 1, 1, 5, 2, 4, 2, 2]
def baseStart_6262650 : Nat := 118140960795 + 6262650 * 2 ^ 59
def prefixEnd_6262650 : Nat := 4983230072969 + 3 ^ 40 * 6262650 * 2
def baseEnd_6262650 : Nat := 3215749620880027586773603

theorem tailTrace_6262650 : CollatzResearch.WordTrace tailWord_6262650 prefixEnd_6262650 3215749620880027586773603 := by
  unfold tailWord_6262650
  simp only [CollatzResearch.WordTrace]
  refine ⟨57104402690374025077964351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152278407174330733541238269 57104402690374025077964351)
  ·
    refine ⟨85656604035561037616946527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57104402690374025077964351 85656604035561037616946527)
    ·
      refine ⟨128484906053341556425419791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85656604035561037616946527 128484906053341556425419791)
      ·
        refine ⟨192727359080012334638129687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128484906053341556425419791 192727359080012334638129687)
        ·
          refine ⟨289091038620018501957194531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192727359080012334638129687 289091038620018501957194531)
          ·
            refine ⟨433636557930027752935791797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289091038620018501957194531 433636557930027752935791797)
            ·
              refine ⟨40653427305940101837730481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 433636557930027752935791797 40653427305940101837730481)
              ·
                refine ⟨30490070479455076378297861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40653427305940101837730481 30490070479455076378297861)
                ·
                  refine ⟨5716888214897826820930849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30490070479455076378297861 5716888214897826820930849)
                  ·
                    refine ⟨4287666161173370115698137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5716888214897826820930849 4287666161173370115698137)
                    ·
                      refine ⟨3215749620880027586773603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4287666161173370115698137 3215749620880027586773603)
                      ·
                        rfl

theorem cell23_6262650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 4, 2, 2].length) (baseStart_6262650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262650 prefixEnd_6262650 := by exact prefixLift 6262650
  have htrace : WordTrace (prefixWord ++ tailWord_6262650) baseStart_6262650 baseEnd_6262650 := by
    simpa [prefixWord, tailWord_6262650, baseEnd_6262650] using wordTrace_append hprefix tailTrace_6262650
  have hstable : (prefixWord ++ tailWord_6262650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262650).length < 2 ^ (prefixWord ++ tailWord_6262650).sum := by decide
  have hdescent : baseEnd_6262650 < baseStart_6262650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262654 : List Nat := [4, 2, 3, 1, 1, 1, 2, 3, 1, 3, 2]
def baseStart_6262654 : Nat := 118140960795 + 6262654 * 2 ^ 59
def prefixEnd_6262654 : Nat := 4983230072969 + 3 ^ 40 * 6262654 * 2
def baseEnd_6262654 : Nat := 3215751674802645571123585

theorem tailTrace_6262654 : CollatzResearch.WordTrace tailWord_6262654 prefixEnd_6262654 3215751674802645571123585 := by
  unfold tailWord_6262654
  simp only [CollatzResearch.WordTrace]
  refine ⟨28552219581685201124375377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152278504435654405996668677 28552219581685201124375377)
  ·
    refine ⟨21414164686263900843281533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28552219581685201124375377 21414164686263900843281533)
    ·
      refine ⟨8030311757348962816230575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21414164686263900843281533 8030311757348962816230575)
      ·
        refine ⟨12045467636023444224345863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8030311757348962816230575 12045467636023444224345863)
        ·
          refine ⟨18068201454035166336518795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12045467636023444224345863 18068201454035166336518795)
          ·
            refine ⟨27102302181052749504778193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18068201454035166336518795 27102302181052749504778193)
            ·
              refine ⟨20326726635789562128583645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27102302181052749504778193 20326726635789562128583645)
              ·
                refine ⟨7622522488421085798218867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20326726635789562128583645 7622522488421085798218867)
                ·
                  refine ⟨11433783732631628697328301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7622522488421085798218867 11433783732631628697328301)
                  ·
                    refine ⟨4287668899736860761498113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11433783732631628697328301 4287668899736860761498113)
                    ·
                      refine ⟨3215751674802645571123585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4287668899736860761498113 3215751674802645571123585)
                      ·
                        rfl

theorem cell23_6262654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_6262654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262654 prefixEnd_6262654 := by exact prefixLift 6262654
  have htrace : WordTrace (prefixWord ++ tailWord_6262654) baseStart_6262654 baseEnd_6262654 := by
    simpa [prefixWord, tailWord_6262654, baseEnd_6262654] using wordTrace_append hprefix tailTrace_6262654
  have hstable : (prefixWord ++ tailWord_6262654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262654).length < 2 ^ (prefixWord ++ tailWord_6262654).sum := by decide
  have hdescent : baseEnd_6262654 < baseStart_6262654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262673 : List Nat := [1, 2, 2, 1, 1, 1, 4, 6, 5]
def baseStart_6262673 : Nat := 118140960795 + 6262673 * 2 ^ 59
def prefixEnd_6262673 : Nat := 4983230072969 + 3 ^ 40 * 6262673 * 2
def baseEnd_6262673 : Nat := 357306825659453444087333

theorem tailTrace_6262673 : CollatzResearch.WordTrace tailWord_6262673 prefixEnd_6262673 357306825659453444087333 := by
  unfold tailWord_6262673
  simp only [CollatzResearch.WordTrace]
  refine ⟨228418449640412775239944673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152278966426941850159963115 228418449640412775239944673)
  ·
    refine ⟨171313837230309581429958505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228418449640412775239944673 171313837230309581429958505)
    ·
      refine ⟨128485377922732186072468879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171313837230309581429958505 128485377922732186072468879)
      ·
        refine ⟨192728066884098279108703319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128485377922732186072468879 192728066884098279108703319)
        ·
          refine ⟨289092100326147418663054979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192728066884098279108703319 289092100326147418663054979)
          ·
            refine ⟨433638150489221127994582469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289092100326147418663054979 433638150489221127994582469)
            ·
              refine ⟨81307153216728961498984213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 433638150489221127994582469 81307153216728961498984213)
              ·
                refine ⟨3811272807034170070264885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81307153216728961498984213 3811272807034170070264885)
                ·
                  refine ⟨357306825659453444087333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3811272807034170070264885 357306825659453444087333)
                  ·
                    rfl

theorem cell23_6262673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 6, 5].length) (baseStart_6262673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262673 prefixEnd_6262673 := by exact prefixLift 6262673
  have htrace : WordTrace (prefixWord ++ tailWord_6262673) baseStart_6262673 baseEnd_6262673 := by
    simpa [prefixWord, tailWord_6262673, baseEnd_6262673] using wordTrace_append hprefix tailTrace_6262673
  have hstable : (prefixWord ++ tailWord_6262673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262673).length < 2 ^ (prefixWord ++ tailWord_6262673).sum := by decide
  have hdescent : baseEnd_6262673 < baseStart_6262673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262684 : List Nat := [2, 2, 3, 3, 1, 2, 1, 3, 2, 2, 2]
def baseStart_6262684 : Nat := 118140960795 + 6262684 * 2 ^ 59
def prefixEnd_6262684 : Nat := 4983230072969 + 3 ^ 40 * 6262684 * 2
def baseEnd_6262684 : Nat := 3215767079222280453748447

theorem tailTrace_6262684 : CollatzResearch.WordTrace tailWord_6262684 prefixEnd_6262684 3215767079222280453748447 := by
  unfold tailWord_6262684
  simp only [CollatzResearch.WordTrace]
  refine ⟨114209425421686462059297553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152279233895581949412396737 114209425421686462059297553)
  ·
    refine ⟨85657069066264846544473165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114209425421686462059297553 85657069066264846544473165)
    ·
      refine ⟨32121400899849317454177437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85657069066264846544473165 32121400899849317454177437)
      ·
        refine ⟨12045525337443494045316539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32121400899849317454177437 12045525337443494045316539)
        ·
          refine ⟨18068288006165241067974809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12045525337443494045316539 18068288006165241067974809)
          ·
            refine ⟨13551216004623930800981107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18068288006165241067974809 13551216004623930800981107)
            ·
              refine ⟨20326824006935896201471661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13551216004623930800981107 20326824006935896201471661)
              ·
                refine ⟨7622559002600961075551873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20326824006935896201471661 7622559002600961075551873)
                ·
                  refine ⟨5716919251950720806663905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7622559002600961075551873 5716919251950720806663905)
                  ·
                    refine ⟨4287689438963040604997929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5716919251950720806663905 4287689438963040604997929)
                    ·
                      refine ⟨3215767079222280453748447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4287689438963040604997929 3215767079222280453748447)
                      ·
                        rfl

theorem cell23_6262684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_6262684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262684 prefixEnd_6262684 := by exact prefixLift 6262684
  have htrace : WordTrace (prefixWord ++ tailWord_6262684) baseStart_6262684 baseEnd_6262684 := by
    simpa [prefixWord, tailWord_6262684, baseEnd_6262684] using wordTrace_append hprefix tailTrace_6262684
  have hstable : (prefixWord ++ tailWord_6262684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262684).length < 2 ^ (prefixWord ++ tailWord_6262684).sum := by decide
  have hdescent : baseEnd_6262684 < baseStart_6262684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262703 : List Nat := [1, 1, 2, 1, 2, 2, 6, 1, 2, 5]
def baseStart_6262703 : Nat := 118140960795 + 6262703 * 2 ^ 59
def prefixEnd_6262703 : Nat := 4983230072969 + 3 ^ 40 * 6262703 * 2
def baseEnd_6262703 : Nat := 1071925611784905293136953

theorem tailTrace_6262703 : CollatzResearch.WordTrace tailWord_6262703 prefixEnd_6262703 1071925611784905293136953 := by
  unfold tailWord_6262703
  simp only [CollatzResearch.WordTrace]
  refine ⟨228419543830304090363536763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152279695886869393575691175 228419543830304090363536763)
  ·
    refine ⟨342629315745456135545305145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228419543830304090363536763 342629315745456135545305145)
    ·
      refine ⟨256971986809092101658978859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342629315745456135545305145 256971986809092101658978859)
      ·
        refine ⟨385457980213638152488468289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256971986809092101658978859 385457980213638152488468289)
        ·
          refine ⟨289093485160228614366351217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385457980213638152488468289 289093485160228614366351217)
          ·
            refine ⟨216820113870171460774763413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289093485160228614366351217 216820113870171460774763413)
            ·
              refine ⟨10163442837664287223817035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 216820113870171460774763413 10163442837664287223817035)
              ·
                refine ⟨15245164256496430835725553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10163442837664287223817035 15245164256496430835725553)
                ·
                  refine ⟨11433873192372323126794165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15245164256496430835725553 11433873192372323126794165)
                  ·
                    refine ⟨1071925611784905293136953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11433873192372323126794165 1071925611784905293136953)
                    ·
                      rfl

theorem cell23_6262703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 5].length) (baseStart_6262703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262703 prefixEnd_6262703 := by exact prefixLift 6262703
  have htrace : WordTrace (prefixWord ++ tailWord_6262703) baseStart_6262703 baseEnd_6262703 := by
    simpa [prefixWord, tailWord_6262703, baseEnd_6262703] using wordTrace_append hprefix tailTrace_6262703
  have hstable : (prefixWord ++ tailWord_6262703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262703).length < 2 ^ (prefixWord ++ tailWord_6262703).sum := by decide
  have hdescent : baseEnd_6262703 < baseStart_6262703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262743 : List Nat := [1, 1, 3, 2, 1, 1, 4, 2, 1, 4, 3]
def baseStart_6262743 : Nat := 118140960795 + 6262743 * 2 ^ 59
def prefixEnd_6262743 : Nat := 4983230072969 + 3 ^ 40 * 6262743 * 2
def baseEnd_6262743 : Nat := 3215797374580895722910675

theorem tailTrace_6262743 : CollatzResearch.WordTrace tailWord_6262743 prefixEnd_6262743 3215797374580895722910675 := by
  unfold tailWord_6262743
  simp only [CollatzResearch.WordTrace]
  refine ⟨228421002750159177194992883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152280668500106118129995255 228421002750159177194992883)
  ·
    refine ⟨342631504125238765792489325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228421002750159177194992883 342631504125238765792489325)
    ·
      refine ⟨128486814046964537172183497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342631504125238765792489325 128486814046964537172183497)
      ·
        refine ⟨96365110535223402879137623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128486814046964537172183497 96365110535223402879137623)
        ·
          refine ⟨144547665802835104318706435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96365110535223402879137623 144547665802835104318706435)
          ·
            refine ⟨216821498704252656478059653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144547665802835104318706435 216821498704252656478059653)
            ·
              refine ⟨40654031007047373089636185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 216821498704252656478059653 40654031007047373089636185)
              ·
                refine ⟨30490523255285529817227139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40654031007047373089636185 30490523255285529817227139)
                ·
                  refine ⟨45735784882928294725840709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30490523255285529817227139 45735784882928294725840709)
                  ·
                    refine ⟨8575459665549055261095133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45735784882928294725840709 8575459665549055261095133)
                    ·
                      refine ⟨3215797374580895722910675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8575459665549055261095133 3215797374580895722910675)
                      ·
                        rfl

theorem cell23_6262743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_6262743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262743 prefixEnd_6262743 := by exact prefixLift 6262743
  have htrace : WordTrace (prefixWord ++ tailWord_6262743) baseStart_6262743 baseEnd_6262743 := by
    simpa [prefixWord, tailWord_6262743, baseEnd_6262743] using wordTrace_append hprefix tailTrace_6262743
  have hstable : (prefixWord ++ tailWord_6262743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262743).length < 2 ^ (prefixWord ++ tailWord_6262743).sum := by decide
  have hdescent : baseEnd_6262743 < baseStart_6262743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262754 : List Nat := [3, 3, 3, 1, 2, 2, 1, 1, 2, 5]
def baseStart_6262754 : Nat := 118140960795 + 6262754 * 2 ^ 59
def prefixEnd_6262754 : Nat := 4983230072969 + 3 ^ 40 * 6262754 * 2
def baseEnd_6262754 : Nat := 1071934340956031726624375

theorem tailTrace_6262754 : CollatzResearch.WordTrace tailWord_6262754 prefixEnd_6262754 1071934340956031726624375 := by
  unfold tailWord_6262754
  simp only [CollatzResearch.WordTrace]
  refine ⟨57105350988279831518410829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152280935968746217382428877 57105350988279831518410829)
  ·
    refine ⟨21414506620604936819404061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57105350988279831518410829 21414506620604936819404061)
    ·
      refine ⟨8030439982726851307276523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21414506620604936819404061 8030439982726851307276523)
      ·
        refine ⟨12045659974090276960914785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8030439982726851307276523 12045659974090276960914785)
        ·
          refine ⟨9034244980567707720686089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12045659974090276960914785 9034244980567707720686089)
          ·
            refine ⟨6775683735425780790514567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9034244980567707720686089 6775683735425780790514567)
            ·
              refine ⟨10163525603138671185771851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6775683735425780790514567 10163525603138671185771851)
              ·
                refine ⟨15245288404708006778657777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10163525603138671185771851 15245288404708006778657777)
                ·
                  refine ⟨11433966303531005083993333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15245288404708006778657777 11433966303531005083993333)
                  ·
                    refine ⟨1071934340956031726624375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11433966303531005083993333 1071934340956031726624375)
                    ·
                      rfl

theorem cell23_6262754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_6262754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262754 prefixEnd_6262754 := by exact prefixLift 6262754
  have htrace : WordTrace (prefixWord ++ tailWord_6262754) baseStart_6262754 baseEnd_6262754 := by
    simpa [prefixWord, tailWord_6262754, baseEnd_6262754] using wordTrace_append hprefix tailTrace_6262754
  have hstable : (prefixWord ++ tailWord_6262754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262754).length < 2 ^ (prefixWord ++ tailWord_6262754).sum := by decide
  have hdescent : baseEnd_6262754 < baseStart_6262754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262767 : List Nat := [1, 1, 2, 1, 4, 2, 4, 3, 1, 4]
def baseStart_6262767 : Nat := 118140960795 + 6262767 * 2 ^ 59
def prefixEnd_6262767 : Nat := 4983230072969 + 3 ^ 40 * 6262767 * 2
def baseEnd_6262767 : Nat := 1071936566038867876336855

theorem tailTrace_6262767 : CollatzResearch.WordTrace tailWord_6262767 prefixEnd_6262767 1071936566038867876336855 := by
  unfold tailWord_6262767
  simp only [CollatzResearch.WordTrace]
  refine ⟨228421878102072229293866555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152281252068048152862577703 228421878102072229293866555)
  ·
    refine ⟨342632817153108343940799833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228421878102072229293866555 342632817153108343940799833)
    ·
      refine ⟨256974612864831257955599875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342632817153108343940799833 256974612864831257955599875)
      ·
        refine ⟨385461919297246886933399813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256974612864831257955599875 385461919297246886933399813)
        ·
          refine ⟨72274109868233791300012465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 385461919297246886933399813 72274109868233791300012465)
          ·
            refine ⟨54205582401175343475009349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72274109868233791300012465 54205582401175343475009349)
            ·
              refine ⟨10163546700220376901564253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54205582401175343475009349 10163546700220376901564253)
              ·
                refine ⟨3811330012582641338086595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10163546700220376901564253 3811330012582641338086595)
                ·
                  refine ⟨5716995018873962007129893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3811330012582641338086595 5716995018873962007129893)
                  ·
                    refine ⟨1071936566038867876336855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5716995018873962007129893 1071936566038867876336855)
                    ·
                      rfl

theorem cell23_6262767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 3, 1, 4].length) (baseStart_6262767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262767 prefixEnd_6262767 := by exact prefixLift 6262767
  have htrace : WordTrace (prefixWord ++ tailWord_6262767) baseStart_6262767 baseEnd_6262767 := by
    simpa [prefixWord, tailWord_6262767, baseEnd_6262767] using wordTrace_append hprefix tailTrace_6262767
  have hstable : (prefixWord ++ tailWord_6262767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262767).length < 2 ^ (prefixWord ++ tailWord_6262767).sum := by decide
  have hdescent : baseEnd_6262767 < baseStart_6262767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262800 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 4, 3, 2]
def baseStart_6262800 : Nat := 118140960795 + 6262800 * 2 ^ 59
def prefixEnd_6262800 : Nat := 4983230072969 + 3 ^ 40 * 6262800 * 2
def baseEnd_6262800 : Nat := 3215826642978201999897913

theorem tailTrace_6262800 : CollatzResearch.WordTrace tailWord_6262800 prefixEnd_6262800 3215826642978201999897913 := by
  unfold tailWord_6262800
  simp only [CollatzResearch.WordTrace]
  refine ⟨114211540855476337964908927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152282054473968450619878569 114211540855476337964908927)
  ·
    refine ⟨171317311283214506947363391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114211540855476337964908927 171317311283214506947363391)
    ·
      refine ⟨256975966924821760421045087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171317311283214506947363391 256975966924821760421045087)
      ·
        refine ⟨385463950387232640631567631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256975966924821760421045087 385463950387232640631567631)
        ·
          refine ⟨578195925580848960947351447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385463950387232640631567631 578195925580848960947351447)
          ·
            refine ⟨867293888371273441421027171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578195925580848960947351447 867293888371273441421027171)
            ·
              refine ⟨1300940832556910162131540757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 867293888371273441421027171 1300940832556910162131540757)
              ·
                refine ⟨60981601526105163849915973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1300940832556910162131540757 60981601526105163849915973)
                ·
                  refine ⟨11434050286144718221859245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60981601526105163849915973 11434050286144718221859245)
                  ·
                    refine ⟨4287768857304269333197217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11434050286144718221859245 4287768857304269333197217)
                    ·
                      refine ⟨3215826642978201999897913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4287768857304269333197217 3215826642978201999897913)
                      ·
                        rfl

theorem cell23_6262800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 4, 3, 2].length) (baseStart_6262800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262800 prefixEnd_6262800 := by exact prefixLift 6262800
  have htrace : WordTrace (prefixWord ++ tailWord_6262800) baseStart_6262800 baseEnd_6262800 := by
    simpa [prefixWord, tailWord_6262800, baseEnd_6262800] using wordTrace_append hprefix tailTrace_6262800
  have hstable : (prefixWord ++ tailWord_6262800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262800).length < 2 ^ (prefixWord ++ tailWord_6262800).sum := by decide
  have hdescent : baseEnd_6262800 < baseStart_6262800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262810 : List Nat := [3, 1, 1, 3, 1, 3, 1, 4, 1, 5]
def baseStart_6262810 : Nat := 118140960795 + 6262810 * 2 ^ 59
def prefixEnd_6262810 : Nat := 4983230072969 + 3 ^ 40 * 6262810 * 2
def baseEnd_6262810 : Nat := 1071943925928248986924289

theorem tailTrace_6262810 : CollatzResearch.WordTrace tailWord_6262810 prefixEnd_6262810 1071943925928248986924289 := by
  unfold tailWord_6262810
  simp only [CollatzResearch.WordTrace]
  refine ⟨57105861610229111909420471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152282297627277631758454589 57105861610229111909420471)
  ·
    refine ⟨85658792415343667864130707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57105861610229111909420471 85658792415343667864130707)
    ·
      refine ⟨128488188623015501796196061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85658792415343667864130707 128488188623015501796196061)
      ·
        refine ⟨48183070733630813173573523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128488188623015501796196061 48183070733630813173573523)
        ·
          refine ⟨72274606100446219760360285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48183070733630813173573523 72274606100446219760360285)
          ·
            refine ⟨27102977287667332410135107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72274606100446219760360285 27102977287667332410135107)
            ·
              refine ⟨40654465931500998615202661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27102977287667332410135107 40654465931500998615202661)
              ·
                refine ⟨7622712362156437240350499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40654465931500998615202661 7622712362156437240350499)
                ·
                  refine ⟨11434068543234655860525749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7622712362156437240350499 11434068543234655860525749)
                  ·
                    refine ⟨1071943925928248986924289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11434068543234655860525749 1071943925928248986924289)
                    ·
                      rfl

theorem cell23_6262810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 1, 5].length) (baseStart_6262810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262810 prefixEnd_6262810 := by exact prefixLift 6262810
  have htrace : WordTrace (prefixWord ++ tailWord_6262810) baseStart_6262810 baseEnd_6262810 := by
    simpa [prefixWord, tailWord_6262810, baseEnd_6262810] using wordTrace_append hprefix tailTrace_6262810
  have hstable : (prefixWord ++ tailWord_6262810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262810).length < 2 ^ (prefixWord ++ tailWord_6262810).sum := by decide
  have hdescent : baseEnd_6262810 < baseStart_6262810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262841 : List Nat := [1, 2, 1, 5, 4, 1, 1, 1, 3, 1, 3]
def baseStart_6262841 : Nat := 118140960795 + 6262841 * 2 ^ 59
def prefixEnd_6262841 : Nat := 4983230072969 + 3 ^ 40 * 6262841 * 2
def baseEnd_6262841 : Nat := 3215847695685036339485225

theorem tailTrace_6262841 : CollatzResearch.WordTrace tailWord_6262841 prefixEnd_6262841 3215847695685036339485225 := by
  unfold tailWord_6262841
  simp only [CollatzResearch.WordTrace]
  refine ⟨228424577103804139932060377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152283051402536093288040251 228424577103804139932060377)
  ·
    refine ⟨171318432827853104949045283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228424577103804139932060377 171318432827853104949045283)
    ·
      refine ⟨256977649241779657423567925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171318432827853104949045283 256977649241779657423567925)
      ·
        refine ⟨24091654616416842883459493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 256977649241779657423567925 24091654616416842883459493)
        ·
          refine ⟨4517185240578158040648655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24091654616416842883459493 4517185240578158040648655)
          ·
            refine ⟨6775777860867237060972983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4517185240578158040648655 6775777860867237060972983)
            ·
              refine ⟨10163666791300855591459475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6775777860867237060972983 10163666791300855591459475)
              ·
                refine ⟨15245500186951283387189213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10163666791300855591459475 15245500186951283387189213)
                ·
                  refine ⟨5717062570106731270195955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15245500186951283387189213 5717062570106731270195955)
                  ·
                    refine ⟨8575593855160096905293933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5717062570106731270195955 8575593855160096905293933)
                    ·
                      refine ⟨3215847695685036339485225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8575593855160096905293933 3215847695685036339485225)
                      ·
                        rfl

theorem cell23_6262841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_6262841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262841 prefixEnd_6262841 := by exact prefixLift 6262841
  have htrace : WordTrace (prefixWord ++ tailWord_6262841) baseStart_6262841 baseEnd_6262841 := by
    simpa [prefixWord, tailWord_6262841, baseEnd_6262841] using wordTrace_append hprefix tailTrace_6262841
  have hstable : (prefixWord ++ tailWord_6262841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262841).length < 2 ^ (prefixWord ++ tailWord_6262841).sum := by decide
  have hdescent : baseEnd_6262841 < baseStart_6262841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262843 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 4]
def baseStart_6262843 : Nat := 118140960795 + 6262843 * 2 ^ 59
def prefixEnd_6262843 : Nat := 4983230072969 + 3 ^ 40 * 6262843 * 2
def baseEnd_6262843 : Nat := 3215848722646345331660215

theorem tailTrace_6262843 : CollatzResearch.WordTrace tailWord_6262843 prefixEnd_6262843 3215848722646345331660215 := by
  unfold tailWord_6262843
  simp only [CollatzResearch.WordTrace]
  refine ⟨228424650049796894273633183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152283100033197929515755455 228424650049796894273633183)
  ·
    refine ⟨342636975074695341410449775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228424650049796894273633183 342636975074695341410449775)
    ·
      refine ⟨513955462612043012115674663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342636975074695341410449775 513955462612043012115674663)
      ·
        refine ⟨770933193918064518173511995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513955462612043012115674663 770933193918064518173511995)
        ·
          refine ⟨1156399790877096777260267993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 770933193918064518173511995 1156399790877096777260267993)
          ·
            refine ⟨867299843157822582945200995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1156399790877096777260267993 867299843157822582945200995)
            ·
              refine ⟨1300949764736733874417801493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 867299843157822582945200995 1300949764736733874417801493)
              ·
                refine ⟨60982020222034400363334445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1300949764736733874417801493 60982020222034400363334445)
                ·
                  refine ⟨22868257583262900136250417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60982020222034400363334445 22868257583262900136250417)
                  ·
                    refine ⟨17151193187447175102187813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22868257583262900136250417 17151193187447175102187813)
                    ·
                      refine ⟨3215848722646345331660215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17151193187447175102187813 3215848722646345331660215)
                      ·
                        rfl

theorem cell23_6262843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 4].length) (baseStart_6262843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262843 prefixEnd_6262843 := by exact prefixLift 6262843
  have htrace : WordTrace (prefixWord ++ tailWord_6262843) baseStart_6262843 baseEnd_6262843 := by
    simpa [prefixWord, tailWord_6262843, baseEnd_6262843] using wordTrace_append hprefix tailTrace_6262843
  have hstable : (prefixWord ++ tailWord_6262843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262843).length < 2 ^ (prefixWord ++ tailWord_6262843).sum := by decide
  have hdescent : baseEnd_6262843 < baseStart_6262843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262877 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_6262877 : Nat := 118140960795 + 6262877 * 2 ^ 59
def prefixEnd_6262877 : Nat := 4983230072969 + 3 ^ 40 * 6262877 * 2
def baseEnd_6262877 : Nat := 3215866180988598198635059

theorem tailTrace_6262877 : CollatzResearch.WordTrace tailWord_6262877 prefixEnd_6262877 3215866180988598198635059 := by
  unfold tailWord_6262877
  simp only [CollatzResearch.WordTrace]
  refine ⟨228425890131673718080370885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152283926754449145386913923 228425890131673718080370885)
  ·
    refine ⟨42829854399688822140069541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228425890131673718080370885 42829854399688822140069541)
    ·
      refine ⟨8030597699941654151263039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42829854399688822140069541 8030597699941654151263039)
      ·
        refine ⟨12045896549912481226894559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8030597699941654151263039 12045896549912481226894559)
        ·
          refine ⟨18068844824868721840341839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12045896549912481226894559 18068844824868721840341839)
          ·
            refine ⟨27103267237303082760512759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18068844824868721840341839 27103267237303082760512759)
            ·
              refine ⟨40654900855954624140769139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27103267237303082760512759 40654900855954624140769139)
              ·
                refine ⟨60982351283931936211153709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40654900855954624140769139 60982351283931936211153709)
                ·
                  refine ⟨22868381731474476079182641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60982351283931936211153709 22868381731474476079182641)
                  ·
                    refine ⟨17151286298605857059386981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22868381731474476079182641 17151286298605857059386981)
                    ·
                      refine ⟨3215866180988598198635059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17151286298605857059386981 3215866180988598198635059)
                      ·
                        rfl

theorem cell23_6262877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_6262877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262877 prefixEnd_6262877 := by exact prefixLift 6262877
  have htrace : WordTrace (prefixWord ++ tailWord_6262877) baseStart_6262877 baseEnd_6262877 := by
    simpa [prefixWord, tailWord_6262877, baseEnd_6262877] using wordTrace_append hprefix tailTrace_6262877
  have hstable : (prefixWord ++ tailWord_6262877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262877).length < 2 ^ (prefixWord ++ tailWord_6262877).sum := by decide
  have hdescent : baseEnd_6262877 < baseStart_6262877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262878 : List Nat := [4, 4, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_6262878 : Nat := 118140960795 + 6262878 * 2 ^ 59
def prefixEnd_6262878 : Nat := 4983230072969 + 3 ^ 40 * 6262878 * 2
def baseEnd_6262878 : Nat := 1071955564823084231574185

theorem tailTrace_6262878 : CollatzResearch.WordTrace tailWord_6262878 prefixEnd_6262878 1071955564823084231574185 := by
  unfold tailWord_6262878
  simp only [CollatzResearch.WordTrace]
  refine ⟨28553240825583761906394661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152283951069780063500771525 28553240825583761906394661)
  ·
    refine ⟨5353732654796955357448999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28553240825583761906394661 5353732654796955357448999)
    ·
      refine ⟨8030598982195433036173499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5353732654796955357448999 8030598982195433036173499)
      ·
        refine ⟨12045898473293149554260249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8030598982195433036173499 12045898473293149554260249)
        ·
          refine ⟨9034423854969862165695187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12045898473293149554260249 9034423854969862165695187)
          ·
            refine ⟨13551635782454793248542781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9034423854969862165695187 13551635782454793248542781)
            ·
              refine ⟨5081863418420547468203543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13551635782454793248542781 5081863418420547468203543)
              ·
                refine ⟨7622795127630821202305315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5081863418420547468203543 7622795127630821202305315)
                ·
                  refine ⟨11434192691446231803457973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7622795127630821202305315 11434192691446231803457973)
                  ·
                    refine ⟨1071955564823084231574185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11434192691446231803457973 1071955564823084231574185)
                    ·
                      rfl

theorem cell23_6262878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_6262878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262878 prefixEnd_6262878 := by exact prefixLift 6262878
  have htrace : WordTrace (prefixWord ++ tailWord_6262878) baseStart_6262878 baseEnd_6262878 := by
    simpa [prefixWord, tailWord_6262878, baseEnd_6262878] using wordTrace_append hprefix tailTrace_6262878
  have hstable : (prefixWord ++ tailWord_6262878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262878).length < 2 ^ (prefixWord ++ tailWord_6262878).sum := by decide
  have hdescent : baseEnd_6262878 < baseStart_6262878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262880 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 3]
def baseStart_6262880 : Nat := 118140960795 + 6262880 * 2 ^ 59
def prefixEnd_6262880 : Nat := 4983230072969 + 3 ^ 40 * 6262880 * 2
def baseEnd_6262880 : Nat := 3215867721430561686897545

theorem tailTrace_6262880 : CollatzResearch.WordTrace tailWord_6262880 prefixEnd_6262880 3215867721430561686897545 := by
  unfold tailWord_6262880
  simp only [CollatzResearch.WordTrace]
  refine ⟨114212999775331424796365047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152283999700441899728486729 114212999775331424796365047)
  ·
    refine ⟨171319499662997137194547571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114212999775331424796365047 171319499662997137194547571)
    ·
      refine ⟨256979249494495705791821357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171319499662997137194547571 256979249494495705791821357)
      ·
        refine ⟨96367218560435889671933009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256979249494495705791821357 96367218560435889671933009)
        ·
          refine ⟨72275413920326917253949757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96367218560435889671933009 72275413920326917253949757)
          ·
            refine ⟨27103280220122593970231159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72275413920326917253949757 27103280220122593970231159)
            ·
              refine ⟨40654920330183890955346739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27103280220122593970231159 40654920330183890955346739)
              ·
                refine ⟨60982380495275836433020109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40654920330183890955346739 60982380495275836433020109)
                ·
                  refine ⟨22868392685728438662382541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60982380495275836433020109 22868392685728438662382541)
                  ·
                    refine ⟨8575647257148164498393453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22868392685728438662382541 8575647257148164498393453)
                    ·
                      refine ⟨3215867721430561686897545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8575647257148164498393453 3215867721430561686897545)
                      ·
                        rfl

theorem cell23_6262880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_6262880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262880 prefixEnd_6262880 := by exact prefixLift 6262880
  have htrace : WordTrace (prefixWord ++ tailWord_6262880) baseStart_6262880 baseEnd_6262880 := by
    simpa [prefixWord, tailWord_6262880, baseEnd_6262880] using wordTrace_append hprefix tailTrace_6262880
  have hstable : (prefixWord ++ tailWord_6262880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262880).length < 2 ^ (prefixWord ++ tailWord_6262880).sum := by decide
  have hdescent : baseEnd_6262880 < baseStart_6262880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262898 : List Nat := [3, 2, 1, 2, 2, 2, 4, 2, 1, 2, 2]
def baseStart_6262898 : Nat := 118140960795 + 6262898 * 2 ^ 59
def prefixEnd_6262898 : Nat := 4983230072969 + 3 ^ 40 * 6262898 * 2
def baseEnd_6262898 : Nat := 3215876964082342616472463

theorem tailTrace_6262898 : CollatzResearch.WordTrace tailWord_6262898 prefixEnd_6262898 3215876964082342616472463 := by
  unfold tailWord_6262898
  simp only [CollatzResearch.WordTrace]
  refine ⟨57106664016149409666721337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152284437376398425777923565 57106664016149409666721337)
  ·
    refine ⟨42829998012112057250041003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57106664016149409666721337 42829998012112057250041003)
    ·
      refine ⟨64244997018168085875061505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42829998012112057250041003 64244997018168085875061505)
      ·
        refine ⟨48183747763626064406296129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64244997018168085875061505 48183747763626064406296129)
        ·
          refine ⟨36137810822719548304722097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48183747763626064406296129 36137810822719548304722097)
          ·
            refine ⟨27103358117039661228541573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36137810822719548304722097 27103358117039661228541573)
            ·
              refine ⟨5081879646944936480351545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27103358117039661228541573 5081879646944936480351545)
              ·
                refine ⟨3811409735208702360263659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5081879646944936480351545 3811409735208702360263659)
                ·
                  refine ⟨5717114602813053540395489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3811409735208702360263659 5717114602813053540395489)
                  ·
                    refine ⟨4287835952109790155296617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5717114602813053540395489 4287835952109790155296617)
                    ·
                      refine ⟨3215876964082342616472463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4287835952109790155296617 3215876964082342616472463)
                      ·
                        rfl

theorem cell23_6262898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_6262898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262898 prefixEnd_6262898 := by exact prefixLift 6262898
  have htrace : WordTrace (prefixWord ++ tailWord_6262898) baseStart_6262898 baseEnd_6262898 := by
    simpa [prefixWord, tailWord_6262898, baseEnd_6262898] using wordTrace_append hprefix tailTrace_6262898
  have hstable : (prefixWord ++ tailWord_6262898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262898).length < 2 ^ (prefixWord ++ tailWord_6262898).sum := by decide
  have hdescent : baseEnd_6262898 < baseStart_6262898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262930 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 1, 8]
def baseStart_6262930 : Nat := 118140960795 + 6262930 * 2 ^ 59
def prefixEnd_6262930 : Nat := 4983230072969 + 3 ^ 40 * 6262930 * 2
def baseEnd_6262930 : Nat := 1071964465154428830424105

theorem tailTrace_6262930 : CollatzResearch.WordTrace tailWord_6262930 prefixEnd_6262930 1071964465154428830424105 := by
  unfold tailWord_6262930
  simp only [CollatzResearch.WordTrace]
  refine ⟨57106955800120427033012561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152285215466987805421366829 57106955800120427033012561)
  ·
    refine ⟨42830216850090320274759421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57106955800120427033012561 42830216850090320274759421)
    ·
      refine ⟨16061331318783870103034783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42830216850090320274759421 16061331318783870103034783)
      ·
        refine ⟨24091996978175805154552175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16061331318783870103034783 24091996978175805154552175)
        ·
          refine ⟨36137995467263707731828263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24091996978175805154552175 36137995467263707731828263)
          ·
            refine ⟨54206993200895561597742395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36137995467263707731828263 54206993200895561597742395)
            ·
              refine ⟨81310489801343342396613593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54206993200895561597742395 81310489801343342396613593)
              ·
                refine ⟨60982867351007506797460195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81310489801343342396613593 60982867351007506797460195)
                ·
                  refine ⟨91474301026511260196190293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60982867351007506797460195 91474301026511260196190293)
                  ·
                    refine ⟨1071964465154428830424105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 91474301026511260196190293 1071964465154428830424105)
                    ·
                      rfl

theorem cell23_6262930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_6262930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262930 prefixEnd_6262930 := by exact prefixLift 6262930
  have htrace : WordTrace (prefixWord ++ tailWord_6262930) baseStart_6262930 baseEnd_6262930 := by
    simpa [prefixWord, tailWord_6262930, baseEnd_6262930] using wordTrace_append hprefix tailTrace_6262930
  have hstable : (prefixWord ++ tailWord_6262930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262930).length < 2 ^ (prefixWord ++ tailWord_6262930).sum := by decide
  have hdescent : baseEnd_6262930 < baseStart_6262930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262940 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 1, 3, 5]
def baseStart_6262940 : Nat := 118140960795 + 6262940 * 2 ^ 59
def prefixEnd_6262940 : Nat := 4983230072969 + 3 ^ 40 * 6262940 * 2
def baseEnd_6262940 : Nat := 3215898530269831452147269

theorem tailTrace_6262940 : CollatzResearch.WordTrace tailWord_6262940 prefixEnd_6262940 3215898530269831452147269 := by
  unfold tailWord_6262940
  simp only [CollatzResearch.WordTrace]
  refine ⟨114214093965222739919957137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152285458620296986559942849 114214093965222739919957137)
  ·
    refine ⟨85660570473917054939967853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114214093965222739919957137 85660570473917054939967853)
    ·
      refine ⟨32122713927718895602487945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85660570473917054939967853 32122713927718895602487945)
      ·
        refine ⟨24092035445789171701865959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32122713927718895602487945 24092035445789171701865959)
        ·
          refine ⟨36138053168683757552798939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24092035445789171701865959 36138053168683757552798939)
          ·
            refine ⟨54207079753025636329198409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36138053168683757552798939 54207079753025636329198409)
            ·
              refine ⟨40655309814769227246898807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54207079753025636329198409 40655309814769227246898807)
              ·
                refine ⟨60982964722153840870348211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40655309814769227246898807 60982964722153840870348211)
                ·
                  refine ⟨91474447083230761305522317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60982964722153840870348211 91474447083230761305522317)
                  ·
                    refine ⟨34302917656211535489570869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91474447083230761305522317 34302917656211535489570869)
                    ·
                      refine ⟨3215898530269831452147269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34302917656211535489570869 3215898530269831452147269)
                      ·
                        rfl

theorem cell23_6262940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_6262940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262940 prefixEnd_6262940 := by exact prefixLift 6262940
  have htrace : WordTrace (prefixWord ++ tailWord_6262940) baseStart_6262940 baseEnd_6262940 := by
    simpa [prefixWord, tailWord_6262940, baseEnd_6262940] using wordTrace_append hprefix tailTrace_6262940
  have hstable : (prefixWord ++ tailWord_6262940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262940).length < 2 ^ (prefixWord ++ tailWord_6262940).sum := by decide
  have hdescent : baseEnd_6262940 < baseStart_6262940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262941 : List Nat := [1, 4, 2, 1, 1, 3, 4, 1, 1, 3, 2]
def baseStart_6262941 : Nat := 118140960795 + 6262941 * 2 ^ 59
def prefixEnd_6262941 : Nat := 4983230072969 + 3 ^ 40 * 6262941 * 2
def baseEnd_6262941 : Nat := 3215899043750485948234765

theorem tailTrace_6262941 : CollatzResearch.WordTrace tailWord_6262941 prefixEnd_6262941 3215899043750485948234765 := by
  unfold tailWord_6262941
  simp only [CollatzResearch.WordTrace]
  refine ⟨228428224403441857010700677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152285482935627904673800451 228428224403441857010700677)
  ·
    refine ⟨42830292075645348189506377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228428224403441857010700677 42830292075645348189506377)
    ·
      refine ⟨32122719056734011142129783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42830292075645348189506377 32122719056734011142129783)
      ·
        refine ⟨48184078585101016713194675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32122719056734011142129783 48184078585101016713194675)
        ·
          refine ⟨72276117877651525069792013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48184078585101016713194675 72276117877651525069792013)
          ·
            refine ⟨27103544204119321901172005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72276117877651525069792013 27103544204119321901172005)
            ·
              refine ⟨5081914538272372856469751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27103544204119321901172005 5081914538272372856469751)
              ·
                refine ⟨7622871807408559284704627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5081914538272372856469751 7622871807408559284704627)
                ·
                  refine ⟨11434307711112838927056941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7622871807408559284704627 11434307711112838927056941)
                  ·
                    refine ⟨4287865391667314597646353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11434307711112838927056941 4287865391667314597646353)
                    ·
                      refine ⟨3215899043750485948234765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4287865391667314597646353 3215899043750485948234765)
                      ·
                        rfl

theorem cell23_6262941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_6262941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262941 prefixEnd_6262941 := by exact prefixLift 6262941
  have htrace : WordTrace (prefixWord ++ tailWord_6262941) baseStart_6262941 baseEnd_6262941 := by
    simpa [prefixWord, tailWord_6262941, baseEnd_6262941] using wordTrace_append hprefix tailTrace_6262941
  have hstable : (prefixWord ++ tailWord_6262941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262941).length < 2 ^ (prefixWord ++ tailWord_6262941).sum := by decide
  have hdescent : baseEnd_6262941 < baseStart_6262941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262948 : List Nat := [2, 3, 1, 2, 5, 1, 1, 2, 2, 1, 3]
def baseStart_6262948 : Nat := 118140960795 + 6262948 * 2 ^ 59
def prefixEnd_6262948 : Nat := 4983230072969 + 3 ^ 40 * 6262948 * 2
def baseEnd_6262948 : Nat := 3215902638115067420847233

theorem tailTrace_6262948 : CollatzResearch.WordTrace tailWord_6262948 prefixEnd_6262948 3215902638115067420847233 := by
  unfold tailWord_6262948
  simp only [CollatzResearch.WordTrace]
  refine ⟨114214239857208248603102749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152285653142944331470803665 114214239857208248603102749)
  ·
    refine ⟨42830339946453093226163531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114214239857208248603102749 42830339946453093226163531)
    ·
      refine ⟨64245509919679639839245297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42830339946453093226163531 64245509919679639839245297)
      ·
        refine ⟨48184132439759729879433973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64245509919679639839245297 48184132439759729879433973)
        ·
          refine ⟨4517262416227474676196935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48184132439759729879433973 4517262416227474676196935)
          ·
            refine ⟨6775893624341212014295403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4517262416227474676196935 6775893624341212014295403)
            ·
              refine ⟨10163840436511818021443105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6775893624341212014295403 10163840436511818021443105)
              ·
                refine ⟨7622880327383863516082329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10163840436511818021443105 7622880327383863516082329)
                ·
                  refine ⟨5717160245537897637061747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7622880327383863516082329 5717160245537897637061747)
                  ·
                    refine ⟨8575740368306846455592621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5717160245537897637061747 8575740368306846455592621)
                    ·
                      refine ⟨3215902638115067420847233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8575740368306846455592621 3215902638115067420847233)
                      ·
                        rfl

theorem cell23_6262948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_6262948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262948 prefixEnd_6262948 := by exact prefixLift 6262948
  have htrace : WordTrace (prefixWord ++ tailWord_6262948) baseStart_6262948 baseEnd_6262948 := by
    simpa [prefixWord, tailWord_6262948, baseEnd_6262948] using wordTrace_append hprefix tailTrace_6262948
  have hstable : (prefixWord ++ tailWord_6262948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262948).length < 2 ^ (prefixWord ++ tailWord_6262948).sum := by decide
  have hdescent : baseEnd_6262948 < baseStart_6262948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262971 : List Nat := [1, 1, 1, 1, 1, 2, 9, 1, 2, 2, 2]
def baseStart_6262971 : Nat := 118140960795 + 6262971 * 2 ^ 59
def prefixEnd_6262971 : Nat := 4983230072969 + 3 ^ 40 * 6262971 * 2
def baseEnd_6262971 : Nat := 3215914448170120830859627

theorem tailTrace_6262971 : CollatzResearch.WordTrace tailWord_6262971 prefixEnd_6262971 3215914448170120830859627 := by
  unfold tailWord_6262971
  simp only [CollatzResearch.WordTrace]
  refine ⟨228429318593333172134292767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152286212395555448089528511 228429318593333172134292767)
  ·
    refine ⟨342643977889999758201439151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228429318593333172134292767 342643977889999758201439151)
    ·
      refine ⟨513965966834999637302158727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342643977889999758201439151 513965966834999637302158727)
      ·
        refine ⟨770948950252499455953238091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513965966834999637302158727 770948950252499455953238091)
        ·
          refine ⟨1156423425378749183929857137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 770948950252499455953238091 1156423425378749183929857137)
          ·
            refine ⟨867317569034061887947392853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1156423425378749183929857137 867317569034061887947392853)
            ·
              refine ⟨5081938881058956374691755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 867317569034061887947392853 5081938881058956374691755)
              ·
                refine ⟨7622908321588434562037633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5081938881058956374691755 7622908321588434562037633)
                ·
                  refine ⟨5717181241191325921528225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7622908321588434562037633 5717181241191325921528225)
                  ·
                    refine ⟨4287885930893494441146169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5717181241191325921528225 4287885930893494441146169)
                    ·
                      refine ⟨3215914448170120830859627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4287885930893494441146169 3215914448170120830859627)
                      ·
                        rfl

theorem cell23_6262971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 2, 2, 2].length) (baseStart_6262971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262971 prefixEnd_6262971 := by exact prefixLift 6262971
  have htrace : WordTrace (prefixWord ++ tailWord_6262971) baseStart_6262971 baseEnd_6262971 := by
    simpa [prefixWord, tailWord_6262971, baseEnd_6262971] using wordTrace_append hprefix tailTrace_6262971
  have hstable : (prefixWord ++ tailWord_6262971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262971).length < 2 ^ (prefixWord ++ tailWord_6262971).sum := by decide
  have hdescent : baseEnd_6262971 < baseStart_6262971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6262994 : List Nat := [3, 2, 2, 2, 1, 2, 3, 3, 5]
def baseStart_6262994 : Nat := 118140960795 + 6262994 * 2 ^ 59
def prefixEnd_6262994 : Nat := 4983230072969 + 3 ^ 40 * 6262994 * 2
def baseEnd_6262994 : Nat := 357325139802797137874669

theorem tailTrace_6262994 : CollatzResearch.WordTrace tailWord_6262994 prefixEnd_6262994 357325139802797137874669 := by
  unfold tailWord_6262994
  simp only [CollatzResearch.WordTrace]
  refine ⟨57107539368062461765595009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152286771648166564708253357 57107539368062461765595009)
  ·
    refine ⟨42830654526046846324196257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57107539368062461765595009 42830654526046846324196257)
    ·
      refine ⟨32122990894535134743147193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42830654526046846324196257 32122990894535134743147193)
      ·
        refine ⟨24092243170901351057360395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32122990894535134743147193 24092243170901351057360395)
        ·
          refine ⟨36138364756352026586040593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24092243170901351057360395 36138364756352026586040593)
          ·
            refine ⟨27103773567264019939530445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36138364756352026586040593 27103773567264019939530445)
            ·
              refine ⟨10163915087724007477323917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27103773567264019939530445 10163915087724007477323917)
              ·
                refine ⟨3811468157896502803996469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10163915087724007477323917 3811468157896502803996469)
                ·
                  refine ⟨357325139802797137874669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3811468157896502803996469 357325139802797137874669)
                  ·
                    rfl

theorem cell23_6262994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 3, 5].length) (baseStart_6262994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6262994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6262994 prefixEnd_6262994 := by exact prefixLift 6262994
  have htrace : WordTrace (prefixWord ++ tailWord_6262994) baseStart_6262994 baseEnd_6262994 := by
    simpa [prefixWord, tailWord_6262994, baseEnd_6262994] using wordTrace_append hprefix tailTrace_6262994
  have hstable : (prefixWord ++ tailWord_6262994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6262994).length < 2 ^ (prefixWord ++ tailWord_6262994).sum := by decide
  have hdescent : baseEnd_6262994 < baseStart_6262994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6262994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263011 : List Nat := [1, 1, 1, 8, 2, 1, 1, 1, 7]
def baseStart_6263011 : Nat := 118140960795 + 6263011 * 2 ^ 59
def prefixEnd_6263011 : Nat := 4983230072969 + 3 ^ 40 * 6263011 * 2
def baseEnd_6263011 : Nat := 357326109710700074928827

theorem tailTrace_6263011 : CollatzResearch.WordTrace tailWord_6263011 prefixEnd_6263011 357326109710700074928827 := by
  unfold tailWord_6263011
  simp only [CollatzResearch.WordTrace]
  refine ⟨228430777513188258965748887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152287185008792172643832591 228430777513188258965748887)
  ·
    refine ⟨342646166269782388448623331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228430777513188258965748887 342646166269782388448623331)
    ·
      refine ⟨513969249404673582672934997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342646166269782388448623331 513969249404673582672934997)
      ·
        refine ⟨6023077141461018546948457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 513969249404673582672934997 6023077141461018546948457)
        ·
          refine ⟨4517307856095763910211343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6023077141461018546948457 4517307856095763910211343)
          ·
            refine ⟨6775961784143645865317015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4517307856095763910211343 6775961784143645865317015)
            ·
              refine ⟨10163942676215468797975523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6775961784143645865317015 10163942676215468797975523)
              ·
                refine ⟨15245914014323203196963285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10163942676215468797975523 15245914014323203196963285)
                ·
                  refine ⟨357326109710700074928827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15245914014323203196963285 357326109710700074928827)
                  ·
                    rfl

theorem cell23_6263011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 7].length) (baseStart_6263011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263011 prefixEnd_6263011 := by exact prefixLift 6263011
  have htrace : WordTrace (prefixWord ++ tailWord_6263011) baseStart_6263011 baseEnd_6263011 := by
    simpa [prefixWord, tailWord_6263011, baseEnd_6263011] using wordTrace_append hprefix tailTrace_6263011
  have hstable : (prefixWord ++ tailWord_6263011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263011).length < 2 ^ (prefixWord ++ tailWord_6263011).sum := by decide
  have hdescent : baseEnd_6263011 < baseStart_6263011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263027 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 1, 6, 2]
def baseStart_6263027 : Nat := 118140960795 + 6263027 * 2 ^ 59
def prefixEnd_6263027 : Nat := 4983230072969 + 3 ^ 40 * 6263027 * 2
def baseEnd_6263027 : Nat := 3215943203086772611759369

theorem tailTrace_6263027 : CollatzResearch.WordTrace tailWord_6263027 prefixEnd_6263027 3215943203086772611759369 := by
  unfold tailWord_6263027
  simp only [CollatzResearch.WordTrace]
  refine ⟨228431361081130293698331335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152287574054086862465554223 228431361081130293698331335)
  ·
    refine ⟨342647041621695440547497003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228431361081130293698331335 342647041621695440547497003)
    ·
      refine ⟨513970562432543160821245505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342647041621695440547497003 513970562432543160821245505)
      ·
        refine ⟨385477921824407370615934129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 513970562432543160821245505 385477921824407370615934129)
        ·
          refine ⟨289108441368305527961950597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385477921824407370615934129 289108441368305527961950597)
          ·
            refine ⟨54207832756557286492865737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 289108441368305527961950597 54207832756557286492865737)
            ·
              refine ⟨40655874567417964869649303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54207832756557286492865737 40655874567417964869649303)
              ·
                refine ⟨60983811851126947304473955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40655874567417964869649303 60983811851126947304473955)
                ·
                  refine ⟨91475717776690420956710933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60983811851126947304473955 91475717776690420956710933)
                  ·
                    refine ⟨4287924270782363482345825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 91475717776690420956710933 4287924270782363482345825)
                    ·
                      refine ⟨3215943203086772611759369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4287924270782363482345825 3215943203086772611759369)
                      ·
                        rfl

theorem cell23_6263027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 6, 2].length) (baseStart_6263027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263027 prefixEnd_6263027 := by exact prefixLift 6263027
  have htrace : WordTrace (prefixWord ++ tailWord_6263027) baseStart_6263027 baseEnd_6263027 := by
    simpa [prefixWord, tailWord_6263027, baseEnd_6263027] using wordTrace_append hprefix tailTrace_6263027
  have hstable : (prefixWord ++ tailWord_6263027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263027).length < 2 ^ (prefixWord ++ tailWord_6263027).sum := by decide
  have hdescent : baseEnd_6263027 < baseStart_6263027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263037 : List Nat := [1, 4, 1, 1, 1, 1, 1, 6, 3, 4]
def baseStart_6263037 : Nat := 118140960795 + 6263037 * 2 ^ 59
def prefixEnd_6263037 : Nat := 4983230072969 + 3 ^ 40 * 6263037 * 2
def baseEnd_6263037 : Nat := 1071982779297772524211441

theorem tailTrace_6263037 : CollatzResearch.WordTrace tailWord_6263037 prefixEnd_6263037 1071982779297772524211441 := by
  unfold tailWord_6263037
  simp only [CollatzResearch.WordTrace]
  refine ⟨228431725811094065406195365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152287817207396043604130243 228431725811094065406195365)
  ·
    refine ⟨42830948589580137263661631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228431725811094065406195365 42830948589580137263661631)
    ·
      refine ⟨64246422884370205895492447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42830948589580137263661631 64246422884370205895492447)
      ·
        refine ⟨96369634326555308843238671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64246422884370205895492447 96369634326555308843238671)
        ·
          refine ⟨144554451489832963264858007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96369634326555308843238671 144554451489832963264858007)
          ·
            refine ⟨216831677234749444897287011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144554451489832963264858007 216831677234749444897287011)
            ·
              refine ⟨325247515852124167345930517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216831677234749444897287011 325247515852124167345930517)
              ·
                refine ⟨15245977305568320344340493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 325247515852124167345930517 15245977305568320344340493)
                ·
                  refine ⟨5717241489588120129127685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15245977305568320344340493 5717241489588120129127685)
                  ·
                    refine ⟨1071982779297772524211441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5717241489588120129127685 1071982779297772524211441)
                    ·
                      rfl

theorem cell23_6263037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_6263037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263037 prefixEnd_6263037 := by exact prefixLift 6263037
  have htrace : WordTrace (prefixWord ++ tailWord_6263037) baseStart_6263037 baseEnd_6263037 := by
    simpa [prefixWord, tailWord_6263037, baseEnd_6263037] using wordTrace_append hprefix tailTrace_6263037
  have hstable : (prefixWord ++ tailWord_6263037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263037).length < 2 ^ (prefixWord ++ tailWord_6263037).sum := by decide
  have hdescent : baseEnd_6263037 < baseStart_6263037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263040 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 4]
def baseStart_6263040 : Nat := 118140960795 + 6263040 * 2 ^ 59
def prefixEnd_6263040 : Nat := 4983230072969 + 3 ^ 40 * 6263040 * 2
def baseEnd_6263040 : Nat := 3215949878335281060896809

theorem tailTrace_6263040 : CollatzResearch.WordTrace tailWord_6263040 prefixEnd_6263040 3215949878335281060896809 := by
  unfold tailWord_6263040
  simp only [CollatzResearch.WordTrace]
  refine ⟨114215917615041598459277287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152287890153388797945703049 114215917615041598459277287)
  ·
    refine ⟨171323876422562397688915931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114215917615041598459277287 171323876422562397688915931)
    ·
      refine ⟨256985814633843596533373897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171323876422562397688915931 256985814633843596533373897)
      ·
        refine ⟨192739360975382697400030423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256985814633843596533373897 192739360975382697400030423)
        ·
          refine ⟨289109041463074046100045635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192739360975382697400030423 289109041463074046100045635)
          ·
            refine ⟨433663562194611069150068453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289109041463074046100045635 433663562194611069150068453)
            ·
              refine ⟨81311917911489575465637835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 433663562194611069150068453 81311917911489575465637835)
              ·
                refine ⟨121967876867234363198456753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81311917911489575465637835 121967876867234363198456753)
                ·
                  refine ⟨91475907650425772398842565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121967876867234363198456753 91475907650425772398842565)
                  ·
                    refine ⟨17151732684454832324782981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91475907650425772398842565 17151732684454832324782981)
                    ·
                      refine ⟨3215949878335281060896809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17151732684454832324782981 3215949878335281060896809)
                      ·
                        rfl

theorem cell23_6263040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_6263040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263040 prefixEnd_6263040 := by exact prefixLift 6263040
  have htrace : WordTrace (prefixWord ++ tailWord_6263040) baseStart_6263040 baseEnd_6263040 := by
    simpa [prefixWord, tailWord_6263040, baseEnd_6263040] using wordTrace_append hprefix tailTrace_6263040
  have hstable : (prefixWord ++ tailWord_6263040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263040).length < 2 ^ (prefixWord ++ tailWord_6263040).sum := by decide
  have hdescent : baseEnd_6263040 < baseStart_6263040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263050 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 10]
def baseStart_6263050 : Nat := 118140960795 + 6263050 * 2 ^ 59
def prefixEnd_6263050 : Nat := 4983230072969 + 3 ^ 40 * 6263050 * 2
def baseEnd_6263050 : Nat := 357328334793536224641307

theorem tailTrace_6263050 : CollatzResearch.WordTrace tailWord_6263050 prefixEnd_6263050 357328334793536224641307 := by
  unfold tailWord_6263050
  simp only [CollatzResearch.WordTrace]
  refine ⟨57108049990011742156604651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152288133306697979084279069 57108049990011742156604651)
  ·
    refine ⟨85662074985017613234906977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57108049990011742156604651 85662074985017613234906977)
    ·
      refine ⟨64246556238763209926180233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85662074985017613234906977 64246556238763209926180233)
      ·
        refine ⟨48184917179072407444635175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64246556238763209926180233 48184917179072407444635175)
        ·
          refine ⟨72277375768608611166952763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48184917179072407444635175 72277375768608611166952763)
          ·
            refine ⟨108416063652912916750429145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72277375768608611166952763 108416063652912916750429145)
            ·
              refine ⟨81312047739684687562821859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108416063652912916750429145 81312047739684687562821859)
              ·
                refine ⟨121968071609527031344232789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81312047739684687562821859 121968071609527031344232789)
                ·
                  refine ⟨357328334793536224641307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 121968071609527031344232789 357328334793536224641307)
                  ·
                    rfl

theorem cell23_6263050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 10].length) (baseStart_6263050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263050 prefixEnd_6263050 := by exact prefixLift 6263050
  have htrace : WordTrace (prefixWord ++ tailWord_6263050) baseStart_6263050 baseEnd_6263050 := by
    simpa [prefixWord, tailWord_6263050, baseEnd_6263050] using wordTrace_append hprefix tailTrace_6263050
  have hstable : (prefixWord ++ tailWord_6263050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263050).length < 2 ^ (prefixWord ++ tailWord_6263050).sum := by decide
  have hdescent : baseEnd_6263050 < baseStart_6263050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263071 : List Nat := [1, 1, 2, 4, 3, 2, 1, 4, 1, 4]
def baseStart_6263071 : Nat := 118140960795 + 6263071 * 2 ^ 59
def prefixEnd_6263071 : Nat := 4983230072969 + 3 ^ 40 * 6263071 * 2
def baseEnd_6263071 : Nat := 1071988598745190146536389

theorem tailTrace_6263071 : CollatzResearch.WordTrace tailWord_6263071 prefixEnd_6263071 1071988598745190146536389 := by
  unfold tailWord_6263071
  simp only [CollatzResearch.WordTrace]
  refine ⟨228432965892970889212933067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152288643928647259475288711 228432965892970889212933067)
  ·
    refine ⟨342649448839456333819399601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228432965892970889212933067 342649448839456333819399601)
    ·
      refine ⟨256987086629592250364549701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342649448839456333819399601 256987086629592250364549701)
      ·
        refine ⟨48185078743048546943353069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 256987086629592250364549701 48185078743048546943353069)
        ·
          refine ⟨18069404528643205103757401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48185078743048546943353069 18069404528643205103757401)
          ·
            refine ⟨13552053396482403827818051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18069404528643205103757401 13552053396482403827818051)
            ·
              refine ⟨20328080094723605741727077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13552053396482403827818051 20328080094723605741727077)
              ·
                refine ⟨3811515017760676076573827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20328080094723605741727077 3811515017760676076573827)
                ·
                  refine ⟨5717272526641014114860741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3811515017760676076573827 5717272526641014114860741)
                  ·
                    refine ⟨1071988598745190146536389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5717272526641014114860741 1071988598745190146536389)
                    ·
                      rfl

theorem cell23_6263071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 4, 1, 4].length) (baseStart_6263071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263071 prefixEnd_6263071 := by exact prefixLift 6263071
  have htrace : WordTrace (prefixWord ++ tailWord_6263071) baseStart_6263071 baseEnd_6263071 := by
    simpa [prefixWord, tailWord_6263071, baseEnd_6263071] using wordTrace_append hprefix tailTrace_6263071
  have hstable : (prefixWord ++ tailWord_6263071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263071).length < 2 ^ (prefixWord ++ tailWord_6263071).sum := by decide
  have hdescent : baseEnd_6263071 < baseStart_6263071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263104 : List Nat := [2, 1, 1, 2, 2, 1, 2, 5, 2, 3, 2]
def baseStart_6263104 : Nat := 118140960795 + 6263104 * 2 ^ 59
def prefixEnd_6263104 : Nat := 4983230072969 + 3 ^ 40 * 6263104 * 2
def baseEnd_6263104 : Nat := 3215982741097168810496515

theorem tailTrace_6263104 : CollatzResearch.WordTrace tailWord_6263104 prefixEnd_6263104 3215982741097168810496515 := by
  unfold tailWord_6263104
  simp only [CollatzResearch.WordTrace]
  refine ⟨114217084750925667924442183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152289446334567557232589577 114217084750925667924442183)
  ·
    refine ⟨171325627126388501886663275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114217084750925667924442183 171325627126388501886663275)
    ·
      refine ⟨256988440689582752829994913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171325627126388501886663275 256988440689582752829994913)
      ·
        refine ⟨192741330517187064622496185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256988440689582752829994913 192741330517187064622496185)
        ·
          refine ⟨144555997887890298466872139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192741330517187064622496185 144555997887890298466872139)
          ·
            refine ⟨216833996831835447700308209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144555997887890298466872139 216833996831835447700308209)
            ·
              refine ⟨162625497623876585775231157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216833996831835447700308209 162625497623876585775231157)
              ·
                refine ⟨15246140402238429916427921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162625497623876585775231157 15246140402238429916427921)
                ·
                  refine ⟨11434605301678822437320941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15246140402238429916427921 11434605301678822437320941)
                  ·
                    refine ⟨4287976988129558413995353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11434605301678822437320941 4287976988129558413995353)
                    ·
                      refine ⟨3215982741097168810496515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4287976988129558413995353 3215982741097168810496515)
                      ·
                        rfl

theorem cell23_6263104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 2, 3, 2].length) (baseStart_6263104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263104 prefixEnd_6263104 := by exact prefixLift 6263104
  have htrace : WordTrace (prefixWord ++ tailWord_6263104) baseStart_6263104 baseEnd_6263104 := by
    simpa [prefixWord, tailWord_6263104, baseEnd_6263104] using wordTrace_append hprefix tailTrace_6263104
  have hstable : (prefixWord ++ tailWord_6263104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263104).length < 2 ^ (prefixWord ++ tailWord_6263104).sum := by decide
  have hdescent : baseEnd_6263104 < baseStart_6263104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263144 : List Nat := [2, 1, 4, 2, 2, 1, 3, 1, 1, 6]
def baseStart_6263144 : Nat := 118140960795 + 6263144 * 2 ^ 59
def prefixEnd_6263144 : Nat := 4983230072969 + 3 ^ 40 * 6263144 * 2
def baseEnd_6263144 : Nat := 1072001093441116217998777

theorem tailTrace_6263144 : CollatzResearch.WordTrace tailWord_6263144 prefixEnd_6263144 1072001093441116217998777 := by
  unfold tailWord_6263144
  simp only [CollatzResearch.WordTrace]
  refine ⟨114217814210853211340170243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152290418947804281786893657 114217814210853211340170243)
  ·
    refine ⟨171326721316279817010255365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114217814210853211340170243 171326721316279817010255365)
    ·
      refine ⟨32123760246802465689422881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171326721316279817010255365 32123760246802465689422881)
      ·
        refine ⟨24092820185101849267067161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32123760246802465689422881 24092820185101849267067161)
        ·
          refine ⟨18069615138826386950300371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24092820185101849267067161 18069615138826386950300371)
          ·
            refine ⟨27104422708239580425450557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18069615138826386950300371 27104422708239580425450557)
            ·
              refine ⟨10164158515589842659543959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27104422708239580425450557 10164158515589842659543959)
              ·
                refine ⟨15246237773384763989315939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10164158515589842659543959 15246237773384763989315939)
                ·
                  refine ⟨22869356660077145983973909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15246237773384763989315939 22869356660077145983973909)
                  ·
                    refine ⟨1072001093441116217998777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22869356660077145983973909 1072001093441116217998777)
                    ·
                      rfl

theorem cell23_6263144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_6263144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263144 prefixEnd_6263144 := by exact prefixLift 6263144
  have htrace : WordTrace (prefixWord ++ tailWord_6263144) baseStart_6263144 baseEnd_6263144 := by
    simpa [prefixWord, tailWord_6263144, baseEnd_6263144] using wordTrace_append hprefix tailTrace_6263144
  have hstable : (prefixWord ++ tailWord_6263144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263144).length < 2 ^ (prefixWord ++ tailWord_6263144).sum := by decide
  have hdescent : baseEnd_6263144 < baseStart_6263144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263236 : List Nat := [2, 3, 3, 2, 3, 1, 2, 2, 1, 2, 2]
def baseStart_6263236 : Nat := 118140960795 + 6263236 * 2 ^ 59
def prefixEnd_6263236 : Nat := 4983230072969 + 3 ^ 40 * 6263236 * 2
def baseEnd_6263236 : Nat := 3216050520543562294045909

theorem tailTrace_6263236 : CollatzResearch.WordTrace tailWord_6263236 prefixEnd_6263236 3216050520543562294045909 := by
  unfold tailWord_6263236
  simp only [CollatzResearch.WordTrace]
  refine ⟨114219491968686561196344781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152292655958248748261793041 114219491968686561196344781)
  ·
    refine ⟨42832309488257460448629293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114219491968686561196344781 42832309488257460448629293)
    ·
      refine ⟨16062116058096547668235985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42832309488257460448629293 16062116058096547668235985)
      ·
        refine ⟨12046587043572410751176989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16062116058096547668235985 12046587043572410751176989)
        ·
          refine ⟨4517470141339654031691371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12046587043572410751176989 4517470141339654031691371)
          ·
            refine ⟨6776205212009481047537057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4517470141339654031691371 6776205212009481047537057)
            ·
              refine ⟨5082153909007110785652793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6776205212009481047537057 5082153909007110785652793)
              ·
                refine ⟨3811615431755333089239595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5082153909007110785652793 3811615431755333089239595)
                ·
                  refine ⟨5717423147632999633859393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3811615431755333089239595 5717423147632999633859393)
                  ·
                    refine ⟨4288067360724749725394545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5717423147632999633859393 4288067360724749725394545)
                    ·
                      refine ⟨3216050520543562294045909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4288067360724749725394545 3216050520543562294045909)
                      ·
                        rfl

theorem cell23_6263236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_6263236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263236 prefixEnd_6263236 := by exact prefixLift 6263236
  have htrace : WordTrace (prefixWord ++ tailWord_6263236) baseStart_6263236 baseEnd_6263236 := by
    simpa [prefixWord, tailWord_6263236, baseEnd_6263236] using wordTrace_append hprefix tailTrace_6263236
  have hstable : (prefixWord ++ tailWord_6263236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263236).length < 2 ^ (prefixWord ++ tailWord_6263236).sum := by decide
  have hdescent : baseEnd_6263236 < baseStart_6263236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263237 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 5, 4, 4]
def baseStart_6263237 : Nat := 118140960795 + 6263237 * 2 ^ 59
def prefixEnd_6263237 : Nat := 4983230072969 + 3 ^ 40 * 6263237 * 2
def baseEnd_6263237 : Nat := 3216051034024216790133403

theorem tailTrace_6263237 : CollatzResearch.WordTrace tailWord_6263237 prefixEnd_6263237 3216051034024216790133403 := by
  unfold tailWord_6263237
  simp only [CollatzResearch.WordTrace]
  refine ⟨228439020410369499563475965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152292680273579666375650643 228439020410369499563475965)
  ·
    refine ⟨85664632653888562336303487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228439020410369499563475965 85664632653888562336303487)
    ·
      refine ⟨128496948980832843504455231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85664632653888562336303487 128496948980832843504455231)
      ·
        refine ⟨192745423471249265256682847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128496948980832843504455231 192745423471249265256682847)
        ·
          refine ⟨289118135206873897885024271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192745423471249265256682847 289118135206873897885024271)
          ·
            refine ⟨433677202810310846827536407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289118135206873897885024271 433677202810310846827536407)
            ·
              refine ⟨650515804215466270241304611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433677202810310846827536407 650515804215466270241304611)
              ·
                refine ⟨975773706323199405361956917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 650515804215466270241304611 975773706323199405361956917)
                ·
                  refine ⟨91478784967799944252683461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 975773706323199405361956917 91478784967799944252683461)
                  ·
                    refine ⟨17152272181462489547378149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91478784967799944252683461 17152272181462489547378149)
                    ·
                      refine ⟨3216051034024216790133403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17152272181462489547378149 3216051034024216790133403)
                      ·
                        rfl

theorem cell23_6263237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_6263237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263237 prefixEnd_6263237 := by exact prefixLift 6263237
  have htrace : WordTrace (prefixWord ++ tailWord_6263237) baseStart_6263237 baseEnd_6263237 := by
    simpa [prefixWord, tailWord_6263237, baseEnd_6263237] using wordTrace_append hprefix tailTrace_6263237
  have hstable : (prefixWord ++ tailWord_6263237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263237).length < 2 ^ (prefixWord ++ tailWord_6263237).sum := by decide
  have hdescent : baseEnd_6263237 < baseStart_6263237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263241 : List Nat := [1, 2, 1, 1, 2, 1, 4, 3, 4, 2, 2]
def baseStart_6263241 : Nat := 118140960795 + 6263241 * 2 ^ 59
def prefixEnd_6263241 : Nat := 4983230072969 + 3 ^ 40 * 6263241 * 2
def baseEnd_6263241 : Nat := 3216053087946834774483385

theorem tailTrace_6263241 : CollatzResearch.WordTrace tailWord_6263241 prefixEnd_6263241 3216053087946834774483385 := by
  unfold tailWord_6263241
  simp only [CollatzResearch.WordTrace]
  refine ⟨228439166302355008246621577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152292777534903338831081051 228439166302355008246621577)
  ·
    refine ⟨171329374726766256184966183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228439166302355008246621577 171329374726766256184966183)
    ·
      refine ⟨256994062090149384277449275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171329374726766256184966183 256994062090149384277449275)
      ·
        refine ⟨385491093135224076416173913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256994062090149384277449275 385491093135224076416173913)
        ·
          refine ⟨289118319851418057312130435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385491093135224076416173913 289118319851418057312130435)
          ·
            refine ⟨433677479777127085968195653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289118319851418057312130435 433677479777127085968195653)
            ·
              refine ⟨81314527458211328619036685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 433677479777127085968195653 81314527458211328619036685)
              ·
                refine ⟨30492947796829248232138757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81314527458211328619036685 30492947796829248232138757)
                ·
                  refine ⟨5717427711905484043526017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30492947796829248232138757 5717427711905484043526017)
                  ·
                    refine ⟨4288070783929113032644513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5717427711905484043526017 4288070783929113032644513)
                    ·
                      refine ⟨3216053087946834774483385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4288070783929113032644513 3216053087946834774483385)
                      ·
                        rfl

theorem cell23_6263241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 4, 2, 2].length) (baseStart_6263241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263241 prefixEnd_6263241 := by exact prefixLift 6263241
  have htrace : WordTrace (prefixWord ++ tailWord_6263241) baseStart_6263241 baseEnd_6263241 := by
    simpa [prefixWord, tailWord_6263241, baseEnd_6263241] using wordTrace_append hprefix tailTrace_6263241
  have hstable : (prefixWord ++ tailWord_6263241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263241).length < 2 ^ (prefixWord ++ tailWord_6263241).sum := by decide
  have hdescent : baseEnd_6263241 < baseStart_6263241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263247 : List Nat := [1, 1, 2, 1, 1, 4, 1, 5, 7]
def baseStart_6263247 : Nat := 118140960795 + 6263247 * 2 ^ 59
def prefixEnd_6263247 : Nat := 4983230072969 + 3 ^ 40 * 6263247 * 2
def baseEnd_6263247 : Nat := 357339574314529083445373

theorem tailTrace_6263247 : CollatzResearch.WordTrace tailWord_6263247 prefixEnd_6263247 357339574314529083445373 := by
  unfold tailWord_6263247
  simp only [CollatzResearch.WordTrace]
  refine ⟨228439385140333271271339995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152292923426888847514226663 228439385140333271271339995)
  ·
    refine ⟨342659077710499906907009993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228439385140333271271339995 342659077710499906907009993)
    ·
      refine ⟨256994308282874930180257495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342659077710499906907009993 256994308282874930180257495)
      ·
        refine ⟨385491462424312395270386243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256994308282874930180257495 385491462424312395270386243)
        ·
          refine ⟨578237193636468592905579365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385491462424312395270386243 578237193636468592905579365)
          ·
            refine ⟨108419473806837861169796131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 578237193636468592905579365 108419473806837861169796131)
            ·
              refine ⟨162629210710256791754694197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108419473806837861169796131 162629210710256791754694197)
              ·
                refine ⟨15246488504086574227002581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162629210710256791754694197 15246488504086574227002581)
                ·
                  refine ⟨357339574314529083445373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15246488504086574227002581 357339574314529083445373)
                  ·
                    rfl

theorem cell23_6263247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 7].length) (baseStart_6263247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263247 prefixEnd_6263247 := by exact prefixLift 6263247
  have htrace : WordTrace (prefixWord ++ tailWord_6263247) baseStart_6263247 baseEnd_6263247 := by
    simpa [prefixWord, tailWord_6263247, baseEnd_6263247] using wordTrace_append hprefix tailTrace_6263247
  have hstable : (prefixWord ++ tailWord_6263247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263247).length < 2 ^ (prefixWord ++ tailWord_6263247).sum := by decide
  have hdescent : baseEnd_6263247 < baseStart_6263247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263258 : List Nat := [3, 1, 1, 2, 3, 1, 1, 5, 2, 2, 2]
def baseStart_6263258 : Nat := 118140960795 + 6263258 * 2 ^ 59
def prefixEnd_6263258 : Nat := 4983230072969 + 3 ^ 40 * 6263258 * 2
def baseEnd_6263258 : Nat := 3216061817117961207970807

theorem tailTrace_6263258 : CollatzResearch.WordTrace tailWord_6263258 prefixEnd_6263258 3216061817117961207970807 := by
  unfold tailWord_6263258
  simp only [CollatzResearch.WordTrace]
  refine ⟨57109946585823355037497607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152293190895528946766660285 57109946585823355037497607)
  ·
    refine ⟨85664919878735032556246411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57109946585823355037497607 85664919878735032556246411)
    ·
      refine ⟨128497379818102548834369617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85664919878735032556246411 128497379818102548834369617)
      ·
        refine ⟨96373034863576911625777213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128497379818102548834369617 96373034863576911625777213)
        ·
          refine ⟨36139888073841341859666455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96373034863576911625777213 36139888073841341859666455)
          ·
            refine ⟨54209832110762012789499683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36139888073841341859666455 54209832110762012789499683)
            ·
              refine ⟨81314748166143019184249525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54209832110762012789499683 81314748166143019184249525)
              ·
                refine ⟨7623257640575908048523393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81314748166143019184249525 7623257640575908048523393)
                ·
                  refine ⟨5717443230431931036392545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7623257640575908048523393 5717443230431931036392545)
                  ·
                    refine ⟨4288082422823948277294409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5717443230431931036392545 4288082422823948277294409)
                    ·
                      refine ⟨3216061817117961207970807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4288082422823948277294409 3216061817117961207970807)
                      ·
                        rfl

theorem cell23_6263258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 2, 2, 2].length) (baseStart_6263258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263258 prefixEnd_6263258 := by exact prefixLift 6263258
  have htrace : WordTrace (prefixWord ++ tailWord_6263258) baseStart_6263258 baseEnd_6263258 := by
    simpa [prefixWord, tailWord_6263258, baseEnd_6263258] using wordTrace_append hprefix tailTrace_6263258
  have hstable : (prefixWord ++ tailWord_6263258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263258).length < 2 ^ (prefixWord ++ tailWord_6263258).sum := by decide
  have hdescent : baseEnd_6263258 < baseStart_6263258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263281 : List Nat := [1, 2, 2, 2, 3, 1, 4, 3, 5]
def baseStart_6263281 : Nat := 118140960795 + 6263281 * 2 ^ 59
def prefixEnd_6263281 : Nat := 4983230072969 + 3 ^ 40 * 6263281 * 2
def baseEnd_6263281 : Nat := 357341514130334957553689

theorem tailTrace_6263281 : CollatzResearch.WordTrace tailWord_6263281 prefixEnd_6263281 357341514130334957553689 := by
  unfold tailWord_6263281
  simp only [CollatzResearch.WordTrace]
  refine ⟨228440625222210095078077697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152293750148140063385385131 228440625222210095078077697)
  ·
    refine ⟨171330468916657571308558273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228440625222210095078077697 171330468916657571308558273)
    ·
      refine ⟨128497851687493178481418705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171330468916657571308558273 128497851687493178481418705)
      ·
        refine ⟨96373388765619883861064029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128497851687493178481418705 96373388765619883861064029)
        ·
          refine ⟨36140020787107456447899011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96373388765619883861064029 36140020787107456447899011)
          ·
            refine ⟨54210031180661184671848517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36140020787107456447899011 54210031180661184671848517)
            ·
              refine ⟨10164380846373972125971597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54210031180661184671848517 10164380846373972125971597)
              ·
                refine ⟨3811642817390239547239349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10164380846373972125971597 3811642817390239547239349)
                ·
                  refine ⟨357341514130334957553689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3811642817390239547239349 357341514130334957553689)
                  ·
                    rfl

theorem cell23_6263281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 3, 5].length) (baseStart_6263281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263281 prefixEnd_6263281 := by exact prefixLift 6263281
  have htrace : WordTrace (prefixWord ++ tailWord_6263281) baseStart_6263281 baseEnd_6263281 := by
    simpa [prefixWord, tailWord_6263281, baseEnd_6263281] using wordTrace_append hprefix tailTrace_6263281
  have hstable : (prefixWord ++ tailWord_6263281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263281).length < 2 ^ (prefixWord ++ tailWord_6263281).sum := by decide
  have hdescent : baseEnd_6263281 < baseStart_6263281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263298 : List Nat := [3, 4, 1, 2, 2, 1, 2, 1, 7]
def baseStart_6263298 : Nat := 118140960795 + 6263298 * 2 ^ 59
def prefixEnd_6263298 : Nat := 4983230072969 + 3 ^ 40 * 6263298 * 2
def baseEnd_6263298 : Nat := 357342484038237894607847

theorem tailTrace_6263298 : CollatzResearch.WordTrace tailWord_6263298 prefixEnd_6263298 357342484038237894607847 := by
  unfold tailWord_6263298
  simp only [CollatzResearch.WordTrace]
  refine ⟨57110311315787126745361637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152294163508765671320964365 57110311315787126745361637)
  ·
    refine ⟨10708183371710086264755307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57110311315787126745361637 10708183371710086264755307)
    ·
      refine ⟨16062275057565129397132961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10708183371710086264755307 16062275057565129397132961)
      ·
        refine ⟨12046706293173847047849721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16062275057565129397132961 12046706293173847047849721)
        ·
          refine ⟨9035029719880385285887291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12046706293173847047849721 9035029719880385285887291)
          ·
            refine ⟨13552544579820577928830937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9035029719880385285887291 13552544579820577928830937)
            ·
              refine ⟨10164408434865433446623203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13552544579820577928830937 10164408434865433446623203)
              ·
                refine ⟨15246612652298150169934805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10164408434865433446623203 15246612652298150169934805)
                ·
                  refine ⟨357342484038237894607847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15246612652298150169934805 357342484038237894607847)
                  ·
                    rfl

theorem cell23_6263298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_6263298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263298 prefixEnd_6263298 := by exact prefixLift 6263298
  have htrace : WordTrace (prefixWord ++ tailWord_6263298) baseStart_6263298 baseEnd_6263298 := by
    simpa [prefixWord, tailWord_6263298, baseEnd_6263298] using wordTrace_append hprefix tailTrace_6263298
  have hstable : (prefixWord ++ tailWord_6263298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263298).length < 2 ^ (prefixWord ++ tailWord_6263298).sum := by decide
  have hdescent : baseEnd_6263298 < baseStart_6263298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263332 : List Nat := [2, 3, 1, 5, 2, 1, 1, 3, 5]
def baseStart_6263332 : Nat := 118140960795 + 6263332 * 2 ^ 59
def prefixEnd_6263332 : Nat := 4983230072969 + 3 ^ 40 * 6263332 * 2
def baseEnd_6263332 : Nat := 357344423854043768716163

theorem tailTrace_6263332 : CollatzResearch.WordTrace tailWord_6263332 prefixEnd_6263332 357344423854043768716163 := by
  unfold tailWord_6263332
  simp only [CollatzResearch.WordTrace]
  refine ⟨114221242672512665394092125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152294990230016887192122833 114221242672512665394092125)
  ·
    refine ⟨42832966002192249522784547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114221242672512665394092125 42832966002192249522784547)
    ·
      refine ⟨64249449003288374284176821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42832966002192249522784547 64249449003288374284176821)
      ·
        refine ⟨6023385844058285089141577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64249449003288374284176821 6023385844058285089141577)
        ·
          refine ⟨4517539383043713816856183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6023385844058285089141577 4517539383043713816856183)
          ·
            refine ⟨6776309074565570725284275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4517539383043713816856183 6776309074565570725284275)
            ·
              refine ⟨10164463611848356087926413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6776309074565570725284275 10164463611848356087926413)
              ·
                refine ⟨3811673854443133532972405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10164463611848356087926413 3811673854443133532972405)
                ·
                  refine ⟨357344423854043768716163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3811673854443133532972405 357344423854043768716163)
                  ·
                    rfl

theorem cell23_6263332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 3, 5].length) (baseStart_6263332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263332 prefixEnd_6263332 := by exact prefixLift 6263332
  have htrace : WordTrace (prefixWord ++ tailWord_6263332) baseStart_6263332 baseEnd_6263332 := by
    simpa [prefixWord, tailWord_6263332, baseEnd_6263332] using wordTrace_append hprefix tailTrace_6263332
  have hstable : (prefixWord ++ tailWord_6263332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263332).length < 2 ^ (prefixWord ++ tailWord_6263332).sum := by decide
  have hdescent : baseEnd_6263332 < baseStart_6263332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263351 : List Nat := [1, 1, 3, 1, 2, 3, 3, 2, 2, 2, 3]
def baseStart_6263351 : Nat := 118140960795 + 6263351 * 2 ^ 59
def prefixEnd_6263351 : Nat := 4983230072969 + 3 ^ 40 * 6263351 * 2
def baseEnd_6263351 : Nat := 3216109570818829344107879

theorem tailTrace_6263351 : CollatzResearch.WordTrace tailWord_6263351 prefixEnd_6263351 3216109570818829344107879 := by
  unfold tailWord_6263351
  simp only [CollatzResearch.WordTrace]
  refine ⟨228443178331956497033125907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152295452221304331355417271 228443178331956497033125907)
  ·
    refine ⟨342664767497934745549688861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228443178331956497033125907 342664767497934745549688861)
    ·
      refine ⟨128499287811725529581133323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342664767497934745549688861 128499287811725529581133323)
      ·
        refine ⟨192748931717588294371699985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128499287811725529581133323 192748931717588294371699985)
        ·
          refine ⟨144561698788191220778774989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192748931717588294371699985 144561698788191220778774989)
          ·
            refine ⟨54210637045571707792040621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144561698788191220778774989 54210637045571707792040621)
            ·
              refine ⟨20328988892089390422015233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54210637045571707792040621 20328988892089390422015233)
              ·
                refine ⟨15246741669067042816511425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20328988892089390422015233 15246741669067042816511425)
                ·
                  refine ⟨11435056251800282112383569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15246741669067042816511425 11435056251800282112383569)
                  ·
                    refine ⟨8576292188850211584287677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11435056251800282112383569 8576292188850211584287677)
                    ·
                      refine ⟨3216109570818829344107879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8576292188850211584287677 3216109570818829344107879)
                      ·
                        rfl

theorem cell23_6263351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 2, 3].length) (baseStart_6263351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263351 prefixEnd_6263351 := by exact prefixLift 6263351
  have htrace : WordTrace (prefixWord ++ tailWord_6263351) baseStart_6263351 baseEnd_6263351 := by
    simpa [prefixWord, tailWord_6263351, baseEnd_6263351] using wordTrace_append hprefix tailTrace_6263351
  have hstable : (prefixWord ++ tailWord_6263351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263351).length < 2 ^ (prefixWord ++ tailWord_6263351).sum := by decide
  have hdescent : baseEnd_6263351 < baseStart_6263351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263354 : List Nat := [3, 1, 1, 1, 3, 3, 2, 1, 8]
def baseStart_6263354 : Nat := 118140960795 + 6263354 * 2 ^ 59
def prefixEnd_6263354 : Nat := 4983230072969 + 3 ^ 40 * 6263354 * 2
def baseEnd_6263354 : Nat := 357345679028976981374485

theorem tailTrace_6263354 : CollatzResearch.WordTrace tailWord_6263354 prefixEnd_6263354 357345679028976981374485 := by
  unfold tailWord_6263354
  simp only [CollatzResearch.WordTrace]
  refine ⟨57110821937736407136371279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152295525167297085696990077 57110821937736407136371279)
  ·
    refine ⟨85666232906604610704556919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57110821937736407136371279 85666232906604610704556919)
    ·
      refine ⟨128499349359906916056835379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85666232906604610704556919 128499349359906916056835379)
      ·
        refine ⟨192749024039860374085253069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128499349359906916056835379 192749024039860374085253069)
        ·
          refine ⟨72280884014947640281969901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192749024039860374085253069 72280884014947640281969901)
          ·
            refine ⟨27105331505605365105738713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72280884014947640281969901 27105331505605365105738713)
            ·
              refine ⟨20328998629204023829304035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27105331505605365105738713 20328998629204023829304035)
              ·
                refine ⟨30493497943806035743956053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20328998629204023829304035 30493497943806035743956053)
                ·
                  refine ⟨357345679028976981374485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30493497943806035743956053 357345679028976981374485)
                  ·
                    rfl

theorem cell23_6263354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 8].length) (baseStart_6263354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263354 prefixEnd_6263354 := by exact prefixLift 6263354
  have htrace : WordTrace (prefixWord ++ tailWord_6263354) baseStart_6263354 baseEnd_6263354 := by
    simpa [prefixWord, tailWord_6263354, baseEnd_6263354] using wordTrace_append hprefix tailTrace_6263354
  have hstable : (prefixWord ++ tailWord_6263354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263354).length < 2 ^ (prefixWord ++ tailWord_6263354).sum := by decide
  have hdescent : baseEnd_6263354 < baseStart_6263354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263371 : List Nat := [1, 1, 1, 1, 3, 1, 8, 1, 6]
def baseStart_6263371 : Nat := 118140960795 + 6263371 * 2 ^ 59
def prefixEnd_6263371 : Nat := 4983230072969 + 3 ^ 40 * 6263371 * 2
def baseEnd_6263371 : Nat := 357346648936879918428643

theorem tailTrace_6263371 : CollatzResearch.WordTrace tailWord_6263371 prefixEnd_6263371 357346648936879918428643 := by
  unfold tailWord_6263371
  simp only [CollatzResearch.WordTrace]
  refine ⟨228443907791884040448853967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152295938527922693632569311 228443907791884040448853967)
  ·
    refine ⟨342665861687826060673280951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228443907791884040448853967 342665861687826060673280951)
    ·
      refine ⟨513998792531739091009921427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342665861687826060673280951 513998792531739091009921427)
      ·
        refine ⟨770998188797608636514882141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513998792531739091009921427 770998188797608636514882141)
        ·
          refine ⟨289124320799103238693080803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 770998188797608636514882141 289124320799103238693080803)
          ·
            refine ⟨433686481198654858039621205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289124320799103238693080803 433686481198654858039621205)
            ·
              refine ⟨5082263451546736617651811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 433686481198654858039621205 5082263451546736617651811)
              ·
                refine ⟨7623395177320104926477717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5082263451546736617651811 7623395177320104926477717)
                ·
                  refine ⟨357346648936879918428643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7623395177320104926477717 357346648936879918428643)
                  ·
                    rfl

theorem cell23_6263371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 6].length) (baseStart_6263371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263371 prefixEnd_6263371 := by exact prefixLift 6263371
  have htrace : WordTrace (prefixWord ++ tailWord_6263371) baseStart_6263371 baseEnd_6263371 := by
    simpa [prefixWord, tailWord_6263371, baseEnd_6263371] using wordTrace_append hprefix tailTrace_6263371
  have hstable : (prefixWord ++ tailWord_6263371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263371).length < 2 ^ (prefixWord ++ tailWord_6263371).sum := by decide
  have hdescent : baseEnd_6263371 < baseStart_6263371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263374 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6]
def baseStart_6263374 : Nat := 118140960795 + 6263374 * 2 ^ 59
def prefixEnd_6263374 : Nat := 4983230072969 + 3 ^ 40 * 6263374 * 2
def baseEnd_6263374 : Nat := 3216121380873882754120273

theorem tailTrace_6263374 : CollatzResearch.WordTrace tailWord_6263374 prefixEnd_6263374 3216121380873882754120273 := by
  unfold tailWord_6263374
  simp only [CollatzResearch.WordTrace]
  refine ⟨28555502151359146495151647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152296011473915447974142117 28555502151359146495151647)
  ·
    refine ⟨42833253227038719742727471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28555502151359146495151647 42833253227038719742727471)
    ·
      refine ⟨64249879840558079614091207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42833253227038719742727471 64249879840558079614091207)
      ·
        refine ⟨96374819760837119421136811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64249879840558079614091207 96374819760837119421136811)
        ·
          refine ⟨144562229641255679131705217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96374819760837119421136811 144562229641255679131705217)
          ·
            refine ⟨108421672230941759348778913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144562229641255679131705217 108421672230941759348778913)
            ·
              refine ⟨81316254173206319511584185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108421672230941759348778913 81316254173206319511584185)
              ·
                refine ⟨60987190629904739633688139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81316254173206319511584185 60987190629904739633688139)
                ·
                  refine ⟨91480785944857109450532209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60987190629904739633688139 91480785944857109450532209)
                  ·
                    refine ⟨68610589458642832087899157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91480785944857109450532209 68610589458642832087899157)
                    ·
                      refine ⟨3216121380873882754120273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68610589458642832087899157 3216121380873882754120273)
                      ·
                        rfl

theorem cell23_6263374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_6263374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263374 prefixEnd_6263374 := by exact prefixLift 6263374
  have htrace : WordTrace (prefixWord ++ tailWord_6263374) baseStart_6263374 baseEnd_6263374 := by
    simpa [prefixWord, tailWord_6263374, baseEnd_6263374] using wordTrace_append hprefix tailTrace_6263374
  have hstable : (prefixWord ++ tailWord_6263374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263374).length < 2 ^ (prefixWord ++ tailWord_6263374).sum := by decide
  have hdescent : baseEnd_6263374 < baseStart_6263374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263391 : List Nat := [1, 1, 2, 3, 1, 1, 1, 5, 1, 5, 2]
def baseStart_6263391 : Nat := 118140960795 + 6263391 * 2 ^ 59
def prefixEnd_6263391 : Nat := 4983230072969 + 3 ^ 40 * 6263391 * 2
def baseEnd_6263391 : Nat := 3216130110045009187607695

theorem tailTrace_6263391 : CollatzResearch.WordTrace tailWord_6263391 prefixEnd_6263391 3216130110045009187607695 := by
  unfold tailWord_6263391
  simp only [CollatzResearch.WordTrace]
  refine ⟨228444637251811583864582027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152296424834541055909721351 228444637251811583864582027)
  ·
    refine ⟨342666955877717375796873041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228444637251811583864582027 342666955877717375796873041)
    ·
      refine ⟨257000216908288031847654781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342666955877717375796873041 257000216908288031847654781)
      ·
        refine ⟨96375081340608011942870543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257000216908288031847654781 96375081340608011942870543)
        ·
          refine ⟨144562622010912017914305815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96375081340608011942870543 144562622010912017914305815)
          ·
            refine ⟨216843933016368026871458723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144562622010912017914305815 216843933016368026871458723)
            ·
              refine ⟨325265899524552040307188085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216843933016368026871458723 325265899524552040307188085)
              ·
                refine ⟨30493678080426753778798883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 325265899524552040307188085 30493678080426753778798883)
                ·
                  refine ⟨45740517120640130668198325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30493678080426753778798883 45740517120640130668198325)
                  ·
                    refine ⟨4288173480060012250143593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45740517120640130668198325 4288173480060012250143593)
                    ·
                      refine ⟨3216130110045009187607695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4288173480060012250143593 3216130110045009187607695)
                      ·
                        rfl

theorem cell23_6263391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 5, 2].length) (baseStart_6263391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263391 prefixEnd_6263391 := by exact prefixLift 6263391
  have htrace : WordTrace (prefixWord ++ tailWord_6263391) baseStart_6263391 baseEnd_6263391 := by
    simpa [prefixWord, tailWord_6263391, baseEnd_6263391] using wordTrace_append hprefix tailTrace_6263391
  have hstable : (prefixWord ++ tailWord_6263391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263391).length < 2 ^ (prefixWord ++ tailWord_6263391).sum := by decide
  have hdescent : baseEnd_6263391 < baseStart_6263391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263431 : List Nat := [1, 1, 4, 2, 1, 2, 4, 1, 1, 6]
def baseStart_6263431 : Nat := 118140960795 + 6263431 * 2 ^ 59
def prefixEnd_6263431 : Nat := 4983230072969 + 3 ^ 40 * 6263431 * 2
def baseEnd_6263431 : Nat := 1072050216423729677035837

theorem tailTrace_6263431 : CollatzResearch.WordTrace tailWord_6263431 prefixEnd_6263431 1072050216423729677035837 := by
  unfold tailWord_6263431
  simp only [CollatzResearch.WordTrace]
  refine ⟨228446096171666670696038147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152297397447777780464025431 228446096171666670696038147)
  ·
    refine ⟨342669144257500006044057221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228446096171666670696038147 342669144257500006044057221)
    ·
      refine ⟨64250464548281251133260729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 342669144257500006044057221 64250464548281251133260729)
      ·
        refine ⟨48187848411210938349945547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64250464548281251133260729 48187848411210938349945547)
        ·
          refine ⟨72281772616816407524918321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48187848411210938349945547 72281772616816407524918321)
          ·
            refine ⟨54211329462612305643688741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72281772616816407524918321 54211329462612305643688741)
            ·
              refine ⟨10164624274239807308191639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54211329462612305643688741 10164624274239807308191639)
              ·
                refine ⟨15246936411359710962287459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10164624274239807308191639 15246936411359710962287459)
                ·
                  refine ⟨22870404617039566443431189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15246936411359710962287459 22870404617039566443431189)
                  ·
                    refine ⟨1072050216423729677035837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22870404617039566443431189 1072050216423729677035837)
                    ·
                      rfl

theorem cell23_6263431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_6263431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263431 prefixEnd_6263431 := by exact prefixLift 6263431
  have htrace : WordTrace (prefixWord ++ tailWord_6263431) baseStart_6263431 baseEnd_6263431 := by
    simpa [prefixWord, tailWord_6263431, baseEnd_6263431] using wordTrace_append hprefix tailTrace_6263431
  have hstable : (prefixWord ++ tailWord_6263431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263431).length < 2 ^ (prefixWord ++ tailWord_6263431).sum := by decide
  have hdescent : baseEnd_6263431 < baseStart_6263431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263438 : List Nat := [4, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4]
def baseStart_6263438 : Nat := 118140960795 + 6263438 * 2 ^ 59
def prefixEnd_6263438 : Nat := 4983230072969 + 3 ^ 40 * 6263438 * 2
def baseEnd_6263438 : Nat := 3216154243635770503719979

theorem tailTrace_6263438 : CollatzResearch.WordTrace tailWord_6263438 prefixEnd_6263438 3216154243635770503719979 := by
  unfold tailWord_6263438
  simp only [CollatzResearch.WordTrace]
  refine ⟨28555793935330163861442871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152297567655094207261028645 28555793935330163861442871)
  ·
    refine ⟨42833690902995245792164307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28555793935330163861442871 42833690902995245792164307)
    ·
      refine ⟨64250536354492868688246461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42833690902995245792164307 64250536354492868688246461)
      ·
        refine ⟨24093951132934825758092423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64250536354492868688246461 24093951132934825758092423)
        ·
          refine ⟨36140926699402238637138635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24093951132934825758092423 36140926699402238637138635)
          ·
            refine ⟨54211390049103357955707953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36140926699402238637138635 54211390049103357955707953)
            ·
              refine ⟨40658542536827518466780965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54211390049103357955707953 40658542536827518466780965)
              ·
                refine ⟨7623476725655159712521431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40658542536827518466780965 7623476725655159712521431)
                ·
                  refine ⟨11435215088482739568782147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7623476725655159712521431 11435215088482739568782147)
                  ·
                    refine ⟨17152822632724109353173221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11435215088482739568782147 17152822632724109353173221)
                    ·
                      refine ⟨3216154243635770503719979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17152822632724109353173221 3216154243635770503719979)
                      ·
                        rfl

theorem cell23_6263438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_6263438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263438 prefixEnd_6263438 := by exact prefixLift 6263438
  have htrace : WordTrace (prefixWord ++ tailWord_6263438) baseStart_6263438 baseEnd_6263438 := by
    simpa [prefixWord, tailWord_6263438, baseEnd_6263438] using wordTrace_append hprefix tailTrace_6263438
  have hstable : (prefixWord ++ tailWord_6263438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263438).length < 2 ^ (prefixWord ++ tailWord_6263438).sum := by decide
  have hdescent : baseEnd_6263438 < baseStart_6263438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263442 : List Nat := [3, 2, 3, 1, 2, 3, 1, 1, 2, 3, 2]
def baseStart_6263442 : Nat := 118140960795 + 6263442 * 2 ^ 59
def prefixEnd_6263442 : Nat := 4983230072969 + 3 ^ 40 * 6263442 * 2
def baseEnd_6263442 : Nat := 3216156297558388488069961

theorem tailTrace_6263442 : CollatzResearch.WordTrace tailWord_6263442 prefixEnd_6263442 3216156297558388488069961 := by
  unfold tailWord_6263442
  simp only [CollatzResearch.WordTrace]
  refine ⟨57111624343656704893672145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152297664916417879716459053 57111624343656704893672145)
  ·
    refine ⟨42833718257742528670254109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57111624343656704893672145 42833718257742528670254109)
    ·
      refine ⟨16062644346653448251345291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42833718257742528670254109 16062644346653448251345291)
      ·
        refine ⟨24093966519980172377017937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16062644346653448251345291 24093966519980172377017937)
        ·
          refine ⟨18070474889985129282763453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24093966519980172377017937 18070474889985129282763453)
          ·
            refine ⟨6776428083744423481036295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18070474889985129282763453 6776428083744423481036295)
            ·
              refine ⟨10164642125616635221554443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6776428083744423481036295 10164642125616635221554443)
              ·
                refine ⟨15246963188424952832331665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10164642125616635221554443 15246963188424952832331665)
                ·
                  refine ⟨11435222391318714624248749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15246963188424952832331665 11435222391318714624248749)
                  ·
                    refine ⟨4288208396744517984093281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11435222391318714624248749 4288208396744517984093281)
                    ·
                      refine ⟨3216156297558388488069961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4288208396744517984093281 3216156297558388488069961)
                      ·
                        rfl

theorem cell23_6263442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_6263442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263442 prefixEnd_6263442 := by exact prefixLift 6263442
  have htrace : WordTrace (prefixWord ++ tailWord_6263442) baseStart_6263442 baseEnd_6263442 := by
    simpa [prefixWord, tailWord_6263442, baseEnd_6263442] using wordTrace_append hprefix tailTrace_6263442
  have hstable : (prefixWord ++ tailWord_6263442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263442).length < 2 ^ (prefixWord ++ tailWord_6263442).sum := by decide
  have hdescent : baseEnd_6263442 < baseStart_6263442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263488 : List Nat := [2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 3]
def baseStart_6263488 : Nat := 118140960795 + 6263488 * 2 ^ 59
def prefixEnd_6263488 : Nat := 4983230072969 + 3 ^ 40 * 6263488 * 2
def baseEnd_6263488 : Nat := 3216179917668495308094749

theorem tailTrace_6263488 : CollatzResearch.WordTrace tailWord_6263488 prefixEnd_6263488 3216179917668495308094749 := by
  unfold tailWord_6263488
  simp only [CollatzResearch.WordTrace]
  refine ⟨114224087566230084715431559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152298783421640112953908745 114224087566230084715431559)
  ·
    refine ⟨171336131349345127073147339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114224087566230084715431559 171336131349345127073147339)
    ·
      refine ⟨257004197024017690609721009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171336131349345127073147339 257004197024017690609721009)
      ·
        refine ⟨192753147768013267957290757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257004197024017690609721009 192753147768013267957290757)
        ·
          refine ⟨36141215206502487741992017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192753147768013267957290757 36141215206502487741992017)
          ·
            refine ⟨27105911404876865806494013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36141215206502487741992017 27105911404876865806494013)
            ·
              refine ⟨10164716776828824677435255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27105911404876865806494013 10164716776828824677435255)
              ·
                refine ⟨15247075165243237016152883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10164716776828824677435255 15247075165243237016152883)
                ·
                  refine ⟨22870612747864855524229325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15247075165243237016152883 22870612747864855524229325)
                  ·
                    refine ⟨8576479780449320821585997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22870612747864855524229325 8576479780449320821585997)
                    ·
                      refine ⟨3216179917668495308094749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8576479780449320821585997 3216179917668495308094749)
                      ·
                        rfl

theorem cell23_6263488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 3].length) (baseStart_6263488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263488 prefixEnd_6263488 := by exact prefixLift 6263488
  have htrace : WordTrace (prefixWord ++ tailWord_6263488) baseStart_6263488 baseEnd_6263488 := by
    simpa [prefixWord, tailWord_6263488, baseEnd_6263488] using wordTrace_append hprefix tailTrace_6263488
  have hstable : (prefixWord ++ tailWord_6263488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263488).length < 2 ^ (prefixWord ++ tailWord_6263488).sum := by decide
  have hdescent : baseEnd_6263488 < baseStart_6263488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263506 : List Nat := [3, 2, 2, 2, 3, 2, 1, 3, 1, 2, 2]
def baseStart_6263506 : Nat := 118140960795 + 6263506 * 2 ^ 59
def prefixEnd_6263506 : Nat := 4983230072969 + 3 ^ 40 * 6263506 * 2
def baseEnd_6263506 : Nat := 3216189160320276237669667

theorem tailTrace_6263506 : CollatzResearch.WordTrace tailWord_6263506 prefixEnd_6263506 3216189160320276237669667 := by
  unfold tailWord_6263506
  simp only [CollatzResearch.WordTrace]
  refine ⟨57112207911598739626254593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152299221097596639003345581 57112207911598739626254593)
  ·
    refine ⟨42834155933699054719690945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57112207911598739626254593 42834155933699054719690945)
    ·
      refine ⟨32125616950274291039768209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42834155933699054719690945 32125616950274291039768209)
      ·
        refine ⟨24094212712705718279826157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32125616950274291039768209 24094212712705718279826157)
        ·
          refine ⟨9035329767264644354934809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24094212712705718279826157 9035329767264644354934809)
          ·
            refine ⟨6776497325448483266201107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9035329767264644354934809 6776497325448483266201107)
            ·
              refine ⟨10164745988172724899301661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6776497325448483266201107 10164745988172724899301661)
              ·
                refine ⟨3811779745564771837238123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10164745988172724899301661 3811779745564771837238123)
                ·
                  refine ⟨5717669618347157755857185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3811779745564771837238123 5717669618347157755857185)
                  ·
                    refine ⟨4288252213760368316892889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5717669618347157755857185 4288252213760368316892889)
                    ·
                      refine ⟨3216189160320276237669667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4288252213760368316892889 3216189160320276237669667)
                      ·
                        rfl

theorem cell23_6263506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_6263506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263506 prefixEnd_6263506 := by exact prefixLift 6263506
  have htrace : WordTrace (prefixWord ++ tailWord_6263506) baseStart_6263506 baseEnd_6263506 := by
    simpa [prefixWord, tailWord_6263506, baseEnd_6263506] using wordTrace_append hprefix tailTrace_6263506
  have hstable : (prefixWord ++ tailWord_6263506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263506).length < 2 ^ (prefixWord ++ tailWord_6263506).sum := by decide
  have hdescent : baseEnd_6263506 < baseStart_6263506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263531 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 2, 4, 3]
def baseStart_6263531 : Nat := 118140960795 + 6263531 * 2 ^ 59
def prefixEnd_6263531 : Nat := 4983230072969 + 3 ^ 40 * 6263531 * 2
def baseEnd_6263531 : Nat := 3216201997336638639857051

theorem tailTrace_6263531 : CollatzResearch.WordTrace tailWord_6263531 prefixEnd_6263531 3216201997336638639857051 := by
  unfold tailWord_6263531
  simp only [CollatzResearch.WordTrace]
  refine ⟨228449743471304387774678447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152299828980869591849785631 228449743471304387774678447)
  ·
    refine ⟨342674615206956581662017671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228449743471304387774678447 342674615206956581662017671)
    ·
      refine ⟨514011922810434872493026507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342674615206956581662017671 514011922810434872493026507)
      ·
        refine ⟨771017884215652308739539761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514011922810434872493026507 771017884215652308739539761)
        ·
          refine ⟨578263413161739231554654821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 771017884215652308739539761 578263413161739231554654821)
          ·
            refine ⟨108424389967826105916497779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 578263413161739231554654821 108424389967826105916497779)
            ·
              refine ⟨162636584951739158874746669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108424389967826105916497779 162636584951739158874746669)
              ·
                refine ⟨60988719356902184578030001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162636584951739158874746669 60988719356902184578030001)
                ·
                  refine ⟨45741539517676638433522501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60988719356902184578030001 45741539517676638433522501)
                  ·
                    refine ⟨8576538659564369706285469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45741539517676638433522501 8576538659564369706285469)
                    ·
                      refine ⟨3216201997336638639857051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8576538659564369706285469 3216201997336638639857051)
                      ·
                        rfl

theorem cell23_6263531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 4, 3].length) (baseStart_6263531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263531 prefixEnd_6263531 := by exact prefixLift 6263531
  have htrace : WordTrace (prefixWord ++ tailWord_6263531) baseStart_6263531 baseEnd_6263531 := by
    simpa [prefixWord, tailWord_6263531, baseEnd_6263531] using wordTrace_append hprefix tailTrace_6263531
  have hstable : (prefixWord ++ tailWord_6263531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263531).length < 2 ^ (prefixWord ++ tailWord_6263531).sum := by decide
  have hdescent : baseEnd_6263531 < baseStart_6263531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263578 : List Nat := [3, 1, 1, 3, 2, 1, 2, 2, 2, 3, 3]
def baseStart_6263578 : Nat := 118140960795 + 6263578 * 2 ^ 59
def prefixEnd_6263578 : Nat := 4983230072969 + 3 ^ 40 * 6263578 * 2
def baseEnd_6263578 : Nat := 3216226130927399955969335

theorem tailTrace_6263578 : CollatzResearch.WordTrace tailWord_6263578 prefixEnd_6263578 3216226130927399955969335 := by
  unfold tailWord_6263578
  simp only [CollatzResearch.WordTrace]
  refine ⟨57112864425533528700409847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152300971801422743201092925 57112864425533528700409847)
  ·
    refine ⟨85669296638300293050614771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57112864425533528700409847 85669296638300293050614771)
    ·
      refine ⟨128503944957450439575922157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85669296638300293050614771 128503944957450439575922157)
      ·
        refine ⟨48188979359043914840970809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128503944957450439575922157 48188979359043914840970809)
        ·
          refine ⟨36141734519282936130728107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48188979359043914840970809 36141734519282936130728107)
          ·
            refine ⟨54212601778924404196092161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36141734519282936130728107 54212601778924404196092161)
            ·
              refine ⟨40659451334193303147069121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54212601778924404196092161 40659451334193303147069121)
              ·
                refine ⟨30494588500644977360301841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40659451334193303147069121 30494588500644977360301841)
                ·
                  refine ⟨22870941375483733020226381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30494588500644977360301841 22870941375483733020226381)
                  ·
                    refine ⟨8576603015806399882584893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22870941375483733020226381 8576603015806399882584893)
                    ·
                      refine ⟨3216226130927399955969335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8576603015806399882584893 3216226130927399955969335)
                      ·
                        rfl

theorem cell23_6263578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_6263578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263578 prefixEnd_6263578 := by exact prefixLift 6263578
  have htrace : WordTrace (prefixWord ++ tailWord_6263578) baseStart_6263578 baseEnd_6263578 := by
    simpa [prefixWord, tailWord_6263578, baseEnd_6263578] using wordTrace_append hprefix tailTrace_6263578
  have hstable : (prefixWord ++ tailWord_6263578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263578).length < 2 ^ (prefixWord ++ tailWord_6263578).sum := by decide
  have hdescent : baseEnd_6263578 < baseStart_6263578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263615 : List Nat := [1, 1, 2, 2, 5, 3, 1, 1, 2, 5]
def baseStart_6263615 : Nat := 118140960795 + 6263615 * 2 ^ 59
def prefixEnd_6263615 : Nat := 4983230072969 + 3 ^ 40 * 6263615 * 2
def baseEnd_6263615 : Nat := 1072081709903872103735555

theorem tailTrace_6263615 : CollatzResearch.WordTrace tailWord_6263615 prefixEnd_6263615 1072081709903872103735555 := by
  unfold tailWord_6263615
  simp only [CollatzResearch.WordTrace]
  refine ⟨228452807203000070120736299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152301871468666713413824199 228452807203000070120736299)
  ·
    refine ⟨342679210804500105181104449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228452807203000070120736299 342679210804500105181104449)
    ·
      refine ⟨257009408103375078885828337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342679210804500105181104449 257009408103375078885828337)
      ·
        refine ⟨192757056077531309164371253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257009408103375078885828337 192757056077531309164371253)
        ·
          refine ⟨18070974007268560234159805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 192757056077531309164371253 18070974007268560234159805)
          ·
            refine ⟨6776615252725710087809927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18070974007268560234159805 6776615252725710087809927)
            ·
              refine ⟨10164922879088565131714891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6776615252725710087809927 10164922879088565131714891)
              ·
                refine ⟨15247384318632847697572337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10164922879088565131714891 15247384318632847697572337)
                ·
                  refine ⟨11435538238974635773179253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15247384318632847697572337 11435538238974635773179253)
                  ·
                    refine ⟨1072081709903872103735555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11435538238974635773179253 1072081709903872103735555)
                    ·
                      rfl

theorem cell23_6263615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 5].length) (baseStart_6263615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263615 prefixEnd_6263615 := by exact prefixLift 6263615
  have htrace : WordTrace (prefixWord ++ tailWord_6263615) baseStart_6263615 baseEnd_6263615 := by
    simpa [prefixWord, tailWord_6263615, baseEnd_6263615] using wordTrace_append hprefix tailTrace_6263615
  have hstable : (prefixWord ++ tailWord_6263615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263615).length < 2 ^ (prefixWord ++ tailWord_6263615).sum := by decide
  have hdescent : baseEnd_6263615 < baseStart_6263615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263621 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 2, 3, 5]
def baseStart_6263621 : Nat := 118140960795 + 6263621 * 2 ^ 59
def prefixEnd_6263621 : Nat := 4983230072969 + 3 ^ 40 * 6263621 * 2
def baseEnd_6263621 : Nat := 3216248210595543287731637

theorem tailTrace_6263621 : CollatzResearch.WordTrace tailWord_6263621 prefixEnd_6263621 3216248210595543287731637 := by
  unfold tailWord_6263621
  simp only [CollatzResearch.WordTrace]
  refine ⟨228453026040978333145454717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152302017360652222096969811 228453026040978333145454717)
  ·
    refine ⟨85669884765366874929545519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228453026040978333145454717 85669884765366874929545519)
    ·
      refine ⟨128504827148050312394318279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85669884765366874929545519 128504827148050312394318279)
      ·
        refine ⟨192757240722075468591477419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128504827148050312394318279 192757240722075468591477419)
        ·
          refine ⟨289135861083113202887216129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192757240722075468591477419 289135861083113202887216129)
          ·
            refine ⟨216851895812334902165412097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289135861083113202887216129 216851895812334902165412097)
            ·
              refine ⟨162638921859251176624059073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216851895812334902165412097 162638921859251176624059073)
              ·
                refine ⟨121979191394438382468044305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162638921859251176624059073 121979191394438382468044305)
                ·
                  refine ⟨91484393545828786851033229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121979191394438382468044305 91484393545828786851033229)
                  ·
                    refine ⟨34306647579685795069137461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91484393545828786851033229 34306647579685795069137461)
                    ·
                      refine ⟨3216248210595543287731637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34306647579685795069137461 3216248210595543287731637)
                      ·
                        rfl

theorem cell23_6263621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_6263621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263621 prefixEnd_6263621 := by exact prefixLift 6263621
  have htrace : WordTrace (prefixWord ++ tailWord_6263621) baseStart_6263621 baseEnd_6263621 := by
    simpa [prefixWord, tailWord_6263621, baseEnd_6263621] using wordTrace_append hprefix tailTrace_6263621
  have hstable : (prefixWord ++ tailWord_6263621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263621).length < 2 ^ (prefixWord ++ tailWord_6263621).sum := by decide
  have hdescent : baseEnd_6263621 < baseStart_6263621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
