import V185TrunkScan23Chunk0650

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3849465 : List Nat := [1, 2, 1, 3, 1, 1, 6, 3, 1, 1, 3]
def baseStart_3849465 : Nat := 118140960795 + 3849465 * 2 ^ 59
def prefixEnd_3849465 : Nat := 4983230072969 + 3 ^ 40 * 3849465 * 2
def baseEnd_3849465 : Nat := 1976625807659886684184139

theorem tailTrace_3849465 : CollatzResearch.WordTrace tailWord_3849465 prefixEnd_3849465 1976625807659886684184139 := by
  unfold tailWord_3849465
  simp only [CollatzResearch.WordTrace]
  refine ⟨140401522999053216125933849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93601015332702144083955899 140401522999053216125933849)
  ·
    refine ⟨105301142249289912094450387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140401522999053216125933849 105301142249289912094450387)
    ·
      refine ⟨157951713373934868141675581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105301142249289912094450387 157951713373934868141675581)
      ·
        refine ⟨59231892515225575553128343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157951713373934868141675581 59231892515225575553128343)
        ·
          refine ⟨88847838772838363329692515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59231892515225575553128343 88847838772838363329692515)
          ·
            refine ⟨133271758159257544994538773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88847838772838363329692515 133271758159257544994538773)
            ·
              refine ⟨6247113663715197421619005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 133271758159257544994538773 6247113663715197421619005)
              ·
                refine ⟨2342667623893199033107127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6247113663715197421619005 2342667623893199033107127)
                ·
                  refine ⟨3514001435839798549660691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2342667623893199033107127 3514001435839798549660691)
                  ·
                    refine ⟨5271002153759697824491037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3514001435839798549660691 5271002153759697824491037)
                    ·
                      refine ⟨1976625807659886684184139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5271002153759697824491037 1976625807659886684184139)
                      ·
                        rfl

theorem cell23_3849465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 3, 1, 1, 3].length) (baseStart_3849465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849465 prefixEnd_3849465 := by exact prefixLift 3849465
  have htrace : WordTrace (prefixWord ++ tailWord_3849465) baseStart_3849465 baseEnd_3849465 := by
    simpa [prefixWord, tailWord_3849465, baseEnd_3849465] using wordTrace_append hprefix tailTrace_3849465
  have hstable : (prefixWord ++ tailWord_3849465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849465).length < 2 ^ (prefixWord ++ tailWord_3849465).sum := by decide
  have hdescent : baseEnd_3849465 < baseStart_3849465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849468 : List Nat := [2, 2, 2, 1, 5, 1, 1, 3, 1, 5]
def baseStart_3849468 : Nat := 118140960795 + 3849468 * 2 ^ 59
def prefixEnd_3849468 : Nat := 4983230072969 + 3 ^ 40 * 3849468 * 2
def baseEnd_3849468 : Nat := 658875782700616724148875

theorem tailTrace_3849468 : CollatzResearch.WordTrace tailWord_3849468 prefixEnd_3849468 658875782700616724148875 := by
  unfold tailWord_3849468
  simp only [CollatzResearch.WordTrace]
  refine ⟨70200816209021173819146529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93601088278694898425528705 70200816209021173819146529)
  ·
    refine ⟨52650612156765880364359897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70200816209021173819146529 52650612156765880364359897)
    ·
      refine ⟨39487959117574410273269923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52650612156765880364359897 39487959117574410273269923)
      ·
        refine ⟨59231938676361615409904885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39487959117574410273269923 59231938676361615409904885)
        ·
          refine ⟨5552994250908901444678583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59231938676361615409904885 5552994250908901444678583)
          ·
            refine ⟨8329491376363352167017875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5552994250908901444678583 8329491376363352167017875)
            ·
              refine ⟨12494237064545028250526813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8329491376363352167017875 12494237064545028250526813)
              ·
                refine ⟨4685338899204385593947555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12494237064545028250526813 4685338899204385593947555)
                ·
                  refine ⟨7028008348806578390921333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4685338899204385593947555 7028008348806578390921333)
                  ·
                    refine ⟨658875782700616724148875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7028008348806578390921333 658875782700616724148875)
                    ·
                      rfl

theorem cell23_3849468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_3849468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849468 prefixEnd_3849468 := by exact prefixLift 3849468
  have htrace : WordTrace (prefixWord ++ tailWord_3849468) baseStart_3849468 baseEnd_3849468 := by
    simpa [prefixWord, tailWord_3849468, baseEnd_3849468] using wordTrace_append hprefix tailTrace_3849468
  have hstable : (prefixWord ++ tailWord_3849468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849468).length < 2 ^ (prefixWord ++ tailWord_3849468).sum := by decide
  have hdescent : baseEnd_3849468 < baseStart_3849468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849481 : List Nat := [1, 2, 1, 1, 3, 3, 3, 1, 4, 4]
def baseStart_3849481 : Nat := 118140960795 + 3849481 * 2 ^ 59
def prefixEnd_3849481 : Nat := 4983230072969 + 3 ^ 40 * 3849481 * 2
def baseEnd_3849481 : Nat := 658878007783452873861355

theorem tailTrace_3849481 : CollatzResearch.WordTrace tailWord_3849481 prefixEnd_3849481 658878007783452873861355 := by
  unfold tailWord_3849481
  simp only [CollatzResearch.WordTrace]
  refine ⟨140402106566995250858516297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93601404377996833905677531 140402106566995250858516297)
  ·
    refine ⟨105301579925246438143887223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140402106566995250858516297 105301579925246438143887223)
    ·
      refine ⟨157952369887869657215830835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105301579925246438143887223 157952369887869657215830835)
      ·
        refine ⟨236928554831804485823746253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157952369887869657215830835 236928554831804485823746253)
        ·
          refine ⟨88848208061926682183904845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236928554831804485823746253 88848208061926682183904845)
          ·
            refine ⟨33318078023222505818964317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88848208061926682183904845 33318078023222505818964317)
            ·
              refine ⟨12494279258708439682111619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33318078023222505818964317 12494279258708439682111619)
              ·
                refine ⟨18741418888062659523167429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12494279258708439682111619 18741418888062659523167429)
                ·
                  refine ⟨3514016041511748660593893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18741418888062659523167429 3514016041511748660593893)
                  ·
                    refine ⟨658878007783452873861355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3514016041511748660593893 658878007783452873861355)
                    ·
                      rfl

theorem cell23_3849481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 4, 4].length) (baseStart_3849481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849481 prefixEnd_3849481 := by exact prefixLift 3849481
  have htrace : WordTrace (prefixWord ++ tailWord_3849481) baseStart_3849481 baseEnd_3849481 := by
    simpa [prefixWord, tailWord_3849481, baseEnd_3849481] using wordTrace_append hprefix tailTrace_3849481
  have hstable : (prefixWord ++ tailWord_3849481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849481).length < 2 ^ (prefixWord ++ tailWord_3849481).sum := by decide
  have hdescent : baseEnd_3849481 < baseStart_3849481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849498 : List Nat := [3, 1, 1, 3, 3, 3, 1, 1, 1, 6]
def baseStart_3849498 : Nat := 118140960795 + 3849498 * 2 ^ 59
def prefixEnd_3849498 : Nat := 4983230072969 + 3 ^ 40 * 3849498 * 2
def baseEnd_3849498 : Nat := 658880917507161685023829

theorem tailTrace_3849498 : CollatzResearch.WordTrace tailWord_3849498 prefixEnd_3849498 658880917507161685023829 := by
  unfold tailWord_3849498
  simp only [CollatzResearch.WordTrace]
  refine ⟨35100681651983415690471287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93601817738622441841256765 35100681651983415690471287)
  ·
    refine ⟨52651022477975123535706931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35100681651983415690471287 52651022477975123535706931)
    ·
      refine ⟨78976533716962685303560397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52651022477975123535706931 78976533716962685303560397)
      ·
        refine ⟨29616200143861006988835149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78976533716962685303560397 29616200143861006988835149)
        ·
          refine ⟨11106075053947877620813181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29616200143861006988835149 11106075053947877620813181)
          ·
            refine ⟨4164778145230454107804943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11106075053947877620813181 4164778145230454107804943)
            ·
              refine ⟨6247167217845681161707415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4164778145230454107804943 6247167217845681161707415)
              ·
                refine ⟨9370750826768521742561123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6247167217845681161707415 9370750826768521742561123)
                ·
                  refine ⟨14056126240152782613841685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9370750826768521742561123 14056126240152782613841685)
                  ·
                    refine ⟨658880917507161685023829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14056126240152782613841685 658880917507161685023829)
                    ·
                      rfl

theorem cell23_3849498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 1, 6].length) (baseStart_3849498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849498 prefixEnd_3849498 := by exact prefixLift 3849498
  have htrace : WordTrace (prefixWord ++ tailWord_3849498) baseStart_3849498 baseEnd_3849498 := by
    simpa [prefixWord, tailWord_3849498, baseEnd_3849498] using wordTrace_append hprefix tailTrace_3849498
  have hstable : (prefixWord ++ tailWord_3849498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849498).length < 2 ^ (prefixWord ++ tailWord_3849498).sum := by decide
  have hdescent : baseEnd_3849498 < baseStart_3849498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849502 : List Nat := [4, 3, 2, 1, 2, 1, 2, 2, 1, 5]
def baseStart_3849502 : Nat := 118140960795 + 3849502 * 2 ^ 59
def prefixEnd_3849502 : Nat := 4983230072969 + 3 ^ 40 * 3849502 * 2
def baseEnd_3849502 : Nat := 658881602148034346473823

theorem tailTrace_3849502 : CollatzResearch.WordTrace tailWord_3849502 prefixEnd_3849502 658881602148034346473823 := by
  unfold tailWord_3849502
  simp only [CollatzResearch.WordTrace]
  refine ⟨17550359062489896430628845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93601914999946114296687173 17550359062489896430628845)
  ·
    refine ⟨6581384648433711161485817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17550359062489896430628845 6581384648433711161485817)
    ·
      refine ⟨4936038486325283371114363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6581384648433711161485817 4936038486325283371114363)
      ·
        refine ⟨7404057729487925056671545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4936038486325283371114363 7404057729487925056671545)
        ·
          refine ⟨5553043297115943792503659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7404057729487925056671545 5553043297115943792503659)
          ·
            refine ⟨8329564945673915688755489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5553043297115943792503659 8329564945673915688755489)
            ·
              refine ⟨6247173709255436766566617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8329564945673915688755489 6247173709255436766566617)
              ·
                refine ⟨4685380281941577574924963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6247173709255436766566617 4685380281941577574924963)
                ·
                  refine ⟨7028070422912366362387445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4685380281941577574924963 7028070422912366362387445)
                  ·
                    refine ⟨658881602148034346473823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7028070422912366362387445 658881602148034346473823)
                    ·
                      rfl

theorem cell23_3849502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_3849502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849502 prefixEnd_3849502 := by exact prefixLift 3849502
  have htrace : WordTrace (prefixWord ++ tailWord_3849502) baseStart_3849502 baseEnd_3849502 := by
    simpa [prefixWord, tailWord_3849502, baseEnd_3849502] using wordTrace_append hprefix tailTrace_3849502
  have hstable : (prefixWord ++ tailWord_3849502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849502).length < 2 ^ (prefixWord ++ tailWord_3849502).sum := by decide
  have hdescent : baseEnd_3849502 < baseStart_3849502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849531 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 3, 9, 2]
def baseStart_3849531 : Nat := 118140960795 + 3849531 * 2 ^ 59
def prefixEnd_3849531 : Nat := 4983230072969 + 3 ^ 40 * 3849531 * 2
def baseEnd_3849531 : Nat := 1976659697383083425958835

theorem tailTrace_3849531 : CollatzResearch.WordTrace tailWord_3849531 prefixEnd_3849531 1976659697383083425958835 := by
  unfold tailWord_3849531
  simp only [CollatzResearch.WordTrace]
  refine ⟨140403930216814109397836447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93602620144542739598557631 140403930216814109397836447)
  ·
    refine ⟨210605895325221164096754671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140403930216814109397836447 210605895325221164096754671)
    ·
      refine ⟨315908842987831746145132007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210605895325221164096754671 315908842987831746145132007)
      ·
        refine ⟨473863264481747619217698011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315908842987831746145132007 473863264481747619217698011)
        ·
          refine ⟨710794896722621428826547017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473863264481747619217698011 710794896722621428826547017)
          ·
            refine ⟨533096172541966071619910263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 710794896722621428826547017 533096172541966071619910263)
            ·
              refine ⟨799644258812949107429865395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533096172541966071619910263 799644258812949107429865395)
              ·
                refine ⟨1199466388219423661144798093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 799644258812949107429865395 1199466388219423661144798093)
                ·
                  refine ⟨449799895582283872929299285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1199466388219423661144798093 449799895582283872929299285)
                  ·
                    refine ⟨2635546263177444567945113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 449799895582283872929299285 2635546263177444567945113)
                    ·
                      refine ⟨1976659697383083425958835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2635546263177444567945113 1976659697383083425958835)
                      ·
                        rfl

theorem cell23_3849531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 9, 2].length) (baseStart_3849531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849531 prefixEnd_3849531 := by exact prefixLift 3849531
  have htrace : WordTrace (prefixWord ++ tailWord_3849531) baseStart_3849531 baseEnd_3849531 := by
    simpa [prefixWord, tailWord_3849531, baseEnd_3849531] using wordTrace_append hprefix tailTrace_3849531
  have hstable : (prefixWord ++ tailWord_3849531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849531).length < 2 ^ (prefixWord ++ tailWord_3849531).sum := by decide
  have hdescent : baseEnd_3849531 < baseStart_3849531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849591 : List Nat := [1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 4]
def baseStart_3849591 : Nat := 118140960795 + 3849591 * 2 ^ 59
def prefixEnd_3849591 : Nat := 4983230072969 + 3 ^ 40 * 3849591 * 2
def baseEnd_3849591 : Nat := 1976690506222353191208559

theorem tailTrace_3849591 : CollatzResearch.WordTrace tailWord_3849591 prefixEnd_3849591 1976690506222353191208559 := by
  unfold tailWord_3849591
  simp only [CollatzResearch.WordTrace]
  refine ⟨140406118596596739645020627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93604079064397826430013751 140406118596596739645020627)
  ·
    refine ⟨210609177894895109467530941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140406118596596739645020627 210609177894895109467530941)
    ·
      refine ⟨78978441710585666050324103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210609177894895109467530941 78978441710585666050324103)
      ·
        refine ⟨118467662565878499075486155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78978441710585666050324103 118467662565878499075486155)
        ·
          refine ⟨177701493848817748613229233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118467662565878499075486155 177701493848817748613229233)
          ·
            refine ⟨133276120386613311459921925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177701493848817748613229233 133276120386613311459921925)
            ·
              refine ⟨24989272572489995898735361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133276120386613311459921925 24989272572489995898735361)
              ·
                refine ⟨18741954429367496924051521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24989272572489995898735361 18741954429367496924051521)
                ·
                  refine ⟨14056465822025622693038641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18741954429367496924051521 14056465822025622693038641)
                  ·
                    refine ⟨10542349366519217019778981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14056465822025622693038641 10542349366519217019778981)
                    ·
                      refine ⟨1976690506222353191208559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10542349366519217019778981 1976690506222353191208559)
                      ·
                        rfl

theorem cell23_3849591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_3849591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849591 prefixEnd_3849591 := by exact prefixLift 3849591
  have htrace : WordTrace (prefixWord ++ tailWord_3849591) baseStart_3849591 baseEnd_3849591 := by
    simpa [prefixWord, tailWord_3849591, baseEnd_3849591] using wordTrace_append hprefix tailTrace_3849591
  have hstable : (prefixWord ++ tailWord_3849591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849591).length < 2 ^ (prefixWord ++ tailWord_3849591).sum := by decide
  have hdescent : baseEnd_3849591 < baseStart_3849591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849608 : List Nat := [2, 1, 3, 3, 1, 3, 1, 1, 2, 2, 4]
def baseStart_3849608 : Nat := 118140960795 + 3849608 * 2 ^ 59
def prefixEnd_3849608 : Nat := 4983230072969 + 3 ^ 40 * 3849608 * 2
def baseEnd_3849608 : Nat := 1976699235393479624695981

theorem tailTrace_3849608 : CollatzResearch.WordTrace tailWord_3849608 prefixEnd_3849608 1976699235393479624695981 := by
  unfold tailWord_3849608
  simp only [CollatzResearch.WordTrace]
  refine ⟨70203369318767575774194739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93604492425023434365592985 70203369318767575774194739)
  ·
    refine ⟨105305053978151363661292109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70203369318767575774194739 105305053978151363661292109)
    ·
      refine ⟨39489395241806761372984541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105305053978151363661292109 39489395241806761372984541)
      ·
        refine ⟨14808523215677535514869203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39489395241806761372984541 14808523215677535514869203)
        ·
          refine ⟨22212784823516303272303805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14808523215677535514869203 22212784823516303272303805)
          ·
            refine ⟨8329794308818613727113927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22212784823516303272303805 8329794308818613727113927)
            ·
              refine ⟨12494691463227920590670891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8329794308818613727113927 12494691463227920590670891)
              ·
                refine ⟨18742037194841880886006337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12494691463227920590670891 18742037194841880886006337)
                ·
                  refine ⟨14056527896131410664504753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18742037194841880886006337 14056527896131410664504753)
                  ·
                    refine ⟨10542395922098557998378565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14056527896131410664504753 10542395922098557998378565)
                    ·
                      refine ⟨1976699235393479624695981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10542395922098557998378565 1976699235393479624695981)
                      ·
                        rfl

theorem cell23_3849608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_3849608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849608 prefixEnd_3849608 := by exact prefixLift 3849608
  have htrace : WordTrace (prefixWord ++ tailWord_3849608) baseStart_3849608 baseEnd_3849608 := by
    simpa [prefixWord, tailWord_3849608, baseEnd_3849608] using wordTrace_append hprefix tailTrace_3849608
  have hstable : (prefixWord ++ tailWord_3849608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849608).length < 2 ^ (prefixWord ++ tailWord_3849608).sum := by decide
  have hdescent : baseEnd_3849608 < baseStart_3849608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849645 : List Nat := [1, 5, 2, 2, 1, 1, 1, 2, 2, 3, 3]
def baseStart_3849645 : Nat := 118140960795 + 3849645 * 2 ^ 59
def prefixEnd_3849645 : Nat := 4983230072969 + 3 ^ 40 * 3849645 * 2
def baseEnd_3849645 : Nat := 1976718234177695979933311

theorem tailTrace_3849645 : CollatzResearch.WordTrace tailWord_3849645 prefixEnd_3849645 1976718234177695979933311 := by
  unfold tailWord_3849645
  simp only [CollatzResearch.WordTrace]
  refine ⟨140408088138401106867486389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93605392092267404578324259 140408088138401106867486389)
  ·
    refine ⟨13163258262975103768826849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140408088138401106867486389 13163258262975103768826849)
    ·
      refine ⟨9872443697231327826620137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13163258262975103768826849 9872443697231327826620137)
      ·
        refine ⟨7404332772923495869965103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9872443697231327826620137 7404332772923495869965103)
        ·
          refine ⟨11106499159385243804947655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7404332772923495869965103 11106499159385243804947655)
          ·
            refine ⟨16659748739077865707421483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11106499159385243804947655 16659748739077865707421483)
            ·
              refine ⟨24989623108616798561132225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16659748739077865707421483 24989623108616798561132225)
              ·
                refine ⟨18742217331462598920849169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24989623108616798561132225 18742217331462598920849169)
                ·
                  refine ⟨14056662998596949190636877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18742217331462598920849169 14056662998596949190636877)
                  ·
                    refine ⟨5271248624473855946488829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14056662998596949190636877 5271248624473855946488829)
                    ·
                      refine ⟨1976718234177695979933311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5271248624473855946488829 1976718234177695979933311)
                      ·
                        rfl

theorem cell23_3849645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_3849645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849645 prefixEnd_3849645 := by exact prefixLift 3849645
  have htrace : WordTrace (prefixWord ++ tailWord_3849645) baseStart_3849645 baseEnd_3849645 := by
    simpa [prefixWord, tailWord_3849645, baseEnd_3849645] using wordTrace_append hprefix tailTrace_3849645
  have hstable : (prefixWord ++ tailWord_3849645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849645).length < 2 ^ (prefixWord ++ tailWord_3849645).sum := by decide
  have hdescent : baseEnd_3849645 < baseStart_3849645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849688 : List Nat := [2, 1, 2, 2, 2, 1, 4, 1, 1, 4, 3]
def baseStart_3849688 : Nat := 118140960795 + 3849688 * 2 ^ 59
def prefixEnd_3849688 : Nat := 4983230072969 + 3 ^ 40 * 3849688 * 2
def baseEnd_3849688 : Nat := 1976740313845839311695613

theorem tailTrace_3849688 : CollatzResearch.WordTrace tailWord_3849688 prefixEnd_3849688 1976740313845839311695613 := by
  unfold tailWord_3849688
  simp only [CollatzResearch.WordTrace]
  refine ⟨70204828238622662605650859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93606437651496883474201145 70204828238622662605650859)
  ·
    refine ⟨105307242357933993908476289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70204828238622662605650859 105307242357933993908476289)
    ·
      refine ⟨78980431768450495431357217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105307242357933993908476289 78980431768450495431357217)
      ·
        refine ⟨59235323826337871573517913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78980431768450495431357217 59235323826337871573517913)
        ·
          refine ⟨44426492869753403680138435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59235323826337871573517913 44426492869753403680138435)
          ·
            refine ⟨66639739304630105520207653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44426492869753403680138435 66639739304630105520207653)
            ·
              refine ⟨12494951119618144785038935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66639739304630105520207653 12494951119618144785038935)
              ·
                refine ⟨18742426679427217177558403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12494951119618144785038935 18742426679427217177558403)
                ·
                  refine ⟨28113640019140825766337605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18742426679427217177558403 28113640019140825766337605)
                  ·
                    refine ⟨5271307503588904831188301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28113640019140825766337605 5271307503588904831188301)
                    ·
                      refine ⟨1976740313845839311695613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5271307503588904831188301 1976740313845839311695613)
                      ·
                        rfl

theorem cell23_3849688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_3849688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849688 prefixEnd_3849688 := by exact prefixLift 3849688
  have htrace : WordTrace (prefixWord ++ tailWord_3849688) baseStart_3849688 baseEnd_3849688 := by
    simpa [prefixWord, tailWord_3849688, baseEnd_3849688] using wordTrace_append hprefix tailTrace_3849688
  have hstable : (prefixWord ++ tailWord_3849688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849688).length < 2 ^ (prefixWord ++ tailWord_3849688).sum := by decide
  have hdescent : baseEnd_3849688 < baseStart_3849688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849711 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 8]
def baseStart_3849711 : Nat := 118140960795 + 3849711 * 2 ^ 59
def prefixEnd_3849711 : Nat := 4983230072969 + 3 ^ 40 * 3849711 * 2
def baseEnd_3849711 : Nat := 1976752123900892721708007

theorem tailTrace_3849711 : CollatzResearch.WordTrace tailWord_3849711 prefixEnd_3849711 1976752123900892721708007 := by
  unfold tailWord_3849711
  simp only [CollatzResearch.WordTrace]
  refine ⟨140410495356162000139388987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93606996904108000092925991 140410495356162000139388987)
  ·
    refine ⟨210615743034243000209083481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140410495356162000139388987 210615743034243000209083481)
    ·
      refine ⟨157961807275682250156812611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210615743034243000209083481 157961807275682250156812611)
      ·
        refine ⟨236942710913523375235218917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157961807275682250156812611 236942710913523375235218917)
        ·
          refine ⟨44426758296285632856603547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236942710913523375235218917 44426758296285632856603547)
          ·
            refine ⟨66640137444428449284905321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44426758296285632856603547 66640137444428449284905321)
            ·
              refine ⟨49980103083321336963678991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66640137444428449284905321 49980103083321336963678991)
              ·
                refine ⟨74970154624982005445518487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49980103083321336963678991 74970154624982005445518487)
                ·
                  refine ⟨112455231937473008168277731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74970154624982005445518487 112455231937473008168277731)
                  ·
                    refine ⟨168682847906209512252416597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112455231937473008168277731 168682847906209512252416597)
                    ·
                      refine ⟨1976752123900892721708007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 168682847906209512252416597 1976752123900892721708007)
                      ·
                        rfl

theorem cell23_3849711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 8].length) (baseStart_3849711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849711 prefixEnd_3849711 := by exact prefixLift 3849711
  have htrace : WordTrace (prefixWord ++ tailWord_3849711) baseStart_3849711 baseEnd_3849711 := by
    simpa [prefixWord, tailWord_3849711, baseEnd_3849711] using wordTrace_append hprefix tailTrace_3849711
  have hstable : (prefixWord ++ tailWord_3849711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849711).length < 2 ^ (prefixWord ++ tailWord_3849711).sum := by decide
  have hdescent : baseEnd_3849711 < baseStart_3849711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849721 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 2, 9]
def baseStart_3849721 : Nat := 118140960795 + 3849721 * 2 ^ 59
def prefixEnd_3849721 : Nat := 4983230072969 + 3 ^ 40 * 3849721 * 2
def baseEnd_3849721 : Nat := 658919086235812560860987

theorem tailTrace_3849721 : CollatzResearch.WordTrace tailWord_3849721 prefixEnd_3849721 658919086235812560860987 := by
  unfold tailWord_3849721
  simp only [CollatzResearch.WordTrace]
  refine ⟨140410860086125771847253017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93607240057417181231502011 140410860086125771847253017)
  ·
    refine ⟨105308145064594328885439763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140410860086125771847253017 105308145064594328885439763)
    ·
      refine ⟨157962217596891493328159645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105308145064594328885439763 157962217596891493328159645)
      ·
        refine ⟨59235831598834309998059867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157962217596891493328159645 59235831598834309998059867)
        ·
          refine ⟨88853747398251464997089801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59235831598834309998059867 88853747398251464997089801)
          ·
            refine ⟨66640310548688598747817351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88853747398251464997089801 66640310548688598747817351)
            ·
              refine ⟨99960465823032898121726027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66640310548688598747817351 99960465823032898121726027)
              ·
                refine ⟨149940698734549347182589041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99960465823032898121726027 149940698734549347182589041)
                ·
                  refine ⟨112455524050912010386941781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149940698734549347182589041 112455524050912010386941781)
                  ·
                    refine ⟨658919086235812560860987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 112455524050912010386941781 658919086235812560860987)
                    ·
                      rfl

theorem cell23_3849721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 9].length) (baseStart_3849721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849721 prefixEnd_3849721 := by exact prefixLift 3849721
  have htrace : WordTrace (prefixWord ++ tailWord_3849721) baseStart_3849721 baseEnd_3849721 := by
    simpa [prefixWord, tailWord_3849721, baseEnd_3849721] using wordTrace_append hprefix tailTrace_3849721
  have hstable : (prefixWord ++ tailWord_3849721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849721).length < 2 ^ (prefixWord ++ tailWord_3849721).sum := by decide
  have hdescent : baseEnd_3849721 < baseStart_3849721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849725 : List Nat := [1, 4, 1, 1, 1, 4, 4, 1, 6]
def baseStart_3849725 : Nat := 118140960795 + 3849725 * 2 ^ 59
def prefixEnd_3849725 : Nat := 4983230072969 + 3 ^ 40 * 3849725 * 2
def baseEnd_3849725 : Nat := 219639923625561740770327

theorem tailTrace_3849725 : CollatzResearch.WordTrace tailWord_3849725 prefixEnd_3849725 219639923625561740770327 := by
  unfold tailWord_3849725
  simp only [CollatzResearch.WordTrace]
  refine ⟨140411005978111280530398629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93607337318740853686932419 140411005978111280530398629)
  ·
    refine ⟨26327063620895865099449743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140411005978111280530398629 26327063620895865099449743)
    ·
      refine ⟨39490595431343797649174615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26327063620895865099449743 39490595431343797649174615)
      ·
        refine ⟨59235893147015696473761923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39490595431343797649174615 59235893147015696473761923)
        ·
          refine ⟨88853839720523544710642885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59235893147015696473761923 88853839720523544710642885)
          ·
            refine ⟨16660094947598164633245541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88853839720523544710642885 16660094947598164633245541)
            ·
              refine ⟨3123767802674655868733539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16660094947598164633245541 3123767802674655868733539)
              ·
                refine ⟨4685651704011983803100309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3123767802674655868733539 4685651704011983803100309)
                ·
                  refine ⟨219639923625561740770327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4685651704011983803100309 219639923625561740770327)
                  ·
                    rfl

theorem cell23_3849725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 6].length) (baseStart_3849725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849725 prefixEnd_3849725 := by exact prefixLift 3849725
  have htrace : WordTrace (prefixWord ++ tailWord_3849725) baseStart_3849725 baseEnd_3849725 := by
    simpa [prefixWord, tailWord_3849725, baseEnd_3849725] using wordTrace_append hprefix tailTrace_3849725
  have hstable : (prefixWord ++ tailWord_3849725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849725).length < 2 ^ (prefixWord ++ tailWord_3849725).sum := by decide
  have hdescent : baseEnd_3849725 < baseStart_3849725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849731 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 7]
def baseStart_3849731 : Nat := 118140960795 + 3849731 * 2 ^ 59
def prefixEnd_3849731 : Nat := 4983230072969 + 3 ^ 40 * 3849731 * 2
def baseEnd_3849731 : Nat := 1976762393513982643457915

theorem tailTrace_3849731 : CollatzResearch.WordTrace tailWord_3849731 prefixEnd_3849731 1976762393513982643457915 := by
  unfold tailWord_3849731
  simp only [CollatzResearch.WordTrace]
  refine ⟨140411224816089543555117047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93607483210726362370078031 140411224816089543555117047)
  ·
    refine ⟨210616837224134315332675571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140411224816089543555117047 210616837224134315332675571)
    ·
      refine ⟨315925255836201472999013357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210616837224134315332675571 315925255836201472999013357)
      ·
        refine ⟨118471970938575552374630009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315925255836201472999013357 118471970938575552374630009)
        ·
          refine ⟨88853978203931664280972507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118471970938575552374630009 88853978203931664280972507)
          ·
            refine ⟨133280967305897496421458761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88853978203931664280972507 133280967305897496421458761)
            ·
              refine ⟨99960725479423122316094071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133280967305897496421458761 99960725479423122316094071)
              ·
                refine ⟨149941088219134683474141107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99960725479423122316094071 149941088219134683474141107)
                ·
                  refine ⟨224911632328702025211211661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149941088219134683474141107 224911632328702025211211661)
                  ·
                    refine ⟨84341862123263259454204373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 224911632328702025211211661 84341862123263259454204373)
                    ·
                      refine ⟨1976762393513982643457915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84341862123263259454204373 1976762393513982643457915)
                      ·
                        rfl

theorem cell23_3849731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_3849731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849731 prefixEnd_3849731 := by exact prefixLift 3849731
  have htrace : WordTrace (prefixWord ++ tailWord_3849731) baseStart_3849731 baseEnd_3849731 := by
    simpa [prefixWord, tailWord_3849731, baseEnd_3849731] using wordTrace_append hprefix tailTrace_3849731
  have hstable : (prefixWord ++ tailWord_3849731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849731).length < 2 ^ (prefixWord ++ tailWord_3849731).sum := by decide
  have hdescent : baseEnd_3849731 < baseStart_3849731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849762 : List Nat := [3, 3, 1, 1, 1, 1, 4, 2, 2, 3, 2]
def baseStart_3849762 : Nat := 118140960795 + 3849762 * 2 ^ 59
def prefixEnd_3849762 : Nat := 4983230072969 + 3 ^ 40 * 3849762 * 2
def baseEnd_3849762 : Nat := 1976778311414272022170273

theorem tailTrace_3849762 : CollatzResearch.WordTrace tailWord_3849762 prefixEnd_3849762 1976778311414272022170273 := by
  unfold tailWord_3849762
  simp only [CollatzResearch.WordTrace]
  refine ⟨35103088869744308962373885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93608236985984823899663693 35103088869744308962373885)
  ·
    refine ⟨13163658326154115860890207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35103088869744308962373885 13163658326154115860890207)
    ·
      refine ⟨19745487489231173791335311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13163658326154115860890207 19745487489231173791335311)
      ·
        refine ⟨29618231233846760687002967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19745487489231173791335311 29618231233846760687002967)
        ·
          refine ⟨44427346850770141030504451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29618231233846760687002967 44427346850770141030504451)
          ·
            refine ⟨66641020276155211545756677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44427346850770141030504451 66641020276155211545756677)
            ·
              refine ⟨12495191301779102164829377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66641020276155211545756677 12495191301779102164829377)
              ·
                refine ⟨9371393476334326623622033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12495191301779102164829377 9371393476334326623622033)
                ·
                  refine ⟨7028545107250744967716525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9371393476334326623622033 7028545107250744967716525)
                  ·
                    refine ⟨2635704415219029362893697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7028545107250744967716525 2635704415219029362893697)
                    ·
                      refine ⟨1976778311414272022170273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2635704415219029362893697 1976778311414272022170273)
                      ·
                        rfl

theorem cell23_3849762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_3849762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849762 prefixEnd_3849762 := by exact prefixLift 3849762
  have htrace : WordTrace (prefixWord ++ tailWord_3849762) baseStart_3849762 baseEnd_3849762 := by
    simpa [prefixWord, tailWord_3849762, baseEnd_3849762] using wordTrace_append hprefix tailTrace_3849762
  have hstable : (prefixWord ++ tailWord_3849762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849762).length < 2 ^ (prefixWord ++ tailWord_3849762).sum := by decide
  have hdescent : baseEnd_3849762 < baseStart_3849762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849778 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5]
def baseStart_3849778 : Nat := 118140960795 + 3849778 * 2 ^ 59
def prefixEnd_3849778 : Nat := 4983230072969 + 3 ^ 40 * 3849778 * 2
def baseEnd_3849778 : Nat := 1976786527104743959570199

theorem tailTrace_3849778 : CollatzResearch.WordTrace tailWord_3849778 prefixEnd_3849778 1976786527104743959570199 := by
  unfold tailWord_3849778
  simp only [CollatzResearch.WordTrace]
  refine ⟨35103234761729817645519497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93608626031279513721385325 35103234761729817645519497)
  ·
    refine ⟨26327426071297363234139623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35103234761729817645519497 26327426071297363234139623)
    ·
      refine ⟨39491139106946044851209435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26327426071297363234139623 39491139106946044851209435)
      ·
        refine ⟨59236708660419067276814153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39491139106946044851209435 59236708660419067276814153)
        ·
          refine ⟨44427531495314300457610615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59236708660419067276814153 44427531495314300457610615)
          ·
            refine ⟨66641297242971450686415923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44427531495314300457610615 66641297242971450686415923)
            ·
              refine ⟨99961945864457176029623885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66641297242971450686415923 99961945864457176029623885)
              ·
                refine ⟨37485729699171441011108957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99961945864457176029623885 37485729699171441011108957)
                ·
                  refine ⟨14057148637189290379165859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37485729699171441011108957 14057148637189290379165859)
                  ·
                    refine ⟨21085722955783935568748789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14057148637189290379165859 21085722955783935568748789)
                    ·
                      refine ⟨1976786527104743959570199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21085722955783935568748789 1976786527104743959570199)
                      ·
                        rfl

theorem cell23_3849778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_3849778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849778 prefixEnd_3849778 := by exact prefixLift 3849778
  have htrace : WordTrace (prefixWord ++ tailWord_3849778) baseStart_3849778 baseEnd_3849778 := by
    simpa [prefixWord, tailWord_3849778, baseEnd_3849778] using wordTrace_append hprefix tailTrace_3849778
  have hstable : (prefixWord ++ tailWord_3849778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849778).length < 2 ^ (prefixWord ++ tailWord_3849778).sum := by decide
  have hdescent : baseEnd_3849778 < baseStart_3849778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849785 : List Nat := [1, 2, 1, 5, 1, 3, 2, 1, 1, 6]
def baseStart_3849785 : Nat := 118140960795 + 3849785 * 2 ^ 59
def prefixEnd_3849785 : Nat := 4983230072969 + 3 ^ 40 * 3849785 * 2
def baseEnd_3849785 : Nat := 658930040489775144060889

theorem tailTrace_3849785 : CollatzResearch.WordTrace tailWord_3849785 prefixEnd_3849785 658930040489775144060889 := by
  unfold tailWord_3849785
  simp only [CollatzResearch.WordTrace]
  refine ⟨140413194357893910777582809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93608796238595940518388539 140413194357893910777582809)
  ·
    refine ⟨105309895768420433083187107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140413194357893910777582809 105309895768420433083187107)
    ·
      refine ⟨157964843652630649624780661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105309895768420433083187107 157964843652630649624780661)
      ·
        refine ⟨14809204092434123402323187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157964843652630649624780661 14809204092434123402323187)
        ·
          refine ⟨22213806138651185103484781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14809204092434123402323187 22213806138651185103484781)
          ·
            refine ⟨8330177301994194413806793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22213806138651185103484781 8330177301994194413806793)
            ·
              refine ⟨6247632976495645810355095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8330177301994194413806793 6247632976495645810355095)
              ·
                refine ⟨9371449464743468715532643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6247632976495645810355095 9371449464743468715532643)
                ·
                  refine ⟨14057174197115203073298965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9371449464743468715532643 14057174197115203073298965)
                  ·
                    refine ⟨658930040489775144060889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14057174197115203073298965 658930040489775144060889)
                    ·
                      rfl

theorem cell23_3849785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 6].length) (baseStart_3849785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849785 prefixEnd_3849785 := by exact prefixLift 3849785
  have htrace : WordTrace (prefixWord ++ tailWord_3849785) baseStart_3849785 baseEnd_3849785 := by
    simpa [prefixWord, tailWord_3849785, baseEnd_3849785] using wordTrace_append hprefix tailTrace_3849785
  have hstable : (prefixWord ++ tailWord_3849785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849785).length < 2 ^ (prefixWord ++ tailWord_3849785).sum := by decide
  have hdescent : baseEnd_3849785 < baseStart_3849785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849812 : List Nat := [2, 4, 1, 1, 1, 2, 3, 3, 1, 2, 3]
def baseStart_3849812 : Nat := 118140960795 + 3849812 * 2 ^ 59
def prefixEnd_3849812 : Nat := 4983230072969 + 3 ^ 40 * 3849812 * 2
def baseEnd_3849812 : Nat := 1976803985446996826545043

theorem tailTrace_3849812 : CollatzResearch.WordTrace tailWord_3849812 prefixEnd_3849812 1976803985446996826545043 := by
  unfold tailWord_3849812
  simp only [CollatzResearch.WordTrace]
  refine ⟨70207089564398047194407845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93609452752530729592543793 70207089564398047194407845)
  ·
    refine ⟨13163829293324633848951471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70207089564398047194407845 13163829293324633848951471)
    ·
      refine ⟨19745743939986950773427207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13163829293324633848951471 19745743939986950773427207)
      ·
        refine ⟨29618615909980426160140811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19745743939986950773427207 29618615909980426160140811)
        ·
          refine ⟨44427923864970639240211217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29618615909980426160140811 44427923864970639240211217)
          ·
            refine ⟨33320942898727979430158413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44427923864970639240211217 33320942898727979430158413)
            ·
              refine ⟨12495353587022992286309405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33320942898727979430158413 12495353587022992286309405)
              ·
                refine ⟨4685757595133622107366027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12495353587022992286309405 4685757595133622107366027)
                ·
                  refine ⟨7028636392700433161049041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4685757595133622107366027 7028636392700433161049041)
                  ·
                    refine ⟨5271477294525324870786781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7028636392700433161049041 5271477294525324870786781)
                    ·
                      refine ⟨1976803985446996826545043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5271477294525324870786781 1976803985446996826545043)
                      ·
                        rfl

theorem cell23_3849812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_3849812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849812 prefixEnd_3849812 := by exact prefixLift 3849812
  have htrace : WordTrace (prefixWord ++ tailWord_3849812) baseStart_3849812 baseEnd_3849812 := by
    simpa [prefixWord, tailWord_3849812, baseEnd_3849812] using wordTrace_append hprefix tailTrace_3849812
  have hstable : (prefixWord ++ tailWord_3849812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849812).length < 2 ^ (prefixWord ++ tailWord_3849812).sum := by decide
  have hdescent : baseEnd_3849812 < baseStart_3849812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849842 : List Nat := [3, 2, 1, 2, 3, 1, 3, 1, 1, 3, 3]
def baseStart_3849842 : Nat := 118140960795 + 3849842 * 2 ^ 59
def prefixEnd_3849842 : Nat := 4983230072969 + 3 ^ 40 * 3849842 * 2
def baseEnd_3849842 : Nat := 1976819389866631709169905

theorem tailTrace_3849842 : CollatzResearch.WordTrace tailWord_3849842 prefixEnd_3849842 1976819389866631709169905 := by
  unfold tailWord_3849842
  simp only [CollatzResearch.WordTrace]
  refine ⟨35103818329671852378101945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93610182212458273008271853 35103818329671852378101945)
  ·
    refine ⟨26327863747253889283576459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35103818329671852378101945 26327863747253889283576459)
    ·
      refine ⟨39491795620880833925364689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26327863747253889283576459 39491795620880833925364689)
      ·
        refine ⟨29618846715660625444023517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39491795620880833925364689 29618846715660625444023517)
        ·
          refine ⟨11107067518372734541508819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29618846715660625444023517 11107067518372734541508819)
          ·
            refine ⟨16660601277559101812263229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11107067518372734541508819 16660601277559101812263229)
            ·
              refine ⟨6247725479084663179598711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16660601277559101812263229 6247725479084663179598711)
              ·
                refine ⟨9371588218626994769398067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6247725479084663179598711 9371588218626994769398067)
                ·
                  refine ⟨14057382327940492154097101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9371588218626994769398067 14057382327940492154097101)
                  ·
                    refine ⟨5271518372977684557786413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14057382327940492154097101 5271518372977684557786413)
                    ·
                      refine ⟨1976819389866631709169905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5271518372977684557786413 1976819389866631709169905)
                      ·
                        rfl

theorem cell23_3849842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_3849842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849842 prefixEnd_3849842 := by exact prefixLift 3849842
  have htrace : WordTrace (prefixWord ++ tailWord_3849842) baseStart_3849842 baseEnd_3849842 := by
    simpa [prefixWord, tailWord_3849842, baseEnd_3849842] using wordTrace_append hprefix tailTrace_3849842
  have hstable : (prefixWord ++ tailWord_3849842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849842).length < 2 ^ (prefixWord ++ tailWord_3849842).sum := by decide
  have hdescent : baseEnd_3849842 < baseStart_3849842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849860 : List Nat := [2, 3, 2, 1, 5, 1, 1, 3, 1, 2, 2]
def baseStart_3849860 : Nat := 118140960795 + 3849860 * 2 ^ 59
def prefixEnd_3849860 : Nat := 4983230072969 + 3 ^ 40 * 3849860 * 2
def baseEnd_3849860 : Nat := 1976828632518412638744823

theorem tailTrace_3849860 : CollatzResearch.WordTrace tailWord_3849860 prefixEnd_3849860 1976828632518412638744823 := by
  unfold tailWord_3849860
  simp only [CollatzResearch.WordTrace]
  refine ⟨70207964916311099293281517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93610619888414799057708689 70207964916311099293281517)
  ·
    refine ⟨26327986843616662234980569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70207964916311099293281517 26327986843616662234980569)
    ·
      refine ⟨19745990132712496676235427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26327986843616662234980569 19745990132712496676235427)
      ·
        refine ⟨29618985199068745014353141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19745990132712496676235427 29618985199068745014353141)
        ·
          refine ⟨2776779862412694845095607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29618985199068745014353141 2776779862412694845095607)
          ·
            refine ⟨4165169793619042267643411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2776779862412694845095607 4165169793619042267643411)
            ·
              refine ⟨6247754690428563401465117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4165169793619042267643411 6247754690428563401465117)
              ·
                refine ⟨2342908008910711275549419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6247754690428563401465117 2342908008910711275549419)
                ·
                  refine ⟨3514362013366066913324129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2342908008910711275549419 3514362013366066913324129)
                  ·
                    refine ⟨2635771510024550184993097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3514362013366066913324129 2635771510024550184993097)
                    ·
                      refine ⟨1976828632518412638744823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2635771510024550184993097 1976828632518412638744823)
                      ·
                        rfl

theorem cell23_3849860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_3849860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849860 prefixEnd_3849860 := by exact prefixLift 3849860
  have htrace : WordTrace (prefixWord ++ tailWord_3849860) baseStart_3849860 baseEnd_3849860 := by
    simpa [prefixWord, tailWord_3849860, baseEnd_3849860] using wordTrace_append hprefix tailTrace_3849860
  have hstable : (prefixWord ++ tailWord_3849860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849860).length < 2 ^ (prefixWord ++ tailWord_3849860).sum := by decide
  have hdescent : baseEnd_3849860 < baseStart_3849860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849885 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 2, 4, 3]
def baseStart_3849885 : Nat := 118140960795 + 3849885 * 2 ^ 59
def prefixEnd_3849885 : Nat := 4983230072969 + 3 ^ 40 * 3849885 * 2
def baseEnd_3849885 : Nat := 1976841469534775040932207

theorem tailTrace_3849885 : CollatzResearch.WordTrace tailWord_3849885 prefixEnd_3849885 1976841469534775040932207 := by
  unfold tailWord_3849885
  simp only [CollatzResearch.WordTrace]
  refine ⟨140416841657531627856223109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93611227771687751904148739 140416841657531627856223109)
  ·
    refine ⟨26328157810787180223041833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140416841657531627856223109 26328157810787180223041833)
    ·
      refine ⟨19746118358090385167281375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26328157810787180223041833 19746118358090385167281375)
      ·
        refine ⟨29619177537135577750922063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19746118358090385167281375 29619177537135577750922063)
        ·
          refine ⟨44428766305703366626383095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29619177537135577750922063 44428766305703366626383095)
          ·
            refine ⟨66643149458555049939574643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44428766305703366626383095 66643149458555049939574643)
            ·
              refine ⟨99964724187832574909361965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66643149458555049939574643 99964724187832574909361965)
              ·
                refine ⟨37486771570437215591010737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99964724187832574909361965 37486771570437215591010737)
                ·
                  refine ⟨28115078677827911693258053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37486771570437215591010737 28115078677827911693258053)
                  ·
                    refine ⟨5271577252092733442485885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28115078677827911693258053 5271577252092733442485885)
                    ·
                      refine ⟨1976841469534775040932207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5271577252092733442485885 1976841469534775040932207)
                      ·
                        rfl

theorem cell23_3849885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_3849885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849885 prefixEnd_3849885 := by exact prefixLift 3849885
  have htrace : WordTrace (prefixWord ++ tailWord_3849885) baseStart_3849885 baseEnd_3849885 := by
    simpa [prefixWord, tailWord_3849885, baseEnd_3849885] using wordTrace_append hprefix tailTrace_3849885
  have hstable : (prefixWord ++ tailWord_3849885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849885).length < 2 ^ (prefixWord ++ tailWord_3849885).sum := by decide
  have hdescent : baseEnd_3849885 < baseStart_3849885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849933 : List Nat := [1, 6, 2, 1, 1, 1, 1, 4, 2, 2, 2]
def baseStart_3849933 : Nat := 118140960795 + 3849933 * 2 ^ 59
def prefixEnd_3849933 : Nat := 4983230072969 + 3 ^ 40 * 3849933 * 2
def baseEnd_3849933 : Nat := 1976866116606190853131987

theorem tailTrace_3849933 : CollatzResearch.WordTrace tailWord_3849933 prefixEnd_3849933 1976866116606190853131987 := by
  unfold tailWord_3849933
  simp only [CollatzResearch.WordTrace]
  refine ⟨140418592361357732053970453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93612394907571821369313635 140418592361357732053970453)
  ·
    refine ⟨6582121516938643690029865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 140418592361357732053970453 6582121516938643690029865)
    ·
      refine ⟨4936591137703982767522399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6582121516938643690029865 4936591137703982767522399)
      ·
        refine ⟨7404886706555974151283599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4936591137703982767522399 7404886706555974151283599)
        ·
          refine ⟨11107330059833961226925399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7404886706555974151283599 11107330059833961226925399)
          ·
            refine ⟨16660995089750941840388099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11107330059833961226925399 16660995089750941840388099)
            ·
              refine ⟨24991492634626412760582149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16660995089750941840388099 24991492634626412760582149)
              ·
                refine ⟨4685904868992452392609153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24991492634626412760582149 4685904868992452392609153)
                ·
                  refine ⟨3514428651744339294456865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4685904868992452392609153 3514428651744339294456865)
                  ·
                    refine ⟨2635821488808254470842649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3514428651744339294456865 2635821488808254470842649)
                    ·
                      refine ⟨1976866116606190853131987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2635821488808254470842649 1976866116606190853131987)
                      ·
                        rfl

theorem cell23_3849933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_3849933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849933 prefixEnd_3849933 := by exact prefixLift 3849933
  have htrace : WordTrace (prefixWord ++ tailWord_3849933) baseStart_3849933 baseEnd_3849933 := by
    simpa [prefixWord, tailWord_3849933, baseEnd_3849933] using wordTrace_append hprefix tailTrace_3849933
  have hstable : (prefixWord ++ tailWord_3849933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849933).length < 2 ^ (prefixWord ++ tailWord_3849933).sum := by decide
  have hdescent : baseEnd_3849933 < baseStart_3849933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849945 : List Nat := [1, 2, 1, 2, 3, 3, 2, 1, 1, 2, 5]
def baseStart_3849945 : Nat := 118140960795 + 3849945 * 2 ^ 59
def prefixEnd_3849945 : Nat := 4983230072969 + 3 ^ 40 * 3849945 * 2
def baseEnd_3849945 : Nat := 1976872278374044806181931

theorem tailTrace_3849945 : CollatzResearch.WordTrace tailWord_3849945 prefixEnd_3849945 1976872278374044806181931 := by
  unfold tailWord_3849945
  simp only [CollatzResearch.WordTrace]
  refine ⟨140419030037314258103407289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93612686691542838735604859 140419030037314258103407289)
  ·
    refine ⟨105314272527985693577555467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140419030037314258103407289 105314272527985693577555467)
    ·
      refine ⟨157971408791978540366333201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105314272527985693577555467 157971408791978540366333201)
      ·
        refine ⟨118478556593983905274749901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157971408791978540366333201 118478556593983905274749901)
        ·
          refine ⟨44429458722743964478031213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118478556593983905274749901 44429458722743964478031213)
          ·
            refine ⟨16661047021028986679261705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44429458722743964478031213 16661047021028986679261705)
            ·
              refine ⟨12495785265771740009446279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16661047021028986679261705 12495785265771740009446279)
              ·
                refine ⟨18743677898657610014169419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12495785265771740009446279 18743677898657610014169419)
                ·
                  refine ⟨28115516847986415021254129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18743677898657610014169419 28115516847986415021254129)
                  ·
                    refine ⟨21086637635989811265940597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28115516847986415021254129 21086637635989811265940597)
                    ·
                      refine ⟨1976872278374044806181931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21086637635989811265940597 1976872278374044806181931)
                      ·
                        rfl

theorem cell23_3849945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_3849945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849945 prefixEnd_3849945 := by exact prefixLift 3849945
  have htrace : WordTrace (prefixWord ++ tailWord_3849945) baseStart_3849945 baseEnd_3849945 := by
    simpa [prefixWord, tailWord_3849945, baseEnd_3849945] using wordTrace_append hprefix tailTrace_3849945
  have hstable : (prefixWord ++ tailWord_3849945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849945).length < 2 ^ (prefixWord ++ tailWord_3849945).sum := by decide
  have hdescent : baseEnd_3849945 < baseStart_3849945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849985 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 2, 1, 6]
def baseStart_3849985 : Nat := 118140960795 + 3849985 * 2 ^ 59
def prefixEnd_3849985 : Nat := 4983230072969 + 3 ^ 40 * 3849985 * 2
def baseEnd_3849985 : Nat := 1976892817600224649681747

theorem tailTrace_3849985 : CollatzResearch.WordTrace tailWord_3849985 prefixEnd_3849985 1976892817600224649681747 := by
  unfold tailWord_3849985
  simp only [CollatzResearch.WordTrace]
  refine ⟨140420488957169344934863409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93613659304779563289908939 140420488957169344934863409)
  ·
    refine ⟨105315366717877008701147557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140420488957169344934863409 105315366717877008701147557)
    ·
      refine ⟨19746631259601939131465167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105315366717877008701147557 19746631259601939131465167)
      ·
        refine ⟨29619946889402908697197751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19746631259601939131465167 29619946889402908697197751)
        ·
          refine ⟨44429920334104363045796627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29619946889402908697197751 44429920334104363045796627)
          ·
            refine ⟨66644880501156544568694941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44429920334104363045796627 66644880501156544568694941)
            ·
              refine ⟨24991830187933704213260603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66644880501156544568694941 24991830187933704213260603)
              ·
                refine ⟨37487745281900556319890905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24991830187933704213260603 37487745281900556319890905)
                ·
                  refine ⟨28115808961425417239918179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37487745281900556319890905 28115808961425417239918179)
                  ·
                    refine ⟨42173713442138125859877269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28115808961425417239918179 42173713442138125859877269)
                    ·
                      refine ⟨1976892817600224649681747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42173713442138125859877269 1976892817600224649681747)
                      ·
                        rfl

theorem cell23_3849985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_3849985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849985 prefixEnd_3849985 := by exact prefixLift 3849985
  have htrace : WordTrace (prefixWord ++ tailWord_3849985) baseStart_3849985 baseEnd_3849985 := by
    simpa [prefixWord, tailWord_3849985, baseEnd_3849985] using wordTrace_append hprefix tailTrace_3849985
  have hstable : (prefixWord ++ tailWord_3849985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849985).length < 2 ^ (prefixWord ++ tailWord_3849985).sum := by decide
  have hdescent : baseEnd_3849985 < baseStart_3849985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849990 : List Nat := [6, 2, 2, 1, 1, 1, 2, 1, 7]
def baseStart_3849990 : Nat := 118140960795 + 3849990 * 2 ^ 59
def prefixEnd_3849990 : Nat := 4983230072969 + 3 ^ 40 * 3849990 * 2
def baseEnd_3849990 : Nat := 219655042778166347791025

theorem tailTrace_3849990 : CollatzResearch.WordTrace tailWord_3849990 prefixEnd_3849990 219655042778166347791025 := by
  unfold tailWord_3849990
  simp only [CollatzResearch.WordTrace]
  refine ⟨4388145978817225962149857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 93613780881434153859196949 4388145978817225962149857)
  ·
    refine ⟨3291109484112919471612393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4388145978817225962149857 3291109484112919471612393)
    ·
      refine ⟨2468332113084689603709295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3291109484112919471612393 2468332113084689603709295)
      ·
        refine ⟨3702498169627034405563943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2468332113084689603709295 3702498169627034405563943)
        ·
          refine ⟨5553747254440551608345915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3702498169627034405563943 5553747254440551608345915)
          ·
            refine ⟨8330620881660827412518873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5553747254440551608345915 8330620881660827412518873)
            ·
              refine ⟨6247965661245620559389155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8330620881660827412518873 6247965661245620559389155)
              ·
                refine ⟨9371948491868430839083733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6247965661245620559389155 9371948491868430839083733)
                ·
                  refine ⟨219655042778166347791025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9371948491868430839083733 219655042778166347791025)
                  ·
                    rfl

theorem cell23_3849990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_3849990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849990 prefixEnd_3849990 := by exact prefixLift 3849990
  have htrace : WordTrace (prefixWord ++ tailWord_3849990) baseStart_3849990 baseEnd_3849990 := by
    simpa [prefixWord, tailWord_3849990, baseEnd_3849990] using wordTrace_append hprefix tailTrace_3849990
  have hstable : (prefixWord ++ tailWord_3849990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849990).length < 2 ^ (prefixWord ++ tailWord_3849990).sum := by decide
  have hdescent : baseEnd_3849990 < baseStart_3849990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849992 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 4, 2, 3]
def baseStart_3849992 : Nat := 118140960795 + 3849992 * 2 ^ 59
def prefixEnd_3849992 : Nat := 4983230072969 + 3 ^ 40 * 3849992 * 2
def baseEnd_3849992 : Nat := 1976896411964806122294215

theorem tailTrace_3849992 : CollatzResearch.WordTrace tailWord_3849992 prefixEnd_3849992 1976896411964806122294215 := by
  unfold tailWord_3849992
  simp only [CollatzResearch.WordTrace]
  refine ⟨70210372134071992565184115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93613829512095990086912153 70210372134071992565184115)
  ·
    refine ⟨105315558201107988847776173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70210372134071992565184115 105315558201107988847776173)
    ·
      refine ⟨39493334325415495817916065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105315558201107988847776173 39493334325415495817916065)
      ·
        refine ⟨29620000744061621863437049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39493334325415495817916065 29620000744061621863437049)
        ·
          refine ⟨22215000558046216397577787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29620000744061621863437049 22215000558046216397577787)
          ·
            refine ⟨33322500837069324596366681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22215000558046216397577787 33322500837069324596366681)
            ·
              refine ⟨24991875627801993447275011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33322500837069324596366681 24991875627801993447275011)
              ·
                refine ⟨37487813441702990170912517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24991875627801993447275011 37487813441702990170912517)
                ·
                  refine ⟨7028965020319310657046097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37487813441702990170912517 7028965020319310657046097)
                  ·
                    refine ⟨5271723765239482992784573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7028965020319310657046097 5271723765239482992784573)
                    ·
                      refine ⟨1976896411964806122294215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5271723765239482992784573 1976896411964806122294215)
                      ·
                        rfl

theorem cell23_3849992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_3849992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849992 prefixEnd_3849992 := by exact prefixLift 3849992
  have htrace : WordTrace (prefixWord ++ tailWord_3849992) baseStart_3849992 baseEnd_3849992 := by
    simpa [prefixWord, tailWord_3849992, baseEnd_3849992] using wordTrace_append hprefix tailTrace_3849992
  have hstable : (prefixWord ++ tailWord_3849992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849992).length < 2 ^ (prefixWord ++ tailWord_3849992).sum := by decide
  have hdescent : baseEnd_3849992 < baseStart_3849992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850015 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 6]
def baseStart_3850015 : Nat := 118140960795 + 3850015 * 2 ^ 59
def prefixEnd_3850015 : Nat := 4983230072969 + 3 ^ 40 * 3850015 * 2
def baseEnd_3850015 : Nat := 1976908222019859532306609

theorem tailTrace_3850015 : CollatzResearch.WordTrace tailWord_3850015 prefixEnd_3850015 1976908222019859532306609 := by
  unfold tailWord_3850015
  simp only [CollatzResearch.WordTrace]
  refine ⟨140421583147060660058455499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93614388764707106705636999 140421583147060660058455499)
  ·
    refine ⟨210632374720590990087683249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140421583147060660058455499 210632374720590990087683249)
    ·
      refine ⟨157974281040443242565762437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210632374720590990087683249 157974281040443242565762437)
      ·
        refine ⟨29620177695083107981080457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157974281040443242565762437 29620177695083107981080457)
        ·
          refine ⟨22215133271312330985810343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29620177695083107981080457 22215133271312330985810343)
          ·
            refine ⟨33322699906968496478715515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22215133271312330985810343 33322699906968496478715515)
            ·
              refine ⟨49984049860452744718073273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33322699906968496478715515 49984049860452744718073273)
              ·
                refine ⟨37488037395339558538554955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49984049860452744718073273 37488037395339558538554955)
                ·
                  refine ⟨56232056093009337807832433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37488037395339558538554955 56232056093009337807832433)
                  ·
                    refine ⟨42174042069757003355874325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56232056093009337807832433 42174042069757003355874325)
                    ·
                      refine ⟨1976908222019859532306609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42174042069757003355874325 1976908222019859532306609)
                      ·
                        rfl

theorem cell23_3850015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_3850015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850015 prefixEnd_3850015 := by exact prefixLift 3850015
  have htrace : WordTrace (prefixWord ++ tailWord_3850015) baseStart_3850015 baseEnd_3850015 := by
    simpa [prefixWord, tailWord_3850015, baseEnd_3850015] using wordTrace_append hprefix tailTrace_3850015
  have hstable : (prefixWord ++ tailWord_3850015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850015).length < 2 ^ (prefixWord ++ tailWord_3850015).sum := by decide
  have hdescent : baseEnd_3850015 < baseStart_3850015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850056 : List Nat := [2, 1, 3, 1, 1, 6, 1, 1, 3, 1, 3]
def baseStart_3850056 : Nat := 118140960795 + 3850056 * 2 ^ 59
def prefixEnd_3850056 : Nat := 4983230072969 + 3 ^ 40 * 3850056 * 2
def baseEnd_3850056 : Nat := 1976929274726693871893921

theorem tailTrace_3850056 : CollatzResearch.WordTrace tailWord_3850056 prefixEnd_3850056 1976929274726693871893921 := by
  unfold tailWord_3850056
  simp only [CollatzResearch.WordTrace]
  refine ⟨70211539269956062030349011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93615385693274749373798681 70211539269956062030349011)
  ·
    refine ⟨105317308904934093045523517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70211539269956062030349011 105317308904934093045523517)
    ·
      refine ⟨39493990839350284892071319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105317308904934093045523517 39493990839350284892071319)
      ·
        refine ⟨59240986259025427338106979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39493990839350284892071319 59240986259025427338106979)
        ·
          refine ⟨88861479388538141007160469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59240986259025427338106979 88861479388538141007160469)
          ·
            refine ⟨4165381846337725359710647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 88861479388538141007160469 4165381846337725359710647)
            ·
              refine ⟨6248072769506588039565971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4165381846337725359710647 6248072769506588039565971)
              ·
                refine ⟨9372109154259882059348957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6248072769506588039565971 9372109154259882059348957)
                ·
                  refine ⟨3514540932847455772255859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9372109154259882059348957 3514540932847455772255859)
                  ·
                    refine ⟨5271811399271183658383789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3514540932847455772255859 5271811399271183658383789)
                    ·
                      refine ⟨1976929274726693871893921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5271811399271183658383789 1976929274726693871893921)
                      ·
                        rfl

theorem cell23_3850056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_3850056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850056 prefixEnd_3850056 := by exact prefixLift 3850056
  have htrace : WordTrace (prefixWord ++ tailWord_3850056) baseStart_3850056 baseEnd_3850056 := by
    simpa [prefixWord, tailWord_3850056, baseEnd_3850056] using wordTrace_append hprefix tailTrace_3850056
  have hstable : (prefixWord ++ tailWord_3850056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850056).length < 2 ^ (prefixWord ++ tailWord_3850056).sum := by decide
  have hdescent : baseEnd_3850056 < baseStart_3850056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850075 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 4]
def baseStart_3850075 : Nat := 118140960795 + 3850075 * 2 ^ 59
def prefixEnd_3850075 : Nat := 4983230072969 + 3 ^ 40 * 3850075 * 2
def baseEnd_3850075 : Nat := 1976939030859129297556333

theorem tailTrace_3850075 : CollatzResearch.WordTrace tailWord_3850075 prefixEnd_3850075 1976939030859129297556333 := by
  unfold tailWord_3850075
  simp only [CollatzResearch.WordTrace]
  refine ⟨140423771526843290305639679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93615847684562193537093119 140423771526843290305639679)
  ·
    refine ⟨210635657290264935458459519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140423771526843290305639679 210635657290264935458459519)
    ·
      refine ⟨315953485935397403187689279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210635657290264935458459519 315953485935397403187689279)
      ·
        refine ⟨473930228903096104781533919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315953485935397403187689279 473930228903096104781533919)
        ·
          refine ⟨710895343354644157172300879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473930228903096104781533919 710895343354644157172300879)
          ·
            refine ⟨1066343015031966235758451319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710895343354644157172300879 1066343015031966235758451319)
            ·
              refine ⟨1599514522547949353637676979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1066343015031966235758451319 1599514522547949353637676979)
              ·
                refine ⟨2399271783821924030456515469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599514522547949353637676979 2399271783821924030456515469)
                ·
                  refine ⟨899726918933221511421193301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2399271783821924030456515469 899726918933221511421193301)
                  ·
                    refine ⟨10543674831248689586967109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 899726918933221511421193301 10543674831248689586967109)
                    ·
                      refine ⟨1976939030859129297556333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10543674831248689586967109 1976939030859129297556333)
                      ·
                        rfl

theorem cell23_3850075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 4].length) (baseStart_3850075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850075 prefixEnd_3850075 := by exact prefixLift 3850075
  have htrace : WordTrace (prefixWord ++ tailWord_3850075) baseStart_3850075 baseEnd_3850075 := by
    simpa [prefixWord, tailWord_3850075, baseEnd_3850075] using wordTrace_append hprefix tailTrace_3850075
  have hstable : (prefixWord ++ tailWord_3850075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850075).length < 2 ^ (prefixWord ++ tailWord_3850075).sum := by decide
  have hdescent : baseEnd_3850075 < baseStart_3850075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850079 : List Nat := [1, 1, 2, 3, 1, 4, 3, 2, 1, 1, 4]
def baseStart_3850079 : Nat := 118140960795 + 3850079 * 2 ^ 59
def prefixEnd_3850079 : Nat := 4983230072969 + 3 ^ 40 * 3850079 * 2
def baseEnd_3850079 : Nat := 1976941084781747281906315

theorem tailTrace_3850079 : CollatzResearch.WordTrace tailWord_3850079 prefixEnd_3850079 1976941084781747281906315 := by
  unfold tailWord_3850079
  simp only [CollatzResearch.WordTrace]
  refine ⟨140423917418828798988785291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93615944945885865992523527 140423917418828798988785291)
  ·
    refine ⟨210635876128243198483177937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140423917418828798988785291 210635876128243198483177937)
    ·
      refine ⟨157976907096182398862383453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210635876128243198483177937 157976907096182398862383453)
      ·
        refine ⟨59241340161068399573393795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157976907096182398862383453 59241340161068399573393795)
        ·
          refine ⟨88862010241602599360090693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59241340161068399573393795 88862010241602599360090693)
          ·
            refine ⟨16661626920300487380017005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88862010241602599360090693 16661626920300487380017005)
            ·
              refine ⟨6248110095112682767506377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16661626920300487380017005 6248110095112682767506377)
              ·
                refine ⟨4686082571334512075629783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6248110095112682767506377 4686082571334512075629783)
                ·
                  refine ⟨7029123857001768113444675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4686082571334512075629783 7029123857001768113444675)
                  ·
                    refine ⟨10543685785502652170167013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7029123857001768113444675 10543685785502652170167013)
                    ·
                      refine ⟨1976941084781747281906315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10543685785502652170167013 1976941084781747281906315)
                      ·
                        rfl

theorem cell23_3850079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_3850079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850079 prefixEnd_3850079 := by exact prefixLift 3850079
  have htrace : WordTrace (prefixWord ++ tailWord_3850079) baseStart_3850079 baseEnd_3850079 := by
    simpa [prefixWord, tailWord_3850079, baseEnd_3850079] using wordTrace_append hprefix tailTrace_3850079
  have hstable : (prefixWord ++ tailWord_3850079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850079).length < 2 ^ (prefixWord ++ tailWord_3850079).sum := by decide
  have hdescent : baseEnd_3850079 < baseStart_3850079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850092 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 4]
def baseStart_3850092 : Nat := 118140960795 + 3850092 * 2 ^ 59
def prefixEnd_3850092 : Nat := 4983230072969 + 3 ^ 40 * 3850092 * 2
def baseEnd_3850092 : Nat := 1976947760030255731043755

theorem tailTrace_3850092 : CollatzResearch.WordTrace tailWord_3850092 prefixEnd_3850092 1976947760030255731043755 := by
  unfold tailWord_3850092
  simp only [CollatzResearch.WordTrace]
  refine ⟨70212195783890851104504265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93616261045187801472672353 70212195783890851104504265)
  ·
    refine ⟨52659146837918138328378199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70212195783890851104504265 52659146837918138328378199)
    ·
      refine ⟨78988720256877207492567299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52659146837918138328378199 78988720256877207492567299)
      ·
        refine ⟨118483080385315811238850949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78988720256877207492567299 118483080385315811238850949)
        ·
          refine ⟨22215577572246714607284553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118483080385315811238850949 22215577572246714607284553)
          ·
            refine ⟨16661683179185035955463415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22215577572246714607284553 16661683179185035955463415)
            ·
              refine ⟨24992524768777553933195123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16661683179185035955463415 24992524768777553933195123)
              ·
                refine ⟨37488787153166330899792685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24992524768777553933195123 37488787153166330899792685)
                ·
                  refine ⟨14058295182437374087422257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37488787153166330899792685 14058295182437374087422257)
                  ·
                    refine ⟨10543721386828030565566693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14058295182437374087422257 10543721386828030565566693)
                    ·
                      refine ⟨1976947760030255731043755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10543721386828030565566693 1976947760030255731043755)
                      ·
                        rfl

theorem cell23_3850092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_3850092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850092 prefixEnd_3850092 := by exact prefixLift 3850092
  have htrace : WordTrace (prefixWord ++ tailWord_3850092) baseStart_3850092 baseEnd_3850092 := by
    simpa [prefixWord, tailWord_3850092, baseEnd_3850092] using wordTrace_append hprefix tailTrace_3850092
  have hstable : (prefixWord ++ tailWord_3850092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850092).length < 2 ^ (prefixWord ++ tailWord_3850092).sum := by decide
  have hdescent : baseEnd_3850092 < baseStart_3850092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850102 : List Nat := [5, 1, 1, 3, 13]
def baseStart_3850102 : Nat := 118140960795 + 3850102 * 2 ^ 59
def prefixEnd_3850102 : Nat := 4983230072969 + 3 ^ 40 * 3850102 * 2
def baseEnd_3850102 : Nat := 2711869540242524954621

theorem tailTrace_3850102 : CollatzResearch.WordTrace tailWord_3850102 prefixEnd_3850102 2711869540242524954621 := by
  unfold tailWord_3850102
  simp only [CollatzResearch.WordTrace]
  refine ⟨8776547268609092119804535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93616504198496982611248373 8776547268609092119804535)
  ·
    refine ⟨13164820902913638179706803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8776547268609092119804535 13164820902913638179706803)
    ·
      refine ⟨19747231354370457269560205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13164820902913638179706803 19747231354370457269560205)
      ·
        refine ⟨7405211757888921476085077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19747231354370457269560205 7405211757888921476085077)
        ·
          refine ⟨2711869540242524954621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 7405211757888921476085077 2711869540242524954621)
          ·
            rfl

theorem cell23_3850102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 13].length) (baseStart_3850102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850102 prefixEnd_3850102 := by exact prefixLift 3850102
  have htrace : WordTrace (prefixWord ++ tailWord_3850102) baseStart_3850102 baseEnd_3850102 := by
    simpa [prefixWord, tailWord_3850102, baseEnd_3850102] using wordTrace_append hprefix tailTrace_3850102
  have hstable : (prefixWord ++ tailWord_3850102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850102).length < 2 ^ (prefixWord ++ tailWord_3850102).sum := by decide
  have hdescent : baseEnd_3850102 < baseStart_3850102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850112 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 3]
def baseStart_3850112 : Nat := 118140960795 + 3850112 * 2 ^ 59
def prefixEnd_3850112 : Nat := 4983230072969 + 3 ^ 40 * 3850112 * 2
def baseEnd_3850112 : Nat := 1976958029643345652793663

theorem tailTrace_3850112 : CollatzResearch.WordTrace tailWord_3850112 prefixEnd_3850112 1976958029643345652793663 := by
  unfold tailWord_3850112
  simp only [CollatzResearch.WordTrace]
  refine ⟨70212560513854622812368295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93616747351806163749824393 70212560513854622812368295)
  ·
    refine ⟨105318840770781934218552443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70212560513854622812368295 105318840770781934218552443)
    ·
      refine ⟨157978261156172901327828665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105318840770781934218552443 157978261156172901327828665)
      ·
        refine ⟨118483695867129675995871499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157978261156172901327828665 118483695867129675995871499)
        ·
          refine ⟨177725543800694513993807249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118483695867129675995871499 177725543800694513993807249)
          ·
            refine ⟨133294157850520885495355437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177725543800694513993807249 133294157850520885495355437)
            ·
              refine ⟨49985309193945332060758289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133294157850520885495355437 49985309193945332060758289)
              ·
                refine ⟨37488981895458999045568717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49985309193945332060758289 37488981895458999045568717)
                ·
                  refine ⟨14058368210797124642088269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37488981895458999045568717 14058368210797124642088269)
                  ·
                    refine ⟨5271888079048921740783101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14058368210797124642088269 5271888079048921740783101)
                    ·
                      refine ⟨1976958029643345652793663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5271888079048921740783101 1976958029643345652793663)
                      ·
                        rfl

theorem cell23_3850112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 3].length) (baseStart_3850112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850112 prefixEnd_3850112 := by exact prefixLift 3850112
  have htrace : WordTrace (prefixWord ++ tailWord_3850112) baseStart_3850112 baseEnd_3850112 := by
    simpa [prefixWord, tailWord_3850112, baseEnd_3850112] using wordTrace_append hprefix tailTrace_3850112
  have hstable : (prefixWord ++ tailWord_3850112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850112).length < 2 ^ (prefixWord ++ tailWord_3850112).sum := by decide
  have hdescent : baseEnd_3850112 < baseStart_3850112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850119 : List Nat := [1, 1, 4, 2, 4, 2, 1, 8]
def baseStart_3850119 : Nat := 118140960795 + 3850119 * 2 ^ 59
def prefixEnd_3850119 : Nat := 4983230072969 + 3 ^ 40 * 3850119 * 2
def baseEnd_3850119 : Nat := 73220800889182486126153

theorem tailTrace_3850119 : CollatzResearch.WordTrace tailWord_3850119 prefixEnd_3850119 73220800889182486126153 := by
  unfold tailWord_3850119
  simp only [CollatzResearch.WordTrace]
  refine ⟨140425376338683885820241411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93616917559122590546827607 140425376338683885820241411)
  ·
    refine ⟨210638064508025828730362117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140425376338683885820241411 210638064508025828730362117)
    ·
      refine ⟨39494637095254842886942897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210638064508025828730362117 39494637095254842886942897)
      ·
        refine ⟨29620977821441132165207173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39494637095254842886942897 29620977821441132165207173)
        ·
          refine ⟨5553933341520212280976345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29620977821441132165207173 5553933341520212280976345)
          ·
            refine ⟨4165450006140159210732259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5553933341520212280976345 4165450006140159210732259)
            ·
              refine ⟨6248175009210238816098389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4165450006140159210732259 6248175009210238816098389)
              ·
                refine ⟨73220800889182486126153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6248175009210238816098389 73220800889182486126153)
                ·
                  rfl

theorem cell23_3850119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 8].length) (baseStart_3850119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850119 prefixEnd_3850119 := by exact prefixLift 3850119
  have htrace : WordTrace (prefixWord ++ tailWord_3850119) baseStart_3850119 baseEnd_3850119 := by
    simpa [prefixWord, tailWord_3850119, baseEnd_3850119] using wordTrace_append hprefix tailTrace_3850119
  have hstable : (prefixWord ++ tailWord_3850119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850119).length < 2 ^ (prefixWord ++ tailWord_3850119).sum := by decide
  have hdescent : baseEnd_3850119 < baseStart_3850119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850134 : List Nat := [5, 3, 1, 1, 3, 1, 1, 1, 2, 3, 2]
def baseStart_3850134 : Nat := 118140960795 + 3850134 * 2 ^ 59
def prefixEnd_3850134 : Nat := 4983230072969 + 3 ^ 40 * 3850134 * 2
def baseEnd_3850134 : Nat := 1976969326217744566718563

theorem tailTrace_3850134 : CollatzResearch.WordTrace tailWord_3850134 prefixEnd_3850134 1976969326217744566718563 := by
  unfold tailWord_3850134
  simp only [CollatzResearch.WordTrace]
  refine ⟨8776620214601846461377341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93617282289086362254691637 8776620214601846461377341)
  ·
    refine ⟨3291232580475692423016503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8776620214601846461377341 3291232580475692423016503)
    ·
      refine ⟨4936848870713538634524755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3291232580475692423016503 4936848870713538634524755)
      ·
        refine ⟨7405273306070307951787133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4936848870713538634524755 7405273306070307951787133)
        ·
          refine ⟨2776977489776365481920175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7405273306070307951787133 2776977489776365481920175)
          ·
            refine ⟨4165466234664548222880263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2776977489776365481920175 4165466234664548222880263)
            ·
              refine ⟨6248199351996822334320395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4165466234664548222880263 6248199351996822334320395)
              ·
                refine ⟨9372299027995233501480593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6248199351996822334320395 9372299027995233501480593)
                ·
                  refine ⟨7029224270996425126110445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9372299027995233501480593 7029224270996425126110445)
                  ·
                    refine ⟨2635959101623659422291417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7029224270996425126110445 2635959101623659422291417)
                    ·
                      refine ⟨1976969326217744566718563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2635959101623659422291417 1976969326217744566718563)
                      ·
                        rfl

theorem cell23_3850134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_3850134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850134 prefixEnd_3850134 := by exact prefixLift 3850134
  have htrace : WordTrace (prefixWord ++ tailWord_3850134) baseStart_3850134 baseEnd_3850134 := by
    simpa [prefixWord, tailWord_3850134, baseEnd_3850134] using wordTrace_append hprefix tailTrace_3850134
  have hstable : (prefixWord ++ tailWord_3850134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850134).length < 2 ^ (prefixWord ++ tailWord_3850134).sum := by decide
  have hdescent : baseEnd_3850134 < baseStart_3850134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850136 : List Nat := [2, 1, 2, 6, 1, 1, 3, 7]
def baseStart_3850136 : Nat := 118140960795 + 3850136 * 2 ^ 59
def prefixEnd_3850136 : Nat := 4983230072969 + 3 ^ 40 * 3850136 * 2
def baseEnd_3850136 : Nat := 73221124191816798477539

theorem tailTrace_3850136 : CollatzResearch.WordTrace tailWord_3850136 prefixEnd_3850136 73221124191816798477539 := by
  unfold tailWord_3850136
  simp only [CollatzResearch.WordTrace]
  refine ⟨70212998189811148861805131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93617330919748198482406841 70212998189811148861805131)
  ·
    refine ⟨105319497284716723292707697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70212998189811148861805131 105319497284716723292707697)
    ·
      refine ⟨78989622963537542469530773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105319497284716723292707697 78989622963537542469530773)
      ·
        refine ⟨3702638576415822303259255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 78989622963537542469530773 3702638576415822303259255)
        ·
          refine ⟨5553957864623733454888883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3702638576415822303259255 5553957864623733454888883)
          ·
            refine ⟨8330936796935600182333325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5553957864623733454888883 8330936796935600182333325)
            ·
              refine ⟨3124101298850850068374997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8330936796935600182333325 3124101298850850068374997)
              ·
                refine ⟨73221124191816798477539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3124101298850850068374997 73221124191816798477539)
                ·
                  rfl

theorem cell23_3850136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 7].length) (baseStart_3850136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850136 prefixEnd_3850136 := by exact prefixLift 3850136
  have htrace : WordTrace (prefixWord ++ tailWord_3850136) baseStart_3850136 baseEnd_3850136 := by
    simpa [prefixWord, tailWord_3850136, baseEnd_3850136] using wordTrace_append hprefix tailTrace_3850136
  have hstable : (prefixWord ++ tailWord_3850136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850136).length < 2 ^ (prefixWord ++ tailWord_3850136).sum := by decide
  have hdescent : baseEnd_3850136 < baseStart_3850136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850186 : List Nat := [3, 1, 2, 1, 2, 1, 5, 1, 1, 4, 2]
def baseStart_3850186 : Nat := 118140960795 + 3850186 * 2 ^ 59
def prefixEnd_3850186 : Nat := 4983230072969 + 3 ^ 40 * 3850186 * 2
def baseEnd_3850186 : Nat := 1976996027211778363268323

theorem tailTrace_3850186 : CollatzResearch.WordTrace tailWord_3850186 prefixEnd_3850186 1976996027211778363268323 := by
  unfold tailWord_3850186
  simp only [CollatzResearch.WordTrace]
  refine ⟨35106955007360289065732603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93618546686294104175286941 35106955007360289065732603)
  ·
    refine ⟨52660432511040433598598905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35106955007360289065732603 52660432511040433598598905)
    ·
      refine ⟨39495324383280325198949179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52660432511040433598598905 39495324383280325198949179)
      ·
        refine ⟨59242986574920487798423769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39495324383280325198949179 59242986574920487798423769)
        ·
          refine ⟨44432239931190365848817827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59242986574920487798423769 44432239931190365848817827)
          ·
            refine ⟨66648359896785548773226741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44432239931190365848817827 66648359896785548773226741)
            ·
              refine ⟨6248283740323645197490007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66648359896785548773226741 6248283740323645197490007)
              ·
                refine ⟨9372425610485467796235011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6248283740323645197490007 9372425610485467796235011)
                ·
                  refine ⟨14058638415728201694352517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9372425610485467796235011 14058638415728201694352517)
                  ·
                    refine ⟨2635994702949037817691097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14058638415728201694352517 2635994702949037817691097)
                    ·
                      refine ⟨1976996027211778363268323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2635994702949037817691097 1976996027211778363268323)
                      ·
                        rfl

theorem cell23_3850186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 1, 4, 2].length) (baseStart_3850186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850186 prefixEnd_3850186 := by exact prefixLift 3850186
  have htrace : WordTrace (prefixWord ++ tailWord_3850186) baseStart_3850186 baseEnd_3850186 := by
    simpa [prefixWord, tailWord_3850186, baseEnd_3850186] using wordTrace_append hprefix tailTrace_3850186
  have hstable : (prefixWord ++ tailWord_3850186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850186).length < 2 ^ (prefixWord ++ tailWord_3850186).sum := by decide
  have hdescent : baseEnd_3850186 < baseStart_3850186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850192 : List Nat := [2, 1, 1, 1, 1, 2, 6, 2, 7]
def baseStart_3850192 : Nat := 118140960795 + 3850192 * 2 ^ 59
def prefixEnd_3850192 : Nat := 4983230072969 + 3 ^ 40 * 3850192 * 2
def baseEnd_3850192 : Nat := 219666567566189482199255

theorem tailTrace_3850192 : CollatzResearch.WordTrace tailWord_3850192 prefixEnd_3850192 219666567566189482199255 := by
  unfold tailWord_3850192
  simp only [CollatzResearch.WordTrace]
  refine ⟨70214019433709709643824415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93618692578279612858432553 70214019433709709643824415)
  ·
    refine ⟨105321029150564564465736623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70214019433709709643824415 105321029150564564465736623)
    ·
      refine ⟨157981543725846846698604935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105321029150564564465736623 157981543725846846698604935)
      ·
        refine ⟨236972315588770270047907403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157981543725846846698604935 236972315588770270047907403)
        ·
          refine ⟨355458473383155405071861105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236972315588770270047907403 355458473383155405071861105)
          ·
            refine ⟨266593855037366553803895829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355458473383155405071861105 266593855037366553803895829)
            ·
              refine ⟨12496586954876557209557617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 266593855037366553803895829 12496586954876557209557617)
              ·
                refine ⟨9372440216157417907168213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12496586954876557209557617 9372440216157417907168213)
                ·
                  refine ⟨219666567566189482199255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9372440216157417907168213 219666567566189482199255)
                  ·
                    rfl

theorem cell23_3850192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 7].length) (baseStart_3850192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850192 prefixEnd_3850192 := by exact prefixLift 3850192
  have htrace : WordTrace (prefixWord ++ tailWord_3850192) baseStart_3850192 baseEnd_3850192 := by
    simpa [prefixWord, tailWord_3850192, baseEnd_3850192] using wordTrace_append hprefix tailTrace_3850192
  have hstable : (prefixWord ++ tailWord_3850192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850192).length < 2 ^ (prefixWord ++ tailWord_3850192).sum := by decide
  have hdescent : baseEnd_3850192 < baseStart_3850192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850232 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 1, 1, 7]
def baseStart_3850232 : Nat := 118140960795 + 3850232 * 2 ^ 59
def prefixEnd_3850232 : Nat := 4983230072969 + 3 ^ 40 * 3850232 * 2
def baseEnd_3850232 : Nat := 1977019647321885183293111

theorem tailTrace_3850232 : CollatzResearch.WordTrace tailWord_3850232 prefixEnd_3850232 1977019647321885183293111 := by
  unfold tailWord_3850232
  simp only [CollatzResearch.WordTrace]
  refine ⟨70214748893637253059552475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93619665191516337412736633 70214748893637253059552475)
  ·
    refine ⟨105322123340455879589328713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70214748893637253059552475 105322123340455879589328713)
    ·
      refine ⟨78991592505341909691996535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105322123340455879589328713 78991592505341909691996535)
      ·
        refine ⟨118487388758012864537994803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78991592505341909691996535 118487388758012864537994803)
        ·
          refine ⟨177731083137019296806992205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118487388758012864537994803 177731083137019296806992205)
          ·
            refine ⟨66649156176382236302622077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177731083137019296806992205 66649156176382236302622077)
            ·
              refine ⟨24993433566143338613483279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66649156176382236302622077 24993433566143338613483279)
              ·
                refine ⟨37490150349215007920224919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24993433566143338613483279 37490150349215007920224919)
                ·
                  refine ⟨56235225523822511880337379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37490150349215007920224919 56235225523822511880337379)
                  ·
                    refine ⟨84352838285733767820506069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56235225523822511880337379 84352838285733767820506069)
                    ·
                      refine ⟨1977019647321885183293111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84352838285733767820506069 1977019647321885183293111)
                      ·
                        rfl

theorem cell23_3850232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_3850232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850232 prefixEnd_3850232 := by exact prefixLift 3850232
  have htrace : WordTrace (prefixWord ++ tailWord_3850232) baseStart_3850232 baseEnd_3850232 := by
    simpa [prefixWord, tailWord_3850232, baseEnd_3850232] using wordTrace_append hprefix tailTrace_3850232
  have hstable : (prefixWord ++ tailWord_3850232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850232).length < 2 ^ (prefixWord ++ tailWord_3850232).sum := by decide
  have hdescent : baseEnd_3850232 < baseStart_3850232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850259 : List Nat := [1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 4]
def baseStart_3850259 : Nat := 118140960795 + 3850259 * 2 ^ 59
def prefixEnd_3850259 : Nat := 4983230072969 + 3 ^ 40 * 3850259 * 2
def baseEnd_3850259 : Nat := 1977033511299556577655487

theorem tailTrace_3850259 : CollatzResearch.WordTrace tailWord_3850259 prefixEnd_3850259 1977033511299556577655487 := by
  unfold tailWord_3850259
  simp only [CollatzResearch.WordTrace]
  refine ⟨140430482558176689730337831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93620321705451126486891887 140430482558176689730337831)
  ·
    refine ⟨210645723837265034595506747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140430482558176689730337831 210645723837265034595506747)
    ·
      refine ⟨315968585755897551893260121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210645723837265034595506747 315968585755897551893260121)
      ·
        refine ⟨236976439316923163919945091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315968585755897551893260121 236976439316923163919945091)
        ·
          refine ⟨355464658975384745879917637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236976439316923163919945091 355464658975384745879917637)
          ·
            refine ⟨66649623557884639852484557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 355464658975384745879917637 66649623557884639852484557)
            ·
              refine ⟨24993608834206739944681709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66649623557884639852484557 24993608834206739944681709)
              ·
                refine ⟨9372603312827527479255641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24993608834206739944681709 9372603312827527479255641)
                ·
                  refine ⟨7029452484620645609441731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9372603312827527479255641 7029452484620645609441731)
                  ·
                    refine ⟨10544178726930968414162597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7029452484620645609441731 10544178726930968414162597)
                    ·
                      refine ⟨1977033511299556577655487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10544178726930968414162597 1977033511299556577655487)
                      ·
                        rfl

theorem cell23_3850259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 4].length) (baseStart_3850259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850259 prefixEnd_3850259 := by exact prefixLift 3850259
  have htrace : WordTrace (prefixWord ++ tailWord_3850259) baseStart_3850259 baseEnd_3850259 := by
    simpa [prefixWord, tailWord_3850259, baseEnd_3850259] using wordTrace_append hprefix tailTrace_3850259
  have hstable : (prefixWord ++ tailWord_3850259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850259).length < 2 ^ (prefixWord ++ tailWord_3850259).sum := by decide
  have hdescent : baseEnd_3850259 < baseStart_3850259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850333 : List Nat := [1, 4, 4, 1, 1, 1, 3, 2, 6]
def baseStart_3850333 : Nat := 118140960795 + 3850333 * 2 ^ 59
def prefixEnd_3850333 : Nat := 4983230072969 + 3 ^ 40 * 3850333 * 2
def baseEnd_3850333 : Nat := 219674612096443254236683

theorem tailTrace_3850333 : CollatzResearch.WordTrace tailWord_3850333 prefixEnd_3850333 219674612096443254236683 := by
  unfold tailWord_3850333
  simp only [CollatzResearch.WordTrace]
  refine ⟨140433181559908600368531653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93622121039939066912354435 140433181559908600368531653)
  ·
    refine ⟨26331221542482862569099685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140433181559908600368531653 26331221542482862569099685)
    ·
      refine ⟨4937104039215536731706191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26331221542482862569099685 4937104039215536731706191)
      ·
        refine ⟨7405656058823305097559287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4937104039215536731706191 7405656058823305097559287)
        ·
          refine ⟨11108484088234957646338931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7405656058823305097559287 11108484088234957646338931)
          ·
            refine ⟨16662726132352436469508397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11108484088234957646338931 16662726132352436469508397)
            ·
              refine ⟨6248522299632163676065649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16662726132352436469508397 6248522299632163676065649)
              ·
                refine ⟨4686391724724122757049237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6248522299632163676065649 4686391724724122757049237)
                ·
                  refine ⟨219674612096443254236683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4686391724724122757049237 219674612096443254236683)
                  ·
                    rfl

theorem cell23_3850333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 6].length) (baseStart_3850333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850333 prefixEnd_3850333 := by exact prefixLift 3850333
  have htrace : WordTrace (prefixWord ++ tailWord_3850333) baseStart_3850333 baseEnd_3850333 := by
    simpa [prefixWord, tailWord_3850333, baseEnd_3850333] using wordTrace_append hprefix tailTrace_3850333
  have hstable : (prefixWord ++ tailWord_3850333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850333).length < 2 ^ (prefixWord ++ tailWord_3850333).sum := by decide
  have hdescent : baseEnd_3850333 < baseStart_3850333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850343 : List Nat := [1, 1, 5, 1, 1, 2, 4, 1, 3, 1, 3]
def baseStart_3850343 : Nat := 118140960795 + 3850343 * 2 ^ 59
def prefixEnd_3850343 : Nat := 4983230072969 + 3 ^ 40 * 3850343 * 2
def baseEnd_3850343 : Nat := 1977076643674534249005101

theorem tailTrace_3850343 : CollatzResearch.WordTrace tailWord_3850343 prefixEnd_3850343 1977076643674534249005101 := by
  unfold tailWord_3850343
  simp only [CollatzResearch.WordTrace]
  refine ⟨140433546289872372076395683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93622364193248248050930455 140433546289872372076395683)
  ·
    refine ⟨210650319434808558114593525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140433546289872372076395683 210650319434808558114593525)
    ·
      refine ⟨19748467447013302323243143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 210650319434808558114593525 19748467447013302323243143)
      ·
        refine ⟨29622701170519953484864715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19748467447013302323243143 29622701170519953484864715)
        ·
          refine ⟨44434051755779930227297073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29622701170519953484864715 44434051755779930227297073)
          ·
            refine ⟨33325538816834947670472805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44434051755779930227297073 33325538816834947670472805)
            ·
              refine ⟨6248538528156552688213651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33325538816834947670472805 6248538528156552688213651)
              ·
                refine ⟨9372807792234829032320477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6248538528156552688213651 9372807792234829032320477)
                ·
                  refine ⟨3514802922088060887120179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9372807792234829032320477 3514802922088060887120179)
                  ·
                    refine ⟨5272204383132091330680269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3514802922088060887120179 5272204383132091330680269)
                    ·
                      refine ⟨1977076643674534249005101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5272204383132091330680269 1977076643674534249005101)
                      ·
                        rfl

theorem cell23_3850343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_3850343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850343 prefixEnd_3850343 := by exact prefixLift 3850343
  have htrace : WordTrace (prefixWord ++ tailWord_3850343) baseStart_3850343 baseEnd_3850343 := by
    simpa [prefixWord, tailWord_3850343, baseEnd_3850343] using wordTrace_append hprefix tailTrace_3850343
  have hstable : (prefixWord ++ tailWord_3850343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850343).length < 2 ^ (prefixWord ++ tailWord_3850343).sum := by decide
  have hdescent : baseEnd_3850343 < baseStart_3850343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850394 : List Nat := [3, 1, 1, 5, 2, 1, 3, 2, 1, 1, 3]
def baseStart_3850394 : Nat := 118140960795 + 3850394 * 2 ^ 59
def prefixEnd_3850394 : Nat := 4983230072969 + 3 ^ 40 * 3850394 * 2
def baseEnd_3850394 : Nat := 1977102831187913549467367

theorem tailTrace_3850394 : CollatzResearch.WordTrace tailWord_3850394 prefixEnd_3850394 1977102831187913549467367 := by
  unfold tailWord_3850394
  simp only [CollatzResearch.WordTrace]
  refine ⟨35108851603171901946625559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93623604275125071857668157 35108851603171901946625559)
  ·
    refine ⟨52663277404757852919938339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35108851603171901946625559 52663277404757852919938339)
    ·
      refine ⟨78994916107136779379907509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52663277404757852919938339 78994916107136779379907509)
      ·
        refine ⟨7405773385044073066866329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78994916107136779379907509 7405773385044073066866329)
        ·
          refine ⟨5554330038783054800149747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7405773385044073066866329 5554330038783054800149747)
          ·
            refine ⟨8331495058174582200224621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5554330038783054800149747 8331495058174582200224621)
            ·
              refine ⟨3124310646815468325084233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8331495058174582200224621 3124310646815468325084233)
              ·
                refine ⟨2343232985111601243813175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3124310646815468325084233 2343232985111601243813175)
                ·
                  refine ⟨3514849477667401865719763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2343232985111601243813175 3514849477667401865719763)
                  ·
                    refine ⟨5272274216501102798579645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3514849477667401865719763 5272274216501102798579645)
                    ·
                      refine ⟨1977102831187913549467367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5272274216501102798579645 1977102831187913549467367)
                      ·
                        rfl

theorem cell23_3850394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_3850394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850394 prefixEnd_3850394 := by exact prefixLift 3850394
  have htrace : WordTrace (prefixWord ++ tailWord_3850394) baseStart_3850394 baseEnd_3850394 := by
    simpa [prefixWord, tailWord_3850394, baseEnd_3850394] using wordTrace_append hprefix tailTrace_3850394
  have hstable : (prefixWord ++ tailWord_3850394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850394).length < 2 ^ (prefixWord ++ tailWord_3850394).sum := by decide
  have hdescent : baseEnd_3850394 < baseStart_3850394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850400 : List Nat := [2, 1, 1, 4, 2, 2, 3, 1, 3, 2, 2]
def baseStart_3850400 : Nat := 118140960795 + 3850400 * 2 ^ 59
def prefixEnd_3850400 : Nat := 4983230072969 + 3 ^ 40 * 3850400 * 2
def baseEnd_3850400 : Nat := 1977105912071840525992339

theorem tailTrace_3850400 : CollatzResearch.WordTrace tailWord_3850400 prefixEnd_3850400 1977105912071840525992339 := by
  unfold tailWord_3850400
  simp only [CollatzResearch.WordTrace]
  refine ⟨70217812625332935405610327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93623750167110580540813769 70217812625332935405610327)
  ·
    refine ⟨105326718937999403108415491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70217812625332935405610327 105326718937999403108415491)
    ·
      refine ⟨157990078406999104662623237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105326718937999403108415491 157990078406999104662623237)
      ·
        refine ⟨29623139701312332124241857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157990078406999104662623237 29623139701312332124241857)
        ·
          refine ⟨22217354775984249093181393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29623139701312332124241857 22217354775984249093181393)
          ·
            refine ⟨16663016081988186819886045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22217354775984249093181393 16663016081988186819886045)
            ·
              refine ⟨6248631030745570057457267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16663016081988186819886045 6248631030745570057457267)
              ·
                refine ⟨9372946546118355086185901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6248631030745570057457267 9372946546118355086185901)
                ·
                  refine ⟨3514854954794383157319713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9372946546118355086185901 3514854954794383157319713)
                  ·
                    refine ⟨2636141216095787367989785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3514854954794383157319713 2636141216095787367989785)
                    ·
                      refine ⟨1977105912071840525992339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2636141216095787367989785 1977105912071840525992339)
                      ·
                        rfl

theorem cell23_3850400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_3850400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850400 prefixEnd_3850400 := by exact prefixLift 3850400
  have htrace : WordTrace (prefixWord ++ tailWord_3850400) baseStart_3850400 baseEnd_3850400 := by
    simpa [prefixWord, tailWord_3850400, baseEnd_3850400] using wordTrace_append hprefix tailTrace_3850400
  have hstable : (prefixWord ++ tailWord_3850400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850400).length < 2 ^ (prefixWord ++ tailWord_3850400).sum := by decide
  have hdescent : baseEnd_3850400 < baseStart_3850400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850414 : List Nat := [4, 1, 4, 2, 2, 1, 1, 2, 1, 5]
def baseStart_3850414 : Nat := 118140960795 + 3850414 * 2 ^ 59
def prefixEnd_3850414 : Nat := 4983230072969 + 3 ^ 40 * 3850414 * 2
def baseEnd_3850414 : Nat := 659037700267001157072425

theorem tailTrace_3850414 : CollatzResearch.WordTrace tailWord_3850414 prefixEnd_3850414 659037700267001157072425 := by
  unfold tailWord_3850414
  simp only [CollatzResearch.WordTrace]
  refine ⟨17554516984076893900278787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93624090581743434134820197 17554516984076893900278787)
  ·
    refine ⟨26331775476115340850418181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17554516984076893900278787 26331775476115340850418181)
    ·
      refine ⟨4937207901771626409453409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26331775476115340850418181 4937207901771626409453409)
      ·
        refine ⟨3702905926328719807090057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4937207901771626409453409 3702905926328719807090057)
        ·
          refine ⟨2777179444746539855317543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3702905926328719807090057 2777179444746539855317543)
          ·
            refine ⟨4165769167119809782976315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2777179444746539855317543 4165769167119809782976315)
            ·
              refine ⟨6248653750679714674464473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4165769167119809782976315 6248653750679714674464473)
              ·
                refine ⟨4686490313009786005848355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6248653750679714674464473 4686490313009786005848355)
                ·
                  refine ⟨7029735469514679008772533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4686490313009786005848355 7029735469514679008772533)
                  ·
                    refine ⟨659037700267001157072425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7029735469514679008772533 659037700267001157072425)
                    ·
                      rfl

theorem cell23_3850414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_3850414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850414 prefixEnd_3850414 := by exact prefixLift 3850414
  have htrace : WordTrace (prefixWord ++ tailWord_3850414) baseStart_3850414 baseEnd_3850414 := by
    simpa [prefixWord, tailWord_3850414, baseEnd_3850414] using wordTrace_append hprefix tailTrace_3850414
  have hstable : (prefixWord ++ tailWord_3850414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850414).length < 2 ^ (prefixWord ++ tailWord_3850414).sum := by decide
  have hdescent : baseEnd_3850414 < baseStart_3850414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850417 : List Nat := [1, 2, 2, 5, 3, 1, 1, 2, 1, 1, 4]
def baseStart_3850417 : Nat := 118140960795 + 3850417 * 2 ^ 59
def prefixEnd_3850417 : Nat := 4983230072969 + 3 ^ 40 * 3850417 * 2
def baseEnd_3850417 : Nat := 1977114641242966959479761

theorem tailTrace_3850417 : CollatzResearch.WordTrace tailWord_3850417 prefixEnd_3850417 1977114641242966959479761 := by
  unfold tailWord_3850417
  simp only [CollatzResearch.WordTrace]
  refine ⟨140436245291604282714589505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93624163527736188476393003 140436245291604282714589505)
  ·
    refine ⟨105327183968703212035942129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140436245291604282714589505 105327183968703212035942129)
    ·
      refine ⟨78995387976527409026956597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105327183968703212035942129 78995387976527409026956597)
      ·
        refine ⟨7405817622799444596277181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78995387976527409026956597 7405817622799444596277181)
        ·
          refine ⟨2777181608549791723603943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7405817622799444596277181 2777181608549791723603943)
          ·
            refine ⟨4165772412824687585405915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2777181608549791723603943 4165772412824687585405915)
            ·
              refine ⟨6248658619237031378108873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4165772412824687585405915 6248658619237031378108873)
              ·
                refine ⟨4686493964427773533581655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6248658619237031378108873 4686493964427773533581655)
                ·
                  refine ⟨7029740946641660300372483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4686493964427773533581655 7029740946641660300372483)
                  ·
                    refine ⟨10544611419962490450558725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7029740946641660300372483 10544611419962490450558725)
                    ·
                      refine ⟨1977114641242966959479761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10544611419962490450558725 1977114641242966959479761)
                      ·
                        rfl

theorem cell23_3850417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_3850417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850417 prefixEnd_3850417 := by exact prefixLift 3850417
  have htrace : WordTrace (prefixWord ++ tailWord_3850417) baseStart_3850417 baseEnd_3850417 := by
    simpa [prefixWord, tailWord_3850417, baseEnd_3850417] using wordTrace_append hprefix tailTrace_3850417
  have hstable : (prefixWord ++ tailWord_3850417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850417).length < 2 ^ (prefixWord ++ tailWord_3850417).sum := by decide
  have hdescent : baseEnd_3850417 < baseStart_3850417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850434 : List Nat := [3, 5, 1, 1, 1, 2, 3, 1, 1, 1, 4]
def baseStart_3850434 : Nat := 118140960795 + 3850434 * 2 ^ 59
def prefixEnd_3850434 : Nat := 4983230072969 + 3 ^ 40 * 3850434 * 2
def baseEnd_3850434 : Nat := 1977123370414093392967183

theorem tailTrace_3850434 : CollatzResearch.WordTrace tailWord_3850434 prefixEnd_3850434 1977123370414093392967183 := by
  unfold tailWord_3850434
  simp only [CollatzResearch.WordTrace]
  refine ⟨35109216333135673654489589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93624576888361796411972237 35109216333135673654489589)
  ·
    refine ⟨3291489031231469405108399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35109216333135673654489589 3291489031231469405108399)
    ·
      refine ⟨4937233546847204107662599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3291489031231469405108399 4937233546847204107662599)
      ·
        refine ⟨7405850320270806161493899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4937233546847204107662599 7405850320270806161493899)
        ·
          refine ⟨11108775480406209242240849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7405850320270806161493899 11108775480406209242240849)
          ·
            refine ⟨8331581610304656931680637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11108775480406209242240849 8331581610304656931680637)
            ·
              refine ⟨3124343103864246349380239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8331581610304656931680637 3124343103864246349380239)
              ·
                refine ⟨4686514655796369524070359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3124343103864246349380239 4686514655796369524070359)
                ·
                  refine ⟨7029771983694554286105539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4686514655796369524070359 7029771983694554286105539)
                  ·
                    refine ⟨10544657975541831429158309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7029771983694554286105539 10544657975541831429158309)
                    ·
                      refine ⟨1977123370414093392967183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10544657975541831429158309 1977123370414093392967183)
                      ·
                        rfl

theorem cell23_3850434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_3850434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850434 prefixEnd_3850434 := by exact prefixLift 3850434
  have htrace : WordTrace (prefixWord ++ tailWord_3850434) baseStart_3850434 baseEnd_3850434 := by
    simpa [prefixWord, tailWord_3850434, baseEnd_3850434] using wordTrace_append hprefix tailTrace_3850434
  have hstable : (prefixWord ++ tailWord_3850434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850434).length < 2 ^ (prefixWord ++ tailWord_3850434).sum := by decide
  have hdescent : baseEnd_3850434 < baseStart_3850434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850450 : List Nat := [3, 2, 2, 2, 1, 2, 1, 4, 2, 1, 3]
def baseStart_3850450 : Nat := 118140960795 + 3850450 * 2 ^ 59
def prefixEnd_3850450 : Nat := 4983230072969 + 3 ^ 40 * 3850450 * 2
def baseEnd_3850450 : Nat := 1977131586104565330367109

theorem tailTrace_3850450 : CollatzResearch.WordTrace tailWord_3850450 prefixEnd_3850450 1977131586104565330367109 := by
  unfold tailWord_3850450
  simp only [CollatzResearch.WordTrace]
  refine ⟨35109362225121182337635201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93624965933656486233693869 35109362225121182337635201)
  ·
    refine ⟨26332021668840886753226401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35109362225121182337635201 26332021668840886753226401)
    ·
      refine ⟨19749016251630665064919801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26332021668840886753226401 19749016251630665064919801)
      ·
        refine ⟨14811762188722998798689851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19749016251630665064919801 14811762188722998798689851)
        ·
          refine ⟨22217643283084498198034777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14811762188722998798689851 22217643283084498198034777)
          ·
            refine ⟨16663232462313373648526083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22217643283084498198034777 16663232462313373648526083)
            ·
              refine ⟨24994848693470060472789125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16663232462313373648526083 24994848693470060472789125)
              ·
                refine ⟨4686534130025636338647961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24994848693470060472789125 4686534130025636338647961)
                ·
                  refine ⟨3514900597519227253985971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4686534130025636338647961 3514900597519227253985971)
                  ·
                    refine ⟨5272350896278840880978957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3514900597519227253985971 5272350896278840880978957)
                    ·
                      refine ⟨1977131586104565330367109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5272350896278840880978957 1977131586104565330367109)
                      ·
                        rfl

theorem cell23_3850450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_3850450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850450 prefixEnd_3850450 := by exact prefixLift 3850450
  have htrace : WordTrace (prefixWord ++ tailWord_3850450) baseStart_3850450 baseEnd_3850450 := by
    simpa [prefixWord, tailWord_3850450, baseEnd_3850450] using wordTrace_append hprefix tailTrace_3850450
  have hstable : (prefixWord ++ tailWord_3850450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850450).length < 2 ^ (prefixWord ++ tailWord_3850450).sum := by decide
  have hdescent : baseEnd_3850450 < baseStart_3850450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850456 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 2, 3, 4]
def baseStart_3850456 : Nat := 118140960795 + 3850456 * 2 ^ 59
def prefixEnd_3850456 : Nat := 4983230072969 + 3 ^ 40 * 3850456 * 2
def baseEnd_3850456 : Nat := 1977134666988492306892081

theorem tailTrace_3850456 : CollatzResearch.WordTrace tailWord_3850456 prefixEnd_3850456 1977134666988492306892081 := by
  unfold tailWord_3850456
  simp only [CollatzResearch.WordTrace]
  refine ⟨70218833869231496187629611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93625111825641994916839481 70218833869231496187629611)
  ·
    refine ⟨105328250803847244281444417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70218833869231496187629611 105328250803847244281444417)
    ·
      refine ⟨78996188102885433211083313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105328250803847244281444417 78996188102885433211083313)
      ·
        refine ⟨59247141077164074908312485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78996188102885433211083313 59247141077164074908312485)
        ·
          refine ⟨11108838951968264045308591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59247141077164074908312485 11108838951968264045308591)
          ·
            refine ⟨16663258427952396067962887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11108838951968264045308591 16663258427952396067962887)
            ·
              refine ⟨24994887641928594101944331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16663258427952396067962887 24994887641928594101944331)
              ·
                refine ⟨37492331462892891152916497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24994887641928594101944331 37492331462892891152916497)
                ·
                  refine ⟨28119248597169668364687373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37492331462892891152916497 28119248597169668364687373)
                  ·
                    refine ⟨10544718223938625636757765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28119248597169668364687373 10544718223938625636757765)
                    ·
                      refine ⟨1977134666988492306892081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10544718223938625636757765 1977134666988492306892081)
                      ·
                        rfl

theorem cell23_3850456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_3850456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850456 prefixEnd_3850456 := by exact prefixLift 3850456
  have htrace : WordTrace (prefixWord ++ tailWord_3850456) baseStart_3850456 baseEnd_3850456 := by
    simpa [prefixWord, tailWord_3850456, baseEnd_3850456] using wordTrace_append hprefix tailTrace_3850456
  have hstable : (prefixWord ++ tailWord_3850456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850456).length < 2 ^ (prefixWord ++ tailWord_3850456).sum := by decide
  have hdescent : baseEnd_3850456 < baseStart_3850456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850459 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 5]
def baseStart_3850459 : Nat := 118140960795 + 3850459 * 2 ^ 59
def prefixEnd_3850459 : Nat := 4983230072969 + 3 ^ 40 * 3850459 * 2
def baseEnd_3850459 : Nat := 1977136207430455795154567

theorem tailTrace_3850459 : CollatzResearch.WordTrace tailWord_3850459 prefixEnd_3850459 1977136207430455795154567 := by
  unfold tailWord_3850459
  simp only [CollatzResearch.WordTrace]
  refine ⟨140437777157452123887618431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93625184771634749258412287 140437777157452123887618431)
  ·
    refine ⟨210656665736178185831427647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140437777157452123887618431 210656665736178185831427647)
    ·
      refine ⟨315984998604267278747141471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210656665736178185831427647 315984998604267278747141471)
      ·
        refine ⟨473977497906400918120712207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315984998604267278747141471 473977497906400918120712207)
        ·
          refine ⟨710966246859601377181068311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473977497906400918120712207 710966246859601377181068311)
          ·
            refine ⟨1066449370289402065771602467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710966246859601377181068311 1066449370289402065771602467)
            ·
              refine ⟨1599674055434103098657403701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1066449370289402065771602467 1599674055434103098657403701)
              ·
                refine ⟨149969442696947165499131597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1599674055434103098657403701 149969442696947165499131597)
                ·
                  refine ⟨56238541011355187062174349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149969442696947165499131597 56238541011355187062174349)
                  ·
                    refine ⟨21089452879258195148315381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56238541011355187062174349 21089452879258195148315381)
                    ·
                      refine ⟨1977136207430455795154567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21089452879258195148315381 1977136207430455795154567)
                      ·
                        rfl

theorem cell23_3850459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 5].length) (baseStart_3850459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850459 prefixEnd_3850459 := by exact prefixLift 3850459
  have htrace : WordTrace (prefixWord ++ tailWord_3850459) baseStart_3850459 baseEnd_3850459 := by
    simpa [prefixWord, tailWord_3850459, baseEnd_3850459] using wordTrace_append hprefix tailTrace_3850459
  have hstable : (prefixWord ++ tailWord_3850459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850459).length < 2 ^ (prefixWord ++ tailWord_3850459).sum := by decide
  have hdescent : baseEnd_3850459 < baseStart_3850459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850476 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 3]
def baseStart_3850476 : Nat := 118140960795 + 3850476 * 2 ^ 59
def prefixEnd_3850476 : Nat := 4983230072969 + 3 ^ 40 * 3850476 * 2
def baseEnd_3850476 : Nat := 1977144936601582228641989

theorem tailTrace_3850476 : CollatzResearch.WordTrace tailWord_3850476 prefixEnd_3850476 1977144936601582228641989 := by
  unfold tailWord_3850476
  simp only [CollatzResearch.WordTrace]
  refine ⟨70219198599195267895493641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93625598132260357193991521 70219198599195267895493641)
  ·
    refine ⟨52664398949396450921620231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70219198599195267895493641 52664398949396450921620231)
    ·
      refine ⟨78996598424094676382430347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52664398949396450921620231 78996598424094676382430347)
      ·
        refine ⟨118494897636142014573645521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78996598424094676382430347 118494897636142014573645521)
        ·
          refine ⟨88871173227106510930234141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118494897636142014573645521 88871173227106510930234141)
          ·
            refine ⟨33326689960164941598837803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88871173227106510930234141 33326689960164941598837803)
            ·
              refine ⟨49990034940247412398256705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33326689960164941598837803 49990034940247412398256705)
              ·
                refine ⟨37492526205185559298692529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49990034940247412398256705 37492526205185559298692529)
                ·
                  refine ⟨28119394653889169474019397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37492526205185559298692529 28119394653889169474019397)
                  ·
                    refine ⟨5272386497604219276378637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28119394653889169474019397 5272386497604219276378637)
                    ·
                      refine ⟨1977144936601582228641989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5272386497604219276378637 1977144936601582228641989)
                      ·
                        rfl

theorem cell23_3850476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 3].length) (baseStart_3850476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850476 prefixEnd_3850476 := by exact prefixLift 3850476
  have htrace : WordTrace (prefixWord ++ tailWord_3850476) baseStart_3850476 baseEnd_3850476 := by
    simpa [prefixWord, tailWord_3850476, baseEnd_3850476] using wordTrace_append hprefix tailTrace_3850476
  have hstable : (prefixWord ++ tailWord_3850476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850476).length < 2 ^ (prefixWord ++ tailWord_3850476).sum := by decide
  have hdescent : baseEnd_3850476 < baseStart_3850476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850513 : List Nat := [1, 2, 2, 1, 1, 5, 2, 4, 5]
def baseStart_3850513 : Nat := 118140960795 + 3850513 * 2 ^ 59
def prefixEnd_3850513 : Nat := 4983230072969 + 3 ^ 40 * 3850513 * 2
def baseEnd_3850513 : Nat := 219684881709533175986591

theorem tailTrace_3850513 : CollatzResearch.WordTrace tailWord_3850513 prefixEnd_3850513 219684881709533175986591 := by
  unfold tailWord_3850513
  simp only [CollatzResearch.WordTrace]
  refine ⟨140439746699256491110084193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93626497799504327406722795 140439746699256491110084193)
  ·
    refine ⟨105329810024442368332563145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140439746699256491110084193 105329810024442368332563145)
    ·
      refine ⟨78997357518331776249422359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105329810024442368332563145 78997357518331776249422359)
      ·
        refine ⟨118496036277497664374133539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78997357518331776249422359 118496036277497664374133539)
        ·
          refine ⟨177744054416246496561200309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118496036277497664374133539 177744054416246496561200309)
          ·
            refine ⟨16663505101523109052612529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 177744054416246496561200309 16663505101523109052612529)
            ·
              refine ⟨12497628826142331789459397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16663505101523109052612529 12497628826142331789459397)
              ·
                refine ⟨2343305404901687210523637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12497628826142331789459397 2343305404901687210523637)
                ·
                  refine ⟨219684881709533175986591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2343305404901687210523637 219684881709533175986591)
                  ·
                    rfl

theorem cell23_3850513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 4, 5].length) (baseStart_3850513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850513 prefixEnd_3850513 := by exact prefixLift 3850513
  have htrace : WordTrace (prefixWord ++ tailWord_3850513) baseStart_3850513 baseEnd_3850513 := by
    simpa [prefixWord, tailWord_3850513, baseEnd_3850513] using wordTrace_append hprefix tailTrace_3850513
  have hstable : (prefixWord ++ tailWord_3850513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850513).length < 2 ^ (prefixWord ++ tailWord_3850513).sum := by decide
  have hdescent : baseEnd_3850513 < baseStart_3850513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850563 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 4, 4, 2]
def baseStart_3850563 : Nat := 118140960795 + 3850563 * 2 ^ 59
def prefixEnd_3850563 : Nat := 4983230072969 + 3 ^ 40 * 3850563 * 2
def baseEnd_3850563 : Nat := 1977189609418523388254089

theorem tailTrace_3850563 : CollatzResearch.WordTrace tailWord_3850563 prefixEnd_3850563 1977189609418523388254089 := by
  unfold tailWord_3850563
  simp only [CollatzResearch.WordTrace]
  refine ⟨140441570349075349649404343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93627713566050233099602895 140441570349075349649404343)
  ·
    refine ⟨210662355523613024474106515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140441570349075349649404343 210662355523613024474106515)
    ·
      refine ⟨315993533285419536711159773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210662355523613024474106515 315993533285419536711159773)
      ·
        refine ⟨118497574982032326266684915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315993533285419536711159773 118497574982032326266684915)
        ·
          refine ⟨177746362473048489400027373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118497574982032326266684915 177746362473048489400027373)
          ·
            refine ⟨66654885927393183525010265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177746362473048489400027373 66654885927393183525010265)
            ·
              refine ⟨49991164445544887643757699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66654885927393183525010265 49991164445544887643757699)
              ·
                refine ⟨74986746668317331465636549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49991164445544887643757699 74986746668317331465636549)
                ·
                  refine ⟨14060015000309499649806853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74986746668317331465636549 14060015000309499649806853)
                  ·
                    refine ⟨2636252812558031184338785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14060015000309499649806853 2636252812558031184338785)
                    ·
                      refine ⟨1977189609418523388254089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2636252812558031184338785 1977189609418523388254089)
                      ·
                        rfl

theorem cell23_3850563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 4, 2].length) (baseStart_3850563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850563 prefixEnd_3850563 := by exact prefixLift 3850563
  have htrace : WordTrace (prefixWord ++ tailWord_3850563) baseStart_3850563 baseEnd_3850563 := by
    simpa [prefixWord, tailWord_3850563, baseEnd_3850563] using wordTrace_append hprefix tailTrace_3850563
  have hstable : (prefixWord ++ tailWord_3850563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850563).length < 2 ^ (prefixWord ++ tailWord_3850563).sum := by decide
  have hdescent : baseEnd_3850563 < baseStart_3850563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850564 : List Nat := [2, 3, 4, 1, 2, 1, 3, 2, 5]
def baseStart_3850564 : Nat := 118140960795 + 3850564 * 2 ^ 59
def prefixEnd_3850564 : Nat := 4983230072969 + 3 ^ 40 * 3850564 * 2
def baseEnd_3850564 : Nat := 219687791433241987149065

theorem tailTrace_3850564 : CollatzResearch.WordTrace tailWord_3850564 prefixEnd_3850564 219687791433241987149065 := by
  unfold tailWord_3850564
  simp only [CollatzResearch.WordTrace]
  refine ⟨70220803411035863410095373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93627737881381151213460497 70220803411035863410095373)
  ·
    refine ⟨26332801279138448778785765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70220803411035863410095373 26332801279138448778785765)
    ·
      refine ⟨4937400239838459146022331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26332801279138448778785765 4937400239838459146022331)
      ·
        refine ⟨7406100359757688719033497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4937400239838459146022331 7406100359757688719033497)
        ·
          refine ⟨5554575269818266539275123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7406100359757688719033497 5554575269818266539275123)
          ·
            refine ⟨8331862904727399808912685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5554575269818266539275123 8331862904727399808912685)
            ·
              refine ⟨3124448589272774928342257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8331862904727399808912685 3124448589272774928342257)
              ·
                refine ⟨2343336441954581196256693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3124448589272774928342257 2343336441954581196256693)
                ·
                  refine ⟨219687791433241987149065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2343336441954581196256693 219687791433241987149065)
                  ·
                    rfl

theorem cell23_3850564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 2, 5].length) (baseStart_3850564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850564 prefixEnd_3850564 := by exact prefixLift 3850564
  have htrace : WordTrace (prefixWord ++ tailWord_3850564) baseStart_3850564 baseEnd_3850564 := by
    simpa [prefixWord, tailWord_3850564, baseEnd_3850564] using wordTrace_append hprefix tailTrace_3850564
  have hstable : (prefixWord ++ tailWord_3850564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850564).length < 2 ^ (prefixWord ++ tailWord_3850564).sum := by decide
  have hdescent : baseEnd_3850564 < baseStart_3850564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850583 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 4, 2, 3]
def baseStart_3850583 : Nat := 118140960795 + 3850583 * 2 ^ 59
def prefixEnd_3850583 : Nat := 4983230072969 + 3 ^ 40 * 3850583 * 2
def baseEnd_3850583 : Nat := 1977199879031613310003997

theorem tailTrace_3850583 : CollatzResearch.WordTrace tailWord_3850583 prefixEnd_3850583 1977199879031613310003997 := by
  unfold tailWord_3850583
  simp only [CollatzResearch.WordTrace]
  refine ⟨140442299809002893065132403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93628199872668595376754935 140442299809002893065132403)
  ·
    refine ⟨210663449713504339597698605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140442299809002893065132403 210663449713504339597698605)
    ·
      refine ⟨78998793642564127349136977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210663449713504339597698605 78998793642564127349136977)
      ·
        refine ⟨59249095231923095511852733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78998793642564127349136977 59249095231923095511852733)
        ·
          refine ⟨22218410711971160816944775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59249095231923095511852733 22218410711971160816944775)
          ·
            refine ⟨33327616067956741225417163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22218410711971160816944775 33327616067956741225417163)
            ·
              refine ⟨49991424101935111838125745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33327616067956741225417163 49991424101935111838125745)
              ·
                refine ⟨37493568076451333878594309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49991424101935111838125745 37493568076451333878594309)
                ·
                  refine ⟨7030044014334625102236433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37493568076451333878594309 7030044014334625102236433)
                  ·
                    refine ⟨5272533010750968826677325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7030044014334625102236433 5272533010750968826677325)
                    ·
                      refine ⟨1977199879031613310003997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5272533010750968826677325 1977199879031613310003997)
                      ·
                        rfl

theorem cell23_3850583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_3850583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850583 prefixEnd_3850583 := by exact prefixLift 3850583
  have htrace : WordTrace (prefixWord ++ tailWord_3850583) baseStart_3850583 baseEnd_3850583 := by
    simpa [prefixWord, tailWord_3850583, baseEnd_3850583] using wordTrace_append hprefix tailTrace_3850583
  have hstable : (prefixWord ++ tailWord_3850583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850583).length < 2 ^ (prefixWord ++ tailWord_3850583).sum := by decide
  have hdescent : baseEnd_3850583 < baseStart_3850583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850600 : List Nat := [2, 1, 4, 2, 2, 1, 1, 3, 2, 2, 3]
def baseStart_3850600 : Nat := 118140960795 + 3850600 * 2 ^ 59
def prefixEnd_3850600 : Nat := 4983230072969 + 3 ^ 40 * 3850600 * 2
def baseEnd_3850600 : Nat := 1977208608202739743491419

theorem tailTrace_3850600 : CollatzResearch.WordTrace tailWord_3850600 prefixEnd_3850600 1977208608202739743491419 := by
  unfold tailWord_3850600
  simp only [CollatzResearch.WordTrace]
  refine ⟨70221459924970652484250627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93628613233294203312334169 70221459924970652484250627)
  ·
    refine ⟨105332189887455978726375941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70221459924970652484250627 105332189887455978726375941)
    ·
      refine ⟨19749785603897996011195489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105332189887455978726375941 19749785603897996011195489)
      ·
        refine ⟨14812339202923497008396617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19749785603897996011195489 14812339202923497008396617)
        ·
          refine ⟨11109254402192622756297463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14812339202923497008396617 11109254402192622756297463)
          ·
            refine ⟨16663881603288934134446195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11109254402192622756297463 16663881603288934134446195)
            ·
              refine ⟨24995822404933401201669293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16663881603288934134446195 24995822404933401201669293)
              ·
                refine ⟨9373433401850025450625985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24995822404933401201669293 9373433401850025450625985)
                ·
                  refine ⟨7030075051387519087969489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9373433401850025450625985 7030075051387519087969489)
                  ·
                    refine ⟨5272556288540639315977117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7030075051387519087969489 5272556288540639315977117)
                    ·
                      refine ⟨1977208608202739743491419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5272556288540639315977117 1977208608202739743491419)
                      ·
                        rfl

theorem cell23_3850600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_3850600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850600 prefixEnd_3850600 := by exact prefixLift 3850600
  have htrace : WordTrace (prefixWord ++ tailWord_3850600) baseStart_3850600 baseEnd_3850600 := by
    simpa [prefixWord, tailWord_3850600, baseEnd_3850600] using wordTrace_append hprefix tailTrace_3850600
  have hstable : (prefixWord ++ tailWord_3850600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850600).length < 2 ^ (prefixWord ++ tailWord_3850600).sum := by decide
  have hdescent : baseEnd_3850600 < baseStart_3850600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850633 : List Nat := [1, 2, 1, 1, 6, 1, 1, 2, 3, 5]
def baseStart_3850633 : Nat := 118140960795 + 3850633 * 2 ^ 59
def prefixEnd_3850633 : Nat := 4983230072969 + 3 ^ 40 * 3850633 * 2
def baseEnd_3850633 : Nat := 659075184354779371459589

theorem tailTrace_3850633 : CollatzResearch.WordTrace tailWord_3850633 prefixEnd_3850633 659075184354779371459589 := by
  unfold tailWord_3850633
  simp only [CollatzResearch.WordTrace]
  refine ⟨140444123458821751604452553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93629415639214501069635035 140444123458821751604452553)
  ·
    refine ⟨105333092594116313703339415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140444123458821751604452553 105333092594116313703339415)
    ·
      refine ⟨157999638891174470555009123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105333092594116313703339415 157999638891174470555009123)
      ·
        refine ⟨236999458336761705832513685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157999638891174470555009123 236999458336761705832513685)
        ·
          refine ⟨11109349609535704960899079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 236999458336761705832513685 11109349609535704960899079)
          ·
            refine ⟨16664024414303557441348619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11109349609535704960899079 16664024414303557441348619)
            ·
              refine ⟨24996036621455336162022929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16664024414303557441348619 24996036621455336162022929)
              ·
                refine ⟨18747027466091502121517197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24996036621455336162022929 18747027466091502121517197)
                ·
                  refine ⟨7030135299784313295568949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18747027466091502121517197 7030135299784313295568949)
                  ·
                    refine ⟨659075184354779371459589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7030135299784313295568949 659075184354779371459589)
                    ·
                      rfl

theorem cell23_3850633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 5].length) (baseStart_3850633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850633 prefixEnd_3850633 := by exact prefixLift 3850633
  have htrace : WordTrace (prefixWord ++ tailWord_3850633) baseStart_3850633 baseEnd_3850633 := by
    simpa [prefixWord, tailWord_3850633, baseEnd_3850633] using wordTrace_append hprefix tailTrace_3850633
  have hstable : (prefixWord ++ tailWord_3850633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850633).length < 2 ^ (prefixWord ++ tailWord_3850633).sum := by decide
  have hdescent : baseEnd_3850633 < baseStart_3850633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850700 : List Nat := [2, 2, 1, 4, 3, 1, 1, 1, 1, 1, 6]
def baseStart_3850700 : Nat := 118140960795 + 3850700 * 2 ^ 59
def prefixEnd_3850700 : Nat := 4983230072969 + 3 ^ 40 * 3850700 * 2
def baseEnd_3850700 : Nat := 1977259956268189352240959

theorem tailTrace_3850700 : CollatzResearch.WordTrace tailWord_3850700 prefixEnd_3850700 1977259956268189352240959 := by
  unfold tailWord_3850700
  simp only [CollatzResearch.WordTrace]
  refine ⟨70223283574789511023570777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93631044766386014698094369 70223283574789511023570777)
  ·
    refine ⟨52667462681092133267678083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70223283574789511023570777 52667462681092133267678083)
    ·
      refine ⟨79001194021638199901517125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52667462681092133267678083 79001194021638199901517125)
      ·
        refine ⟨14812723879057162481534461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79001194021638199901517125 14812723879057162481534461)
        ·
          refine ⟨5554771454646435930575423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14812723879057162481534461 5554771454646435930575423)
          ·
            refine ⟨8332157181969653895863135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5554771454646435930575423 8332157181969653895863135)
            ·
              refine ⟨12498235772954480843794703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8332157181969653895863135 12498235772954480843794703)
              ·
                refine ⟨18747353659431721265692055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12498235772954480843794703 18747353659431721265692055)
                ·
                  refine ⟨28121030489147581898538083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18747353659431721265692055 28121030489147581898538083)
                  ·
                    refine ⟨42181545733721372847807125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28121030489147581898538083 42181545733721372847807125)
                    ·
                      refine ⟨1977259956268189352240959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42181545733721372847807125 1977259956268189352240959)
                      ·
                        rfl

theorem cell23_3850700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_3850700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850700 prefixEnd_3850700 := by exact prefixLift 3850700
  have htrace : WordTrace (prefixWord ++ tailWord_3850700) baseStart_3850700 baseEnd_3850700 := by
    simpa [prefixWord, tailWord_3850700, baseEnd_3850700] using wordTrace_append hprefix tailTrace_3850700
  have hstable : (prefixWord ++ tailWord_3850700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850700).length < 2 ^ (prefixWord ++ tailWord_3850700).sum := by decide
  have hdescent : baseEnd_3850700 < baseStart_3850700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850710 : List Nat := [5, 2, 1, 1, 1, 1, 3, 9]
def baseStart_3850710 : Nat := 118140960795 + 3850710 * 2 ^ 59
def prefixEnd_3850710 : Nat := 4983230072969 + 3 ^ 40 * 3850710 * 2
def baseEnd_3850710 : Nat := 73232040410175344930219

theorem tailTrace_3850710 : CollatzResearch.WordTrace tailWord_3850710 prefixEnd_3850710 73232040410175344930219 := by
  unfold tailWord_3850710
  simp only [CollatzResearch.WordTrace]
  refine ⟨8777933242471424609687849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93631287919695195836670389 8777933242471424609687849)
  ·
    refine ⟨6583449931853568457265887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8777933242471424609687849 6583449931853568457265887)
    ·
      refine ⟨9875174897780352685898831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6583449931853568457265887 9875174897780352685898831)
      ·
        refine ⟨14812762346670529028848247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9875174897780352685898831 14812762346670529028848247)
        ·
          refine ⟨22219143520005793543272371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14812762346670529028848247 22219143520005793543272371)
          ·
            refine ⟨33328715280008690314908557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22219143520005793543272371 33328715280008690314908557)
            ·
              refine ⟨12498268230003258868090709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33328715280008690314908557 12498268230003258868090709)
              ·
                refine ⟨73232040410175344930219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12498268230003258868090709 73232040410175344930219)
                ·
                  rfl

theorem cell23_3850710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 9].length) (baseStart_3850710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850710 prefixEnd_3850710 := by exact prefixLift 3850710
  have htrace : WordTrace (prefixWord ++ tailWord_3850710) baseStart_3850710 baseEnd_3850710 := by
    simpa [prefixWord, tailWord_3850710, baseEnd_3850710] using wordTrace_append hprefix tailTrace_3850710
  have hstable : (prefixWord ++ tailWord_3850710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850710).length < 2 ^ (prefixWord ++ tailWord_3850710).sum := by decide
  have hdescent : baseEnd_3850710 < baseStart_3850710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850720 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 6, 1, 3]
def baseStart_3850720 : Nat := 118140960795 + 3850720 * 2 ^ 59
def prefixEnd_3850720 : Nat := 4983230072969 + 3 ^ 40 * 3850720 * 2
def baseEnd_3850720 : Nat := 1977270225881279273990867

theorem tailTrace_3850720 : CollatzResearch.WordTrace tailWord_3850720 prefixEnd_3850720 1977270225881279273990867 := by
  unfold tailWord_3850720
  simp only [CollatzResearch.WordTrace]
  refine ⟨70223648304753282731434807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93631531073004376975246409 70223648304753282731434807)
  ·
    refine ⟨105335472457129924097152211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70223648304753282731434807 105335472457129924097152211)
    ·
      refine ⟨158003208685694886145728317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105335472457129924097152211 158003208685694886145728317)
      ·
        refine ⟨59251203257135582304648119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158003208685694886145728317 59251203257135582304648119)
        ·
          refine ⟨88876804885703373456972179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59251203257135582304648119 88876804885703373456972179)
          ·
            refine ⟨133315207328555060185458269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88876804885703373456972179 133315207328555060185458269)
            ·
              refine ⟨49993202748208147569546851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133315207328555060185458269 49993202748208147569546851)
              ·
                refine ⟨74989804122312221354320277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49993202748208147569546851 74989804122312221354320277)
                ·
                  refine ⟨3515147068233385375983763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 74989804122312221354320277 3515147068233385375983763)
                  ·
                    refine ⟨5272720602350078063975645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3515147068233385375983763 5272720602350078063975645)
                    ·
                      refine ⟨1977270225881279273990867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5272720602350078063975645 1977270225881279273990867)
                      ·
                        rfl

theorem cell23_3850720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_3850720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850720 prefixEnd_3850720 := by exact prefixLift 3850720
  have htrace : WordTrace (prefixWord ++ tailWord_3850720) baseStart_3850720 baseEnd_3850720 := by
    simpa [prefixWord, tailWord_3850720, baseEnd_3850720] using wordTrace_append hprefix tailTrace_3850720
  have hstable : (prefixWord ++ tailWord_3850720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850720).length < 2 ^ (prefixWord ++ tailWord_3850720).sum := by decide
  have hdescent : baseEnd_3850720 < baseStart_3850720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850737 : List Nat := [1, 2, 2, 2, 3, 1, 2, 4, 2, 1, 3]
def baseStart_3850737 : Nat := 118140960795 + 3850737 * 2 ^ 59
def prefixEnd_3850737 : Nat := 4983230072969 + 3 ^ 40 * 3850737 * 2
def baseEnd_3850737 : Nat := 1977278955052405707478289

theorem tailTrace_3850737 : CollatzResearch.WordTrace tailWord_3850737 prefixEnd_3850737 1977278955052405707478289 := by
  unfold tailWord_3850737
  simp only [CollatzResearch.WordTrace]
  refine ⟨140447916650444977366238465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93631944433629984910825643 140447916650444977366238465)
  ·
    refine ⟨105335937487833733024678849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140447916650444977366238465 105335937487833733024678849)
    ·
      refine ⟨79001953115875299768509137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105335937487833733024678849 79001953115875299768509137)
      ·
        refine ⟨59251464836906474826381853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79001953115875299768509137 59251464836906474826381853)
        ·
          refine ⟨22219299313839928059893195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59251464836906474826381853 22219299313839928059893195)
          ·
            refine ⟨33328948970759892089839793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22219299313839928059893195 33328948970759892089839793)
            ·
              refine ⟨24996711728069919067379845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33328948970759892089839793 24996711728069919067379845)
              ·
                refine ⟨4686883449013109825133721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24996711728069919067379845 4686883449013109825133721)
                ·
                  refine ⟨3515162586759832368850291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4686883449013109825133721 3515162586759832368850291)
                  ·
                    refine ⟨5272743880139748553275437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3515162586759832368850291 5272743880139748553275437)
                    ·
                      refine ⟨1977278955052405707478289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5272743880139748553275437 1977278955052405707478289)
                      ·
                        rfl

theorem cell23_3850737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_3850737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850737 prefixEnd_3850737 := by exact prefixLift 3850737
  have htrace : WordTrace (prefixWord ++ tailWord_3850737) baseStart_3850737 baseEnd_3850737 := by
    simpa [prefixWord, tailWord_3850737, baseEnd_3850737] using wordTrace_append hprefix tailTrace_3850737
  have hstable : (prefixWord ++ tailWord_3850737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850737).length < 2 ^ (prefixWord ++ tailWord_3850737).sum := by decide
  have hdescent : baseEnd_3850737 < baseStart_3850737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850738 : List Nat := [3, 2, 1, 4, 3, 1, 1, 1, 3, 2, 2]
def baseStart_3850738 : Nat := 118140960795 + 3850738 * 2 ^ 59
def prefixEnd_3850738 : Nat := 4983230072969 + 3 ^ 40 * 3850738 * 2
def baseEnd_3850738 : Nat := 1977279468533060203565785

theorem tailTrace_3850738 : CollatzResearch.WordTrace tailWord_3850738 prefixEnd_3850738 1977279468533060203565785 := by
  unfold tailWord_3850738
  simp only [CollatzResearch.WordTrace]
  refine ⟨35111988280860338634256217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93631968748960903024683245 35111988280860338634256217)
  ·
    refine ⟨26333991210645253975692163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35111988280860338634256217 26333991210645253975692163)
    ·
      refine ⟨39500986815967880963538245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26333991210645253975692163 39500986815967880963538245)
      ·
        refine ⟨7406435027993977680663421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39500986815967880963538245 7406435027993977680663421)
        ·
          refine ⟨2777413135497741630248783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7406435027993977680663421 2777413135497741630248783)
          ·
            refine ⟨4166119703246612445373175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2777413135497741630248783 4166119703246612445373175)
            ·
              refine ⟨6249179554869918668059763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4166119703246612445373175 6249179554869918668059763)
              ·
                refine ⟨9373769332304878002089645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6249179554869918668059763 9373769332304878002089645)
                ·
                  refine ⟨3515163499614329250783617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9373769332304878002089645 3515163499614329250783617)
                  ·
                    refine ⟨2636372624710746938087713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3515163499614329250783617 2636372624710746938087713)
                    ·
                      refine ⟨1977279468533060203565785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2636372624710746938087713 1977279468533060203565785)
                      ·
                        rfl

theorem cell23_3850738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_3850738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850738 prefixEnd_3850738 := by exact prefixLift 3850738
  have htrace : WordTrace (prefixWord ++ tailWord_3850738) baseStart_3850738 baseEnd_3850738 := by
    simpa [prefixWord, tailWord_3850738, baseEnd_3850738] using wordTrace_append hprefix tailTrace_3850738
  have hstable : (prefixWord ++ tailWord_3850738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850738).length < 2 ^ (prefixWord ++ tailWord_3850738).sum := by decide
  have hdescent : baseEnd_3850738 < baseStart_3850738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850758 : List Nat := [6, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_3850758 : Nat := 118140960795 + 3850758 * 2 ^ 59
def prefixEnd_3850758 : Nat := 4983230072969 + 3 ^ 40 * 3850758 * 2
def baseEnd_3850758 : Nat := 1977289738146150125315693

theorem tailTrace_3850758 : CollatzResearch.WordTrace tailWord_3850758 prefixEnd_3850758 1977289738146150125315693 := by
  unfold tailWord_3850758
  simp only [CollatzResearch.WordTrace]
  refine ⟨4389021330730278061023529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 93632455055579265301835285 4389021330730278061023529)
  ·
    refine ⟨3291765998047708545767647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4389021330730278061023529 3291765998047708545767647)
    ·
      refine ⟨4937648997071562818651471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3291765998047708545767647 4937648997071562818651471)
      ·
        refine ⟨7406473495607344227977207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4937648997071562818651471 7406473495607344227977207)
        ·
          refine ⟨11109710243411016341965811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7406473495607344227977207 11109710243411016341965811)
          ·
            refine ⟨16664565365116524512948717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11109710243411016341965811 16664565365116524512948717)
            ·
              refine ⟨6249212011918696692355769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16664565365116524512948717 6249212011918696692355769)
              ·
                refine ⟨4686909008939022519266827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6249212011918696692355769 4686909008939022519266827)
                ·
                  refine ⟨7030363513408533778900241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4686909008939022519266827 7030363513408533778900241)
                  ·
                    refine ⟨5272772635056400334175181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7030363513408533778900241 5272772635056400334175181)
                    ·
                      refine ⟨1977289738146150125315693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5272772635056400334175181 1977289738146150125315693)
                      ·
                        rfl

theorem cell23_3850758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_3850758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850758 prefixEnd_3850758 := by exact prefixLift 3850758
  have htrace : WordTrace (prefixWord ++ tailWord_3850758) baseStart_3850758 baseEnd_3850758 := by
    simpa [prefixWord, tailWord_3850758, baseEnd_3850758] using wordTrace_append hprefix tailTrace_3850758
  have hstable : (prefixWord ++ tailWord_3850758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850758).length < 2 ^ (prefixWord ++ tailWord_3850758).sum := by decide
  have hdescent : baseEnd_3850758 < baseStart_3850758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850764 : List Nat := [2, 2, 1, 2, 4, 1, 3, 2, 1, 3, 2]
def baseStart_3850764 : Nat := 118140960795 + 3850764 * 2 ^ 59
def prefixEnd_3850764 : Nat := 4983230072969 + 3 ^ 40 * 3850764 * 2
def baseEnd_3850764 : Nat := 1977292819030077101840665

theorem tailTrace_3850764 : CollatzResearch.WordTrace tailWord_3850764 prefixEnd_3850764 1977292819030077101840665 := by
  unfold tailWord_3850764
  simp only [CollatzResearch.WordTrace]
  refine ⟨70224450710673580488735673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93632600947564773984980897 70224450710673580488735673)
  ·
    refine ⟨52668338033005185366551755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70224450710673580488735673 52668338033005185366551755)
    ·
      refine ⟨79002507049507778049827633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52668338033005185366551755 79002507049507778049827633)
      ·
        refine ⟨59251880287130833537370725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79002507049507778049827633 59251880287130833537370725)
        ·
          refine ⟨11109727553837031288257011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59251880287130833537370725 11109727553837031288257011)
          ·
            refine ⟨16664591330755546932385517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11109727553837031288257011 16664591330755546932385517)
            ·
              refine ⟨6249221749033330099644569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16664591330755546932385517 6249221749033330099644569)
              ·
                refine ⟨4686916311774997574733427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6249221749033330099644569 4686916311774997574733427)
                ·
                  refine ⟨7030374467662496362100141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4686916311774997574733427 7030374467662496362100141)
                  ·
                    refine ⟨2636390425373436135787553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7030374467662496362100141 2636390425373436135787553)
                    ·
                      refine ⟨1977292819030077101840665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2636390425373436135787553 1977292819030077101840665)
                      ·
                        rfl

theorem cell23_3850764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 1, 3, 2].length) (baseStart_3850764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850764 prefixEnd_3850764 := by exact prefixLift 3850764
  have htrace : WordTrace (prefixWord ++ tailWord_3850764) baseStart_3850764 baseEnd_3850764 := by
    simpa [prefixWord, tailWord_3850764, baseEnd_3850764] using wordTrace_append hprefix tailTrace_3850764
  have hstable : (prefixWord ++ tailWord_3850764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850764).length < 2 ^ (prefixWord ++ tailWord_3850764).sum := by decide
  have hdescent : baseEnd_3850764 < baseStart_3850764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850780 : List Nat := [2, 2, 3, 1, 2, 2, 2, 1, 2, 1, 5]
def baseStart_3850780 : Nat := 118140960795 + 3850780 * 2 ^ 59
def prefixEnd_3850780 : Nat := 4983230072969 + 3 ^ 40 * 3850780 * 2
def baseEnd_3850780 : Nat := 1977301034720549039240591

theorem tailTrace_3850780 : CollatzResearch.WordTrace tailWord_3850780 prefixEnd_3850780 1977301034720549039240591 := by
  unfold tailWord_3850780
  simp only [CollatzResearch.WordTrace]
  refine ⟨70224742494644597855026897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93632989992859463806702529 70224742494644597855026897)
  ·
    refine ⟨52668556870983448391270173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70224742494644597855026897 52668556870983448391270173)
    ·
      refine ⟨19750708826618793146726315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52668556870983448391270173 19750708826618793146726315)
      ·
        refine ⟨29626063239928189720089473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19750708826618793146726315 29626063239928189720089473)
        ·
          refine ⟨22219547429946142290067105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29626063239928189720089473 22219547429946142290067105)
          ·
            refine ⟨16664660572459606717550329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22219547429946142290067105 16664660572459606717550329)
            ·
              refine ⟨12498495429344705038162747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16664660572459606717550329 12498495429344705038162747)
              ·
                refine ⟨18747743144017057557244121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12498495429344705038162747 18747743144017057557244121)
                ·
                  refine ⟨14060807358012793167933091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18747743144017057557244121 14060807358012793167933091)
                  ·
                    refine ⟨21091211037019189751899637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14060807358012793167933091 21091211037019189751899637)
                    ·
                      refine ⟨1977301034720549039240591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21091211037019189751899637 1977301034720549039240591)
                      ·
                        rfl

theorem cell23_3850780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_3850780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850780 prefixEnd_3850780 := by exact prefixLift 3850780
  have htrace : WordTrace (prefixWord ++ tailWord_3850780) baseStart_3850780 baseEnd_3850780 := by
    simpa [prefixWord, tailWord_3850780, baseEnd_3850780] using wordTrace_append hprefix tailTrace_3850780
  have hstable : (prefixWord ++ tailWord_3850780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850780).length < 2 ^ (prefixWord ++ tailWord_3850780).sum := by decide
  have hdescent : baseEnd_3850780 < baseStart_3850780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850781 : List Nat := [1, 4, 2, 2, 1, 3, 3, 1, 1, 3, 2]
def baseStart_3850781 : Nat := 118140960795 + 3850781 * 2 ^ 59
def prefixEnd_3850781 : Nat := 4983230072969 + 3 ^ 40 * 3850781 * 2
def baseEnd_3850781 : Nat := 1977301548201203535328087

theorem tailTrace_3850781 : CollatzResearch.WordTrace tailWord_3850781 prefixEnd_3850781 1977301548201203535328087 := by
  unfold tailWord_3850781
  simp only [CollatzResearch.WordTrace]
  refine ⟨140449521462285572880840197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93633014308190381920560131 140449521462285572880840197)
  ·
    refine ⟨26334285274178544915157537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140449521462285572880840197 26334285274178544915157537)
    ·
      refine ⟨19750713955633908686368153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26334285274178544915157537 19750713955633908686368153)
      ·
        refine ⟨14813035466725431514776115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19750713955633908686368153 14813035466725431514776115)
        ·
          refine ⟨22219553200088147272164173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14813035466725431514776115 22219553200088147272164173)
          ·
            refine ⟨8332332450033055227061565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22219553200088147272164173 8332332450033055227061565)
            ·
              refine ⟨3124624668762395710148087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8332332450033055227061565 3124624668762395710148087)
              ·
                refine ⟨4686937003143593565222131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3124624668762395710148087 4686937003143593565222131)
                ·
                  refine ⟨7030405504715390347833197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4686937003143593565222131 7030405504715390347833197)
                  ·
                    refine ⟨2636402064268271380437449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7030405504715390347833197 2636402064268271380437449)
                    ·
                      refine ⟨1977301548201203535328087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2636402064268271380437449 1977301548201203535328087)
                      ·
                        rfl

theorem cell23_3850781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_3850781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850781 prefixEnd_3850781 := by exact prefixLift 3850781
  have htrace : WordTrace (prefixWord ++ tailWord_3850781) baseStart_3850781 baseEnd_3850781 := by
    simpa [prefixWord, tailWord_3850781, baseEnd_3850781] using wordTrace_append hprefix tailTrace_3850781
  have hstable : (prefixWord ++ tailWord_3850781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850781).length < 2 ^ (prefixWord ++ tailWord_3850781).sum := by decide
  have hdescent : baseEnd_3850781 < baseStart_3850781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850804 : List Nat := [2, 5, 1, 3, 1, 1, 1, 1, 2, 6]
def baseStart_3850804 : Nat := 118140960795 + 3850804 * 2 ^ 59
def prefixEnd_3850804 : Nat := 4983230072969 + 3 ^ 40 * 3850804 * 2
def baseEnd_3850804 : Nat := 659104452752085648446827

theorem tailTrace_3850804 : CollatzResearch.WordTrace tailWord_3850804 prefixEnd_3850804 659104452752085648446827 := by
  unfold tailWord_3850804
  simp only [CollatzResearch.WordTrace]
  refine ⟨70225180170601123904463733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93633573560801498539284977 70225180170601123904463733)
  ·
    refine ⟨6583610640993855366043475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70225180170601123904463733 6583610640993855366043475)
    ·
      refine ⟨9875415961490783049065213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6583610640993855366043475 9875415961490783049065213)
      ·
        refine ⟨3703280985559043643399455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9875415961490783049065213 3703280985559043643399455)
        ·
          refine ⟨5554921478338565465099183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3703280985559043643399455 5554921478338565465099183)
          ·
            refine ⟨8332382217507848197648775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5554921478338565465099183 8332382217507848197648775)
            ·
              refine ⟨12498573326261772296473163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8332382217507848197648775 12498573326261772296473163)
              ·
                refine ⟨18747859989392658444709745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12498573326261772296473163 18747859989392658444709745)
                ·
                  refine ⟨14060894992044493833532309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18747859989392658444709745 14060894992044493833532309)
                  ·
                    refine ⟨659104452752085648446827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14060894992044493833532309 659104452752085648446827)
                    ·
                      rfl

theorem cell23_3850804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_3850804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850804 prefixEnd_3850804 := by exact prefixLift 3850804
  have htrace : WordTrace (prefixWord ++ tailWord_3850804) baseStart_3850804 baseEnd_3850804 := by
    simpa [prefixWord, tailWord_3850804, baseEnd_3850804] using wordTrace_append hprefix tailTrace_3850804
  have hstable : (prefixWord ++ tailWord_3850804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850804).length < 2 ^ (prefixWord ++ tailWord_3850804).sum := by decide
  have hdescent : baseEnd_3850804 < baseStart_3850804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850810 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 1, 5, 3]
def baseStart_3850810 : Nat := 118140960795 + 3850810 * 2 ^ 59
def prefixEnd_3850810 : Nat := 4983230072969 + 3 ^ 40 * 3850810 * 2
def baseEnd_3850810 : Nat := 1977316439140183921865453

theorem tailTrace_3850810 : CollatzResearch.WordTrace tailWord_3850810 prefixEnd_3850810 1977316439140183921865453 := by
  unfold tailWord_3850810
  simp only [CollatzResearch.WordTrace]
  refine ⟨35112644794795127708411471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93633719452787007222430589 35112644794795127708411471)
  ·
    refine ⟨52668967192192691562617207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35112644794795127708411471 52668967192192691562617207)
    ·
      refine ⟨79003450788289037343925811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52668967192192691562617207 79003450788289037343925811)
      ·
        refine ⟨118505176182433556015888717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79003450788289037343925811 118505176182433556015888717)
        ·
          refine ⟨44439441068412583505958269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118505176182433556015888717 44439441068412583505958269)
          ·
            refine ⟨16664790400654718814734351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44439441068412583505958269 16664790400654718814734351)
            ·
              refine ⟨24997185600982078222101527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16664790400654718814734351 24997185600982078222101527)
              ·
                refine ⟨37495778401473117333152291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24997185600982078222101527 37495778401473117333152291)
                ·
                  refine ⟨56243667602209675999728437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37495778401473117333152291 56243667602209675999728437)
                  ·
                    refine ⟨5272843837707157124974541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56243667602209675999728437 5272843837707157124974541)
                    ·
                      refine ⟨1977316439140183921865453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5272843837707157124974541 1977316439140183921865453)
                      ·
                        rfl

theorem cell23_3850810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 1, 5, 3].length) (baseStart_3850810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850810 prefixEnd_3850810 := by exact prefixLift 3850810
  have htrace : WordTrace (prefixWord ++ tailWord_3850810) baseStart_3850810 baseEnd_3850810 := by
    simpa [prefixWord, tailWord_3850810, baseEnd_3850810] using wordTrace_append hprefix tailTrace_3850810
  have hstable : (prefixWord ++ tailWord_3850810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850810).length < 2 ^ (prefixWord ++ tailWord_3850810).sum := by decide
  have hdescent : baseEnd_3850810 < baseStart_3850810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850887 : List Nat := [1, 1, 4, 2, 1, 2, 2, 3, 2, 2, 3]
def baseStart_3850887 : Nat := 118140960795 + 3850887 * 2 ^ 59
def prefixEnd_3850887 : Nat := 4983230072969 + 3 ^ 40 * 3850887 * 2
def baseEnd_3850887 : Nat := 1977355977150580120602599

theorem tailTrace_3850887 : CollatzResearch.WordTrace tailWord_3850887 prefixEnd_3850887 1977355977150580120602599 := by
  unfold tailWord_3850887
  simp only [CollatzResearch.WordTrace]
  refine ⟨140453387599901552984198915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93635591733267701989465943 140453387599901552984198915)
  ·
    refine ⟨210680081399852329476298373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140453387599901552984198915 210680081399852329476298373)
    ·
      refine ⟨39502515262472311776805945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210680081399852329476298373 39502515262472311776805945)
      ·
        refine ⟨29626886446854233832604459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39502515262472311776805945 29626886446854233832604459)
        ·
          refine ⟨44440329670281350748906689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29626886446854233832604459 44440329670281350748906689)
          ·
            refine ⟨33330247252711013061680017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44440329670281350748906689 33330247252711013061680017)
            ·
              refine ⟨24997685439533259796260013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33330247252711013061680017 24997685439533259796260013)
              ·
                refine ⟨9374132039824972423597505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24997685439533259796260013 9374132039824972423597505)
                ·
                  refine ⟨7030599029868729317698129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9374132039824972423597505 7030599029868729317698129)
                  ·
                    refine ⟨5272949272401546988273597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7030599029868729317698129 5272949272401546988273597)
                    ·
                      refine ⟨1977355977150580120602599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5272949272401546988273597 1977355977150580120602599)
                      ·
                        rfl

theorem cell23_3850887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_3850887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850887 prefixEnd_3850887 := by exact prefixLift 3850887
  have htrace : WordTrace (prefixWord ++ tailWord_3850887) baseStart_3850887 baseEnd_3850887 := by
    simpa [prefixWord, tailWord_3850887, baseEnd_3850887] using wordTrace_append hprefix tailTrace_3850887
  have hstable : (prefixWord ++ tailWord_3850887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850887).length < 2 ^ (prefixWord ++ tailWord_3850887).sum := by decide
  have hdescent : baseEnd_3850887 < baseStart_3850887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850944 : List Nat := [2, 1, 1, 2, 4, 2, 1, 3, 2, 3, 2]
def baseStart_3850944 : Nat := 118140960795 + 3850944 * 2 ^ 59
def prefixEnd_3850944 : Nat := 4983230072969 + 3 ^ 40 * 3850944 * 2
def baseEnd_3850944 : Nat := 1977385245547886397589837

theorem tailTrace_3850944 : CollatzResearch.WordTrace tailWord_3850944 prefixEnd_3850944 1977385245547886397589837 := by
  unfold tailWord_3850944
  simp only [CollatzResearch.WordTrace]
  refine ⟨70227733280347525859511943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93636977707130034479349257 70227733280347525859511943)
  ·
    refine ⟨105341599920521288789267915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70227733280347525859511943 105341599920521288789267915)
    ·
      refine ⟨158012399880781933183901873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105341599920521288789267915 158012399880781933183901873)
      ·
        refine ⟨118509299910586449887926405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158012399880781933183901873 118509299910586449887926405)
        ·
          refine ⟨22220493733234959353986201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118509299910586449887926405 22220493733234959353986201)
          ·
            refine ⟨16665370299926219515489651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22220493733234959353986201 16665370299926219515489651)
            ·
              refine ⟨24998055449889329273234477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16665370299926219515489651 24998055449889329273234477)
              ·
                refine ⟨9374270793708498477462929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24998055449889329273234477 9374270793708498477462929)
                ·
                  refine ⟨7030703095281373858097197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9374270793708498477462929 7030703095281373858097197)
                  ·
                    refine ⟨2636513660730515196786449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7030703095281373858097197 2636513660730515196786449)
                    ·
                      refine ⟨1977385245547886397589837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2636513660730515196786449 1977385245547886397589837)
                      ·
                        rfl

theorem cell23_3850944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 2, 3, 2].length) (baseStart_3850944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850944 prefixEnd_3850944 := by exact prefixLift 3850944
  have htrace : WordTrace (prefixWord ++ tailWord_3850944) baseStart_3850944 baseEnd_3850944 := by
    simpa [prefixWord, tailWord_3850944, baseEnd_3850944] using wordTrace_append hprefix tailTrace_3850944
  have hstable : (prefixWord ++ tailWord_3850944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850944).length < 2 ^ (prefixWord ++ tailWord_3850944).sum := by decide
  have hdescent : baseEnd_3850944 < baseStart_3850944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850968 : List Nat := [2, 1, 2, 2, 3, 2, 4, 2, 1, 1, 3]
def baseStart_3850968 : Nat := 118140960795 + 3850968 * 2 ^ 59
def prefixEnd_3850968 : Nat := 4983230072969 + 3 ^ 40 * 3850968 * 2
def baseEnd_3850968 : Nat := 1977397569083594303689727

theorem tailTrace_3850968 : CollatzResearch.WordTrace tailWord_3850968 prefixEnd_3850968 1977397569083594303689727 := by
  unfold tailWord_3850968
  simp only [CollatzResearch.WordTrace]
  refine ⟨70228170956304051908948779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93637561275072069211931705 70228170956304051908948779)
  ·
    refine ⟨105342256434456077863423169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70228170956304051908948779 105342256434456077863423169)
    ·
      refine ⟨79006692325842058397567377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105342256434456077863423169 79006692325842058397567377)
      ·
        refine ⟨59255019244381543798175533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79006692325842058397567377 59255019244381543798175533)
        ·
          refine ⟨22220632216643078924315825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59255019244381543798175533 22220632216643078924315825)
          ·
            refine ⟨16665474162482309193236869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22220632216643078924315825 16665474162482309193236869)
            ·
              refine ⟨3124776405465432973731913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16665474162482309193236869 3124776405465432973731913)
              ·
                refine ⟨2343582304099074730298935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3124776405465432973731913 2343582304099074730298935)
                ·
                  refine ⟨3515373456148612095448403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2343582304099074730298935 3515373456148612095448403)
                  ·
                    refine ⟨5273060184222918143172605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3515373456148612095448403 5273060184222918143172605)
                    ·
                      refine ⟨1977397569083594303689727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5273060184222918143172605 1977397569083594303689727)
                      ·
                        rfl

theorem cell23_3850968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 2, 1, 1, 3].length) (baseStart_3850968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850968 prefixEnd_3850968 := by exact prefixLift 3850968
  have htrace : WordTrace (prefixWord ++ tailWord_3850968) baseStart_3850968 baseEnd_3850968 := by
    simpa [prefixWord, tailWord_3850968, baseEnd_3850968] using wordTrace_append hprefix tailTrace_3850968
  have hstable : (prefixWord ++ tailWord_3850968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850968).length < 2 ^ (prefixWord ++ tailWord_3850968).sum := by decide
  have hdescent : baseEnd_3850968 < baseStart_3850968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850984 : List Nat := [2, 1, 4, 1, 4, 1, 2, 1, 1, 6]
def baseStart_3850984 : Nat := 118140960795 + 3850984 * 2 ^ 59
def prefixEnd_3850984 : Nat := 4983230072969 + 3 ^ 40 * 3850984 * 2
def baseEnd_3850984 : Nat := 659135261591355413696551

theorem tailTrace_3850984 : CollatzResearch.WordTrace tailWord_3850984 prefixEnd_3850984 659135261591355413696551 := by
  unfold tailWord_3850984
  simp only [CollatzResearch.WordTrace]
  refine ⟨70228462740275069275240003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93637950320366759033653337 70228462740275069275240003)
  ·
    refine ⟨105342694110412603912860005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70228462740275069275240003 105342694110412603912860005)
    ·
      refine ⟨19751755145702363233661251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105342694110412603912860005 19751755145702363233661251)
      ·
        refine ⟨29627632718553544850491877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19751755145702363233661251 29627632718553544850491877)
        ·
          refine ⟨5555181134728789659467227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29627632718553544850491877 5555181134728789659467227)
          ·
            refine ⟨8332771702093184489200841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5555181134728789659467227 8332771702093184489200841)
            ·
              refine ⟨6249578776569888366900631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8332771702093184489200841 6249578776569888366900631)
              ·
                refine ⟨9374368164854832550350947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6249578776569888366900631 9374368164854832550350947)
                ·
                  refine ⟨14061552247282248825526421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9374368164854832550350947 14061552247282248825526421)
                  ·
                    refine ⟨659135261591355413696551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14061552247282248825526421 659135261591355413696551)
                    ·
                      rfl

theorem cell23_3850984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_3850984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850984 prefixEnd_3850984 := by exact prefixLift 3850984
  have htrace : WordTrace (prefixWord ++ tailWord_3850984) baseStart_3850984 baseEnd_3850984 := by
    simpa [prefixWord, tailWord_3850984, baseEnd_3850984] using wordTrace_append hprefix tailTrace_3850984
  have hstable : (prefixWord ++ tailWord_3850984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850984).length < 2 ^ (prefixWord ++ tailWord_3850984).sum := by decide
  have hdescent : baseEnd_3850984 < baseStart_3850984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850991 : List Nat := [1, 1, 2, 1, 5, 3, 1, 2, 3, 2, 2]
def baseStart_3850991 : Nat := 118140960795 + 3850991 * 2 ^ 59
def prefixEnd_3850991 : Nat := 4983230072969 + 3 ^ 40 * 3850991 * 2
def baseEnd_3850991 : Nat := 1977409379138647713702121

theorem tailTrace_3850991 : CollatzResearch.WordTrace tailWord_3850991 prefixEnd_3850991 1977409379138647713702121 := by
  unfold tailWord_3850991
  simp only [CollatzResearch.WordTrace]
  refine ⟨140457180791524778745984827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93638120527683185830656551 140457180791524778745984827)
  ·
    refine ⟨210685771187287168118977241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140457180791524778745984827 210685771187287168118977241)
    ·
      refine ⟨158014328390465376089232931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210685771187287168118977241 158014328390465376089232931)
      ·
        refine ⟨237021492585698064133849397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158014328390465376089232931 237021492585698064133849397)
        ·
          refine ⟨22220764929909193512548381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 237021492585698064133849397 22220764929909193512548381)
          ·
            refine ⟨8332786848715947567205643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22220764929909193512548381 8332786848715947567205643)
            ·
              refine ⟨12499180273073921350808465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8332786848715947567205643 12499180273073921350808465)
              ·
                refine ⟨9374385204805441013106349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12499180273073921350808465 9374385204805441013106349)
                ·
                  refine ⟨3515394451802040379914881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9374385204805441013106349 3515394451802040379914881)
                  ·
                    refine ⟨2636545838851530284936161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3515394451802040379914881 2636545838851530284936161)
                    ·
                      refine ⟨1977409379138647713702121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2636545838851530284936161 1977409379138647713702121)
                      ·
                        rfl

theorem cell23_3850991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 3, 2, 2].length) (baseStart_3850991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850991 prefixEnd_3850991 := by exact prefixLift 3850991
  have htrace : WordTrace (prefixWord ++ tailWord_3850991) baseStart_3850991 baseEnd_3850991 := by
    simpa [prefixWord, tailWord_3850991, baseEnd_3850991] using wordTrace_append hprefix tailTrace_3850991
  have hstable : (prefixWord ++ tailWord_3850991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850991).length < 2 ^ (prefixWord ++ tailWord_3850991).sum := by decide
  have hdescent : baseEnd_3850991 < baseStart_3850991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850994 : List Nat := [3, 2, 1, 3, 1, 2, 2, 1, 3, 2, 3]
def baseStart_3850994 : Nat := 118140960795 + 3850994 * 2 ^ 59
def prefixEnd_3850994 : Nat := 4983230072969 + 3 ^ 40 * 3850994 * 2
def baseEnd_3850994 : Nat := 1977410919580611201964607

theorem tailTrace_3850994 : CollatzResearch.WordTrace tailWord_3850994 prefixEnd_3850994 1977410919580611201964607 := by
  unfold tailWord_3850994
  simp only [CollatzResearch.WordTrace]
  refine ⟨35114322552628477564586009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93638193473675940172229357 35114322552628477564586009)
  ·
    refine ⟨26335741914471358173439507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35114322552628477564586009 26335741914471358173439507)
    ·
      refine ⟨39503612871707037260159261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26335741914471358173439507 39503612871707037260159261)
      ·
        refine ⟨14813854826890138972559723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39503612871707037260159261 14813854826890138972559723)
        ·
          refine ⟨22220782240335208458839585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14813854826890138972559723 22220782240335208458839585)
          ·
            refine ⟨16665586680251406344129689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22220782240335208458839585 16665586680251406344129689)
            ·
              refine ⟨12499190010188554758097267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16665586680251406344129689 12499190010188554758097267)
              ·
                refine ⟨18748785015282832137145901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12499190010188554758097267 18748785015282832137145901)
                ·
                  refine ⟨7030794380731062051429713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18748785015282832137145901 7030794380731062051429713)
                  ·
                    refine ⟨5273095785548296538572285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7030794380731062051429713 5273095785548296538572285)
                    ·
                      refine ⟨1977410919580611201964607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5273095785548296538572285 1977410919580611201964607)
                      ·
                        rfl

theorem cell23_3850994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_3850994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3850994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3850994 prefixEnd_3850994 := by exact prefixLift 3850994
  have htrace : WordTrace (prefixWord ++ tailWord_3850994) baseStart_3850994 baseEnd_3850994 := by
    simpa [prefixWord, tailWord_3850994, baseEnd_3850994] using wordTrace_append hprefix tailTrace_3850994
  have hstable : (prefixWord ++ tailWord_3850994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850994).length < 2 ^ (prefixWord ++ tailWord_3850994).sum := by decide
  have hdescent : baseEnd_3850994 < baseStart_3850994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851054 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_3851054 : Nat := 118140960795 + 3851054 * 2 ^ 59
def prefixEnd_3851054 : Nat := 4983230072969 + 3 ^ 40 * 3851054 * 2
def baseEnd_3851054 : Nat := 1977441728419880967214331

theorem tailTrace_3851054 : CollatzResearch.WordTrace tailWord_3851054 prefixEnd_3851054 1977441728419880967214331 := by
  unfold tailWord_3851054
  simp only [CollatzResearch.WordTrace]
  refine ⟨17557434823787067563191027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93639652393531027003685477 17557434823787067563191027)
  ·
    refine ⟨26336152235680601344786541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17557434823787067563191027 26336152235680601344786541)
    ·
      refine ⟨9876057088380225504294953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26336152235680601344786541 9876057088380225504294953)
      ·
        refine ⟨7407042816285169128221215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9876057088380225504294953 7407042816285169128221215)
        ·
          refine ⟨11110564224427753692331823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7407042816285169128221215 11110564224427753692331823)
          ·
            refine ⟨16665846336641630538497735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11110564224427753692331823 16665846336641630538497735)
            ·
              refine ⟨24998769504962445807746603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16665846336641630538497735 24998769504962445807746603)
              ·
                refine ⟨37498154257443668711619905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24998769504962445807746603 37498154257443668711619905)
                ·
                  refine ⟨28123615693082751533714929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37498154257443668711619905 28123615693082751533714929)
                  ·
                    refine ⟨21092711769812063650286197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28123615693082751533714929 21092711769812063650286197)
                    ·
                      refine ⟨1977441728419880967214331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21092711769812063650286197 1977441728419880967214331)
                      ·
                        rfl

theorem cell23_3851054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_3851054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851054 prefixEnd_3851054 := by exact prefixLift 3851054
  have htrace : WordTrace (prefixWord ++ tailWord_3851054) baseStart_3851054 baseEnd_3851054 := by
    simpa [prefixWord, tailWord_3851054, baseEnd_3851054] using wordTrace_append hprefix tailTrace_3851054
  have hstable : (prefixWord ++ tailWord_3851054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851054).length < 2 ^ (prefixWord ++ tailWord_3851054).sum := by decide
  have hdescent : baseEnd_3851054 < baseStart_3851054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851064 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 3, 4, 2]
def baseStart_3851064 : Nat := 118140960795 + 3851064 * 2 ^ 59
def prefixEnd_3851064 : Nat := 4983230072969 + 3 ^ 40 * 3851064 * 2
def baseEnd_3851064 : Nat := 1977446863226425928089285

theorem tailTrace_3851064 : CollatzResearch.WordTrace tailWord_3851064 prefixEnd_3851064 1977446863226425928089285 := by
  unfold tailWord_3851064
  simp only [CollatzResearch.WordTrace]
  refine ⟨70229921660130156106696123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93639895546840208142261497 70229921660130156106696123)
  ·
    refine ⟨105344882490195234160044185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70229921660130156106696123 105344882490195234160044185)
    ·
      refine ⟨79008661867646425620033139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105344882490195234160044185 79008661867646425620033139)
      ·
        refine ⟨118512992801469638430049709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79008661867646425620033139 118512992801469638430049709)
        ·
          refine ⟨44442372300551114411268641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118512992801469638430049709 44442372300551114411268641)
          ·
            refine ⟨33331779225413335808451481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44442372300551114411268641 33331779225413335808451481)
            ·
              refine ⟨24998834419060001856338611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33331779225413335808451481 24998834419060001856338611)
              ·
                refine ⟨37498251628590002784507917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24998834419060001856338611 37498251628590002784507917)
                ·
                  refine ⟨14061844360721251044190469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37498251628590002784507917 14061844360721251044190469)
                  ·
                    refine ⟨2636595817635234570785713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14061844360721251044190469 2636595817635234570785713)
                    ·
                      refine ⟨1977446863226425928089285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2636595817635234570785713 1977446863226425928089285)
                      ·
                        rfl

theorem cell23_3851064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 3, 4, 2].length) (baseStart_3851064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851064 prefixEnd_3851064 := by exact prefixLift 3851064
  have htrace : WordTrace (prefixWord ++ tailWord_3851064) baseStart_3851064 baseEnd_3851064 := by
    simpa [prefixWord, tailWord_3851064, baseEnd_3851064] using wordTrace_append hprefix tailTrace_3851064
  have hstable : (prefixWord ++ tailWord_3851064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851064).length < 2 ^ (prefixWord ++ tailWord_3851064).sum := by decide
  have hdescent : baseEnd_3851064 < baseStart_3851064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851077 : List Nat := [1, 3, 1, 1, 1, 2, 2, 4, 2, 2, 4]
def baseStart_3851077 : Nat := 118140960795 + 3851077 * 2 ^ 59
def prefixEnd_3851077 : Nat := 4983230072969 + 3 ^ 40 * 3851077 * 2
def baseEnd_3851077 : Nat := 1977453538474934377226725

theorem tailTrace_3851077 : CollatzResearch.WordTrace tailWord_3851077 prefixEnd_3851077 1977453538474934377226725 := by
  unfold tailWord_3851077
  simp only [CollatzResearch.WordTrace]
  refine ⟨140460317469213215433615485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93640211646142143622410323 140460317469213215433615485)
  ·
    refine ⟨52672619050954955787605807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140460317469213215433615485 52672619050954955787605807)
    ·
      refine ⟨79008928576432433681408711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52672619050954955787605807 79008928576432433681408711)
      ·
        refine ⟨118513392864648650522113067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79008928576432433681408711 118513392864648650522113067)
        ·
          refine ⟨177770089296972975783169601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118513392864648650522113067 177770089296972975783169601)
          ·
            refine ⟨133327566972729731837377201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177770089296972975783169601 133327566972729731837377201)
            ·
              refine ⟨99995675229547298878032901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133327566972729731837377201 99995675229547298878032901)
              ·
                refine ⟨18749189105540118539631169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99995675229547298878032901 18749189105540118539631169)
                ·
                  refine ⟨14061891829155088904723377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18749189105540118539631169 14061891829155088904723377)
                  ·
                    refine ⟨10546418871866316678542533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14061891829155088904723377 10546418871866316678542533)
                    ·
                      refine ⟨1977453538474934377226725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10546418871866316678542533 1977453538474934377226725)
                      ·
                        rfl

theorem cell23_3851077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_3851077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851077 prefixEnd_3851077 := by exact prefixLift 3851077
  have htrace : WordTrace (prefixWord ++ tailWord_3851077) baseStart_3851077 baseEnd_3851077 := by
    simpa [prefixWord, tailWord_3851077, baseEnd_3851077] using wordTrace_append hprefix tailTrace_3851077
  have hstable : (prefixWord ++ tailWord_3851077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851077).length < 2 ^ (prefixWord ++ tailWord_3851077).sum := by decide
  have hdescent : baseEnd_3851077 < baseStart_3851077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851081 : List Nat := [1, 2, 1, 1, 2, 5, 2, 1, 4, 2, 2]
def baseStart_3851081 : Nat := 118140960795 + 3851081 * 2 ^ 59
def prefixEnd_3851081 : Nat := 4983230072969 + 3 ^ 40 * 3851081 * 2
def baseEnd_3851081 : Nat := 1977455592397552361576707

theorem tailTrace_3851081 : CollatzResearch.WordTrace tailWord_3851081 prefixEnd_3851081 1977455592397552361576707 := by
  unfold tailWord_3851081
  simp only [CollatzResearch.WordTrace]
  refine ⟨140460463361198724116761097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93640308907465816077840731 140460463361198724116761097)
  ·
    refine ⟨105345347520899043087570823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140460463361198724116761097 105345347520899043087570823)
    ·
      refine ⟨158018021281348564631356235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105345347520899043087570823 158018021281348564631356235)
      ·
        refine ⟨237027031922022846947034353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158018021281348564631356235 237027031922022846947034353)
        ·
          refine ⟨177770273941517135210275765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237027031922022846947034353 177770273941517135210275765)
          ·
            refine ⟨16665963182017231425963353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 177770273941517135210275765 16665963182017231425963353)
            ·
              refine ⟨12499472386512923569472515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16665963182017231425963353 12499472386512923569472515)
              ·
                refine ⟨18749208579769385354208773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12499472386512923569472515 18749208579769385354208773)
                ·
                  refine ⟨3515476608706759753914145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18749208579769385354208773 3515476608706759753914145)
                  ·
                    refine ⟨2636607456530069815435609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3515476608706759753914145 2636607456530069815435609)
                    ·
                      refine ⟨1977455592397552361576707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2636607456530069815435609 1977455592397552361576707)
                      ·
                        rfl

theorem cell23_3851081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 4, 2, 2].length) (baseStart_3851081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851081 prefixEnd_3851081 := by exact prefixLift 3851081
  have htrace : WordTrace (prefixWord ++ tailWord_3851081) baseStart_3851081 baseEnd_3851081 := by
    simpa [prefixWord, tailWord_3851081, baseEnd_3851081] using wordTrace_append hprefix tailTrace_3851081
  have hstable : (prefixWord ++ tailWord_3851081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851081).length < 2 ^ (prefixWord ++ tailWord_3851081).sum := by decide
  have hdescent : baseEnd_3851081 < baseStart_3851081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851092 : List Nat := [2, 4, 1, 1, 5, 1, 2, 1, 2, 1, 3]
def baseStart_3851092 : Nat := 118140960795 + 3851092 * 2 ^ 59
def prefixEnd_3851092 : Nat := 4983230072969 + 3 ^ 40 * 3851092 * 2
def baseEnd_3851092 : Nat := 1977461240684751818539157

theorem tailTrace_3851092 : CollatzResearch.WordTrace tailWord_3851092 prefixEnd_3851092 1977461240684751818539157 := by
  unfold tailWord_3851092
  simp only [CollatzResearch.WordTrace]
  refine ⟨70230432282079436497705765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93640576376105915330274353 70230432282079436497705765)
  ·
    refine ⟨13168206052889894343319831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70230432282079436497705765 13168206052889894343319831)
    ·
      refine ⟨19752309079334841514979747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13168206052889894343319831 19752309079334841514979747)
      ·
        refine ⟨29628463619002262272469621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19752309079334841514979747 29628463619002262272469621)
        ·
          refine ⟨2777668464281462088044027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29628463619002262272469621 2777668464281462088044027)
          ·
            refine ⟨4166502696422193132066041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2777668464281462088044027 4166502696422193132066041)
            ·
              refine ⟨3124877022316644849049531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4166502696422193132066041 3124877022316644849049531)
              ·
                refine ⟨4687315533474967273574297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3124877022316644849049531 4687315533474967273574297)
                ·
                  refine ⟨3515486650106225455180723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4687315533474967273574297 3515486650106225455180723)
                  ·
                    refine ⟨5273229975159338182771085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3515486650106225455180723 5273229975159338182771085)
                    ·
                      refine ⟨1977461240684751818539157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5273229975159338182771085 1977461240684751818539157)
                      ·
                        rfl

theorem cell23_3851092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_3851092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851092 prefixEnd_3851092 := by exact prefixLift 3851092
  have htrace : WordTrace (prefixWord ++ tailWord_3851092) baseStart_3851092 baseEnd_3851092 := by
    simpa [prefixWord, tailWord_3851092, baseEnd_3851092] using wordTrace_append hprefix tailTrace_3851092
  have hstable : (prefixWord ++ tailWord_3851092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851092).length < 2 ^ (prefixWord ++ tailWord_3851092).sum := by decide
  have hdescent : baseEnd_3851092 < baseStart_3851092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851098 : List Nat := [3, 1, 1, 2, 1, 5, 1, 3, 2, 2, 2]
def baseStart_3851098 : Nat := 118140960795 + 3851098 * 2 ^ 59
def prefixEnd_3851098 : Nat := 4983230072969 + 3 ^ 40 * 3851098 * 2
def baseEnd_3851098 : Nat := 1977464321568678795064129

theorem tailTrace_3851098 : CollatzResearch.WordTrace tailWord_3851098 prefixEnd_3851098 1977464321568678795064129 := by
  unfold tailWord_3851098
  simp only [CollatzResearch.WordTrace]
  refine ⟨35115270850534284005032487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93640722268091424013419965 35115270850534284005032487)
  ·
    refine ⟨52672906275801426007548731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35115270850534284005032487 52672906275801426007548731)
    ·
      refine ⟨79009359413702139011323097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52672906275801426007548731 79009359413702139011323097)
      ·
        refine ⟨59257019560276604258492323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79009359413702139011323097 59257019560276604258492323)
        ·
          refine ⟨88885529340414906387738485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59257019560276604258492323 88885529340414906387738485)
          ·
            refine ⟨8333018375663897473850483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88885529340414906387738485 8333018375663897473850483)
            ·
              refine ⟨12499527563495846210775725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8333018375663897473850483 12499527563495846210775725)
              ·
                refine ⟨4687322836310942329040897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12499527563495846210775725 4687322836310942329040897)
                ·
                  refine ⟨3515492127233206746780673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4687322836310942329040897 3515492127233206746780673)
                  ·
                    refine ⟨2636619095424905060085505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3515492127233206746780673 2636619095424905060085505)
                    ·
                      refine ⟨1977464321568678795064129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2636619095424905060085505 1977464321568678795064129)
                      ·
                        rfl

theorem cell23_3851098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 2, 2, 2].length) (baseStart_3851098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851098 prefixEnd_3851098 := by exact prefixLift 3851098
  have htrace : WordTrace (prefixWord ++ tailWord_3851098) baseStart_3851098 baseEnd_3851098 := by
    simpa [prefixWord, tailWord_3851098, baseEnd_3851098] using wordTrace_append hprefix tailTrace_3851098
  have hstable : (prefixWord ++ tailWord_3851098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851098).length < 2 ^ (prefixWord ++ tailWord_3851098).sum := by decide
  have hdescent : baseEnd_3851098 < baseStart_3851098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851144 : List Nat := [2, 1, 3, 3, 2, 1, 2, 1, 1, 2, 5]
def baseStart_3851144 : Nat := 118140960795 + 3851144 * 2 ^ 59
def prefixEnd_3851144 : Nat := 4983230072969 + 3 ^ 40 * 3851144 * 2
def baseEnd_3851144 : Nat := 1977487941678785615088917

theorem tailTrace_3851144 : CollatzResearch.WordTrace tailWord_3851144 prefixEnd_3851144 1977487941678785615088917 := by
  unfold tailWord_3851144
  simp only [CollatzResearch.WordTrace]
  refine ⟨70231380579985242938152243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93641840773313657250869657 70231380579985242938152243)
  ·
    refine ⟨105347070869977864407228365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70231380579985242938152243 105347070869977864407228365)
    ·
      refine ⟨39505151576241699152710637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105347070869977864407228365 39505151576241699152710637)
      ·
        refine ⟨14814431841090637182266489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39505151576241699152710637 14814431841090637182266489)
        ·
          refine ⟨11110823880817977886699867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14814431841090637182266489 11110823880817977886699867)
          ·
            refine ⟨16666235821226966830049801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11110823880817977886699867 16666235821226966830049801)
            ·
              refine ⟨12499676865920225122537351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16666235821226966830049801 12499676865920225122537351)
              ·
                refine ⟨18749515298880337683806027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12499676865920225122537351 18749515298880337683806027)
                ·
                  refine ⟨28124272948320506525709041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18749515298880337683806027 28124272948320506525709041)
                  ·
                    refine ⟨21093204711240379894281781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28124272948320506525709041 21093204711240379894281781)
                    ·
                      refine ⟨1977487941678785615088917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21093204711240379894281781 1977487941678785615088917)
                      ·
                        rfl

theorem cell23_3851144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_3851144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851144 prefixEnd_3851144 := by exact prefixLift 3851144
  have htrace : WordTrace (prefixWord ++ tailWord_3851144) baseStart_3851144 baseEnd_3851144 := by
    simpa [prefixWord, tailWord_3851144, baseEnd_3851144] using wordTrace_append hprefix tailTrace_3851144
  have hstable : (prefixWord ++ tailWord_3851144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851144).length < 2 ^ (prefixWord ++ tailWord_3851144).sum := by decide
  have hdescent : baseEnd_3851144 < baseStart_3851144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851177 : List Nat := [1, 2, 1, 1, 1, 1, 6, 2, 8]
def baseStart_3851177 : Nat := 118140960795 + 3851177 * 2 ^ 59
def prefixEnd_3851177 : Nat := 4983230072969 + 3 ^ 40 * 3851177 * 2
def baseEnd_3851177 : Nat := 219722765171153776219585

theorem tailTrace_3851177 : CollatzResearch.WordTrace tailWord_3851177 prefixEnd_3851177 219722765171153776219585 := by
  unfold tailWord_3851177
  simp only [CollatzResearch.WordTrace]
  refine ⟨140463964768850932512255785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93642643179233955008170523 140463964768850932512255785)
  ·
    refine ⟨105347973576638199384191839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140463964768850932512255785 105347973576638199384191839)
    ·
      refine ⟨158021960364957299076287759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105347973576638199384191839 158021960364957299076287759)
      ·
        refine ⟨237032940547435948614431639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158021960364957299076287759 237032940547435948614431639)
        ·
          refine ⟨355549410821153922921647459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237032940547435948614431639 355549410821153922921647459)
          ·
            refine ⟨533324116231730884382471189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355549410821153922921647459 533324116231730884382471189)
            ·
              refine ⟨24999567948362385205428337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 533324116231730884382471189 24999567948362385205428337)
              ·
                refine ⟨18749675961271788904071253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24999567948362385205428337 18749675961271788904071253)
                ·
                  refine ⟨219722765171153776219585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18749675961271788904071253 219722765171153776219585)
                  ·
                    rfl

theorem cell23_3851177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 8].length) (baseStart_3851177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851177 prefixEnd_3851177 := by exact prefixLift 3851177
  have htrace : WordTrace (prefixWord ++ tailWord_3851177) baseStart_3851177 baseEnd_3851177 := by
    simpa [prefixWord, tailWord_3851177, baseEnd_3851177] using wordTrace_append hprefix tailTrace_3851177
  have hstable : (prefixWord ++ tailWord_3851177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851177).length < 2 ^ (prefixWord ++ tailWord_3851177).sum := by decide
  have hdescent : baseEnd_3851177 < baseStart_3851177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851198 : List Nat := [4, 2, 1, 1, 1, 2, 1, 6, 1, 4]
def baseStart_3851198 : Nat := 118140960795 + 3851198 * 2 ^ 59
def prefixEnd_3851198 : Nat := 4983230072969 + 3 ^ 40 * 3851198 * 2
def baseEnd_3851198 : Nat := 659171889878042801271223

theorem tailTrace_3851198 : CollatzResearch.WordTrace tailWord_3851198 prefixEnd_3851198 659171889878042801271223 := by
  unfold tailWord_3851198
  simp only [CollatzResearch.WordTrace]
  refine ⟨17558091337721856637346281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93643153801183235399180165 17558091337721856637346281)
  ·
    refine ⟨13168568503291392478009711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17558091337721856637346281 13168568503291392478009711)
    ·
      refine ⟨19752852754937088717014567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13168568503291392478009711 19752852754937088717014567)
      ·
        refine ⟨29629279132405633075521851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19752852754937088717014567 29629279132405633075521851)
        ·
          refine ⟨44443918698608449613282777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29629279132405633075521851 44443918698608449613282777)
          ·
            refine ⟨33332939023956337209962083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44443918698608449613282777 33332939023956337209962083)
            ·
              refine ⟨49999408535934505814943125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33332939023956337209962083 49999408535934505814943125)
              ·
                refine ⟨2343722275121929960075459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49999408535934505814943125 2343722275121929960075459)
                ·
                  refine ⟨3515583412682894940113189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2343722275121929960075459 3515583412682894940113189)
                  ·
                    refine ⟨659171889878042801271223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3515583412682894940113189 659171889878042801271223)
                    ·
                      rfl

theorem cell23_3851198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_3851198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851198 prefixEnd_3851198 := by exact prefixLift 3851198
  have htrace : WordTrace (prefixWord ++ tailWord_3851198) baseStart_3851198 baseEnd_3851198 := by
    simpa [prefixWord, tailWord_3851198, baseEnd_3851198] using wordTrace_append hprefix tailTrace_3851198
  have hstable : (prefixWord ++ tailWord_3851198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851198).length < 2 ^ (prefixWord ++ tailWord_3851198).sum := by decide
  have hdescent : baseEnd_3851198 < baseStart_3851198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851211 : List Nat := [1, 1, 1, 1, 3, 6, 3, 1, 6]
def baseStart_3851211 : Nat := 118140960795 + 3851211 * 2 ^ 59
def prefixEnd_3851211 : Nat := 4983230072969 + 3 ^ 40 * 3851211 * 2
def baseEnd_3851211 : Nat := 219724704986959650327901

theorem tailTrace_3851211 : CollatzResearch.WordTrace tailWord_3851211 prefixEnd_3851211 219724704986959650327901 := by
  unfold tailWord_3851211
  simp only [CollatzResearch.WordTrace]
  refine ⟨140465204850727756318993487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93643469900485170879328991 140465204850727756318993487)
  ·
    refine ⟨210697807276091634478490231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140465204850727756318993487 210697807276091634478490231)
    ·
      refine ⟨316046710914137451717735347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210697807276091634478490231 316046710914137451717735347)
      ·
        refine ⟨474070066371206177576603021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316046710914137451717735347 474070066371206177576603021)
        ·
          refine ⟨177776274889202316591226133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 474070066371206177576603021 177776274889202316591226133)
          ·
            refine ⟨8333262885431358590213725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 177776274889202316591226133 8333262885431358590213725)
            ·
              refine ⟨3124973582036759471330147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8333262885431358590213725 3124973582036759471330147)
              ·
                refine ⟨4687460373055139206995221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3124973582036759471330147 4687460373055139206995221)
                ·
                  refine ⟨219724704986959650327901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4687460373055139206995221 219724704986959650327901)
                  ·
                    rfl

theorem cell23_3851211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 6].length) (baseStart_3851211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851211 prefixEnd_3851211 := by exact prefixLift 3851211
  have htrace : WordTrace (prefixWord ++ tailWord_3851211) baseStart_3851211 baseEnd_3851211 := by
    simpa [prefixWord, tailWord_3851211, baseEnd_3851211] using wordTrace_append hprefix tailTrace_3851211
  have hstable : (prefixWord ++ tailWord_3851211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851211).length < 2 ^ (prefixWord ++ tailWord_3851211).sum := by decide
  have hdescent : baseEnd_3851211 < baseStart_3851211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851244 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 4]
def baseStart_3851244 : Nat := 118140960795 + 3851244 * 2 ^ 59
def prefixEnd_3851244 : Nat := 4983230072969 + 3 ^ 40 * 3851244 * 2
def baseEnd_3851244 : Nat := 1977539289744235223838457

theorem tailTrace_3851244 : CollatzResearch.WordTrace tailWord_3851244 prefixEnd_3851244 1977539289744235223838457 := by
  unfold tailWord_3851244
  simp only [CollatzResearch.WordTrace]
  refine ⟨70233204229804101477472393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93644272306405468636629857 70233204229804101477472393)
  ·
    refine ⟨52674903172353076108104295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70233204229804101477472393 52674903172353076108104295)
    ·
      refine ⟨79012354758529614162156443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52674903172353076108104295 79012354758529614162156443)
      ·
        refine ⟨118518532137794421243234665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79012354758529614162156443 118518532137794421243234665)
        ·
          refine ⟨88888899103345815932425999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118518532137794421243234665 88888899103345815932425999)
          ·
            refine ⟨133333348655018723898638999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88888899103345815932425999 133333348655018723898638999)
            ·
              refine ⟨200000022982528085847958499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133333348655018723898638999 200000022982528085847958499)
              ·
                refine ⟨300000034473792128771937749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200000022982528085847958499 300000034473792128771937749)
                ·
                  refine ⟨7031250807979503018092291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 300000034473792128771937749 7031250807979503018092291)
                  ·
                    refine ⟨10546876211969254527138437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7031250807979503018092291 10546876211969254527138437)
                    ·
                      refine ⟨1977539289744235223838457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10546876211969254527138437 1977539289744235223838457)
                      ·
                        rfl

theorem cell23_3851244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_3851244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851244 prefixEnd_3851244 := by exact prefixLift 3851244
  have htrace : WordTrace (prefixWord ++ tailWord_3851244) baseStart_3851244 baseEnd_3851244 := by
    simpa [prefixWord, tailWord_3851244, baseEnd_3851244] using wordTrace_append hprefix tailTrace_3851244
  have hstable : (prefixWord ++ tailWord_3851244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851244).length < 2 ^ (prefixWord ++ tailWord_3851244).sum := by decide
  have hdescent : baseEnd_3851244 < baseStart_3851244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851262 : List Nat := [4, 2, 2, 2, 3, 1, 2, 1, 6]
def baseStart_3851262 : Nat := 118140960795 + 3851262 * 2 ^ 59
def prefixEnd_3851262 : Nat := 4983230072969 + 3 ^ 40 * 3851262 * 2
def baseEnd_3851262 : Nat := 219727614710668461490375

theorem tailTrace_3851262 : CollatzResearch.WordTrace tailWord_3851262 prefixEnd_3851262 219727614710668461490375 := by
  unfold tailWord_3851262
  simp only [CollatzResearch.WordTrace]
  refine ⟨17558383121692874003637505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93644709982361994686066693 17558383121692874003637505)
  ·
    refine ⟨13168787341269655502728129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17558383121692874003637505 13168787341269655502728129)
    ·
      refine ⟨9876590505952241627046097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13168787341269655502728129 9876590505952241627046097)
      ·
        refine ⟨7407442879464181220284573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9876590505952241627046097 7407442879464181220284573)
        ·
          refine ⟨2777791079799067957606715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7407442879464181220284573 2777791079799067957606715)
          ·
            refine ⟨4166686619698601936410073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2777791079799067957606715 4166686619698601936410073)
            ·
              refine ⟨3125014964773951452307555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4166686619698601936410073 3125014964773951452307555)
              ·
                refine ⟨4687522447160927178461333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3125014964773951452307555 4687522447160927178461333)
                ·
                  refine ⟨219727614710668461490375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4687522447160927178461333 219727614710668461490375)
                  ·
                    rfl

theorem cell23_3851262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_3851262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851262 prefixEnd_3851262 := by exact prefixLift 3851262
  have htrace : WordTrace (prefixWord ++ tailWord_3851262) baseStart_3851262 baseEnd_3851262 := by
    simpa [prefixWord, tailWord_3851262, baseEnd_3851262] using wordTrace_append hprefix tailTrace_3851262
  have hstable : (prefixWord ++ tailWord_3851262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851262).length < 2 ^ (prefixWord ++ tailWord_3851262).sum := by decide
  have hdescent : baseEnd_3851262 < baseStart_3851262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851278 : List Nat := [4, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4]
def baseStart_3851278 : Nat := 118140960795 + 3851278 * 2 ^ 59
def prefixEnd_3851278 : Nat := 4983230072969 + 3 ^ 40 * 3851278 * 2
def baseEnd_3851278 : Nat := 1977556748086488090813301

theorem tailTrace_3851278 : CollatzResearch.WordTrace tailWord_3851278 prefixEnd_3851278 1977556748086488090813301 := by
  unfold tailWord_3851278
  simp only [CollatzResearch.WordTrace]
  refine ⟨17558456067685628345210311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93645099027656684507788325 17558456067685628345210311)
  ·
    refine ⟨26337684101528442517815467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17558456067685628345210311 26337684101528442517815467)
    ·
      refine ⟨39506526152292663776723201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26337684101528442517815467 39506526152292663776723201)
      ·
        refine ⟨29629894614219497832542401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39506526152292663776723201 29629894614219497832542401)
        ·
          refine ⟨22222420960664623374406801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29629894614219497832542401 22222420960664623374406801)
          ·
            refine ⟨16666815720498467530805101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22222420960664623374406801 16666815720498467530805101)
            ·
              refine ⟨6250055895186925324051913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16666815720498467530805101 6250055895186925324051913)
              ·
                refine ⟨4687541921390193993038935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6250055895186925324051913 4687541921390193993038935)
                ·
                  refine ⟨7031312882085290989558403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4687541921390193993038935 7031312882085290989558403)
                  ·
                    refine ⟨10546969323127936484337605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7031312882085290989558403 10546969323127936484337605)
                    ·
                      refine ⟨1977556748086488090813301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10546969323127936484337605 1977556748086488090813301)
                      ·
                        rfl

theorem cell23_3851278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_3851278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851278 prefixEnd_3851278 := by exact prefixLift 3851278
  have htrace : WordTrace (prefixWord ++ tailWord_3851278) baseStart_3851278 baseEnd_3851278 := by
    simpa [prefixWord, tailWord_3851278, baseEnd_3851278] using wordTrace_append hprefix tailTrace_3851278
  have hstable : (prefixWord ++ tailWord_3851278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851278).length < 2 ^ (prefixWord ++ tailWord_3851278).sum := by decide
  have hdescent : baseEnd_3851278 < baseStart_3851278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851298 : List Nat := [3, 3, 1, 1, 1, 5, 1, 1, 1, 1, 5]
def baseStart_3851298 : Nat := 118140960795 + 3851298 * 2 ^ 59
def prefixEnd_3851298 : Nat := 4983230072969 + 3 ^ 40 * 3851298 * 2
def baseEnd_3851298 : Nat := 1977567017699578012563209

theorem tailTrace_3851298 : CollatzResearch.WordTrace tailWord_3851298 prefixEnd_3851298 1977567017699578012563209 := by
  unfold tailWord_3851298
  simp only [CollatzResearch.WordTrace]
  refine ⟨35117094500353142544352637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93645585334275046784940365 35117094500353142544352637)
  ·
    refine ⟨13168910437632428454132239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35117094500353142544352637 13168910437632428454132239)
    ·
      refine ⟨19753365656448642681198359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13168910437632428454132239 19753365656448642681198359)
      ·
        refine ⟨29630048484672964021797539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19753365656448642681198359 29630048484672964021797539)
        ·
          refine ⟨44445072727009446032696309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29630048484672964021797539 44445072727009446032696309)
          ·
            refine ⟨4166725568157135565565279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44445072727009446032696309 4166725568157135565565279)
            ·
              refine ⟨6250088352235703348347919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4166725568157135565565279 6250088352235703348347919)
              ·
                refine ⟨9375132528353555022521879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6250088352235703348347919 9375132528353555022521879)
                ·
                  refine ⟨14062698792530332533782819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9375132528353555022521879 14062698792530332533782819)
                  ·
                    refine ⟨21094048188795498800674229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14062698792530332533782819 21094048188795498800674229)
                    ·
                      refine ⟨1977567017699578012563209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21094048188795498800674229 1977567017699578012563209)
                      ·
                        rfl

theorem cell23_3851298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_3851298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851298 prefixEnd_3851298 := by exact prefixLift 3851298
  have htrace : WordTrace (prefixWord ++ tailWord_3851298) baseStart_3851298 baseEnd_3851298 := by
    simpa [prefixWord, tailWord_3851298, baseEnd_3851298] using wordTrace_append hprefix tailTrace_3851298
  have hstable : (prefixWord ++ tailWord_3851298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851298).length < 2 ^ (prefixWord ++ tailWord_3851298).sum := by decide
  have hdescent : baseEnd_3851298 < baseStart_3851298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851306 : List Nat := [3, 1, 4, 1, 4, 1, 2, 2, 1, 1, 3]
def baseStart_3851306 : Nat := 118140960795 + 3851306 * 2 ^ 59
def prefixEnd_3851306 : Nat := 4983230072969 + 3 ^ 40 * 3851306 * 2
def baseEnd_3851306 : Nat := 1977571125544813981263173

theorem tailTrace_3851306 : CollatzResearch.WordTrace tailWord_3851306 prefixEnd_3851306 1977571125544813981263173 := by
  unfold tailWord_3851306
  simp only [CollatzResearch.WordTrace]
  refine ⟨35117167446345896885925443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93645779856922391695801181 35117167446345896885925443)
  ·
    refine ⟨52675751169518845328888165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35117167446345896885925443 52675751169518845328888165)
    ·
      refine ⟨9876703344284783499166531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52675751169518845328888165 9876703344284783499166531)
      ·
        refine ⟨14815055016427175248749797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9876703344284783499166531 14815055016427175248749797)
        ·
          refine ⟨2777822815580095359140587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14815055016427175248749797 2777822815580095359140587)
          ·
            refine ⟨4166734223370143038710881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2777822815580095359140587 4166734223370143038710881)
            ·
              refine ⟨3125050667527607279033161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4166734223370143038710881 3125050667527607279033161)
              ·
                refine ⟨2343788000645705459274871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3125050667527607279033161 2343788000645705459274871)
                ·
                  refine ⟨3515682000968558188912307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2343788000645705459274871 3515682000968558188912307)
                  ·
                    refine ⟨5273523001452837283368461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3515682000968558188912307 5273523001452837283368461)
                    ·
                      refine ⟨1977571125544813981263173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5273523001452837283368461 1977571125544813981263173)
                      ·
                        rfl

theorem cell23_3851306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_3851306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851306 prefixEnd_3851306 := by exact prefixLift 3851306
  have htrace : WordTrace (prefixWord ++ tailWord_3851306) baseStart_3851306 baseEnd_3851306 := by
    simpa [prefixWord, tailWord_3851306, baseEnd_3851306] using wordTrace_append hprefix tailTrace_3851306
  have hstable : (prefixWord ++ tailWord_3851306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851306).length < 2 ^ (prefixWord ++ tailWord_3851306).sum := by decide
  have hdescent : baseEnd_3851306 < baseStart_3851306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851311 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 8, 1, 3]
def baseStart_3851311 : Nat := 118140960795 + 3851311 * 2 ^ 59
def prefixEnd_3851311 : Nat := 4983230072969 + 3 ^ 40 * 3851311 * 2
def baseEnd_3851311 : Nat := 1977573692948086461700649

theorem tailTrace_3851311 : CollatzResearch.WordTrace tailWord_3851311 prefixEnd_3851311 1977573692948086461700649 := by
  unfold tailWord_3851311
  simp only [CollatzResearch.WordTrace]
  refine ⟨140468852150365473397633787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93645901433576982265089191 140468852150365473397633787)
  ·
    refine ⟨210703278225548210096450681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140468852150365473397633787 210703278225548210096450681)
    ·
      refine ⟨158027458669161157572338011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210703278225548210096450681 158027458669161157572338011)
      ·
        refine ⟨237041188003741736358507017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158027458669161157572338011 237041188003741736358507017)
        ·
          refine ⟨177780891002806302268880263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237041188003741736358507017 177780891002806302268880263)
          ·
            refine ⟨266671336504209453403320395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177780891002806302268880263 266671336504209453403320395)
            ·
              refine ⟨400007004756314180104980593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266671336504209453403320395 400007004756314180104980593)
              ·
                refine ⟨300005253567235635078735445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 400007004756314180104980593 300005253567235635078735445)
                ·
                  refine ⟨3515686565241042598578931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 300005253567235635078735445 3515686565241042598578931)
                  ·
                    refine ⟨5273529847861563897868397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3515686565241042598578931 5273529847861563897868397)
                    ·
                      refine ⟨1977573692948086461700649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5273529847861563897868397 1977573692948086461700649)
                      ·
                        rfl

theorem cell23_3851311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 8, 1, 3].length) (baseStart_3851311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851311 prefixEnd_3851311 := by exact prefixLift 3851311
  have htrace : WordTrace (prefixWord ++ tailWord_3851311) baseStart_3851311 baseEnd_3851311 := by
    simpa [prefixWord, tailWord_3851311, baseEnd_3851311] using wordTrace_append hprefix tailTrace_3851311
  have hstable : (prefixWord ++ tailWord_3851311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851311).length < 2 ^ (prefixWord ++ tailWord_3851311).sum := by decide
  have hdescent : baseEnd_3851311 < baseStart_3851311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851314 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 1, 9]
def baseStart_3851314 : Nat := 118140960795 + 3851314 * 2 ^ 59
def prefixEnd_3851314 : Nat := 4983230072969 + 3 ^ 40 * 3851314 * 2
def baseEnd_3851314 : Nat := 659191744463349983321045

theorem tailTrace_3851314 : CollatzResearch.WordTrace tailWord_3851314 prefixEnd_3851314 659191744463349983321045 := by
  unfold tailWord_3851314
  simp only [CollatzResearch.WordTrace]
  refine ⟨35117240392338651227498249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93645974379569736606661997 35117240392338651227498249)
  ·
    refine ⟨26337930294253988420623687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35117240392338651227498249 26337930294253988420623687)
    ·
      refine ⟨39506895441380982630935531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26337930294253988420623687 39506895441380982630935531)
      ·
        refine ⟨59260343162071473946403297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39506895441380982630935531 59260343162071473946403297)
        ·
          refine ⟨44445257371553605459802473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59260343162071473946403297 44445257371553605459802473)
          ·
            refine ⟨33333943028665204094851855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44445257371553605459802473 33333943028665204094851855)
            ·
              refine ⟨50000914542997806142277783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33333943028665204094851855 50000914542997806142277783)
              ·
                refine ⟨75001371814496709213416675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50000914542997806142277783 75001371814496709213416675)
                ·
                  refine ⟨112502057721745063820125013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75001371814496709213416675 112502057721745063820125013)
                  ·
                    refine ⟨659191744463349983321045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 112502057721745063820125013 659191744463349983321045)
                    ·
                      rfl

theorem cell23_3851314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_3851314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851314 prefixEnd_3851314 := by exact prefixLift 3851314
  have htrace : WordTrace (prefixWord ++ tailWord_3851314) baseStart_3851314 baseEnd_3851314 := by
    simpa [prefixWord, tailWord_3851314, baseEnd_3851314] using wordTrace_append hprefix tailTrace_3851314
  have hstable : (prefixWord ++ tailWord_3851314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851314).length < 2 ^ (prefixWord ++ tailWord_3851314).sum := by decide
  have hdescent : baseEnd_3851314 < baseStart_3851314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851318 : List Nat := [5, 1, 2, 1, 1, 4, 1, 8]
def baseStart_3851318 : Nat := 118140960795 + 3851318 * 2 ^ 59
def prefixEnd_3851318 : Nat := 4983230072969 + 3 ^ 40 * 3851318 * 2
def baseEnd_3851318 : Nat := 73243603233802516085671

theorem tailTrace_3851318 : CollatzResearch.WordTrace tailWord_3851318 prefixEnd_3851318 73243603233802516085671 := by
  unfold tailWord_3851318
  simp only [CollatzResearch.WordTrace]
  refine ⟨8779319216333757099571163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93646071640893409062092405 8779319216333757099571163)
  ·
    refine ⟨13168978824500635649356745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8779319216333757099571163 13168978824500635649356745)
    ·
      refine ⟨9876734118375476737017559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13168978824500635649356745 9876734118375476737017559)
      ·
        refine ⟨14815101177563215105526339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9876734118375476737017559 14815101177563215105526339)
        ·
          refine ⟨22222651766344822658289509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14815101177563215105526339 22222651766344822658289509)
          ·
            refine ⟨4166747206189654248429283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22222651766344822658289509 4166747206189654248429283)
            ·
              refine ⟨6250120809284481372643925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4166747206189654248429283 6250120809284481372643925)
              ·
                refine ⟨73243603233802516085671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6250120809284481372643925 73243603233802516085671)
                ·
                  rfl

theorem cell23_3851318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 8].length) (baseStart_3851318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851318 prefixEnd_3851318 := by exact prefixLift 3851318
  have htrace : WordTrace (prefixWord ++ tailWord_3851318) baseStart_3851318 baseEnd_3851318 := by
    simpa [prefixWord, tailWord_3851318, baseEnd_3851318] using wordTrace_append hprefix tailTrace_3851318
  have hstable : (prefixWord ++ tailWord_3851318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851318).length < 2 ^ (prefixWord ++ tailWord_3851318).sum := by decide
  have hdescent : baseEnd_3851318 < baseStart_3851318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851328 : List Nat := [2, 1, 1, 2, 2, 3, 1, 5, 2, 1, 3]
def baseStart_3851328 : Nat := 118140960795 + 3851328 * 2 ^ 59
def prefixEnd_3851328 : Nat := 4983230072969 + 3 ^ 40 * 3851328 * 2
def baseEnd_3851328 : Nat := 1977582422119212895188071

theorem tailTrace_3851328 : CollatzResearch.WordTrace tailWord_3851328 prefixEnd_3851328 1977582422119212895188071 := by
  unfold tailWord_3851328
  simp only [CollatzResearch.WordTrace]
  refine ⟨70234736095651942650501319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93646314794202590200668425 70234736095651942650501319)
  ·
    refine ⟨105352104143477913975751979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70234736095651942650501319 105352104143477913975751979)
    ·
      refine ⟨158028156215216870963627969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105352104143477913975751979 158028156215216870963627969)
      ·
        refine ⟨118521117161412653222720977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158028156215216870963627969 118521117161412653222720977)
        ·
          refine ⟨88890837871059489917040733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118521117161412653222720977 88890837871059489917040733)
          ·
            refine ⟨33334064201647308718890275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88890837871059489917040733 33334064201647308718890275)
            ·
              refine ⟨50001096302470963078335413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33334064201647308718890275 50001096302470963078335413)
              ·
                refine ⟨4687602778356652788593945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50001096302470963078335413 4687602778356652788593945)
                ·
                  refine ⟨3515702083767489591445459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4687602778356652788593945 3515702083767489591445459)
                  ·
                    refine ⟨5273553125651234387168189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3515702083767489591445459 5273553125651234387168189)
                    ·
                      refine ⟨1977582422119212895188071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5273553125651234387168189 1977582422119212895188071)
                      ·
                        rfl

theorem cell23_3851328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 2, 1, 3].length) (baseStart_3851328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851328 prefixEnd_3851328 := by exact prefixLift 3851328
  have htrace : WordTrace (prefixWord ++ tailWord_3851328) baseStart_3851328 baseEnd_3851328 := by
    simpa [prefixWord, tailWord_3851328, baseEnd_3851328] using wordTrace_append hprefix tailTrace_3851328
  have hstable : (prefixWord ++ tailWord_3851328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851328).length < 2 ^ (prefixWord ++ tailWord_3851328).sum := by decide
  have hdescent : baseEnd_3851328 < baseStart_3851328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851338 : List Nat := [3, 1, 2, 1, 1, 2, 4, 1, 3, 3, 2]
def baseStart_3851338 : Nat := 118140960795 + 3851338 * 2 ^ 59
def prefixEnd_3851338 : Nat := 4983230072969 + 3 ^ 40 * 3851338 * 2
def baseEnd_3851338 : Nat := 1977587556925757856063025

theorem tailTrace_3851338 : CollatzResearch.WordTrace tailWord_3851338 prefixEnd_3851338 1977587556925757856063025 := by
  unfold tailWord_3851338
  simp only [CollatzResearch.WordTrace]
  refine ⟨35117459230316914252216667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93646557947511771339244445 35117459230316914252216667)
  ·
    refine ⟨52676188845475371378325001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35117459230316914252216667 52676188845475371378325001)
    ·
      refine ⟨39507141634106528533743751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52676188845475371378325001 39507141634106528533743751)
      ·
        refine ⟨59260712451159792800615627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39507141634106528533743751 59260712451159792800615627)
        ·
          refine ⟨88891068676739689200923441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59260712451159792800615627 88891068676739689200923441)
          ·
            refine ⟨66668301507554766900692581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88891068676739689200923441 66668301507554766900692581)
            ·
              refine ⟨12500306532666518793879859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66668301507554766900692581 12500306532666518793879859)
              ·
                refine ⟨18750459798999778190819789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12500306532666518793879859 18750459798999778190819789)
                ·
                  refine ⟨7031422424624916821557421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18750459798999778190819789 7031422424624916821557421)
                  ·
                    refine ⟨2636783409234343808084033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7031422424624916821557421 2636783409234343808084033)
                    ·
                      refine ⟨1977587556925757856063025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2636783409234343808084033 1977587556925757856063025)
                      ·
                        rfl

theorem cell23_3851338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 3, 3, 2].length) (baseStart_3851338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851338 prefixEnd_3851338 := by exact prefixLift 3851338
  have htrace : WordTrace (prefixWord ++ tailWord_3851338) baseStart_3851338 baseEnd_3851338 := by
    simpa [prefixWord, tailWord_3851338, baseEnd_3851338] using wordTrace_append hprefix tailTrace_3851338
  have hstable : (prefixWord ++ tailWord_3851338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851338).length < 2 ^ (prefixWord ++ tailWord_3851338).sum := by decide
  have hdescent : baseEnd_3851338 < baseStart_3851338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851362 : List Nat := [3, 3, 2, 2, 1, 1, 3, 2, 2, 1, 3]
def baseStart_3851362 : Nat := 118140960795 + 3851362 * 2 ^ 59
def prefixEnd_3851362 : Nat := 4983230072969 + 3 ^ 40 * 3851362 * 2
def baseEnd_3851362 : Nat := 1977599880461465762162915

theorem tailTrace_3851362 : CollatzResearch.WordTrace tailWord_3851362 prefixEnd_3851362 1977599880461465762162915 := by
  unfold tailWord_3851362
  simp only [CollatzResearch.WordTrace]
  refine ⟨35117678068295177276935085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93647141515453806071826893 35117678068295177276935085)
  ·
    refine ⟨13169129275610691478850657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35117678068295177276935085 13169129275610691478850657)
    ·
      refine ⟨9876846956708018609137993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13169129275610691478850657 9876846956708018609137993)
      ·
        refine ⟨7407635217531013956853495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9876846956708018609137993 7407635217531013956853495)
        ·
          refine ⟨11111452826296520935280243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7407635217531013956853495 11111452826296520935280243)
          ·
            refine ⟨16667179239444781402920365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11111452826296520935280243 16667179239444781402920365)
            ·
              refine ⟨6250192214791793026095137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16667179239444781402920365 6250192214791793026095137)
              ·
                refine ⟨4687644161093844769571353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6250192214791793026095137 4687644161093844769571353)
                ·
                  refine ⟨3515733120820383577178515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4687644161093844769571353 3515733120820383577178515)
                  ·
                    refine ⟨5273599681230575365767773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3515733120820383577178515 5273599681230575365767773)
                    ·
                      refine ⟨1977599880461465762162915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5273599681230575365767773 1977599880461465762162915)
                      ·
                        rfl

theorem cell23_3851362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_3851362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851362 prefixEnd_3851362 := by exact prefixLift 3851362
  have htrace : WordTrace (prefixWord ++ tailWord_3851362) baseStart_3851362 baseEnd_3851362 := by
    simpa [prefixWord, tailWord_3851362, baseEnd_3851362] using wordTrace_append hprefix tailTrace_3851362
  have hstable : (prefixWord ++ tailWord_3851362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851362).length < 2 ^ (prefixWord ++ tailWord_3851362).sum := by decide
  have hdescent : baseEnd_3851362 < baseStart_3851362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851425 : List Nat := [1, 2, 3, 3, 1, 1, 5, 2, 5]
def baseStart_3851425 : Nat := 118140960795 + 3851425 * 2 ^ 59
def prefixEnd_3851425 : Nat := 4983230072969 + 3 ^ 40 * 3851425 * 2
def baseEnd_3851425 : Nat := 219736914415855446186125

theorem tailTrace_3851425 : CollatzResearch.WordTrace tailWord_3851425 prefixEnd_3851425 219736914415855446186125 := by
  unfold tailWord_3851425
  simp only [CollatzResearch.WordTrace]
  refine ⟨140473010071952470867283729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93648673381301647244855819 140473010071952470867283729)
  ·
    refine ⟨105354757553964353150462797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140473010071952470867283729 105354757553964353150462797)
    ·
      refine ⟨39508034082736632431423549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105354757553964353150462797 39508034082736632431423549)
      ·
        refine ⟨14815512781026237161783831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39508034082736632431423549 14815512781026237161783831)
        ·
          refine ⟨22223269171539355742675747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14815512781026237161783831 22223269171539355742675747)
          ·
            refine ⟨33334903757309033614013621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22223269171539355742675747 33334903757309033614013621)
            ·
              refine ⟨3125147227247721901313777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33334903757309033614013621 3125147227247721901313777)
              ·
                refine ⟨2343860420435791425985333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3125147227247721901313777 2343860420435791425985333)
                ·
                  refine ⟨219736914415855446186125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2343860420435791425985333 219736914415855446186125)
                  ·
                    rfl

theorem cell23_3851425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 2, 5].length) (baseStart_3851425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851425 prefixEnd_3851425 := by exact prefixLift 3851425
  have htrace : WordTrace (prefixWord ++ tailWord_3851425) baseStart_3851425 baseEnd_3851425 := by
    simpa [prefixWord, tailWord_3851425, baseEnd_3851425] using wordTrace_append hprefix tailTrace_3851425
  have hstable : (prefixWord ++ tailWord_3851425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851425).length < 2 ^ (prefixWord ++ tailWord_3851425).sum := by decide
  have hdescent : baseEnd_3851425 < baseStart_3851425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851476 : List Nat := [2, 4, 1, 4, 2, 1, 2, 2, 5]
def baseStart_3851476 : Nat := 118140960795 + 3851476 * 2 ^ 59
def prefixEnd_3851476 : Nat := 4983230072969 + 3 ^ 40 * 3851476 * 2
def baseEnd_3851476 : Nat := 219739824139564257348599

theorem tailTrace_3851476 : CollatzResearch.WordTrace tailWord_3851476 prefixEnd_3851476 219739824139564257348599 := by
  unfold tailWord_3851476
  simp only [CollatzResearch.WordTrace]
  refine ⟨70237435097383853288695141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93649913463178471051593521 70237435097383853288695141)
  ·
    refine ⟨13169519080759472491630339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70237435097383853288695141 13169519080759472491630339)
    ·
      refine ⟨19754278621139208737445509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13169519080759472491630339 19754278621139208737445509)
      ·
        refine ⟨3703927241463601638271033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19754278621139208737445509 3703927241463601638271033)
        ·
          refine ⟨2777945431097701228703275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3703927241463601638271033 2777945431097701228703275)
          ·
            refine ⟨4166918146646551843054913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2777945431097701228703275 4166918146646551843054913)
            ·
              refine ⟨3125188609984913882291185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4166918146646551843054913 3125188609984913882291185)
              ·
                refine ⟨2343891457488685411718389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3125188609984913882291185 2343891457488685411718389)
                ·
                  refine ⟨219739824139564257348599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2343891457488685411718389 219739824139564257348599)
                  ·
                    rfl

theorem cell23_3851476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_3851476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851476 prefixEnd_3851476 := by exact prefixLift 3851476
  have htrace : WordTrace (prefixWord ++ tailWord_3851476) baseStart_3851476 baseEnd_3851476 := by
    simpa [prefixWord, tailWord_3851476, baseEnd_3851476] using wordTrace_append hprefix tailTrace_3851476
  have hstable : (prefixWord ++ tailWord_3851476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851476).length < 2 ^ (prefixWord ++ tailWord_3851476).sum := by decide
  have hdescent : baseEnd_3851476 < baseStart_3851476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851498 : List Nat := [3, 1, 3, 1, 1, 3, 2, 3, 6]
def baseStart_3851498 : Nat := 118140960795 + 3851498 * 2 ^ 59
def prefixEnd_3851498 : Nat := 4983230072969 + 3 ^ 40 * 3851498 * 2
def baseEnd_3851498 : Nat := 219741079314497470006921

theorem tailTrace_3851498 : CollatzResearch.WordTrace tailWord_3851498 prefixEnd_3851498 219741079314497470006921 := by
  unfold tailWord_3851498
  simp only [CollatzResearch.WordTrace]
  refine ⟨35118918150172001083672787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93650448400458669556460765 35118918150172001083672787)
  ·
    refine ⟨52678377225258001625509181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35118918150172001083672787 52678377225258001625509181)
    ·
      refine ⟨19754391459471750609565943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52678377225258001625509181 19754391459471750609565943)
      ·
        refine ⟨29631587189207625914348915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19754391459471750609565943 29631587189207625914348915)
        ·
          refine ⟨44447380783811438871523373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29631587189207625914348915 44447380783811438871523373)
          ·
            refine ⟨16667767793929289576821265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44447380783811438871523373 16667767793929289576821265)
            ·
              refine ⟨12500825845446967182615949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16667767793929289576821265 12500825845446967182615949)
              ·
                refine ⟨4687809692042612693480981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12500825845446967182615949 4687809692042612693480981)
                ·
                  refine ⟨219741079314497470006921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4687809692042612693480981 219741079314497470006921)
                  ·
                    rfl

theorem cell23_3851498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 6].length) (baseStart_3851498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851498 prefixEnd_3851498 := by exact prefixLift 3851498
  have htrace : WordTrace (prefixWord ++ tailWord_3851498) baseStart_3851498 baseEnd_3851498 := by
    simpa [prefixWord, tailWord_3851498, baseEnd_3851498] using wordTrace_append hprefix tailTrace_3851498
  have hstable : (prefixWord ++ tailWord_3851498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851498).length < 2 ^ (prefixWord ++ tailWord_3851498).sum := by decide
  have hdescent : baseEnd_3851498 < baseStart_3851498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851548 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 5, 1, 4]
def baseStart_3851548 : Nat := 118140960795 + 3851548 * 2 ^ 59
def prefixEnd_3851548 : Nat := 4983230072969 + 3 ^ 40 * 3851548 * 2
def baseEnd_3851548 : Nat := 1977695387863202034437059

theorem tailTrace_3851548 : CollatzResearch.WordTrace tailWord_3851548 prefixEnd_3851548 1977695387863202034437059 := by
  unfold tailWord_3851548
  simp only [CollatzResearch.WordTrace]
  refine ⟨70238748125253431437005649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93651664167004575249340865 70238748125253431437005649)
  ·
    refine ⟨52679061093940073577754237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70238748125253431437005649 52679061093940073577754237)
    ·
      refine ⟨19754647910227527591657839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52679061093940073577754237 19754647910227527591657839)
      ·
        refine ⟨29631971865341291387486759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19754647910227527591657839 29631971865341291387486759)
        ·
          refine ⟨44447957798011937081230139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29631971865341291387486759 44447957798011937081230139)
          ·
            refine ⟨66671936697017905621845209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44447957798011937081230139 66671936697017905621845209)
            ·
              refine ⟨50003952522763429216383907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66671936697017905621845209 50003952522763429216383907)
              ·
                refine ⟨75005928784145143824575861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50003952522763429216383907 75005928784145143824575861)
                ·
                  refine ⟨7031805823513607233553987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75005928784145143824575861 7031805823513607233553987)
                  ·
                    refine ⟨10547708735270410850330981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7031805823513607233553987 10547708735270410850330981)
                    ·
                      refine ⟨1977695387863202034437059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10547708735270410850330981 1977695387863202034437059)
                      ·
                        rfl

theorem cell23_3851548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_3851548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851548 prefixEnd_3851548 := by exact prefixLift 3851548
  have htrace : WordTrace (prefixWord ++ tailWord_3851548) baseStart_3851548 baseEnd_3851548 := by
    simpa [prefixWord, tailWord_3851548, baseEnd_3851548] using wordTrace_append hprefix tailTrace_3851548
  have hstable : (prefixWord ++ tailWord_3851548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851548).length < 2 ^ (prefixWord ++ tailWord_3851548).sum := by decide
  have hdescent : baseEnd_3851548 < baseStart_3851548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851562 : List Nat := [3, 1, 4, 2, 1, 2, 2, 2, 1, 5]
def baseStart_3851562 : Nat := 118140960795 + 3851562 * 2 ^ 59
def prefixEnd_3851562 : Nat := 4983230072969 + 3 ^ 40 * 3851562 * 2
def baseEnd_3851562 : Nat := 659234192197454993220665

theorem tailTrace_3851562 : CollatzResearch.WordTrace tailWord_3851562 prefixEnd_3851562 659234192197454993220665 := by
  unfold tailWord_3851562
  simp only [CollatzResearch.WordTrace]
  refine ⟨35119501718114035816255235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93652004581637428843347293 35119501718114035816255235)
  ·
    refine ⟨52679252577171053724382853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35119501718114035816255235 52679252577171053724382853)
    ·
      refine ⟨9877359858219572573321785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52679252577171053724382853 9877359858219572573321785)
      ·
        refine ⟨7408019893664679429991339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9877359858219572573321785 7408019893664679429991339)
        ·
          refine ⟨11112029840497019144987009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7408019893664679429991339 11112029840497019144987009)
          ·
            refine ⟨8334022380372764358740257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11112029840497019144987009 8334022380372764358740257)
            ·
              refine ⟨6250516785279573269055193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8334022380372764358740257 6250516785279573269055193)
              ·
                refine ⟨4687887588959679951791395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6250516785279573269055193 4687887588959679951791395)
                ·
                  refine ⟨7031831383439519927687093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4687887588959679951791395 7031831383439519927687093)
                  ·
                    refine ⟨659234192197454993220665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7031831383439519927687093 659234192197454993220665)
                    ·
                      rfl

theorem cell23_3851562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_3851562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851562 prefixEnd_3851562 := by exact prefixLift 3851562
  have htrace : WordTrace (prefixWord ++ tailWord_3851562) baseStart_3851562 baseEnd_3851562 := by
    simpa [prefixWord, tailWord_3851562, baseEnd_3851562] using wordTrace_append hprefix tailTrace_3851562
  have hstable : (prefixWord ++ tailWord_3851562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851562).length < 2 ^ (prefixWord ++ tailWord_3851562).sum := by decide
  have hdescent : baseEnd_3851562 < baseStart_3851562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851578 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 3, 2, 4]
def baseStart_3851578 : Nat := 118140960795 + 3851578 * 2 ^ 59
def prefixEnd_3851578 : Nat := 4983230072969 + 3 ^ 40 * 3851578 * 2
def baseEnd_3851578 : Nat := 1977710792282836917061921

theorem tailTrace_3851578 : CollatzResearch.WordTrace tailWord_3851578 prefixEnd_3851578 1977710792282836917061921 := by
  unfold tailWord_3851578
  simp only [CollatzResearch.WordTrace]
  refine ⟨35119647610099544499400847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93652393626932118665068925 35119647610099544499400847)
  ·
    refine ⟨52679471415149316749101271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35119647610099544499400847 52679471415149316749101271)
    ·
      refine ⟨79019207122723975123651907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52679471415149316749101271 79019207122723975123651907)
      ·
        refine ⟨118528810684085962685477861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79019207122723975123651907 118528810684085962685477861)
        ·
          refine ⟨22224152003266118003527099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118528810684085962685477861 22224152003266118003527099)
          ·
            refine ⟨33336228004899177005290649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22224152003266118003527099 33336228004899177005290649)
            ·
              refine ⟨25002171003674382753967987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33336228004899177005290649 25002171003674382753967987)
              ·
                refine ⟨37503256505511574130951981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25002171003674382753967987 37503256505511574130951981)
                ·
                  refine ⟨14063721189566840299106993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37503256505511574130951981 14063721189566840299106993)
                  ·
                    refine ⟨10547790892175130224330245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14063721189566840299106993 10547790892175130224330245)
                    ·
                      refine ⟨1977710792282836917061921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10547790892175130224330245 1977710792282836917061921)
                      ·
                        rfl

theorem cell23_3851578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_3851578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851578 prefixEnd_3851578 := by exact prefixLift 3851578
  have htrace : WordTrace (prefixWord ++ tailWord_3851578) baseStart_3851578 baseEnd_3851578 := by
    simpa [prefixWord, tailWord_3851578, baseEnd_3851578] using wordTrace_append hprefix tailTrace_3851578
  have hstable : (prefixWord ++ tailWord_3851578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851578).length < 2 ^ (prefixWord ++ tailWord_3851578).sum := by decide
  have hdescent : baseEnd_3851578 < baseStart_3851578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851585 : List Nat := [1, 2, 5, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_3851585 : Nat := 118140960795 + 3851585 * 2 ^ 59
def prefixEnd_3851585 : Nat := 4983230072969 + 3 ^ 40 * 3851585 * 2
def baseEnd_3851585 : Nat := 1977714386647418389674389

theorem tailTrace_3851585 : CollatzResearch.WordTrace tailWord_3851585 prefixEnd_3851585 1977714386647418389674389 := by
  unfold tailWord_3851585
  simp only [CollatzResearch.WordTrace]
  refine ⟨140478845751372818193108209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93652563834248545462072139 140478845751372818193108209)
  ·
    refine ⟨105359134313529613644831157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140478845751372818193108209 105359134313529613644831157)
    ·
      refine ⟨9877418841893401279202921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105359134313529613644831157 9877418841893401279202921)
      ·
        refine ⟨7408064131420050959402191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9877418841893401279202921 7408064131420050959402191)
        ·
          refine ⟨11112096197130076439103287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7408064131420050959402191 11112096197130076439103287)
          ·
            refine ⟨16668144295695114658654931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11112096197130076439103287 16668144295695114658654931)
            ·
              refine ⟨25002216443542671987982397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16668144295695114658654931 25002216443542671987982397)
              ·
                refine ⟨9375831166328501995493399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25002216443542671987982397 9375831166328501995493399)
                ·
                  refine ⟨14063746749492752993240099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9375831166328501995493399 14063746749492752993240099)
                  ·
                    refine ⟨21095620124239129489860149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14063746749492752993240099 21095620124239129489860149)
                    ·
                      refine ⟨1977714386647418389674389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21095620124239129489860149 1977714386647418389674389)
                      ·
                        rfl

theorem cell23_3851585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_3851585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851585 prefixEnd_3851585 := by exact prefixLift 3851585
  have htrace : WordTrace (prefixWord ++ tailWord_3851585) baseStart_3851585 baseEnd_3851585 := by
    simpa [prefixWord, tailWord_3851585, baseEnd_3851585] using wordTrace_append hprefix tailTrace_3851585
  have hstable : (prefixWord ++ tailWord_3851585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851585).length < 2 ^ (prefixWord ++ tailWord_3851585).sum := by decide
  have hdescent : baseEnd_3851585 < baseStart_3851585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851613 : List Nat := [1, 4, 5, 1, 2, 1, 1, 2, 1, 5]
def baseStart_3851613 : Nat := 118140960795 + 3851613 * 2 ^ 59
def prefixEnd_3851613 : Nat := 4983230072969 + 3 ^ 40 * 3851613 * 2
def baseEnd_3851613 : Nat := 659242921368581426708087

theorem tailTrace_3851613 : CollatzResearch.WordTrace tailWord_3851613 prefixEnd_3851613 659242921368581426708087 := by
  unfold tailWord_3851613
  simp only [CollatzResearch.WordTrace]
  refine ⟨140479866995271378975127493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93653244663514252650084995 140479866995271378975127493)
  ·
    refine ⟨26339975061613383557836405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140479866995271378975127493 26339975061613383557836405)
    ·
      refine ⟨2469372662026254708547163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26339975061613383557836405 2469372662026254708547163)
      ·
        refine ⟨3704058993039382062820745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2469372662026254708547163 3704058993039382062820745)
        ·
          refine ⟨2778044244779536547115559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3704058993039382062820745 2778044244779536547115559)
          ·
            refine ⟨4167066367169304820673339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2778044244779536547115559 4167066367169304820673339)
            ·
              refine ⟨6250599550753957231010009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4167066367169304820673339 6250599550753957231010009)
              ·
                refine ⟨4687949663065467923257507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6250599550753957231010009 4687949663065467923257507)
                ·
                  refine ⟨7031924494598201884886261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4687949663065467923257507 7031924494598201884886261)
                  ·
                    refine ⟨659242921368581426708087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7031924494598201884886261 659242921368581426708087)
                    ·
                      rfl

theorem cell23_3851613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_3851613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851613 prefixEnd_3851613 := by exact prefixLift 3851613
  have htrace : WordTrace (prefixWord ++ tailWord_3851613) baseStart_3851613 baseEnd_3851613 := by
    simpa [prefixWord, tailWord_3851613, baseEnd_3851613] using wordTrace_append hprefix tailTrace_3851613
  have hstable : (prefixWord ++ tailWord_3851613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851613).length < 2 ^ (prefixWord ++ tailWord_3851613).sum := by decide
  have hdescent : baseEnd_3851613 < baseStart_3851613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851650 : List Nat := [3, 4, 2, 1, 1, 1, 4, 2, 1, 2, 2]
def baseStart_3851650 : Nat := 118140960795 + 3851650 * 2 ^ 59
def prefixEnd_3851650 : Nat := 4983230072969 + 3 ^ 40 * 3851650 * 2
def baseEnd_3851650 : Nat := 1977747762889960635361591

theorem tailTrace_3851650 : CollatzResearch.WordTrace tailWord_3851650 prefixEnd_3851650 1977747762889960635361591 := by
  unfold tailWord_3851650
  simp only [CollatzResearch.WordTrace]
  refine ⟨35120304124034333573556101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93654144330758222862816269 35120304124034333573556101)
  ·
    refine ⟨6585057023256437545041769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35120304124034333573556101 6585057023256437545041769)
    ·
      refine ⟨4938792767442328158781327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6585057023256437545041769 4938792767442328158781327)
      ·
        refine ⟨7408189151163492238171991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4938792767442328158781327 7408189151163492238171991)
        ·
          refine ⟨11112283726745238357257987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7408189151163492238171991 11112283726745238357257987)
          ·
            refine ⟨16668425590117857535886981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11112283726745238357257987 16668425590117857535886981)
            ·
              refine ⟨3125329798147098287978809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16668425590117857535886981 3125329798147098287978809)
              ·
                refine ⟨2343997348610323715984107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3125329798147098287978809 2343997348610323715984107)
                ·
                  refine ⟨3515996022915485573976161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2343997348610323715984107 3515996022915485573976161)
                  ·
                    refine ⟨2636997017186614180482121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3515996022915485573976161 2636997017186614180482121)
                    ·
                      refine ⟨1977747762889960635361591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2636997017186614180482121 1977747762889960635361591)
                      ·
                        rfl

theorem cell23_3851650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_3851650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851650 prefixEnd_3851650 := by exact prefixLift 3851650
  have htrace : WordTrace (prefixWord ++ tailWord_3851650) baseStart_3851650 baseEnd_3851650 := by
    simpa [prefixWord, tailWord_3851650, baseEnd_3851650] using wordTrace_append hprefix tailTrace_3851650
  have hstable : (prefixWord ++ tailWord_3851650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851650).length < 2 ^ (prefixWord ++ tailWord_3851650).sum := by decide
  have hdescent : baseEnd_3851650 < baseStart_3851650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851693 : List Nat := [1, 5, 2, 2, 1, 3, 2, 1, 1, 3, 2]
def baseStart_3851693 : Nat := 118140960795 + 3851693 * 2 ^ 59
def prefixEnd_3851693 : Nat := 4983230072969 + 3 ^ 40 * 3851693 * 2
def baseEnd_3851693 : Nat := 1977769842558103967123893

theorem tailTrace_3851693 : CollatzResearch.WordTrace tailWord_3851693 prefixEnd_3851693 1977769842558103967123893 := by
  unfold tailWord_3851693
  simp only [CollatzResearch.WordTrace]
  refine ⟨140482784834981552638039733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93655189889987701758693155 140482784834981552638039733)
  ·
    refine ⟨13170261078279520559816225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140482784834981552638039733 13170261078279520559816225)
    ·
      refine ⟨9877695808709640419862169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13170261078279520559816225 9877695808709640419862169)
      ·
        refine ⟨7408271856532230314896627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9877695808709640419862169 7408271856532230314896627)
        ·
          refine ⟨11112407784798345472344941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7408271856532230314896627 11112407784798345472344941)
          ·
            refine ⟨4167152919299379552129353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11112407784798345472344941 4167152919299379552129353)
            ·
              refine ⟨3125364689474534664097015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4167152919299379552129353 3125364689474534664097015)
              ·
                refine ⟨4688047034211801996145523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3125364689474534664097015 4688047034211801996145523)
                ·
                  refine ⟨7032070551317702994218285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4688047034211801996145523 7032070551317702994218285)
                  ·
                    refine ⟨2637026456744138622831857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7032070551317702994218285 2637026456744138622831857)
                    ·
                      refine ⟨1977769842558103967123893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2637026456744138622831857 1977769842558103967123893)
                      ·
                        rfl

theorem cell23_3851693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_3851693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851693 prefixEnd_3851693 := by exact prefixLift 3851693
  have htrace : WordTrace (prefixWord ++ tailWord_3851693) baseStart_3851693 baseEnd_3851693 := by
    simpa [prefixWord, tailWord_3851693, baseEnd_3851693] using wordTrace_append hprefix tailTrace_3851693
  have hstable : (prefixWord ++ tailWord_3851693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851693).length < 2 ^ (prefixWord ++ tailWord_3851693).sum := by decide
  have hdescent : baseEnd_3851693 < baseStart_3851693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851715 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 1, 7, 2]
def baseStart_3851715 : Nat := 118140960795 + 3851715 * 2 ^ 59
def prefixEnd_3851715 : Nat := 4983230072969 + 3 ^ 40 * 3851715 * 2
def baseEnd_3851715 : Nat := 1977781139132502881048791

theorem tailTrace_3851715 : CollatzResearch.WordTrace tailWord_3851715 prefixEnd_3851715 1977781139132502881048791 := by
  unfold tailWord_3851715
  simp only [CollatzResearch.WordTrace]
  refine ⟨140483587240901850395340599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93655724827267900263560399 140483587240901850395340599)
  ·
    refine ⟨210725380861352775593010899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140483587240901850395340599 210725380861352775593010899)
    ·
      refine ⟨316088071292029163389516349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210725380861352775593010899 316088071292029163389516349)
      ·
        refine ⟨118533026734510936271068631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316088071292029163389516349 118533026734510936271068631)
        ·
          refine ⟨177799540101766404406602947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118533026734510936271068631 177799540101766404406602947)
          ·
            refine ⟨266699310152649606609904421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177799540101766404406602947 266699310152649606609904421)
            ·
              refine ⟨50006120653621801239357079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 266699310152649606609904421 50006120653621801239357079)
              ·
                refine ⟨75009180980432701859035619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50006120653621801239357079 75009180980432701859035619)
                ·
                  refine ⟨112513771470649052788553429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75009180980432701859035619 112513771470649052788553429)
                  ·
                    refine ⟨2637041518843337174731721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 112513771470649052788553429 2637041518843337174731721)
                    ·
                      refine ⟨1977781139132502881048791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2637041518843337174731721 1977781139132502881048791)
                      ·
                        rfl

theorem cell23_3851715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 7, 2].length) (baseStart_3851715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851715 prefixEnd_3851715 := by exact prefixLift 3851715
  have htrace : WordTrace (prefixWord ++ tailWord_3851715) baseStart_3851715 baseEnd_3851715 := by
    simpa [prefixWord, tailWord_3851715, baseEnd_3851715] using wordTrace_append hprefix tailTrace_3851715
  have hstable : (prefixWord ++ tailWord_3851715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851715).length < 2 ^ (prefixWord ++ tailWord_3851715).sum := by decide
  have hdescent : baseEnd_3851715 < baseStart_3851715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851745 : List Nat := [1, 2, 3, 1, 2, 3, 2, 1, 1, 3, 4]
def baseStart_3851745 : Nat := 118140960795 + 3851745 * 2 ^ 59
def prefixEnd_3851745 : Nat := 4983230072969 + 3 ^ 40 * 3851745 * 2
def baseEnd_3851745 : Nat := 1977796543552137763673653

theorem tailTrace_3851745 : CollatzResearch.WordTrace tailWord_3851745 prefixEnd_3851745 1977796543552137763673653 := by
  unfold tailWord_3851745
  simp only [CollatzResearch.WordTrace]
  refine ⟨140484681430793165518932689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93656454287195443679288459 140484681430793165518932689)
  ·
    refine ⟨105363511073094874139199517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140484681430793165518932689 105363511073094874139199517)
    ·
      refine ⟨39511316652410577802199819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105363511073094874139199517 39511316652410577802199819)
      ·
        refine ⟨59266974978615866703299729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39511316652410577802199819 59266974978615866703299729)
        ·
          refine ⟨44450231233961900027474797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59266974978615866703299729 44450231233961900027474797)
          ·
            refine ⟨16668836712735712510303049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44450231233961900027474797 16668836712735712510303049)
            ·
              refine ⟨12501627534551784382727287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16668836712735712510303049 12501627534551784382727287)
              ·
                refine ⟨18752441301827676574090931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12501627534551784382727287 18752441301827676574090931)
                ·
                  refine ⟨28128661952741514861136397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18752441301827676574090931 28128661952741514861136397)
                  ·
                    refine ⟨10548248232278068072926149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28128661952741514861136397 10548248232278068072926149)
                    ·
                      refine ⟨1977796543552137763673653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10548248232278068072926149 1977796543552137763673653)
                      ·
                        rfl

theorem cell23_3851745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_3851745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851745 prefixEnd_3851745 := by exact prefixLift 3851745
  have htrace : WordTrace (prefixWord ++ tailWord_3851745) baseStart_3851745 baseEnd_3851745 := by
    simpa [prefixWord, tailWord_3851745, baseEnd_3851745] using wordTrace_append hprefix tailTrace_3851745
  have hstable : (prefixWord ++ tailWord_3851745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851745).length < 2 ^ (prefixWord ++ tailWord_3851745).sum := by decide
  have hdescent : baseEnd_3851745 < baseStart_3851745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851762 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 4, 1, 4]
def baseStart_3851762 : Nat := 118140960795 + 3851762 * 2 ^ 59
def prefixEnd_3851762 : Nat := 4983230072969 + 3 ^ 40 * 3851762 * 2
def baseEnd_3851762 : Nat := 1977805272723264197161075

theorem tailTrace_3851762 : CollatzResearch.WordTrace tailWord_3851762 prefixEnd_3851762 1977805272723264197161075 := by
  unfold tailWord_3851762
  simp only [CollatzResearch.WordTrace]
  refine ⟨35121325367932894355575385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93656867647821051614867693 35121325367932894355575385)
  ·
    refine ⟨26340994025949670766681539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35121325367932894355575385 26340994025949670766681539)
    ·
      refine ⟨39511491038924506150022309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26340994025949670766681539 39511491038924506150022309)
      ·
        refine ⟨7408404569798344903129183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39511491038924506150022309 7408404569798344903129183)
        ·
          refine ⟨11112606854697517354693775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7408404569798344903129183 11112606854697517354693775)
          ·
            refine ⟨16668910282046276032040663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11112606854697517354693775 16668910282046276032040663)
            ·
              refine ⟨25003365423069414048060995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16668910282046276032040663 25003365423069414048060995)
              ·
                refine ⟨37505048134604121072091493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25003365423069414048060995 37505048134604121072091493)
                ·
                  refine ⟨7032196525238272701017155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37505048134604121072091493 7032196525238272701017155)
                  ·
                    refine ⟨10548294787857409051525733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7032196525238272701017155 10548294787857409051525733)
                    ·
                      refine ⟨1977805272723264197161075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10548294787857409051525733 1977805272723264197161075)
                      ·
                        rfl

theorem cell23_3851762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_3851762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851762 prefixEnd_3851762 := by exact prefixLift 3851762
  have htrace : WordTrace (prefixWord ++ tailWord_3851762) baseStart_3851762 baseEnd_3851762 := by
    simpa [prefixWord, tailWord_3851762, baseEnd_3851762] using wordTrace_append hprefix tailTrace_3851762
  have hstable : (prefixWord ++ tailWord_3851762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851762).length < 2 ^ (prefixWord ++ tailWord_3851762).sum := by decide
  have hdescent : baseEnd_3851762 < baseStart_3851762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851772 : List Nat := [2, 2, 2, 1, 2, 1, 5, 1, 3, 4]
def baseStart_3851772 : Nat := 118140960795 + 3851772 * 2 ^ 59
def prefixEnd_3851772 : Nat := 4983230072969 + 3 ^ 40 * 3851772 * 2
def baseEnd_3851772 : Nat := 659270135843269719345343

theorem tailTrace_3851772 : CollatzResearch.WordTrace tailWord_3851772 prefixEnd_3851772 659270135843269719345343 := by
  unfold tailWord_3851772
  simp only [CollatzResearch.WordTrace]
  refine ⟨70242833100847674565082785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93657110801130232753443713 70242833100847674565082785)
  ·
    refine ⟨52682124825635755923812089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70242833100847674565082785 52682124825635755923812089)
    ·
      refine ⟨39511593619226816942859067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52682124825635755923812089 39511593619226816942859067)
      ·
        refine ⟨59267390428840225414288601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39511593619226816942859067 59267390428840225414288601)
        ·
          refine ⟨44450542821630169060716451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59267390428840225414288601 44450542821630169060716451)
          ·
            refine ⟨66675814232445253591074677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44450542821630169060716451 66675814232445253591074677)
            ·
              refine ⟨6250857584291742524163251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66675814232445253591074677 6250857584291742524163251)
              ·
                refine ⟨9376286376437613786244877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6250857584291742524163251 9376286376437613786244877)
                ·
                  refine ⟨3516107391164105169841829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9376286376437613786244877 3516107391164105169841829)
                  ·
                    refine ⟨659270135843269719345343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3516107391164105169841829 659270135843269719345343)
                    ·
                      rfl

theorem cell23_3851772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_3851772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851772 prefixEnd_3851772 := by exact prefixLift 3851772
  have htrace : WordTrace (prefixWord ++ tailWord_3851772) baseStart_3851772 baseEnd_3851772 := by
    simpa [prefixWord, tailWord_3851772, baseEnd_3851772] using wordTrace_append hprefix tailTrace_3851772
  have hstable : (prefixWord ++ tailWord_3851772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851772).length < 2 ^ (prefixWord ++ tailWord_3851772).sum := by decide
  have hdescent : baseEnd_3851772 < baseStart_3851772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851785 : List Nat := [1, 2, 1, 1, 3, 1, 5, 3, 6]
def baseStart_3851785 : Nat := 118140960795 + 3851785 * 2 ^ 59
def prefixEnd_3851785 : Nat := 4983230072969 + 3 ^ 40 * 3851785 * 2
def baseEnd_3851785 : Nat := 219757453642035289685941

theorem tailTrace_3851785 : CollatzResearch.WordTrace tailWord_3851785 prefixEnd_3851785 219757453642035289685941 := by
  unfold tailWord_3851785
  simp only [CollatzResearch.WordTrace]
  refine ⟨140486140350648252350388809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93657426900432168233592539 140486140350648252350388809)
  ·
    refine ⟨105364605262986189262791607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140486140350648252350388809 105364605262986189262791607)
    ·
      refine ⟨158046907894479283894187411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105364605262986189262791607 158046907894479283894187411)
      ·
        refine ⟨237070361841718925841281117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158046907894479283894187411 237070361841718925841281117)
        ·
          refine ⟨88901385690644597190480419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237070361841718925841281117 88901385690644597190480419)
          ·
            refine ⟨133352078535966895785720629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88901385690644597190480419 133352078535966895785720629)
            ·
              refine ⟨12501757362746896479911309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133352078535966895785720629 12501757362746896479911309)
              ·
                refine ⟨4688159011030086179966741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12501757362746896479911309 4688159011030086179966741)
                ·
                  refine ⟨219757453642035289685941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4688159011030086179966741 219757453642035289685941)
                  ·
                    rfl

theorem cell23_3851785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 6].length) (baseStart_3851785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851785 prefixEnd_3851785 := by exact prefixLift 3851785
  have htrace : WordTrace (prefixWord ++ tailWord_3851785) baseStart_3851785 baseEnd_3851785 := by
    simpa [prefixWord, tailWord_3851785, baseEnd_3851785] using wordTrace_append hprefix tailTrace_3851785
  have hstable : (prefixWord ++ tailWord_3851785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851785).length < 2 ^ (prefixWord ++ tailWord_3851785).sum := by decide
  have hdescent : baseEnd_3851785 < baseStart_3851785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851796 : List Nat := [2, 4, 3, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_3851796 : Nat := 118140960795 + 3851796 * 2 ^ 59
def prefixEnd_3851796 : Nat := 4983230072969 + 3 ^ 40 * 3851796 * 2
def baseEnd_3851796 : Nat := 1977822731065517064135919

theorem tailTrace_3851796 : CollatzResearch.WordTrace tailWord_3851796 prefixEnd_3851796 1977822731065517064135919 := by
  unfold tailWord_3851796
  simp only [CollatzResearch.WordTrace]
  refine ⟨70243270776804200614519621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93657694369072267486026161 70243270776804200614519621)
  ·
    refine ⟨13170613270650787615222429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70243270776804200614519621 13170613270650787615222429)
    ·
      refine ⟨4938979976494045355708411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13170613270650787615222429 4938979976494045355708411)
      ·
        refine ⟨7408469964741068033562617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4938979976494045355708411 7408469964741068033562617)
        ·
          refine ⟨5556352473555801025171963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7408469964741068033562617 5556352473555801025171963)
          ·
            refine ⟨8334528710333701537757945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5556352473555801025171963 8334528710333701537757945)
            ·
              refine ⟨6250896532750276153318459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8334528710333701537757945 6250896532750276153318459)
              ·
                refine ⟨9376344799125414229977689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6250896532750276153318459 9376344799125414229977689)
                ·
                  refine ⟨7032258599344060672483267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9376344799125414229977689 7032258599344060672483267)
                  ·
                    refine ⟨10548387899016091008724901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7032258599344060672483267 10548387899016091008724901)
                    ·
                      refine ⟨1977822731065517064135919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10548387899016091008724901 1977822731065517064135919)
                      ·
                        rfl

theorem cell23_3851796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_3851796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851796 prefixEnd_3851796 := by exact prefixLift 3851796
  have htrace : WordTrace (prefixWord ++ tailWord_3851796) baseStart_3851796 baseEnd_3851796 := by
    simpa [prefixWord, tailWord_3851796, baseEnd_3851796] using wordTrace_append hprefix tailTrace_3851796
  have hstable : (prefixWord ++ tailWord_3851796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851796).length < 2 ^ (prefixWord ++ tailWord_3851796).sum := by decide
  have hdescent : baseEnd_3851796 < baseStart_3851796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851852 : List Nat := [2, 2, 1, 3, 1, 3, 2, 1, 3, 1, 4]
def baseStart_3851852 : Nat := 118140960795 + 3851852 * 2 ^ 59
def prefixEnd_3851852 : Nat := 4983230072969 + 3 ^ 40 * 3851852 * 2
def baseEnd_3851852 : Nat := 1977851485982168845035661

theorem tailTrace_3851852 : CollatzResearch.WordTrace tailWord_3851852 prefixEnd_3851852 1977851485982168845035661 := by
  unfold tailWord_3851852
  simp only [CollatzResearch.WordTrace]
  refine ⟨70244292020702761396538905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93659056027603681862051873 70244292020702761396538905)
  ·
    refine ⟨52683219015527071047404179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70244292020702761396538905 52683219015527071047404179)
    ·
      refine ⟨79024828523290606571106269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52683219015527071047404179 79024828523290606571106269)
      ·
        refine ⟨29634310696233977464164851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79024828523290606571106269 29634310696233977464164851)
        ·
          refine ⟨44451466044350966196247277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29634310696233977464164851 44451466044350966196247277)
          ·
            refine ⟨16669299766631612323592729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44451466044350966196247277 16669299766631612323592729)
            ·
              refine ⟨12501974824973709242694547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16669299766631612323592729 12501974824973709242694547)
              ·
                refine ⟨18752962237460563864041821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12501974824973709242694547 18752962237460563864041821)
                ·
                  refine ⟨7032360839047711449015683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18752962237460563864041821 7032360839047711449015683)
                  ·
                    refine ⟨10548541258571567173523525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7032360839047711449015683 10548541258571567173523525)
                    ·
                      refine ⟨1977851485982168845035661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10548541258571567173523525 1977851485982168845035661)
                      ·
                        rfl

theorem cell23_3851852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_3851852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851852 prefixEnd_3851852 := by exact prefixLift 3851852
  have htrace : WordTrace (prefixWord ++ tailWord_3851852) baseStart_3851852 baseEnd_3851852 := by
    simpa [prefixWord, tailWord_3851852, baseEnd_3851852] using wordTrace_append hprefix tailTrace_3851852
  have hstable : (prefixWord ++ tailWord_3851852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851852).length < 2 ^ (prefixWord ++ tailWord_3851852).sum := by decide
  have hdescent : baseEnd_3851852 < baseStart_3851852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851875 : List Nat := [1, 1, 1, 5, 1, 4, 10]
def baseStart_3851875 : Nat := 118140960795 + 3851875 * 2 ^ 59
def prefixEnd_3851875 : Nat := 4983230072969 + 3 ^ 40 * 3851875 * 2
def baseEnd_3851875 : Nat := 24418065383175583395655

theorem tailTrace_3851875 : CollatzResearch.WordTrace tailWord_3851875 prefixEnd_3851875 24418065383175583395655 := by
  unfold tailWord_3851875
  simp only [CollatzResearch.WordTrace]
  refine ⟨140489422920322197721165079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93659615280214798480776719 140489422920322197721165079)
  ·
    refine ⟨210734134380483296581747619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140489422920322197721165079 210734134380483296581747619)
    ·
      refine ⟨316101201570724944872621429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210734134380483296581747619 316101201570724944872621429)
      ·
        refine ⟨29634487647255463581808259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 316101201570724944872621429 29634487647255463581808259)
        ·
          refine ⟨44451731470883195372712389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29634487647255463581808259 44451731470883195372712389)
          ·
            refine ⟨8334699650790599132383573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44451731470883195372712389 8334699650790599132383573)
            ·
              refine ⟨24418065383175583395655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8334699650790599132383573 24418065383175583395655)
              ·
                rfl

theorem cell23_3851875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 10].length) (baseStart_3851875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851875 prefixEnd_3851875 := by exact prefixLift 3851875
  have htrace : WordTrace (prefixWord ++ tailWord_3851875) baseStart_3851875 baseEnd_3851875 := by
    simpa [prefixWord, tailWord_3851875, baseEnd_3851875] using wordTrace_append hprefix tailTrace_3851875
  have hstable : (prefixWord ++ tailWord_3851875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851875).length < 2 ^ (prefixWord ++ tailWord_3851875).sum := by decide
  have hdescent : baseEnd_3851875 < baseStart_3851875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851879 : List Nat := [1, 1, 5, 1, 1, 1, 5, 2, 2, 4]
def baseStart_3851879 : Nat := 118140960795 + 3851879 * 2 ^ 59
def prefixEnd_3851879 : Nat := 4983230072969 + 3 ^ 40 * 3851879 * 2
def baseEnd_3851879 : Nat := 659288449986613413132679

theorem tailTrace_3851879 : CollatzResearch.WordTrace tailWord_3851879 prefixEnd_3851879 659288449986613413132679 := by
  unfold tailWord_3851879
  simp only [CollatzResearch.WordTrace]
  refine ⟨140489568812307706404310691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93659712541538470936207127 140489568812307706404310691)
  ·
    refine ⟨210734353218461559606466037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140489568812307706404310691 210734353218461559606466037)
    ·
      refine ⟨19756345614230771213106191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 210734353218461559606466037 19756345614230771213106191)
      ·
        refine ⟨29634518421346156819659287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19756345614230771213106191 29634518421346156819659287)
        ·
          refine ⟨44451777632019235229488931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29634518421346156819659287 44451777632019235229488931)
          ·
            refine ⟨66677666448028852844233397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44451777632019235229488931 66677666448028852844233397)
            ·
              refine ⟨6251031229502704954146881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66677666448028852844233397 6251031229502704954146881)
              ·
                refine ⟨4688273422127028715610161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6251031229502704954146881 4688273422127028715610161)
                ·
                  refine ⟨3516205066595271536707621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4688273422127028715610161 3516205066595271536707621)
                  ·
                    refine ⟨659288449986613413132679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3516205066595271536707621 659288449986613413132679)
                    ·
                      rfl

theorem cell23_3851879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_3851879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851879 prefixEnd_3851879 := by exact prefixLift 3851879
  have htrace : WordTrace (prefixWord ++ tailWord_3851879) baseStart_3851879 baseEnd_3851879 := by
    simpa [prefixWord, tailWord_3851879, baseEnd_3851879] using wordTrace_append hprefix tailTrace_3851879
  have hstable : (prefixWord ++ tailWord_3851879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851879).length < 2 ^ (prefixWord ++ tailWord_3851879).sum := by decide
  have hdescent : baseEnd_3851879 < baseStart_3851879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851915 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 5]
def baseStart_3851915 : Nat := 118140960795 + 3851915 * 2 ^ 59
def prefixEnd_3851915 : Nat := 4983230072969 + 3 ^ 40 * 3851915 * 2
def baseEnd_3851915 : Nat := 1977883835263402098547871

theorem tailTrace_3851915 : CollatzResearch.WordTrace tailWord_3851915 prefixEnd_3851915 1977883835263402098547871 := by
  unfold tailWord_3851915
  simp only [CollatzResearch.WordTrace]
  refine ⟨140490881840177284552621199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93660587893451523035080799 140490881840177284552621199)
  ·
    refine ⟨210736322760265926828931799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140490881840177284552621199 210736322760265926828931799)
    ·
      refine ⟨316104484140398890243397699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210736322760265926828931799 316104484140398890243397699)
      ·
        refine ⟨474156726210598335365096549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316104484140398890243397699 474156726210598335365096549)
        ·
          refine ⟨88904386164487187880955603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 474156726210598335365096549 88904386164487187880955603)
          ·
            refine ⟨133356579246730781821433405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88904386164487187880955603 133356579246730781821433405)
            ·
              refine ⟨50008717217524043183037527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133356579246730781821433405 50008717217524043183037527)
              ·
                refine ⟨75013075826286064774556291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50008717217524043183037527 75013075826286064774556291)
                ·
                  refine ⟨112519613739429097161834437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75013075826286064774556291 112519613739429097161834437)
                  ·
                    refine ⟨21097427576142955717843957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112519613739429097161834437 21097427576142955717843957)
                    ·
                      refine ⟨1977883835263402098547871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21097427576142955717843957 1977883835263402098547871)
                      ·
                        rfl

theorem cell23_3851915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 5].length) (baseStart_3851915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851915 prefixEnd_3851915 := by exact prefixLift 3851915
  have htrace : WordTrace (prefixWord ++ tailWord_3851915) baseStart_3851915 baseEnd_3851915 := by
    simpa [prefixWord, tailWord_3851915, baseEnd_3851915] using wordTrace_append hprefix tailTrace_3851915
  have hstable : (prefixWord ++ tailWord_3851915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851915).length < 2 ^ (prefixWord ++ tailWord_3851915).sum := by decide
  have hdescent : baseEnd_3851915 < baseStart_3851915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851925 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 1, 2, 8]
def baseStart_3851925 : Nat := 118140960795 + 3851925 * 2 ^ 59
def prefixEnd_3851925 : Nat := 4983230072969 + 3 ^ 40 * 3851925 * 2
def baseEnd_3851925 : Nat := 1977888970069947059422825

theorem tailTrace_3851925 : CollatzResearch.WordTrace tailWord_3851925 prefixEnd_3851925 1977888970069947059422825 := by
  unfold tailWord_3851925
  simp only [CollatzResearch.WordTrace]
  refine ⟨140491246570141056260485229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93660831046760704173656819 140491246570141056260485229)
  ·
    refine ⟨52684217463802896097681961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140491246570141056260485229 52684217463802896097681961)
    ·
      refine ⟨39513163097852172073261471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52684217463802896097681961 39513163097852172073261471)
      ·
        refine ⟨59269744646778258109892207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39513163097852172073261471 59269744646778258109892207)
        ·
          refine ⟨88904616970167387164838311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59269744646778258109892207 88904616970167387164838311)
          ·
            refine ⟨133356925455251080747257467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88904616970167387164838311 133356925455251080747257467)
            ·
              refine ⟨200035388182876621120886201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133356925455251080747257467 200035388182876621120886201)
              ·
                refine ⟨150026541137157465840664651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200035388182876621120886201 150026541137157465840664651)
                ·
                  refine ⟨225039811705736198760996977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150026541137157465840664651 225039811705736198760996977)
                  ·
                    refine ⟨168779858779302149070747733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 225039811705736198760996977 168779858779302149070747733)
                    ·
                      refine ⟨1977888970069947059422825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 168779858779302149070747733 1977888970069947059422825)
                      ·
                        rfl

theorem cell23_3851925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_3851925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851925 prefixEnd_3851925 := by exact prefixLift 3851925
  have htrace : WordTrace (prefixWord ++ tailWord_3851925) baseStart_3851925 baseEnd_3851925 := by
    simpa [prefixWord, tailWord_3851925, baseEnd_3851925] using wordTrace_append hprefix tailTrace_3851925
  have hstable : (prefixWord ++ tailWord_3851925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851925).length < 2 ^ (prefixWord ++ tailWord_3851925).sum := by decide
  have hdescent : baseEnd_3851925 < baseStart_3851925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851962 : List Nat := [3, 1, 1, 1, 2, 4, 1, 2, 2, 1, 5]
def baseStart_3851962 : Nat := 118140960795 + 3851962 * 2 ^ 59
def prefixEnd_3851962 : Nat := 4983230072969 + 3 ^ 40 * 3851962 * 2
def baseEnd_3851962 : Nat := 1977907968854163414660155

theorem tailTrace_3851962 : CollatzResearch.WordTrace tailWord_3851962 prefixEnd_3851962 1977907968854163414660155 := by
  unfold tailWord_3851962
  simp only [CollatzResearch.WordTrace]
  refine ⟨35123149017751752894895535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93661730714004674386388093 35123149017751752894895535)
  ·
    refine ⟨52684723526627629342343303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35123149017751752894895535 52684723526627629342343303)
    ·
      refine ⟨79027085289941444013514955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52684723526627629342343303 79027085289941444013514955)
      ·
        refine ⟨118540627934912166020272433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79027085289941444013514955 118540627934912166020272433)
        ·
          refine ⟨88905470951184124515204325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118540627934912166020272433 88905470951184124515204325)
          ·
            refine ⟨16669775803347023346600811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88905470951184124515204325 16669775803347023346600811)
            ·
              refine ⟨25004663705020535019901217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16669775803347023346600811 25004663705020535019901217)
              ·
                refine ⟨18753497778765401264925913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25004663705020535019901217 18753497778765401264925913)
                ·
                  refine ⟨14065123334074050948694435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18753497778765401264925913 14065123334074050948694435)
                  ·
                    refine ⟨21097685001111076423041653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14065123334074050948694435 21097685001111076423041653)
                    ·
                      refine ⟨1977907968854163414660155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21097685001111076423041653 1977907968854163414660155)
                      ·
                        rfl

theorem cell23_3851962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_3851962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851962 prefixEnd_3851962 := by exact prefixLift 3851962
  have htrace : WordTrace (prefixWord ++ tailWord_3851962) baseStart_3851962 baseEnd_3851962 := by
    simpa [prefixWord, tailWord_3851962, baseEnd_3851962] using wordTrace_append hprefix tailTrace_3851962
  have hstable : (prefixWord ++ tailWord_3851962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851962).length < 2 ^ (prefixWord ++ tailWord_3851962).sum := by decide
  have hdescent : baseEnd_3851962 < baseStart_3851962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851970 : List Nat := [3, 5, 1, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_3851970 : Nat := 118140960795 + 3851970 * 2 ^ 59
def prefixEnd_3851970 : Nat := 4983230072969 + 3 ^ 40 * 3851970 * 2
def baseEnd_3851970 : Nat := 1977912076699399383360119

theorem tailTrace_3851970 : CollatzResearch.WordTrace tailWord_3851970 prefixEnd_3851970 1977912076699399383360119 := by
  unfold tailWord_3851970
  simp only [CollatzResearch.WordTrace]
  refine ⟨35123221963744507236468341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93661925236652019297248909 35123221963744507236468341)
  ·
    refine ⟨3292802059101047553418907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35123221963744507236468341 3292802059101047553418907)
    ·
      refine ⟨4939203088651571330128361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3292802059101047553418907 4939203088651571330128361)
      ·
        refine ⟨3704402316488678497596271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4939203088651571330128361 3704402316488678497596271)
        ·
          refine ⟨5556603474733017746394407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3704402316488678497596271 5556603474733017746394407)
          ·
            refine ⟨8334905212099526619591611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5556603474733017746394407 8334905212099526619591611)
            ·
              refine ⟨12502357818149289929387417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8334905212099526619591611 12502357818149289929387417)
              ·
                refine ⟨9376768363611967447040563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12502357818149289929387417 9376768363611967447040563)
                ·
                  refine ⟨14065152545417951170560845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9376768363611967447040563 14065152545417951170560845)
                  ·
                    refine ⟨5274432204531731688960317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14065152545417951170560845 5274432204531731688960317)
                    ·
                      refine ⟨1977912076699399383360119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5274432204531731688960317 1977912076699399383360119)
                      ·
                        rfl

theorem cell23_3851970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_3851970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851970 prefixEnd_3851970 := by exact prefixLift 3851970
  have htrace : WordTrace (prefixWord ++ tailWord_3851970) baseStart_3851970 baseEnd_3851970 := by
    simpa [prefixWord, tailWord_3851970, baseEnd_3851970] using wordTrace_append hprefix tailTrace_3851970
  have hstable : (prefixWord ++ tailWord_3851970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851970).length < 2 ^ (prefixWord ++ tailWord_3851970).sum := by decide
  have hdescent : baseEnd_3851970 < baseStart_3851970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851980 : List Nat := [2, 2, 1, 5, 2, 1, 3, 1, 1, 3, 2]
def baseStart_3851980 : Nat := 118140960795 + 3851980 * 2 ^ 59
def prefixEnd_3851980 : Nat := 4983230072969 + 3 ^ 40 * 3851980 * 2
def baseEnd_3851980 : Nat := 1977917211505944344235073

theorem tailTrace_3851980 : CollatzResearch.WordTrace tailWord_3851980 prefixEnd_3851980 1977917211505944344235073 := by
  unfold tailWord_3851980
  simp only [CollatzResearch.WordTrace]
  refine ⟨70246626292470900326868697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93662168389961200435824929 70246626292470900326868697)
  ·
    refine ⟨52684969719353175245151523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70246626292470900326868697 52684969719353175245151523)
    ·
      refine ⟨79027454579029762867727285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52684969719353175245151523 79027454579029762867727285)
      ·
        refine ⟨7408823866784040268849433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79027454579029762867727285 7408823866784040268849433)
        ·
          refine ⟨5556617900088030201637075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7408823866784040268849433 5556617900088030201637075)
          ·
            refine ⟨8334926850132045302455613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5556617900088030201637075 8334926850132045302455613)
            ·
              refine ⟨3125597568799516988420855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8334926850132045302455613 3125597568799516988420855)
              ·
                refine ⟨4688396353199275482631283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3125597568799516988420855 4688396353199275482631283)
                ·
                  refine ⟨7032594529798913223946925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4688396353199275482631283 7032594529798913223946925)
                  ·
                    refine ⟨2637222948674592458980097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7032594529798913223946925 2637222948674592458980097)
                    ·
                      refine ⟨1977917211505944344235073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2637222948674592458980097 1977917211505944344235073)
                      ·
                        rfl

theorem cell23_3851980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_3851980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851980 prefixEnd_3851980 := by exact prefixLift 3851980
  have htrace : WordTrace (prefixWord ++ tailWord_3851980) baseStart_3851980 baseEnd_3851980 := by
    simpa [prefixWord, tailWord_3851980, baseEnd_3851980] using wordTrace_append hprefix tailTrace_3851980
  have hstable : (prefixWord ++ tailWord_3851980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851980).length < 2 ^ (prefixWord ++ tailWord_3851980).sum := by decide
  have hdescent : baseEnd_3851980 < baseStart_3851980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851993 : List Nat := [1, 2, 1, 2, 3, 4, 2, 2, 2, 2, 2]
def baseStart_3851993 : Nat := 118140960795 + 3851993 * 2 ^ 59
def prefixEnd_3851993 : Nat := 4983230072969 + 3 ^ 40 * 3851993 * 2
def baseEnd_3851993 : Nat := 1977923886754452793372513

theorem tailTrace_3851993 : CollatzResearch.WordTrace tailWord_3851993 prefixEnd_3851993 1977923886754452793372513 := by
  unfold tailWord_3851993
  simp only [CollatzResearch.WordTrace]
  refine ⟨140493726733894703873960633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93662484489263135915973755 140493726733894703873960633)
  ·
    refine ⟨105370295050421027905470475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140493726733894703873960633 105370295050421027905470475)
    ·
      refine ⟨158055442575631541858205713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105370295050421027905470475 158055442575631541858205713)
      ·
        refine ⟨118541581931723656393654285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158055442575631541858205713 118541581931723656393654285)
        ·
          refine ⟨44453093224396371147620357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118541581931723656393654285 44453093224396371147620357)
          ·
            refine ⟨8334954979574319590178817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44453093224396371147620357 8334954979574319590178817)
            ·
              refine ⟨6251216234680739692634113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8334954979574319590178817 6251216234680739692634113)
              ·
                refine ⟨4688412176010554769475585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6251216234680739692634113 4688412176010554769475585)
                ·
                  refine ⟨3516309132007916077106689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4688412176010554769475585 3516309132007916077106689)
                  ·
                    refine ⟨2637231849005937057830017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3516309132007916077106689 2637231849005937057830017)
                    ·
                      refine ⟨1977923886754452793372513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2637231849005937057830017 1977923886754452793372513)
                      ·
                        rfl

theorem cell23_3851993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 2, 2, 2].length) (baseStart_3851993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851993 prefixEnd_3851993 := by exact prefixLift 3851993
  have htrace : WordTrace (prefixWord ++ tailWord_3851993) baseStart_3851993 baseEnd_3851993 := by
    simpa [prefixWord, tailWord_3851993, baseEnd_3851993] using wordTrace_append hprefix tailTrace_3851993
  have hstable : (prefixWord ++ tailWord_3851993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851993).length < 2 ^ (prefixWord ++ tailWord_3851993).sum := by decide
  have hdescent : baseEnd_3851993 < baseStart_3851993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851999 : List Nat := [1, 1, 2, 3, 2, 2, 3, 4, 5]
def baseStart_3851999 : Nat := 118140960795 + 3851999 * 2 ^ 59
def prefixEnd_3851999 : Nat := 4983230072969 + 3 ^ 40 * 3851999 * 2
def baseEnd_3851999 : Nat := 219769663070931085544165

theorem tailTrace_3851999 : CollatzResearch.WordTrace tailWord_3851999 prefixEnd_3851999 219769663070931085544165 := by
  unfold tailWord_3851999
  simp only [CollatzResearch.WordTrace]
  refine ⟨140493945571872966898679051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93662630381248644599119367 140493945571872966898679051)
  ·
    refine ⟨210740918357809450348018577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140493945571872966898679051 210740918357809450348018577)
    ·
      refine ⟨158055688768357087761013933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210740918357809450348018577 158055688768357087761013933)
      ·
        refine ⟨59270883288133907910380225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158055688768357087761013933 59270883288133907910380225)
        ·
          refine ⟨44453162466100430932785169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59270883288133907910380225 44453162466100430932785169)
          ·
            refine ⟨33339871849575323199588877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44453162466100430932785169 33339871849575323199588877)
            ·
              refine ⟨12502451943590746199845829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33339871849575323199588877 12502451943590746199845829)
              ·
                refine ⟨2344209739423264912471093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12502451943590746199845829 2344209739423264912471093)
                ·
                  refine ⟨219769663070931085544165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2344209739423264912471093 219769663070931085544165)
                  ·
                    rfl

theorem cell23_3851999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 4, 5].length) (baseStart_3851999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3851999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3851999 prefixEnd_3851999 := by exact prefixLift 3851999
  have htrace : WordTrace (prefixWord ++ tailWord_3851999) baseStart_3851999 baseEnd_3851999 := by
    simpa [prefixWord, tailWord_3851999, baseEnd_3851999] using wordTrace_append hprefix tailTrace_3851999
  have hstable : (prefixWord ++ tailWord_3851999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851999).length < 2 ^ (prefixWord ++ tailWord_3851999).sum := by decide
  have hdescent : baseEnd_3851999 < baseStart_3851999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852012 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 4, 5]
def baseStart_3852012 : Nat := 118140960795 + 3852012 * 2 ^ 59
def prefixEnd_3852012 : Nat := 4983230072969 + 3 ^ 40 * 3852012 * 2
def baseEnd_3852012 : Nat := 659311214295629406344975

theorem tailTrace_3852012 : CollatzResearch.WordTrace tailWord_3852012 prefixEnd_3852012 659311214295629406344975 := by
  unfold tailWord_3852012
  simp only [CollatzResearch.WordTrace]
  refine ⟨70247209860412935059451145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93662946480550580079268193 70247209860412935059451145)
  ·
    refine ⟨52685407395309701294588359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70247209860412935059451145 52685407395309701294588359)
    ·
      refine ⟨79028111092964551941882539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52685407395309701294588359 79028111092964551941882539)
      ·
        refine ⟨118542166639446827912823809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79028111092964551941882539 118542166639446827912823809)
        ·
          refine ⟨88906624979585120934617857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118542166639446827912823809 88906624979585120934617857)
          ·
            refine ⟨66679968734688840700963393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88906624979585120934617857 66679968734688840700963393)
            ·
              refine ⟨50009976551016630525722545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66679968734688840700963393 50009976551016630525722545)
              ·
                refine ⟨37507482413262472894291909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50009976551016630525722545 37507482413262472894291909)
                ·
                  refine ⟨7032652952486713667679733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37507482413262472894291909 7032652952486713667679733)
                  ·
                    refine ⟨659311214295629406344975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7032652952486713667679733 659311214295629406344975)
                    ·
                      rfl

theorem cell23_3852012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 5].length) (baseStart_3852012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852012 prefixEnd_3852012 := by exact prefixLift 3852012
  have htrace : WordTrace (prefixWord ++ tailWord_3852012) baseStart_3852012 baseEnd_3852012 := by
    simpa [prefixWord, tailWord_3852012, baseEnd_3852012] using wordTrace_append hprefix tailTrace_3852012
  have hstable : (prefixWord ++ tailWord_3852012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852012).length < 2 ^ (prefixWord ++ tailWord_3852012).sum := by decide
  have hdescent : baseEnd_3852012 < baseStart_3852012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852032 : List Nat := [2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 4]
def baseStart_3852032 : Nat := 118140960795 + 3852032 * 2 ^ 59
def prefixEnd_3852032 : Nat := 4983230072969 + 3 ^ 40 * 3852032 * 2
def baseEnd_3852032 : Nat := 1977943912499978140784833

theorem tailTrace_3852032 : CollatzResearch.WordTrace tailWord_3852032 prefixEnd_3852032 1977943912499978140784833 := by
  unfold tailWord_3852032
  simp only [CollatzResearch.WordTrace]
  refine ⟨70247574590376706767315175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93663432787168942356420233 70247574590376706767315175)
  ·
    refine ⟨105371361885565060150972763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70247574590376706767315175 105371361885565060150972763)
    ·
      refine ⟨158057042828347590226459145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105371361885565060150972763 158057042828347590226459145)
      ·
        refine ⟨118542782121260692669844359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158057042828347590226459145 118542782121260692669844359)
        ·
          refine ⟨177814173181891039004766539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118542782121260692669844359 177814173181891039004766539)
          ·
            refine ⟨266721259772836558507149809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177814173181891039004766539 266721259772836558507149809)
            ·
              refine ⟨200040944829627418880362357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266721259772836558507149809 200040944829627418880362357)
              ·
                refine ⟨18753838577777570520033971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 200040944829627418880362357 18753838577777570520033971)
                ·
                  refine ⟨28130757866666355780050957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18753838577777570520033971 28130757866666355780050957)
                  ·
                    refine ⟨10549034199999883417519109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28130757866666355780050957 10549034199999883417519109)
                    ·
                      refine ⟨1977943912499978140784833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10549034199999883417519109 1977943912499978140784833)
                      ·
                        rfl

theorem cell23_3852032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_3852032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852032 prefixEnd_3852032 := by exact prefixLift 3852032
  have htrace : WordTrace (prefixWord ++ tailWord_3852032) baseStart_3852032 baseEnd_3852032 := by
    simpa [prefixWord, tailWord_3852032, baseEnd_3852032] using wordTrace_append hprefix tailTrace_3852032
  have hstable : (prefixWord ++ tailWord_3852032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852032).length < 2 ^ (prefixWord ++ tailWord_3852032).sum := by decide
  have hdescent : baseEnd_3852032 < baseStart_3852032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852038 : List Nat := [6, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3]
def baseStart_3852038 : Nat := 118140960795 + 3852038 * 2 ^ 59
def prefixEnd_3852038 : Nat := 4983230072969 + 3 ^ 40 * 3852038 * 2
def baseEnd_3852038 : Nat := 1977946993383905117309807

theorem tailTrace_3852038 : CollatzResearch.WordTrace tailWord_3852038 prefixEnd_3852038 1977946993383905117309807 := by
  unfold tailWord_3852038
  simp only [CollatzResearch.WordTrace]
  refine ⟨4390480250585364892479649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 93663578679154451039565845 4390480250585364892479649)
  ·
    refine ⟨3292860187939023669359737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4390480250585364892479649 3292860187939023669359737)
    ·
      refine ⟨2469645140954267752019803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3292860187939023669359737 2469645140954267752019803)
      ·
        refine ⟨3704467711431401628029705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2469645140954267752019803 3704467711431401628029705)
        ·
          refine ⟨2778350783573551221022279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3704467711431401628029705 2778350783573551221022279)
          ·
            refine ⟨4167526175360326831533419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2778350783573551221022279 4167526175360326831533419)
            ·
              refine ⟨6251289263040490247300129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4167526175360326831533419 6251289263040490247300129)
              ·
                refine ⟨4688466947280367685475097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6251289263040490247300129 4688466947280367685475097)
                ·
                  refine ⟨3516350210460275764106323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4688466947280367685475097 3516350210460275764106323)
                  ·
                    refine ⟨5274525315690413646159485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3516350210460275764106323 5274525315690413646159485)
                    ·
                      refine ⟨1977946993383905117309807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5274525315690413646159485 1977946993383905117309807)
                      ·
                        rfl

theorem cell23_3852038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_3852038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852038 prefixEnd_3852038 := by exact prefixLift 3852038
  have htrace : WordTrace (prefixWord ++ tailWord_3852038) baseStart_3852038 baseEnd_3852038 := by
    simpa [prefixWord, tailWord_3852038, baseEnd_3852038] using wordTrace_append hprefix tailTrace_3852038
  have hstable : (prefixWord ++ tailWord_3852038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852038).length < 2 ^ (prefixWord ++ tailWord_3852038).sum := by decide
  have hdescent : baseEnd_3852038 < baseStart_3852038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852066 : List Nat := [3, 3, 1, 1, 2, 1, 1, 3, 2, 4, 2]
def baseStart_3852066 : Nat := 118140960795 + 3852066 * 2 ^ 59
def prefixEnd_3852066 : Nat := 4983230072969 + 3 ^ 40 * 3852066 * 2
def baseEnd_3852066 : Nat := 1977961370842231007759677

theorem tailTrace_3852066 : CollatzResearch.WordTrace tailWord_3852066 prefixEnd_3852066 1977961370842231007759677 := by
  unfold tailWord_3852066
  simp only [CollatzResearch.WordTrace]
  refine ⟨35124097315657559335342013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93664259508420158227578701 35124097315657559335342013)
  ·
    refine ⟨13171536493371584750753255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35124097315657559335342013 13171536493371584750753255)
    ·
      refine ⟨19757304740057377126129883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13171536493371584750753255 19757304740057377126129883)
      ·
        refine ⟨29635957110086065689194825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19757304740057377126129883 29635957110086065689194825)
        ·
          refine ⟨22226967832564549266896119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29635957110086065689194825 22226967832564549266896119)
          ·
            refine ⟨33340451748846823900344179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22226967832564549266896119 33340451748846823900344179)
            ·
              refine ⟨50010677623270235850516269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33340451748846823900344179 50010677623270235850516269)
              ·
                refine ⟨18754004108726338443943601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50010677623270235850516269 18754004108726338443943601)
                ·
                  refine ⟨14065503081544753832957701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18754004108726338443943601 14065503081544753832957701)
                  ·
                    refine ⟨2637281827789641343679569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14065503081544753832957701 2637281827789641343679569)
                    ·
                      refine ⟨1977961370842231007759677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2637281827789641343679569 1977961370842231007759677)
                      ·
                        rfl

theorem cell23_3852066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_3852066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852066 prefixEnd_3852066 := by exact prefixLift 3852066
  have htrace : WordTrace (prefixWord ++ tailWord_3852066) baseStart_3852066 baseEnd_3852066 := by
    simpa [prefixWord, tailWord_3852066, baseEnd_3852066] using wordTrace_append hprefix tailTrace_3852066
  have hstable : (prefixWord ++ tailWord_3852066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852066).length < 2 ^ (prefixWord ++ tailWord_3852066).sum := by decide
  have hdescent : baseEnd_3852066 < baseStart_3852066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852069 : List Nat := [1, 3, 1, 2, 3, 2, 1, 2, 1, 4, 3]
def baseStart_3852069 : Nat := 118140960795 + 3852069 * 2 ^ 59
def prefixEnd_3852069 : Nat := 4983230072969 + 3 ^ 40 * 3852069 * 2
def baseEnd_3852069 : Nat := 1977962911284194496022163

theorem tailTrace_3852069 : CollatzResearch.WordTrace tailWord_3852069 prefixEnd_3852069 1977962911284194496022163 := by
  unfold tailWord_3852069
  simp only [CollatzResearch.WordTrace]
  refine ⟨140496498681619368853727261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93664332454412912569151507 140496498681619368853727261)
  ·
    refine ⟨52686187005607263320147723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140496498681619368853727261 52686187005607263320147723)
    ·
      refine ⟨79029280508410894980221585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52686187005607263320147723 79029280508410894980221585)
      ·
        refine ⟨59271960381308171235166189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79029280508410894980221585 59271960381308171235166189)
        ·
          refine ⟨22226985142990564213187321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59271960381308171235166189 22226985142990564213187321)
          ·
            refine ⟨16670238857242923159890491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22226985142990564213187321 16670238857242923159890491)
            ·
              refine ⟨25005358285864384739835737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16670238857242923159890491 25005358285864384739835737)
              ·
                refine ⟨18754018714398288554876803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25005358285864384739835737 18754018714398288554876803)
                ·
                  refine ⟨28131028071597432832315205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18754018714398288554876803 28131028071597432832315205)
                  ·
                    refine ⟨5274567763424518656059101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28131028071597432832315205 5274567763424518656059101)
                    ·
                      refine ⟨1977962911284194496022163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5274567763424518656059101 1977962911284194496022163)
                      ·
                        rfl

theorem cell23_3852069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_3852069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852069 prefixEnd_3852069 := by exact prefixLift 3852069
  have htrace : WordTrace (prefixWord ++ tailWord_3852069) baseStart_3852069 baseEnd_3852069 := by
    simpa [prefixWord, tailWord_3852069, baseEnd_3852069] using wordTrace_append hprefix tailTrace_3852069
  have hstable : (prefixWord ++ tailWord_3852069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852069).length < 2 ^ (prefixWord ++ tailWord_3852069).sum := by decide
  have hdescent : baseEnd_3852069 < baseStart_3852069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852112 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 7]
def baseStart_3852112 : Nat := 118140960795 + 3852112 * 2 ^ 59
def prefixEnd_3852112 : Nat := 4983230072969 + 3 ^ 40 * 3852112 * 2
def baseEnd_3852112 : Nat := 1977984990952337827784465

theorem tailTrace_3852112 : CollatzResearch.WordTrace tailWord_3852112 prefixEnd_3852112 1977984990952337827784465 := by
  unfold tailWord_3852112
  simp only [CollatzResearch.WordTrace]
  refine ⟨70249033510231793598771295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93665378013642391465028393 70249033510231793598771295)
  ·
    refine ⟨105373550265347690398156943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70249033510231793598771295 105373550265347690398156943)
    ·
      refine ⟨158060325398021535597235415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105373550265347690398156943 158060325398021535597235415)
      ·
        refine ⟨237090488097032303395853123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158060325398021535597235415 237090488097032303395853123)
        ·
          refine ⟨355635732145548455093779685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237090488097032303395853123 355635732145548455093779685)
          ·
            refine ⟨66681699777290335330083691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 355635732145548455093779685 66681699777290335330083691)
            ·
              refine ⟨100022549665935502995125537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66681699777290335330083691 100022549665935502995125537)
              ·
                refine ⟨75016912249451627246344153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100022549665935502995125537 75016912249451627246344153)
                ·
                  refine ⟨56262684187088720434758115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75016912249451627246344153 56262684187088720434758115)
                  ·
                    refine ⟨84394026280633080652137173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56262684187088720434758115 84394026280633080652137173)
                    ·
                      refine ⟨1977984990952337827784465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84394026280633080652137173 1977984990952337827784465)
                      ·
                        rfl

theorem cell23_3852112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 7].length) (baseStart_3852112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852112 prefixEnd_3852112 := by exact prefixLift 3852112
  have htrace : WordTrace (prefixWord ++ tailWord_3852112) baseStart_3852112 baseEnd_3852112 := by
    simpa [prefixWord, tailWord_3852112, baseEnd_3852112] using wordTrace_append hprefix tailTrace_3852112
  have hstable : (prefixWord ++ tailWord_3852112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852112).length < 2 ^ (prefixWord ++ tailWord_3852112).sum := by decide
  have hdescent : baseEnd_3852112 < baseStart_3852112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852169 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 3, 2, 4]
def baseStart_3852169 : Nat := 118140960795 + 3852169 * 2 ^ 59
def prefixEnd_3852169 : Nat := 4983230072969 + 3 ^ 40 * 3852169 * 2
def baseEnd_3852169 : Nat := 1978014259349644104771703

theorem tailTrace_3852169 : CollatzResearch.WordTrace tailWord_3852169 prefixEnd_3852169 1978014259349644104771703 := by
  unfold tailWord_3852169
  simp only [CollatzResearch.WordTrace]
  refine ⟨140500145981257085932367561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93666763987504723954911707 140500145981257085932367561)
  ·
    refine ⟨105375109485942814449275671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140500145981257085932367561 105375109485942814449275671)
    ·
      refine ⟨158062664228914221673913507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105375109485942814449275671 158062664228914221673913507)
      ·
        refine ⟨237093996343371332510870261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158062664228914221673913507 237093996343371332510870261)
        ·
          refine ⟨22227562157191062422894087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 237093996343371332510870261 22227562157191062422894087)
          ·
            refine ⟨33341343235786593634341131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22227562157191062422894087 33341343235786593634341131)
            ·
              refine ⟨50012014853679890451511697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33341343235786593634341131 50012014853679890451511697)
              ·
                refine ⟨37509011140259917838633773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50012014853679890451511697 37509011140259917838633773)
                ·
                  refine ⟨14065879177597469189487665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37509011140259917838633773 14065879177597469189487665)
                  ·
                    refine ⟨10549409383198101892115749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14065879177597469189487665 10549409383198101892115749)
                    ·
                      refine ⟨1978014259349644104771703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10549409383198101892115749 1978014259349644104771703)
                      ·
                        rfl

theorem cell23_3852169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 2, 4].length) (baseStart_3852169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852169 prefixEnd_3852169 := by exact prefixLift 3852169
  have htrace : WordTrace (prefixWord ++ tailWord_3852169) baseStart_3852169 baseEnd_3852169 := by
    simpa [prefixWord, tailWord_3852169, baseEnd_3852169] using wordTrace_append hprefix tailTrace_3852169
  have hstable : (prefixWord ++ tailWord_3852169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852169).length < 2 ^ (prefixWord ++ tailWord_3852169).sum := by decide
  have hdescent : baseEnd_3852169 < baseStart_3852169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852186 : List Nat := [3, 1, 1, 4, 2, 1, 1, 3, 1, 2, 4]
def baseStart_3852186 : Nat := 118140960795 + 3852186 * 2 ^ 59
def prefixEnd_3852186 : Nat := 4983230072969 + 3 ^ 40 * 3852186 * 2
def baseEnd_3852186 : Nat := 1978022988520770538259125

theorem tailTrace_3852186 : CollatzResearch.WordTrace tailWord_3852186 prefixEnd_3852186 1978022988520770538259125 := by
  unfold tailWord_3852186
  simp only [CollatzResearch.WordTrace]
  refine ⟨35125191505548874458934103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93667177348130331890490941 35125191505548874458934103)
  ·
    refine ⟨52687787258323311688401155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35125191505548874458934103 52687787258323311688401155)
    ·
      refine ⟨79031680887484967532601733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52687787258323311688401155 79031680887484967532601733)
      ·
        refine ⟨14818440166403431412362825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79031680887484967532601733 14818440166403431412362825)
        ·
          refine ⟨11113830124802573559272119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14818440166403431412362825 11113830124802573559272119)
          ·
            refine ⟨16670745187203860338908179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11113830124802573559272119 16670745187203860338908179)
            ·
              refine ⟨25006117780805790508362269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16670745187203860338908179 25006117780805790508362269)
              ·
                refine ⟨9377294167802171440635851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25006117780805790508362269 9377294167802171440635851)
                ·
                  refine ⟨14065941251703257160953777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9377294167802171440635851 14065941251703257160953777)
                  ·
                    refine ⟨10549455938777442870715333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14065941251703257160953777 10549455938777442870715333)
                    ·
                      refine ⟨1978022988520770538259125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10549455938777442870715333 1978022988520770538259125)
                      ·
                        rfl

theorem cell23_3852186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_3852186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852186 prefixEnd_3852186 := by exact prefixLift 3852186
  have htrace : WordTrace (prefixWord ++ tailWord_3852186) baseStart_3852186 baseEnd_3852186 := by
    simpa [prefixWord, tailWord_3852186, baseEnd_3852186] using wordTrace_append hprefix tailTrace_3852186
  have hstable : (prefixWord ++ tailWord_3852186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852186).length < 2 ^ (prefixWord ++ tailWord_3852186).sum := by decide
  have hdescent : baseEnd_3852186 < baseStart_3852186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852196 : List Nat := [2, 3, 1, 2, 1, 4, 3, 7]
def baseStart_3852196 : Nat := 118140960795 + 3852196 * 2 ^ 59
def prefixEnd_3852196 : Nat := 4983230072969 + 3 ^ 40 * 3852196 * 2
def baseEnd_3852196 : Nat := 73260300863974648116077

theorem tailTrace_3852196 : CollatzResearch.WordTrace tailWord_3852196 prefixEnd_3852196 73260300863974648116077 := by
  unfold tailWord_3852196
  simp only [CollatzResearch.WordTrace]
  refine ⟨70250565376079634771800221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93667420501439513029066961 70250565376079634771800221)
  ·
    refine ⟨26343962016029863039425083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70250565376079634771800221 26343962016029863039425083)
    ·
      refine ⟨39515943024044794559137625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26343962016029863039425083 39515943024044794559137625)
      ·
        refine ⟨29636957268033595919353219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39515943024044794559137625 29636957268033595919353219)
        ·
          refine ⟨44455435902050393879029829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29636957268033595919353219 44455435902050393879029829)
          ·
            refine ⟨8335394231634448852318093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44455435902050393879029829 8335394231634448852318093)
            ·
              refine ⟨3125772836862918319619285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8335394231634448852318093 3125772836862918319619285)
              ·
                refine ⟨73260300863974648116077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3125772836862918319619285 73260300863974648116077)
                ·
                  rfl

theorem cell23_3852196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 7].length) (baseStart_3852196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852196 prefixEnd_3852196 := by exact prefixLift 3852196
  have htrace : WordTrace (prefixWord ++ tailWord_3852196) baseStart_3852196 baseEnd_3852196 := by
    simpa [prefixWord, tailWord_3852196, baseEnd_3852196] using wordTrace_append hprefix tailTrace_3852196
  have hstable : (prefixWord ++ tailWord_3852196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852196).length < 2 ^ (prefixWord ++ tailWord_3852196).sum := by decide
  have hdescent : baseEnd_3852196 < baseStart_3852196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852229 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 2, 3, 4]
def baseStart_3852229 : Nat := 118140960795 + 3852229 * 2 ^ 59
def prefixEnd_3852229 : Nat := 4983230072969 + 3 ^ 40 * 3852229 * 2
def baseEnd_3852229 : Nat := 1978045068188913870021427

theorem tailTrace_3852229 : CollatzResearch.WordTrace tailWord_3852229 prefixEnd_3852229 1978045068188913870021427 := by
  unfold tailWord_3852229
  simp only [CollatzResearch.WordTrace]
  refine ⟨140502334361039716179551741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93668222907359810786367827 140502334361039716179551741)
  ·
    refine ⟨52688375385389893567331903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140502334361039716179551741 52688375385389893567331903)
    ·
      refine ⟨79032563078084840350997855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52688375385389893567331903 79032563078084840350997855)
      ·
        refine ⟨118548844617127260526496783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79032563078084840350997855 118548844617127260526496783)
        ·
          refine ⟨177823266925690890789745175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118548844617127260526496783 177823266925690890789745175)
          ·
            refine ⟨266734900388536336184617763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177823266925690890789745175 266734900388536336184617763)
            ·
              refine ⟨400102350582804504276926645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266734900388536336184617763 400102350582804504276926645)
              ·
                refine ⟨37509595367137922275961873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 400102350582804504276926645 37509595367137922275961873)
                ·
                  refine ⟨28132196525353441706971405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37509595367137922275961873 28132196525353441706971405)
                  ·
                    refine ⟨10549573697007540640114277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28132196525353441706971405 10549573697007540640114277)
                    ·
                      refine ⟨1978045068188913870021427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10549573697007540640114277 1978045068188913870021427)
                      ·
                        rfl

theorem cell23_3852229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_3852229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852229 prefixEnd_3852229 := by exact prefixLift 3852229
  have htrace : WordTrace (prefixWord ++ tailWord_3852229) baseStart_3852229 baseEnd_3852229 := by
    simpa [prefixWord, tailWord_3852229, baseEnd_3852229] using wordTrace_append hprefix tailTrace_3852229
  have hstable : (prefixWord ++ tailWord_3852229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852229).length < 2 ^ (prefixWord ++ tailWord_3852229).sum := by decide
  have hdescent : baseEnd_3852229 < baseStart_3852229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852239 : List Nat := [1, 1, 2, 1, 1, 5, 1, 3, 2, 6]
def baseStart_3852239 : Nat := 118140960795 + 3852239 * 2 ^ 59
def prefixEnd_3852239 : Nat := 4983230072969 + 3 ^ 40 * 3852239 * 2
def baseEnd_3852239 : Nat := 659350067665152943632127

theorem tailTrace_3852239 : CollatzResearch.WordTrace tailWord_3852239 prefixEnd_3852239 659350067665152943632127 := by
  unfold tailWord_3852239
  simp only [CollatzResearch.WordTrace]
  refine ⟨140502699091003487887415771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93668466060668991924943847 140502699091003487887415771)
  ·
    refine ⟨210754048636505231831123657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140502699091003487887415771 210754048636505231831123657)
    ·
      refine ⟨158065536477378923873342743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210754048636505231831123657 158065536477378923873342743)
      ·
        refine ⟨237098304716068385810014115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158065536477378923873342743 237098304716068385810014115)
        ·
          refine ⟨355647457074102578715021173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237098304716068385810014115 355647457074102578715021173)
          ·
            refine ⟨33341949100697116754533235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 355647457074102578715021173 33341949100697116754533235)
            ·
              refine ⟨50012923651045675131799853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33341949100697116754533235 50012923651045675131799853)
              ·
                refine ⟨18754846369142128174424945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50012923651045675131799853 18754846369142128174424945)
                ·
                  refine ⟨14066134776856596130818709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18754846369142128174424945 14066134776856596130818709)
                  ·
                    refine ⟨659350067665152943632127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14066134776856596130818709 659350067665152943632127)
                    ·
                      rfl

theorem cell23_3852239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 6].length) (baseStart_3852239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852239 prefixEnd_3852239 := by exact prefixLift 3852239
  have htrace : WordTrace (prefixWord ++ tailWord_3852239) baseStart_3852239 baseEnd_3852239 := by
    simpa [prefixWord, tailWord_3852239, baseEnd_3852239] using wordTrace_append hprefix tailTrace_3852239
  have hstable : (prefixWord ++ tailWord_3852239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852239).length < 2 ^ (prefixWord ++ tailWord_3852239).sum := by decide
  have hdescent : baseEnd_3852239 < baseStart_3852239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852258 : List Nat := [3, 3, 3, 1, 3, 1, 1, 3, 1, 2, 2]
def baseStart_3852258 : Nat := 118140960795 + 3852258 * 2 ^ 59
def prefixEnd_3852258 : Nat := 4983230072969 + 3 ^ 40 * 3852258 * 2
def baseEnd_3852258 : Nat := 1978059959127894256558795

theorem tailTrace_3852258 : CollatzResearch.WordTrace tailWord_3852258 prefixEnd_3852258 1978059959127894256558795 := by
  unfold tailWord_3852258
  simp only [CollatzResearch.WordTrace]
  refine ⟨35125848019483663533089357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93668928051956436088238285 35125848019483663533089357)
  ·
    refine ⟨13172193007306373824908509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35125848019483663533089357 13172193007306373824908509)
    ·
      refine ⟨4939572377739890184340691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13172193007306373824908509 4939572377739890184340691)
      ·
        refine ⟨7409358566609835276511037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4939572377739890184340691 7409358566609835276511037)
        ·
          refine ⟨2778509462478688228691639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7409358566609835276511037 2778509462478688228691639)
          ·
            refine ⟨4167764193718032343037459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2778509462478688228691639 4167764193718032343037459)
            ·
              refine ⟨6251646290577048514556189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4167764193718032343037459 6251646290577048514556189)
              ·
                refine ⟨2344367358966393192958571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6251646290577048514556189 2344367358966393192958571)
                ·
                  refine ⟨3516551038449589789437857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2344367358966393192958571 3516551038449589789437857)
                  ·
                    refine ⟨2637413278837192342078393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3516551038449589789437857 2637413278837192342078393)
                    ·
                      refine ⟨1978059959127894256558795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2637413278837192342078393 1978059959127894256558795)
                      ·
                        rfl

theorem cell23_3852258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_3852258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852258 prefixEnd_3852258 := by exact prefixLift 3852258
  have htrace : WordTrace (prefixWord ++ tailWord_3852258) baseStart_3852258 baseEnd_3852258 := by
    simpa [prefixWord, tailWord_3852258, baseEnd_3852258] using wordTrace_append hprefix tailTrace_3852258
  have hstable : (prefixWord ++ tailWord_3852258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852258).length < 2 ^ (prefixWord ++ tailWord_3852258).sum := by decide
  have hdescent : baseEnd_3852258 < baseStart_3852258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852266 : List Nat := [3, 1, 3, 1, 2, 1, 3, 1, 2, 1, 5]
def baseStart_3852266 : Nat := 118140960795 + 3852266 * 2 ^ 59
def prefixEnd_3852266 : Nat := 4983230072969 + 3 ^ 40 * 3852266 * 2
def baseEnd_3852266 : Nat := 1978064066973130225258757

theorem tailTrace_3852266 : CollatzResearch.WordTrace tailWord_3852266 prefixEnd_3852266 1978064066973130225258757 := by
  unfold tailWord_3852266
  simp only [CollatzResearch.WordTrace]
  refine ⟨35125920965476417874662163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93669122574603780999099101 35125920965476417874662163)
  ·
    refine ⟨52688881448214626811993245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35125920965476417874662163 52688881448214626811993245)
    ·
      refine ⟨19758330543080485054497467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52688881448214626811993245 19758330543080485054497467)
      ·
        refine ⟨29637495814620727581746201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19758330543080485054497467 29637495814620727581746201)
        ·
          refine ⟨22228121860965545686309651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29637495814620727581746201 22228121860965545686309651)
          ·
            refine ⟨33342182791448318529464477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22228121860965545686309651 33342182791448318529464477)
            ·
              refine ⟨12503318546793119448549179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33342182791448318529464477 12503318546793119448549179)
              ·
                refine ⟨18754977820189679172823769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12503318546793119448549179 18754977820189679172823769)
                ·
                  refine ⟨14066233365142259379617827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18754977820189679172823769 14066233365142259379617827)
                  ·
                    refine ⟨21099350047713389069426741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14066233365142259379617827 21099350047713389069426741)
                    ·
                      refine ⟨1978064066973130225258757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21099350047713389069426741 1978064066973130225258757)
                      ·
                        rfl

theorem cell23_3852266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_3852266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852266 prefixEnd_3852266 := by exact prefixLift 3852266
  have htrace : WordTrace (prefixWord ++ tailWord_3852266) baseStart_3852266 baseEnd_3852266 := by
    simpa [prefixWord, tailWord_3852266, baseEnd_3852266] using wordTrace_append hprefix tailTrace_3852266
  have hstable : (prefixWord ++ tailWord_3852266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852266).length < 2 ^ (prefixWord ++ tailWord_3852266).sum := by decide
  have hdescent : baseEnd_3852266 < baseStart_3852266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852296 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 1, 5, 3]
def baseStart_3852296 : Nat := 118140960795 + 3852296 * 2 ^ 59
def prefixEnd_3852296 : Nat := 4983230072969 + 3 ^ 40 * 3852296 * 2
def baseEnd_3852296 : Nat := 1978079471392765107883619

theorem tailTrace_3852296 : CollatzResearch.WordTrace tailWord_3852296 prefixEnd_3852296 1978079471392765107883619 := by
  unfold tailWord_3852296
  simp only [CollatzResearch.WordTrace]
  refine ⟨70252389025898493311120371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93669852034531324414827161 70252389025898493311120371)
  ·
    refine ⟨105378583538847739966680557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70252389025898493311120371 105378583538847739966680557)
    ·
      refine ⟨39516968827067902487505209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105378583538847739966680557 39516968827067902487505209)
      ·
        refine ⟨29637726620300926865628907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39516968827067902487505209 29637726620300926865628907)
        ·
          refine ⟨44456589930451390298443361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29637726620300926865628907 44456589930451390298443361)
          ·
            refine ⟨33342442447838542723832521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44456589930451390298443361 33342442447838542723832521)
            ·
              refine ⟨25006831835878907042874391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33342442447838542723832521 25006831835878907042874391)
              ·
                refine ⟨37510247753818360564311587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25006831835878907042874391 37510247753818360564311587)
                ·
                  refine ⟨56265371630727540846467381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37510247753818360564311587 56265371630727540846467381)
                  ·
                    refine ⟨5274878590380706954356317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56265371630727540846467381 5274878590380706954356317)
                    ·
                      refine ⟨1978079471392765107883619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5274878590380706954356317 1978079471392765107883619)
                      ·
                        rfl

theorem cell23_3852296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_3852296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852296 prefixEnd_3852296 := by exact prefixLift 3852296
  have htrace : WordTrace (prefixWord ++ tailWord_3852296) baseStart_3852296 baseEnd_3852296 := by
    simpa [prefixWord, tailWord_3852296, baseEnd_3852296] using wordTrace_append hprefix tailTrace_3852296
  have hstable : (prefixWord ++ tailWord_3852296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852296).length < 2 ^ (prefixWord ++ tailWord_3852296).sum := by decide
  have hdescent : baseEnd_3852296 < baseStart_3852296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852329 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 6, 8]
def baseStart_3852329 : Nat := 118140960795 + 3852329 * 2 ^ 59
def prefixEnd_3852329 : Nat := 4983230072969 + 3 ^ 40 * 3852329 * 2
def baseEnd_3852329 : Nat := 659365472084787826256989

theorem tailTrace_3852329 : CollatzResearch.WordTrace tailWord_3852329 prefixEnd_3852329 659365472084787826256989 := by
  unfold tailWord_3852329
  simp only [CollatzResearch.WordTrace]
  refine ⟨140505981660677433258192041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93670654440451622172128027 140505981660677433258192041)
  ·
    refine ⟨105379486245508074943644031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140505981660677433258192041 105379486245508074943644031)
    ·
      refine ⟨158069229368262112415466047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105379486245508074943644031 158069229368262112415466047)
      ·
        refine ⟨237103844052393168623199071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158069229368262112415466047 237103844052393168623199071)
        ·
          refine ⟨355655766078589752934798607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237103844052393168623199071 355655766078589752934798607)
          ·
            refine ⟨533483649117884629402197911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355655766078589752934798607 533483649117884629402197911)
            ·
              refine ⟨800225473676826944103296867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533483649117884629402197911 800225473676826944103296867)
              ·
                refine ⟨1200338210515240416154945301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 800225473676826944103296867 1200338210515240416154945301)
                ·
                  refine ⟨56265853617901894507263061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1200338210515240416154945301 56265853617901894507263061)
                  ·
                    refine ⟨659365472084787826256989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56265853617901894507263061 659365472084787826256989)
                    ·
                      rfl

theorem cell23_3852329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 8].length) (baseStart_3852329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852329 prefixEnd_3852329 := by exact prefixLift 3852329
  have htrace : WordTrace (prefixWord ++ tailWord_3852329) baseStart_3852329 baseEnd_3852329 := by
    simpa [prefixWord, tailWord_3852329, baseEnd_3852329] using wordTrace_append hprefix tailTrace_3852329
  have hstable : (prefixWord ++ tailWord_3852329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852329).length < 2 ^ (prefixWord ++ tailWord_3852329).sum := by decide
  have hdescent : baseEnd_3852329 < baseStart_3852329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852373 : List Nat := [1, 3, 2, 2, 1, 4, 1, 1, 1, 4, 3]
def baseStart_3852373 : Nat := 118140960795 + 3852373 * 2 ^ 59
def prefixEnd_3852373 : Nat := 4983230072969 + 3 ^ 40 * 3852373 * 2
def baseEnd_3852373 : Nat := 1978119009403161306620765

theorem tailTrace_3852373 : CollatzResearch.WordTrace tailWord_3852373 prefixEnd_3852373 1978119009403161306620765 := by
  unfold tailWord_3852373
  simp only [CollatzResearch.WordTrace]
  refine ⟨140507586472518028772793773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93671724315012019181862515 140507586472518028772793773)
  ·
    refine ⟨52690344927194260789797665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140507586472518028772793773 52690344927194260789797665)
    ·
      refine ⟨39517758695395695592348249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52690344927194260789797665 39517758695395695592348249)
      ·
        refine ⟨29638319021546771694261187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39517758695395695592348249 29638319021546771694261187)
        ·
          refine ⟨44457478532320157541391781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29638319021546771694261187 44457478532320157541391781)
          ·
            refine ⟨8335777224810029539010959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44457478532320157541391781 8335777224810029539010959)
            ·
              refine ⟨12503665837215044308516439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8335777224810029539010959 12503665837215044308516439)
              ·
                refine ⟨18755498755822566462774659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12503665837215044308516439 18755498755822566462774659)
                ·
                  refine ⟨28133248133733849694161989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18755498755822566462774659 28133248133733849694161989)
                  ·
                    refine ⟨5274984025075096817655373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28133248133733849694161989 5274984025075096817655373)
                    ·
                      refine ⟨1978119009403161306620765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5274984025075096817655373 1978119009403161306620765)
                      ·
                        rfl

theorem cell23_3852373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_3852373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852373 prefixEnd_3852373 := by exact prefixLift 3852373
  have htrace : WordTrace (prefixWord ++ tailWord_3852373) baseStart_3852373 baseEnd_3852373 := by
    simpa [prefixWord, tailWord_3852373, baseEnd_3852373] using wordTrace_append hprefix tailTrace_3852373
  have hstable : (prefixWord ++ tailWord_3852373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852373).length < 2 ^ (prefixWord ++ tailWord_3852373).sum := by decide
  have hdescent : baseEnd_3852373 < baseStart_3852373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852396 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 6]
def baseStart_3852396 : Nat := 118140960795 + 3852396 * 2 ^ 59
def prefixEnd_3852396 : Nat := 4983230072969 + 3 ^ 40 * 3852396 * 2
def baseEnd_3852396 : Nat := 1978130819458214716633159

theorem tailTrace_3852396 : CollatzResearch.WordTrace tailWord_3852396 prefixEnd_3852396 1978130819458214716633159 := by
  unfold tailWord_3852396
  simp only [CollatzResearch.WordTrace]
  refine ⟨70254212675717351850440521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93672283567623135800587361 70254212675717351850440521)
  ·
    refine ⟨52690659506788013887830391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70254212675717351850440521 52690659506788013887830391)
    ·
      refine ⟨79035989260182020831745587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52690659506788013887830391 79035989260182020831745587)
      ·
        refine ⟨118553983890273031247618381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79035989260182020831745587 118553983890273031247618381)
        ·
          refine ⟨44457743958852386717856893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118553983890273031247618381 44457743958852386717856893)
          ·
            refine ⟨16671653984569645019196335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44457743958852386717856893 16671653984569645019196335)
            ·
              refine ⟨25007480976854467528794503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16671653984569645019196335 25007480976854467528794503)
              ·
                refine ⟨37511221465281701293191755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25007480976854467528794503 37511221465281701293191755)
                ·
                  refine ⟨56266832197922551939787633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37511221465281701293191755 56266832197922551939787633)
                  ·
                    refine ⟨42200124148441913954840725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56266832197922551939787633 42200124148441913954840725)
                    ·
                      refine ⟨1978130819458214716633159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42200124148441913954840725 1978130819458214716633159)
                      ·
                        rfl

theorem cell23_3852396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_3852396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852396 prefixEnd_3852396 := by exact prefixLift 3852396
  have htrace : WordTrace (prefixWord ++ tailWord_3852396) baseStart_3852396 baseEnd_3852396 := by
    simpa [prefixWord, tailWord_3852396, baseEnd_3852396] using wordTrace_append hprefix tailTrace_3852396
  have hstable : (prefixWord ++ tailWord_3852396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852396).length < 2 ^ (prefixWord ++ tailWord_3852396).sum := by decide
  have hdescent : baseEnd_3852396 < baseStart_3852396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852420 : List Nat := [2, 3, 2, 1, 2, 1, 1, 4, 3, 1, 3]
def baseStart_3852420 : Nat := 118140960795 + 3852420 * 2 ^ 59
def prefixEnd_3852420 : Nat := 4983230072969 + 3 ^ 40 * 3852420 * 2
def baseEnd_3852420 : Nat := 1978143142993922622733049

theorem tailTrace_3852420 : CollatzResearch.WordTrace tailWord_3852420 prefixEnd_3852420 1978143142993922622733049 := by
  unfold tailWord_3852420
  simp only [CollatzResearch.WordTrace]
  refine ⟨70254650351673877899877357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93672867135565170533169809 70254650351673877899877357)
  ·
    refine ⟨26345493881877704212454009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70254650351673877899877357 26345493881877704212454009)
    ·
      refine ⟨19759120411408278159340507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26345493881877704212454009 19759120411408278159340507)
      ·
        refine ⟨29638680617112417239010761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19759120411408278159340507 29638680617112417239010761)
        ·
          refine ⟨22229010462834312929258071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29638680617112417239010761 22229010462834312929258071)
          ·
            refine ⟨33343515694251469393887107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22229010462834312929258071 33343515694251469393887107)
            ·
              refine ⟨50015273541377204090830661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33343515694251469393887107 50015273541377204090830661)
              ·
                refine ⟨9377863789008225767030749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50015273541377204090830661 9377863789008225767030749)
                ·
                  refine ⟨3516698920878084662636531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9377863789008225767030749 3516698920878084662636531)
                  ·
                    refine ⟨5275048381317126993954797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3516698920878084662636531 5275048381317126993954797)
                    ·
                      refine ⟨1978143142993922622733049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5275048381317126993954797 1978143142993922622733049)
                      ·
                        rfl

theorem cell23_3852420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_3852420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852420 prefixEnd_3852420 := by exact prefixLift 3852420
  have htrace : WordTrace (prefixWord ++ tailWord_3852420) baseStart_3852420 baseEnd_3852420 := by
    simpa [prefixWord, tailWord_3852420, baseEnd_3852420] using wordTrace_append hprefix tailTrace_3852420
  have hstable : (prefixWord ++ tailWord_3852420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852420).length < 2 ^ (prefixWord ++ tailWord_3852420).sum := by decide
  have hdescent : baseEnd_3852420 < baseStart_3852420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852423 : List Nat := [1, 1, 4, 2, 1, 1, 3, 4, 1, 5]
def baseStart_3852423 : Nat := 118140960795 + 3852423 * 2 ^ 59
def prefixEnd_3852423 : Nat := 4983230072969 + 3 ^ 40 * 3852423 * 2
def baseEnd_3852423 : Nat := 659381561145295370331845

theorem tailTrace_3852423 : CollatzResearch.WordTrace tailWord_3852423 prefixEnd_3852423 659381561145295370331845 := by
  unfold tailWord_3852423
  simp only [CollatzResearch.WordTrace]
  refine ⟨140509410122336887312113923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93672940081557924874742615 140509410122336887312113923)
  ·
    refine ⟨210764115183505330968170885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140509410122336887312113923 210764115183505330968170885)
    ·
      refine ⟨39518271596907249556532041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210764115183505330968170885 39518271596907249556532041)
      ·
        refine ⟨29638703697680437167399031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39518271596907249556532041 29638703697680437167399031)
        ·
          refine ⟨44458055546520655751098547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29638703697680437167399031 44458055546520655751098547)
          ·
            refine ⟨66687083319780983626647821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44458055546520655751098547 66687083319780983626647821)
            ·
              refine ⟨25007656244917868859992933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66687083319780983626647821 25007656244917868859992933)
              ·
                refine ⟨4688935545922100411248675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25007656244917868859992933 4688935545922100411248675)
                ·
                  refine ⟨7033403318883150616873013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4688935545922100411248675 7033403318883150616873013)
                  ·
                    refine ⟨659381561145295370331845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7033403318883150616873013 659381561145295370331845)
                    ·
                      rfl

theorem cell23_3852423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_3852423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852423 prefixEnd_3852423 := by exact prefixLift 3852423
  have htrace : WordTrace (prefixWord ++ tailWord_3852423) baseStart_3852423 baseEnd_3852423 := by
    simpa [prefixWord, tailWord_3852423, baseEnd_3852423] using wordTrace_append hprefix tailTrace_3852423
  have hstable : (prefixWord ++ tailWord_3852423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852423).length < 2 ^ (prefixWord ++ tailWord_3852423).sum := by decide
  have hdescent : baseEnd_3852423 < baseStart_3852423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852443 : List Nat := [1, 1, 1, 1, 1, 1, 2, 9, 1, 1, 4]
def baseStart_3852443 : Nat := 118140960795 + 3852443 * 2 ^ 59
def prefixEnd_3852443 : Nat := 4983230072969 + 3 ^ 40 * 3852443 * 2
def baseEnd_3852443 : Nat := 1978154953048976032745443

theorem tailTrace_3852443 : CollatzResearch.WordTrace tailWord_3852443 prefixEnd_3852443 1978154953048976032745443 := by
  unfold tailWord_3852443
  simp only [CollatzResearch.WordTrace]
  refine ⟨140510139582264430727841983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93673426388176287151894655 140510139582264430727841983)
  ·
    refine ⟨210765209373396646091762975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140510139582264430727841983 210765209373396646091762975)
    ·
      refine ⟨316147814060094969137644463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210765209373396646091762975 316147814060094969137644463)
      ·
        refine ⟨474221721090142453706466695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316147814060094969137644463 474221721090142453706466695)
        ·
          refine ⟨711332581635213680559700043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474221721090142453706466695 711332581635213680559700043)
          ·
            refine ⟨1066998872452820520839550065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711332581635213680559700043 1066998872452820520839550065)
            ·
              refine ⟨800249154339615390629662549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1066998872452820520839550065 800249154339615390629662549)
              ·
                refine ⟨4688959888708683929470679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 800249154339615390629662549 4688959888708683929470679)
                ·
                  refine ⟨7033439833063025894206019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4688959888708683929470679 7033439833063025894206019)
                  ·
                    refine ⟨10550159749594538841309029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7033439833063025894206019 10550159749594538841309029)
                    ·
                      refine ⟨1978154953048976032745443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10550159749594538841309029 1978154953048976032745443)
                      ·
                        rfl

theorem cell23_3852443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 1, 4].length) (baseStart_3852443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852443 prefixEnd_3852443 := by exact prefixLift 3852443
  have htrace : WordTrace (prefixWord ++ tailWord_3852443) baseStart_3852443 baseEnd_3852443 := by
    simpa [prefixWord, tailWord_3852443, baseEnd_3852443] using wordTrace_append hprefix tailTrace_3852443
  have hstable : (prefixWord ++ tailWord_3852443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852443).length < 2 ^ (prefixWord ++ tailWord_3852443).sum := by decide
  have hdescent : baseEnd_3852443 < baseStart_3852443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852447 : List Nat := [1, 1, 2, 6, 1, 2, 1, 2, 2, 3, 2]
def baseStart_3852447 : Nat := 118140960795 + 3852447 * 2 ^ 59
def prefixEnd_3852447 : Nat := 4983230072969 + 3 ^ 40 * 3852447 * 2
def baseEnd_3852447 : Nat := 1978157006971594017095425

theorem tailTrace_3852447 : CollatzResearch.WordTrace tailWord_3852447 prefixEnd_3852447 1978157006971594017095425 := by
  unfold tailWord_3852447
  simp only [CollatzResearch.WordTrace]
  refine ⟨140510285474249939410987595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93673523649499959607325063 140510285474249939410987595)
  ·
    refine ⟨210765428211374909116481393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140510285474249939410987595 210765428211374909116481393)
    ·
      refine ⟨158074071158531181837361045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210765428211374909116481393 158074071158531181837361045)
      ·
        refine ⟨7409722085556149148626299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 158074071158531181837361045 7409722085556149148626299)
        ·
          refine ⟨11114583128334223722939449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7409722085556149148626299 11114583128334223722939449)
          ·
            refine ⟨8335937346250667792204587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11114583128334223722939449 8335937346250667792204587)
            ·
              refine ⟨12503906019376001688306881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8335937346250667792204587 12503906019376001688306881)
              ·
                refine ⟨9377929514532001266230161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12503906019376001688306881 9377929514532001266230161)
                ·
                  refine ⟨7033447135899000949672621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9377929514532001266230161 7033447135899000949672621)
                  ·
                    refine ⟨2637542675962125356127233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7033447135899000949672621 2637542675962125356127233)
                    ·
                      refine ⟨1978157006971594017095425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2637542675962125356127233 1978157006971594017095425)
                      ·
                        rfl

theorem cell23_3852447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_3852447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852447 prefixEnd_3852447 := by exact prefixLift 3852447
  have htrace : WordTrace (prefixWord ++ tailWord_3852447) baseStart_3852447 baseEnd_3852447 := by
    simpa [prefixWord, tailWord_3852447, baseEnd_3852447] using wordTrace_append hprefix tailTrace_3852447
  have hstable : (prefixWord ++ tailWord_3852447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852447).length < 2 ^ (prefixWord ++ tailWord_3852447).sum := by decide
  have hdescent : baseEnd_3852447 < baseStart_3852447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852453 : List Nat := [1, 3, 1, 2, 1, 3, 1, 3, 4, 4]
def baseStart_3852453 : Nat := 118140960795 + 3852453 * 2 ^ 59
def prefixEnd_3852453 : Nat := 4983230072969 + 3 ^ 40 * 3852453 * 2
def baseEnd_3852453 : Nat := 659386695951840331206799

theorem tailTrace_3852453 : CollatzResearch.WordTrace tailWord_3852453 prefixEnd_3852453 659386695951840331206799 := by
  unfold tailWord_3852453
  simp only [CollatzResearch.WordTrace]
  refine ⟨140510504312228202435706013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93673669541485468290470675 140510504312228202435706013)
  ·
    refine ⟨52691439117085575913389755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140510504312228202435706013 52691439117085575913389755)
    ·
      refine ⟨79037158675628363870084633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52691439117085575913389755 79037158675628363870084633)
      ·
        refine ⟨59277869006721272902563475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79037158675628363870084633 59277869006721272902563475)
        ·
          refine ⟨88916803510081909353845213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59277869006721272902563475 88916803510081909353845213)
          ·
            refine ⟨33343801316280716007691955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88916803510081909353845213 33343801316280716007691955)
            ·
              refine ⟨50015701974421074011537933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33343801316280716007691955 50015701974421074011537933)
              ·
                refine ⟨18755888240407902754326725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50015701974421074011537933 18755888240407902754326725)
                ·
                  refine ⟨3516729045076481766436261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18755888240407902754326725 3516729045076481766436261)
                  ·
                    refine ⟨659386695951840331206799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3516729045076481766436261 659386695951840331206799)
                    ·
                      rfl

theorem cell23_3852453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 4, 4].length) (baseStart_3852453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852453 prefixEnd_3852453 := by exact prefixLift 3852453
  have htrace : WordTrace (prefixWord ++ tailWord_3852453) baseStart_3852453 baseEnd_3852453 := by
    simpa [prefixWord, tailWord_3852453, baseEnd_3852453] using wordTrace_append hprefix tailTrace_3852453
  have hstable : (prefixWord ++ tailWord_3852453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852453).length < 2 ^ (prefixWord ++ tailWord_3852453).sum := by decide
  have hdescent : baseEnd_3852453 < baseStart_3852453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852463 : List Nat := [1, 1, 2, 1, 2, 3, 1, 4, 3, 2, 3]
def baseStart_3852463 : Nat := 118140960795 + 3852463 * 2 ^ 59
def prefixEnd_3852463 : Nat := 4983230072969 + 3 ^ 40 * 3852463 * 2
def baseEnd_3852463 : Nat := 1978165222662065954495351

theorem tailTrace_3852463 : CollatzResearch.WordTrace tailWord_3852463 prefixEnd_3852463 1978165222662065954495351 := by
  unfold tailWord_3852463
  simp only [CollatzResearch.WordTrace]
  refine ⟨140510869042191974143570043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93673912694794649429046695 140510869042191974143570043)
  ·
    refine ⟨210766303563287961215355065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140510869042191974143570043 210766303563287961215355065)
    ·
      refine ⟨158074727672465970911516299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210766303563287961215355065 158074727672465970911516299)
      ·
        refine ⟨237112091508698956367274449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158074727672465970911516299 237112091508698956367274449)
        ·
          refine ⟨177834068631524217275455837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237112091508698956367274449 177834068631524217275455837)
          ·
            refine ⟨66687775736821581478295939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177834068631524217275455837 66687775736821581478295939)
            ·
              refine ⟨100031663605232372217443909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66687775736821581478295939 100031663605232372217443909)
              ·
                refine ⟨18755936925981069790770733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100031663605232372217443909 18755936925981069790770733)
                ·
                  refine ⟨7033476347242901171539025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18755936925981069790770733 7033476347242901171539025)
                  ·
                    refine ⟨5275107260432175878654269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7033476347242901171539025 5275107260432175878654269)
                    ·
                      refine ⟨1978165222662065954495351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5275107260432175878654269 1978165222662065954495351)
                      ·
                        rfl

theorem cell23_3852463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 2, 3].length) (baseStart_3852463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852463 prefixEnd_3852463 := by exact prefixLift 3852463
  have htrace : WordTrace (prefixWord ++ tailWord_3852463) baseStart_3852463 baseEnd_3852463 := by
    simpa [prefixWord, tailWord_3852463, baseEnd_3852463] using wordTrace_append hprefix tailTrace_3852463
  have hstable : (prefixWord ++ tailWord_3852463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852463).length < 2 ^ (prefixWord ++ tailWord_3852463).sum := by decide
  have hdescent : baseEnd_3852463 < baseStart_3852463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852473 : List Nat := [1, 2, 1, 4, 1, 2, 2, 3, 1, 2, 4]
def baseStart_3852473 : Nat := 118140960795 + 3852473 * 2 ^ 59
def prefixEnd_3852473 : Nat := 4983230072969 + 3 ^ 40 * 3852473 * 2
def baseEnd_3852473 : Nat := 1978170357468610915370305

theorem tailTrace_3852473 : CollatzResearch.WordTrace tailWord_3852473 prefixEnd_3852473 1978170357468610915370305 := by
  unfold tailWord_3852473
  simp only [CollatzResearch.WordTrace]
  refine ⟨140511233772155745851434073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93674155848103830567622715 140511233772155745851434073)
  ·
    refine ⟨105383425329116809388575555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140511233772155745851434073 105383425329116809388575555)
    ·
      refine ⟨158075137993675214082863333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105383425329116809388575555 158075137993675214082863333)
      ·
        refine ⟨29639088373814102640536875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158075137993675214082863333 29639088373814102640536875)
        ·
          refine ⟨44458632560721153960805313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29639088373814102640536875 44458632560721153960805313)
          ·
            refine ⟨33343974420540865470603985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44458632560721153960805313 33343974420540865470603985)
            ·
              refine ⟨25007980815405649102952989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33343974420540865470603985 25007980815405649102952989)
              ·
                refine ⟨9377992805777118413607371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25007980815405649102952989 9377992805777118413607371)
                ·
                  refine ⟨14066989208665677620411057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9377992805777118413607371 14066989208665677620411057)
                  ·
                    refine ⟨10550241906499258215308293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14066989208665677620411057 10550241906499258215308293)
                    ·
                      refine ⟨1978170357468610915370305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10550241906499258215308293 1978170357468610915370305)
                      ·
                        rfl

theorem cell23_3852473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_3852473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852473 prefixEnd_3852473 := by exact prefixLift 3852473
  have htrace : WordTrace (prefixWord ++ tailWord_3852473) baseStart_3852473 baseEnd_3852473 := by
    simpa [prefixWord, tailWord_3852473, baseEnd_3852473] using wordTrace_append hprefix tailTrace_3852473
  have hstable : (prefixWord ++ tailWord_3852473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852473).length < 2 ^ (prefixWord ++ tailWord_3852473).sum := by decide
  have hdescent : baseEnd_3852473 < baseStart_3852473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852480 : List Nat := [2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 3]
def baseStart_3852480 : Nat := 118140960795 + 3852480 * 2 ^ 59
def prefixEnd_3852480 : Nat := 4983230072969 + 3 ^ 40 * 3852480 * 2
def baseEnd_3852480 : Nat := 1978173951833192387982773

theorem tailTrace_3852480 : CollatzResearch.WordTrace tailWord_3852480 prefixEnd_3852480 1978173951833192387982773 := by
  unfold tailWord_3852480
  simp only [CollatzResearch.WordTrace]
  refine ⟨70255744541565193023469447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93674326055420257364625929 70255744541565193023469447)
  ·
    refine ⟨105383616812347789535204171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70255744541565193023469447 105383616812347789535204171)
    ·
      refine ⟨158075425218521684302806257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105383616812347789535204171 158075425218521684302806257)
      ·
        refine ⟨118556568913891263227104693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158075425218521684302806257 118556568913891263227104693)
        ·
          refine ⟨11114678335677305927541065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118556568913891263227104693 11114678335677305927541065)
          ·
            refine ⟨8336008751757979445655799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11114678335677305927541065 8336008751757979445655799)
            ·
              refine ⟨12504013127636969168483699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8336008751757979445655799 12504013127636969168483699)
              ·
                refine ⟨18756019691455453752725549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12504013127636969168483699 18756019691455453752725549)
                ·
                  refine ⟨7033507384295795157272081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18756019691455453752725549 7033507384295795157272081)
                  ·
                    refine ⟨5275130538221846367954061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7033507384295795157272081 5275130538221846367954061)
                    ·
                      refine ⟨1978173951833192387982773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5275130538221846367954061 1978173951833192387982773)
                      ·
                        rfl

theorem cell23_3852480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 3].length) (baseStart_3852480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852480 prefixEnd_3852480 := by exact prefixLift 3852480
  have htrace : WordTrace (prefixWord ++ tailWord_3852480) baseStart_3852480 baseEnd_3852480 := by
    simpa [prefixWord, tailWord_3852480, baseEnd_3852480] using wordTrace_append hprefix tailTrace_3852480
  have hstable : (prefixWord ++ tailWord_3852480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852480).length < 2 ^ (prefixWord ++ tailWord_3852480).sum := by decide
  have hdescent : baseEnd_3852480 < baseStart_3852480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852496 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 6, 7]
def baseStart_3852496 : Nat := 118140960795 + 3852496 * 2 ^ 59
def prefixEnd_3852496 : Nat := 4983230072969 + 3 ^ 40 * 3852496 * 2
def baseEnd_3852496 : Nat := 659394055841221441794233

theorem tailTrace_3852496 : CollatzResearch.WordTrace tailWord_3852496 prefixEnd_3852496 659394055841221441794233 := by
  unfold tailWord_3852496
  simp only [CollatzResearch.WordTrace]
  refine ⟨70256036325536210389760671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93674715100714947186347561 70256036325536210389760671)
  ·
    refine ⟨105384054488304315584641007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70256036325536210389760671 105384054488304315584641007)
    ·
      refine ⟨158076081732456473376961511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105384054488304315584641007 158076081732456473376961511)
      ·
        refine ⟨237114122598684710065442267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158076081732456473376961511 237114122598684710065442267)
        ·
          refine ⟨355671183898027065098163401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237114122598684710065442267 355671183898027065098163401)
          ·
            refine ⟨266753387923520298823622551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355671183898027065098163401 266753387923520298823622551)
            ·
              refine ⟨400130081885280448235433827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266753387923520298823622551 400130081885280448235433827)
              ·
                refine ⟨600195122827920672353150741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400130081885280448235433827 600195122827920672353150741)
                ·
                  refine ⟨28134146382558781516553941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 600195122827920672353150741 28134146382558781516553941)
                  ·
                    refine ⟨659394055841221441794233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28134146382558781516553941 659394055841221441794233)
                    ·
                      rfl

theorem cell23_3852496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 6, 7].length) (baseStart_3852496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852496 prefixEnd_3852496 := by exact prefixLift 3852496
  have htrace : WordTrace (prefixWord ++ tailWord_3852496) baseStart_3852496 baseEnd_3852496 := by
    simpa [prefixWord, tailWord_3852496, baseEnd_3852496] using wordTrace_append hprefix tailTrace_3852496
  have hstable : (prefixWord ++ tailWord_3852496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852496).length < 2 ^ (prefixWord ++ tailWord_3852496).sum := by decide
  have hdescent : baseEnd_3852496 < baseStart_3852496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852527 : List Nat := [1, 1, 2, 1, 6, 1, 2, 3, 2, 1, 3]
def baseStart_3852527 : Nat := 118140960795 + 3852527 * 2 ^ 59
def prefixEnd_3852527 : Nat := 4983230072969 + 3 ^ 40 * 3852527 * 2
def baseEnd_3852527 : Nat := 1978198085423953704095057

theorem tailTrace_3852527 : CollatzResearch.WordTrace tailWord_3852527 prefixEnd_3852527 1978198085423953704095057 := by
  unfold tailWord_3852527
  simp only [CollatzResearch.WordTrace]
  refine ⟨140513203313960113073899835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93675468875973408715933223 140513203313960113073899835)
  ·
    refine ⟨210769804970940169610849753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140513203313960113073899835 210769804970940169610849753)
    ·
      refine ⟨158077353728205127208137315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210769804970940169610849753 158077353728205127208137315)
      ·
        refine ⟨237116030592307690812205973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158077353728205127208137315 237116030592307690812205973)
        ·
          refine ⟨11114813934014423006822155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 237116030592307690812205973 11114813934014423006822155)
          ·
            refine ⟨16672220901021634510233233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11114813934014423006822155 16672220901021634510233233)
            ·
              refine ⟨12504165675766225882674925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16672220901021634510233233 12504165675766225882674925)
              ·
                refine ⟨4689062128412334706003097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12504165675766225882674925 4689062128412334706003097)
                ·
                  refine ⟨3516796596309251029502323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4689062128412334706003097 3516796596309251029502323)
                  ·
                    refine ⟨5275194894463876544253485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3516796596309251029502323 5275194894463876544253485)
                    ·
                      refine ⟨1978198085423953704095057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5275194894463876544253485 1978198085423953704095057)
                      ·
                        rfl

theorem cell23_3852527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 2, 1, 3].length) (baseStart_3852527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852527 prefixEnd_3852527 := by exact prefixLift 3852527
  have htrace : WordTrace (prefixWord ++ tailWord_3852527) baseStart_3852527 baseEnd_3852527 := by
    simpa [prefixWord, tailWord_3852527, baseEnd_3852527] using wordTrace_append hprefix tailTrace_3852527
  have hstable : (prefixWord ++ tailWord_3852527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852527).length < 2 ^ (prefixWord ++ tailWord_3852527).sum := by decide
  have hdescent : baseEnd_3852527 < baseStart_3852527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852554 : List Nat := [3, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2]
def baseStart_3852554 : Nat := 118140960795 + 3852554 * 2 ^ 59
def prefixEnd_3852554 : Nat := 4983230072969 + 3 ^ 40 * 3852554 * 2
def baseEnd_3852554 : Nat := 1978211949401625098457433

theorem tailTrace_3852554 : CollatzResearch.WordTrace tailWord_3852554 prefixEnd_3852554 1978211949401625098457433 := by
  unfold tailWord_3852554
  simp only [CollatzResearch.WordTrace]
  refine ⟨35128547021215574171283179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93676125389908197790088477 35128547021215574171283179)
  ·
    refine ⟨52692820531823361256924769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35128547021215574171283179 52692820531823361256924769)
    ·
      refine ⟨39519615398867520942693577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52692820531823361256924769 39519615398867520942693577)
      ·
        refine ⟨29639711549150640707020183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39519615398867520942693577 29639711549150640707020183)
        ·
          refine ⟨44459567323725961060530275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29639711549150640707020183 44459567323725961060530275)
          ·
            refine ⟨66689350985588941590795413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44459567323725961060530275 66689350985588941590795413)
            ·
              refine ⟨3126063327449481637068535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66689350985588941590795413 3126063327449481637068535)
              ·
                refine ⟨4689094991174222455602803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3126063327449481637068535 4689094991174222455602803)
                ·
                  refine ⟨7033642486761333683404205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4689094991174222455602803 7033642486761333683404205)
                  ·
                    refine ⟨2637615932535500131276577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7033642486761333683404205 2637615932535500131276577)
                    ·
                      refine ⟨1978211949401625098457433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2637615932535500131276577 1978211949401625098457433)
                      ·
                        rfl

theorem cell23_3852554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_3852554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852554 prefixEnd_3852554 := by exact prefixLift 3852554
  have htrace : WordTrace (prefixWord ++ tailWord_3852554) baseStart_3852554 baseEnd_3852554 := by
    simpa [prefixWord, tailWord_3852554, baseEnd_3852554] using wordTrace_append hprefix tailTrace_3852554
  have hstable : (prefixWord ++ tailWord_3852554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852554).length < 2 ^ (prefixWord ++ tailWord_3852554).sum := by decide
  have hdescent : baseEnd_3852554 < baseStart_3852554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852580 : List Nat := [2, 3, 1, 3, 1, 2, 2, 1, 2, 2, 4]
def baseStart_3852580 : Nat := 118140960795 + 3852580 * 2 ^ 59
def prefixEnd_3852580 : Nat := 4983230072969 + 3 ^ 40 * 3852580 * 2
def baseEnd_3852580 : Nat := 1978225299898641996732313

theorem tailTrace_3852580 : CollatzResearch.WordTrace tailWord_3852580 prefixEnd_3852580 1978225299898641996732313 := by
  unfold tailWord_3852580
  simp only [CollatzResearch.WordTrace]
  refine ⟨70257568191384051562789597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93676757588512068750386129 70257568191384051562789597)
  ·
    refine ⟨26346588071769019336046099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70257568191384051562789597 26346588071769019336046099)
    ·
      refine ⟨39519882107653529004069149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26346588071769019336046099 39519882107653529004069149)
      ·
        refine ⟨14819955790370073376525931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39519882107653529004069149 14819955790370073376525931)
        ·
          refine ⟨22229933685555110064788897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14819955790370073376525931 22229933685555110064788897)
          ·
            refine ⟨16672450264166332548591673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22229933685555110064788897 16672450264166332548591673)
            ·
              refine ⟨12504337698124749411443755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16672450264166332548591673 12504337698124749411443755)
              ·
                refine ⟨18756506547187124117165633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12504337698124749411443755 18756506547187124117165633)
                ·
                  refine ⟨14067379910390343087874225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18756506547187124117165633 14067379910390343087874225)
                  ·
                    refine ⟨10550534932792757315905669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14067379910390343087874225 10550534932792757315905669)
                    ·
                      refine ⟨1978225299898641996732313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10550534932792757315905669 1978225299898641996732313)
                      ·
                        rfl

theorem cell23_3852580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_3852580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852580 prefixEnd_3852580 := by exact prefixLift 3852580
  have htrace : WordTrace (prefixWord ++ tailWord_3852580) baseStart_3852580 baseEnd_3852580 := by
    simpa [prefixWord, tailWord_3852580, baseEnd_3852580] using wordTrace_append hprefix tailTrace_3852580
  have hstable : (prefixWord ++ tailWord_3852580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852580).length < 2 ^ (prefixWord ++ tailWord_3852580).sum := by decide
  have hdescent : baseEnd_3852580 < baseStart_3852580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852620 : List Nat := [2, 2, 1, 3, 2, 1, 3, 2, 2, 5]
def baseStart_3852620 : Nat := 118140960795 + 3852620 * 2 ^ 59
def prefixEnd_3852620 : Nat := 4983230072969 + 3 ^ 40 * 3852620 * 2
def baseEnd_3852620 : Nat := 659415279708273946744043

theorem tailTrace_3852620 : CollatzResearch.WordTrace tailWord_3852620 prefixEnd_3852620 659415279708273946744043 := by
  unfold tailWord_3852620
  simp only [CollatzResearch.WordTrace]
  refine ⟨70258297651311594978517657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93677730201748793304690209 70258297651311594978517657)
  ·
    refine ⟨52693723238483696233888243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70258297651311594978517657 52693723238483696233888243)
    ·
      refine ⟨79040584857725544350832365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52693723238483696233888243 79040584857725544350832365)
      ·
        refine ⟨29640219321647079131562137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79040584857725544350832365 29640219321647079131562137)
        ·
          refine ⟨22230164491235309348671603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29640219321647079131562137 22230164491235309348671603)
          ·
            refine ⟨33345246736852964023007405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22230164491235309348671603 33345246736852964023007405)
            ·
              refine ⟨12504467526319861508627777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33345246736852964023007405 12504467526319861508627777)
              ·
                refine ⟨9378350644739896131470833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12504467526319861508627777 9378350644739896131470833)
                ·
                  refine ⟨7033762983554922098603125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9378350644739896131470833 7033762983554922098603125)
                  ·
                    refine ⟨659415279708273946744043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7033762983554922098603125 659415279708273946744043)
                    ·
                      rfl

theorem cell23_3852620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 2, 5].length) (baseStart_3852620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852620 prefixEnd_3852620 := by exact prefixLift 3852620
  have htrace : WordTrace (prefixWord ++ tailWord_3852620) baseStart_3852620 baseEnd_3852620 := by
    simpa [prefixWord, tailWord_3852620, baseEnd_3852620] using wordTrace_append hprefix tailTrace_3852620
  have hstable : (prefixWord ++ tailWord_3852620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852620).length < 2 ^ (prefixWord ++ tailWord_3852620).sum := by decide
  have hdescent : baseEnd_3852620 < baseStart_3852620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852623 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 4]
def baseStart_3852623 : Nat := 118140960795 + 3852623 * 2 ^ 59
def prefixEnd_3852623 : Nat := 4983230072969 + 3 ^ 40 * 3852623 * 2
def baseEnd_3852623 : Nat := 1978247379566785328494615

theorem tailTrace_3852623 : CollatzResearch.WordTrace tailWord_3852623 prefixEnd_3852623 1978247379566785328494615 := by
  unfold tailWord_3852623
  simp only [CollatzResearch.WordTrace]
  refine ⟨140516704721612321469394523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93677803147741547646263015 140516704721612321469394523)
  ·
    refine ⟨210775057082418482204091785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140516704721612321469394523 210775057082418482204091785)
    ·
      refine ⟨158081292811813861653068839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210775057082418482204091785 158081292811813861653068839)
      ·
        refine ⟨237121939217720792479603259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158081292811813861653068839 237121939217720792479603259)
        ·
          refine ⟨355682908826581188719404889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237121939217720792479603259 355682908826581188719404889)
          ·
            refine ⟨266762181619935891539553667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355682908826581188719404889 266762181619935891539553667)
            ·
              refine ⟨400143272429903837309330501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266762181619935891539553667 400143272429903837309330501)
              ·
                refine ⟨75026863580606969495499469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 400143272429903837309330501 75026863580606969495499469)
                ·
                  refine ⟨28135073842727613560812301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75026863580606969495499469 28135073842727613560812301)
                  ·
                    refine ⟨10550652691022855085304613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28135073842727613560812301 10550652691022855085304613)
                    ·
                      refine ⟨1978247379566785328494615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10550652691022855085304613 1978247379566785328494615)
                      ·
                        rfl

theorem cell23_3852623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 4].length) (baseStart_3852623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852623 prefixEnd_3852623 := by exact prefixLift 3852623
  have htrace : WordTrace (prefixWord ++ tailWord_3852623) baseStart_3852623 baseEnd_3852623 := by
    simpa [prefixWord, tailWord_3852623, baseEnd_3852623] using wordTrace_append hprefix tailTrace_3852623
  have hstable : (prefixWord ++ tailWord_3852623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852623).length < 2 ^ (prefixWord ++ tailWord_3852623).sum := by decide
  have hdescent : baseEnd_3852623 < baseStart_3852623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852663 : List Nat := [1, 1, 3, 1, 1, 2, 2, 4, 8]
def baseStart_3852663 : Nat := 118140960795 + 3852663 * 2 ^ 59
def prefixEnd_3852663 : Nat := 4983230072969 + 3 ^ 40 * 3852663 * 2
def baseEnd_3852663 : Nat := 219807546532551685777159

theorem tailTrace_3852663 : CollatzResearch.WordTrace tailWord_3852663 prefixEnd_3852663 219807546532551685777159 := by
  unfold tailWord_3852663
  simp only [CollatzResearch.WordTrace]
  refine ⟨140518163641467408300850643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93678775760978272200567095 140518163641467408300850643)
  ·
    refine ⟨210777245462201112451275965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140518163641467408300850643 210777245462201112451275965)
    ·
      refine ⟨79041467048325417169228487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210777245462201112451275965 79041467048325417169228487)
      ·
        refine ⟨118562200572488125753842731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79041467048325417169228487 118562200572488125753842731)
        ·
          refine ⟨177843300858732188630764097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118562200572488125753842731 177843300858732188630764097)
          ·
            refine ⟨133382475644049141473073073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177843300858732188630764097 133382475644049141473073073)
            ·
              refine ⟨100036856733036856104804805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133382475644049141473073073 100036856733036856104804805)
              ·
                refine ⟨18756910637444410519650901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100036856733036856104804805 18756910637444410519650901)
                ·
                  refine ⟨219807546532551685777159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18756910637444410519650901 219807546532551685777159)
                  ·
                    rfl

theorem cell23_3852663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 8].length) (baseStart_3852663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852663 prefixEnd_3852663 := by exact prefixLift 3852663
  have htrace : WordTrace (prefixWord ++ tailWord_3852663) baseStart_3852663 baseEnd_3852663 := by
    simpa [prefixWord, tailWord_3852663, baseEnd_3852663] using wordTrace_append hprefix tailTrace_3852663
  have hstable : (prefixWord ++ tailWord_3852663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852663).length < 2 ^ (prefixWord ++ tailWord_3852663).sum := by decide
  have hdescent : baseEnd_3852663 < baseStart_3852663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852684 : List Nat := [2, 2, 1, 2, 1, 5, 1, 4, 1, 4]
def baseStart_3852684 : Nat := 118140960795 + 3852684 * 2 ^ 59
def prefixEnd_3852684 : Nat := 4983230072969 + 3 ^ 40 * 3852684 * 2
def baseEnd_3852684 : Nat := 659426233962236529943945

theorem tailTrace_3852684 : CollatzResearch.WordTrace tailWord_3852684 prefixEnd_3852684 659426233962236529943945 := by
  unfold tailWord_3852684
  simp only [CollatzResearch.WordTrace]
  refine ⟨70259464787195664443682553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93679286382927552591576737 70259464787195664443682553)
  ·
    refine ⟨52694598590396748332761915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70259464787195664443682553 52694598590396748332761915)
    ·
      refine ⟨79041897885595122499142873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52694598590396748332761915 79041897885595122499142873)
      ·
        refine ⟨59281423414196341874357155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79041897885595122499142873 59281423414196341874357155)
        ·
          refine ⟨88922135121294512811535733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59281423414196341874357155 88922135121294512811535733)
          ·
            refine ⟨8336450167621360576081475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88922135121294512811535733 8336450167621360576081475)
            ·
              refine ⟨12504675251432040864122213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8336450167621360576081475 12504675251432040864122213)
              ·
                refine ⟨2344626609643507662022915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12504675251432040864122213 2344626609643507662022915)
                ·
                  refine ⟨3516939914465261493034373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2344626609643507662022915 3516939914465261493034373)
                  ·
                    refine ⟨659426233962236529943945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3516939914465261493034373 659426233962236529943945)
                    ·
                      rfl

theorem cell23_3852684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 4, 1, 4].length) (baseStart_3852684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852684 prefixEnd_3852684 := by exact prefixLift 3852684
  have htrace : WordTrace (prefixWord ++ tailWord_3852684) baseStart_3852684 baseEnd_3852684 := by
    simpa [prefixWord, tailWord_3852684, baseEnd_3852684] using wordTrace_append hprefix tailTrace_3852684
  have hstable : (prefixWord ++ tailWord_3852684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852684).length < 2 ^ (prefixWord ++ tailWord_3852684).sum := by decide
  have hdescent : baseEnd_3852684 < baseStart_3852684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852707 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 5, 1, 3]
def baseStart_3852707 : Nat := 118140960795 + 3852707 * 2 ^ 59
def prefixEnd_3852707 : Nat := 4983230072969 + 3 ^ 40 * 3852707 * 2
def baseEnd_3852707 : Nat := 1978290511941762999844229

theorem tailTrace_3852707 : CollatzResearch.WordTrace tailWord_3852707 prefixEnd_3852707 1978290511941762999844229 := by
  unfold tailWord_3852707
  simp only [CollatzResearch.WordTrace]
  refine ⟨140519768453308003815452375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93679845635538669210301583 140519768453308003815452375)
  ·
    refine ⟨210779652679962005723178563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140519768453308003815452375 210779652679962005723178563)
    ·
      refine ⟨316169479019943008584767845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210779652679962005723178563 316169479019943008584767845)
      ·
        refine ⟨59281777316239314109643971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 316169479019943008584767845 59281777316239314109643971)
        ·
          refine ⟨88922665974358971164465957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59281777316239314109643971 88922665974358971164465957)
          ·
            refine ⟨16672999870192307093337367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88922665974358971164465957 16672999870192307093337367)
            ·
              refine ⟨25009499805288460640006051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16672999870192307093337367 25009499805288460640006051)
              ·
                refine ⟨37514249707932690960009077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25009499805288460640006051 37514249707932690960009077)
                ·
                  refine ⟨3516960910118689777500851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37514249707932690960009077 3516960910118689777500851)
                  ·
                    refine ⟨5275441365178034666251277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3516960910118689777500851 5275441365178034666251277)
                    ·
                      refine ⟨1978290511941762999844229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5275441365178034666251277 1978290511941762999844229)
                      ·
                        rfl

theorem cell23_3852707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_3852707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852707 prefixEnd_3852707 := by exact prefixLift 3852707
  have htrace : WordTrace (prefixWord ++ tailWord_3852707) baseStart_3852707 baseEnd_3852707 := by
    simpa [prefixWord, tailWord_3852707, baseEnd_3852707] using wordTrace_append hprefix tailTrace_3852707
  have hstable : (prefixWord ++ tailWord_3852707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852707).length < 2 ^ (prefixWord ++ tailWord_3852707).sum := by decide
  have hdescent : baseEnd_3852707 < baseStart_3852707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852727 : List Nat := [1, 1, 3, 1, 3, 4, 1, 3, 1, 5]
def baseStart_3852727 : Nat := 118140960795 + 3852727 * 2 ^ 59
def prefixEnd_3852727 : Nat := 4983230072969 + 3 ^ 40 * 3852727 * 2
def baseEnd_3852727 : Nat := 659433593851617640531379

theorem tailTrace_3852727 : CollatzResearch.WordTrace tailWord_3852727 prefixEnd_3852727 659433593851617640531379 := by
  unfold tailWord_3852727
  simp only [CollatzResearch.WordTrace]
  refine ⟨140520497913235547231180435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93680331942157031487453623 140520497913235547231180435)
  ·
    refine ⟨210780746869853320846770653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140520497913235547231180435 210780746869853320846770653)
    ·
      refine ⟨79042780076194995317538995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210780746869853320846770653 79042780076194995317538995)
      ·
        refine ⟨118564170114292492976308493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79042780076194995317538995 118564170114292492976308493)
        ·
          refine ⟨44461563792859684866115685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118564170114292492976308493 44461563792859684866115685)
          ·
            refine ⟨8336543211161190912396691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44461563792859684866115685 8336543211161190912396691)
            ·
              refine ⟨12504814816741786368595037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8336543211161190912396691 12504814816741786368595037)
              ·
                refine ⟨4689305556278169888223139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12504814816741786368595037 4689305556278169888223139)
                ·
                  refine ⟨7033958334417254832334709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4689305556278169888223139 7033958334417254832334709)
                  ·
                    refine ⟨659433593851617640531379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7033958334417254832334709 659433593851617640531379)
                    ·
                      rfl

theorem cell23_3852727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 5].length) (baseStart_3852727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852727 prefixEnd_3852727 := by exact prefixLift 3852727
  have htrace : WordTrace (prefixWord ++ tailWord_3852727) baseStart_3852727 baseEnd_3852727 := by
    simpa [prefixWord, tailWord_3852727, baseEnd_3852727] using wordTrace_append hprefix tailTrace_3852727
  have hstable : (prefixWord ++ tailWord_3852727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852727).length < 2 ^ (prefixWord ++ tailWord_3852727).sum := by decide
  have hdescent : baseEnd_3852727 < baseStart_3852727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852734 : List Nat := [4, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2]
def baseStart_3852734 : Nat := 118140960795 + 3852734 * 2 ^ 59
def prefixEnd_3852734 : Nat := 4983230072969 + 3 ^ 40 * 3852734 * 2
def baseEnd_3852734 : Nat := 1978304375919434394206605

theorem tailTrace_3852734 : CollatzResearch.WordTrace tailWord_3852734 prefixEnd_3852734 1978304375919434394206605 := by
  unfold tailWord_3852734
  simp only [CollatzResearch.WordTrace]
  refine ⟨17565094153026273428335657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93680502149473458284456837 17565094153026273428335657)
  ·
    refine ⟨13173820614769705071251743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17565094153026273428335657 13173820614769705071251743)
    ·
      refine ⟨19760730922154557606877615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13173820614769705071251743 19760730922154557606877615)
      ·
        refine ⟨29641096383231836410316423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19760730922154557606877615 29641096383231836410316423)
        ·
          refine ⟨44461644574847754615474635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29641096383231836410316423 44461644574847754615474635)
          ·
            refine ⟨66692466862271631923211953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44461644574847754615474635 66692466862271631923211953)
            ·
              refine ⟨50019350146703723942408965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66692466862271631923211953 50019350146703723942408965)
              ·
                refine ⟨9378628152506948239201681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50019350146703723942408965 9378628152506948239201681)
                ·
                  refine ⟨7033971114380211179401261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9378628152506948239201681 7033971114380211179401261)
                  ·
                    refine ⟨2637739167892579192275473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7033971114380211179401261 2637739167892579192275473)
                    ·
                      refine ⟨1978304375919434394206605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2637739167892579192275473 1978304375919434394206605)
                      ·
                        rfl

theorem cell23_3852734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_3852734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852734 prefixEnd_3852734 := by exact prefixLift 3852734
  have htrace : WordTrace (prefixWord ++ tailWord_3852734) baseStart_3852734 baseEnd_3852734 := by
    simpa [prefixWord, tailWord_3852734, baseEnd_3852734] using wordTrace_append hprefix tailTrace_3852734
  have hstable : (prefixWord ++ tailWord_3852734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852734).length < 2 ^ (prefixWord ++ tailWord_3852734).sum := by decide
  have hdescent : baseEnd_3852734 < baseStart_3852734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852757 : List Nat := [1, 3, 2, 3, 1, 2, 3, 1, 1, 6]
def baseStart_3852757 : Nat := 118140960795 + 3852757 * 2 ^ 59
def prefixEnd_3852757 : Nat := 4983230072969 + 3 ^ 40 * 3852757 * 2
def baseEnd_3852757 : Nat := 659438728658162601406333

theorem tailTrace_3852757 : CollatzResearch.WordTrace tailWord_3852757 prefixEnd_3852757 659438728658162601406333 := by
  unfold tailWord_3852757
  simp only [CollatzResearch.WordTrace]
  refine ⟨140521592103126862354772525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93681061402084574903181683 140521592103126862354772525)
  ·
    refine ⟨52695597038672573383039697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140521592103126862354772525 52695597038672573383039697)
    ·
      refine ⟨39521697779004430037279773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52695597038672573383039697 39521697779004430037279773)
      ·
        refine ⟨14820636667126661263979915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39521697779004430037279773 14820636667126661263979915)
        ·
          refine ⟨22230955000689991895969873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14820636667126661263979915 22230955000689991895969873)
          ·
            refine ⟨16673216250517493921977405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22230955000689991895969873 16673216250517493921977405)
            ·
              refine ⟨6252456093944060220741527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16673216250517493921977405 6252456093944060220741527)
              ·
                refine ⟨9378684140916090331112291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6252456093944060220741527 9378684140916090331112291)
                ·
                  refine ⟨14068026211374135496668437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9378684140916090331112291 14068026211374135496668437)
                  ·
                    refine ⟨659438728658162601406333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14068026211374135496668437 659438728658162601406333)
                    ·
                      rfl

theorem cell23_3852757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_3852757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852757 prefixEnd_3852757 := by exact prefixLift 3852757
  have htrace : WordTrace (prefixWord ++ tailWord_3852757) baseStart_3852757 baseEnd_3852757 := by
    simpa [prefixWord, tailWord_3852757, baseEnd_3852757] using wordTrace_append hprefix tailTrace_3852757
  have hstable : (prefixWord ++ tailWord_3852757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852757).length < 2 ^ (prefixWord ++ tailWord_3852757).sum := by decide
  have hdescent : baseEnd_3852757 < baseStart_3852757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852854 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_3852854 : Nat := 118140960795 + 3852854 * 2 ^ 59
def prefixEnd_3852854 : Nat := 4983230072969 + 3 ^ 40 * 3852854 * 2
def baseEnd_3852854 : Nat := 1978365993597973924706053

theorem tailTrace_3852854 : CollatzResearch.WordTrace tailWord_3852854 prefixEnd_3852854 1978365993597973924706053 := by
  unfold tailWord_3852854
  simp only [CollatzResearch.WordTrace]
  refine ⟨8782820623985965495065851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93683419989183631947369077 8782820623985965495065851)
  ·
    refine ⟨13174230935978948242598777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8782820623985965495065851 13174230935978948242598777)
    ·
      refine ⟨9880673201984211181949083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13174230935978948242598777 9880673201984211181949083)
      ·
        refine ⟨14821009802976316772923625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9880673201984211181949083 14821009802976316772923625)
        ·
          refine ⟨11115757352232237579692719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14821009802976316772923625 11115757352232237579692719)
          ·
            refine ⟨16673636028348356369539079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11115757352232237579692719 16673636028348356369539079)
            ·
              refine ⟨25010454042522534554308619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16673636028348356369539079 25010454042522534554308619)
              ·
                refine ⟨37515681063783801831462929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25010454042522534554308619 37515681063783801831462929)
                ·
                  refine ⟨28136760797837851373597197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37515681063783801831462929 28136760797837851373597197)
                  ·
                    refine ⟨10551285299189194265098949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28136760797837851373597197 10551285299189194265098949)
                    ·
                      refine ⟨1978365993597973924706053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10551285299189194265098949 1978365993597973924706053)
                      ·
                        rfl

theorem cell23_3852854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_3852854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852854 prefixEnd_3852854 := by exact prefixLift 3852854
  have htrace : WordTrace (prefixWord ++ tailWord_3852854) baseStart_3852854 baseEnd_3852854 := by
    simpa [prefixWord, tailWord_3852854, baseEnd_3852854] using wordTrace_append hprefix tailTrace_3852854
  have hstable : (prefixWord ++ tailWord_3852854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852854).length < 2 ^ (prefixWord ++ tailWord_3852854).sum := by decide
  have hdescent : baseEnd_3852854 < baseStart_3852854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852857 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 1, 6, 3]
def baseStart_3852857 : Nat := 118140960795 + 3852857 * 2 ^ 59
def prefixEnd_3852857 : Nat := 4983230072969 + 3 ^ 40 * 3852857 * 2
def baseEnd_3852857 : Nat := 1978367534039937412968539

theorem tailTrace_3852857 : CollatzResearch.WordTrace tailWord_3852857 prefixEnd_3852857 1978367534039937412968539 := by
  unfold tailWord_3852857
  simp only [CollatzResearch.WordTrace]
  refine ⟨140525239402764579433412825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93683492935176386288941883 140525239402764579433412825)
  ·
    refine ⟨105393929552073434575059619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140525239402764579433412825 105393929552073434575059619)
    ·
      refine ⟨158090894328110151862589429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105393929552073434575059619 158090894328110151862589429)
      ·
        refine ⟨14821021343260326737117759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 158090894328110151862589429 14821021343260326737117759)
        ·
          refine ⟨22231532014890490105676639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14821021343260326737117759 22231532014890490105676639)
          ·
            refine ⟨33347298022335735158514959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22231532014890490105676639 33347298022335735158514959)
            ·
              refine ⟨50020947033503602737772439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33347298022335735158514959 50020947033503602737772439)
              ·
                refine ⟨75031420550255404106658659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50020947033503602737772439 75031420550255404106658659)
                ·
                  refine ⟨112547130825383106159987989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75031420550255404106658659 112547130825383106159987989)
                  ·
                    refine ⟨5275646757439833101249437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112547130825383106159987989 5275646757439833101249437)
                    ·
                      refine ⟨1978367534039937412968539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5275646757439833101249437 1978367534039937412968539)
                      ·
                        rfl

theorem cell23_3852857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_3852857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852857 prefixEnd_3852857 := by exact prefixLift 3852857
  have htrace : WordTrace (prefixWord ++ tailWord_3852857) baseStart_3852857 baseEnd_3852857 := by
    simpa [prefixWord, tailWord_3852857, baseEnd_3852857] using wordTrace_append hprefix tailTrace_3852857
  have hstable : (prefixWord ++ tailWord_3852857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852857).length < 2 ^ (prefixWord ++ tailWord_3852857).sum := by decide
  have hdescent : baseEnd_3852857 < baseStart_3852857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852871 : List Nat := [1, 1, 4, 1, 4, 2, 2, 1, 1, 4, 2]
def baseStart_3852871 : Nat := 118140960795 + 3852871 * 2 ^ 59
def prefixEnd_3852871 : Nat := 4983230072969 + 3 ^ 40 * 3852871 * 2
def baseEnd_3852871 : Nat := 1978374722769100358193475

theorem tailTrace_3852871 : CollatzResearch.WordTrace tailWord_3852871 prefixEnd_3852871 1978374722769100358193475 := by
  unfold tailWord_3852871
  simp only [CollatzResearch.WordTrace]
  refine ⟨140525750024713859824422467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93683833349809239882948311 140525750024713859824422467)
  ·
    refine ⟨210788625037070789736633701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140525750024713859824422467 210788625037070789736633701)
    ·
      refine ⟨39522867194450773075618819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210788625037070789736633701 39522867194450773075618819)
      ·
        refine ⟨59284300791676159613428229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39522867194450773075618819 59284300791676159613428229)
        ·
          refine ⟨11115806398439279927517793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59284300791676159613428229 11115806398439279927517793)
          ·
            refine ⟨8336854798829459945638345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11115806398439279927517793 8336854798829459945638345)
            ·
              refine ⟨6252641099122094959228759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8336854798829459945638345 6252641099122094959228759)
              ·
                refine ⟨9378961648683142438843139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6252641099122094959228759 9378961648683142438843139)
                ·
                  refine ⟨14068442473024713658264709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9378961648683142438843139 14068442473024713658264709)
                  ·
                    refine ⟨2637832963692133810924633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14068442473024713658264709 2637832963692133810924633)
                    ·
                      refine ⟨1978374722769100358193475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2637832963692133810924633 1978374722769100358193475)
                      ·
                        rfl

theorem cell23_3852871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 4, 2].length) (baseStart_3852871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852871 prefixEnd_3852871 := by exact prefixLift 3852871
  have htrace : WordTrace (prefixWord ++ tailWord_3852871) baseStart_3852871 baseEnd_3852871 := by
    simpa [prefixWord, tailWord_3852871, baseEnd_3852871] using wordTrace_append hprefix tailTrace_3852871
  have hstable : (prefixWord ++ tailWord_3852871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852871).length < 2 ^ (prefixWord ++ tailWord_3852871).sum := by decide
  have hdescent : baseEnd_3852871 < baseStart_3852871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852887 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 1, 5, 3]
def baseStart_3852887 : Nat := 118140960795 + 3852887 * 2 ^ 59
def prefixEnd_3852887 : Nat := 4983230072969 + 3 ^ 40 * 3852887 * 2
def baseEnd_3852887 : Nat := 1978382938459572295593401

theorem tailTrace_3852887 : CollatzResearch.WordTrace tailWord_3852887 prefixEnd_3852887 1978382938459572295593401 := by
  unfold tailWord_3852887
  simp only [CollatzResearch.WordTrace]
  refine ⟨140526333592655894557004915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93684222395103929704669943 140526333592655894557004915)
  ·
    refine ⟨210789500388983841835507373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140526333592655894557004915 210789500388983841835507373)
    ·
      refine ⟨79046062645868940688315265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210789500388983841835507373 79046062645868940688315265)
      ·
        refine ⟨59284546984401705516236449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79046062645868940688315265 59284546984401705516236449)
        ·
          refine ⟨44463410238301279137177337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59284546984401705516236449 44463410238301279137177337)
          ·
            refine ⟨33347557678725959352883003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44463410238301279137177337 33347557678725959352883003)
            ·
              refine ⟨50021336518088939029324505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33347557678725959352883003 50021336518088939029324505)
              ·
                refine ⟨37516002388566704271993379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50021336518088939029324505 37516002388566704271993379)
                ·
                  refine ⟨56274003582850056407990069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37516002388566704271993379 56274003582850056407990069)
                  ·
                    refine ⟨5275687835892192788249069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56274003582850056407990069 5275687835892192788249069)
                    ·
                      refine ⟨1978382938459572295593401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5275687835892192788249069 1978382938459572295593401)
                      ·
                        rfl

theorem cell23_3852887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_3852887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852887 prefixEnd_3852887 := by exact prefixLift 3852887
  have htrace : WordTrace (prefixWord ++ tailWord_3852887) baseStart_3852887 baseEnd_3852887 := by
    simpa [prefixWord, tailWord_3852887, baseEnd_3852887] using wordTrace_append hprefix tailTrace_3852887
  have hstable : (prefixWord ++ tailWord_3852887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852887).length < 2 ^ (prefixWord ++ tailWord_3852887).sum := by decide
  have hdescent : baseEnd_3852887 < baseStart_3852887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852892 : List Nat := [2, 2, 4, 1, 4, 1, 2, 1, 1, 3, 2]
def baseStart_3852892 : Nat := 118140960795 + 3852892 * 2 ^ 59
def prefixEnd_3852892 : Nat := 4983230072969 + 3 ^ 40 * 3852892 * 2
def baseEnd_3852892 : Nat := 1978385505862844776030879

theorem tailTrace_3852892 : CollatzResearch.WordTrace tailWord_3852892 prefixEnd_3852892 1978385505862844776030879 := by
  unfold tailWord_3852892
  simp only [CollatzResearch.WordTrace]
  refine ⟨70263257978818890205468465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93684343971758520273957953 70263257978818890205468465)
  ·
    refine ⟨52697443484114167654101349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70263257978818890205468465 52697443484114167654101349)
    ·
      refine ⟨9880770653271406435144003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52697443484114167654101349 9880770653271406435144003)
      ·
        refine ⟨14821155979907109652716005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9880770653271406435144003 14821155979907109652716005)
        ·
          refine ⟨2778966746232583059884251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14821155979907109652716005 2778966746232583059884251)
          ·
            refine ⟨4168450119348874589826377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2778966746232583059884251 4168450119348874589826377)
            ·
              refine ⟨3126337589511655942369783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4168450119348874589826377 3126337589511655942369783)
              ·
                refine ⟨4689506384267483913554675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3126337589511655942369783 4689506384267483913554675)
                ·
                  refine ⟨7034259576401225870332013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4689506384267483913554675 7034259576401225870332013)
                  ·
                    refine ⟨2637847341150459701374505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7034259576401225870332013 2637847341150459701374505)
                    ·
                      refine ⟨1978385505862844776030879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2637847341150459701374505 1978385505862844776030879)
                      ·
                        rfl

theorem cell23_3852892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_3852892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852892 prefixEnd_3852892 := by exact prefixLift 3852892
  have htrace : WordTrace (prefixWord ++ tailWord_3852892) baseStart_3852892 baseEnd_3852892 := by
    simpa [prefixWord, tailWord_3852892, baseEnd_3852892] using wordTrace_append hprefix tailTrace_3852892
  have hstable : (prefixWord ++ tailWord_3852892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852892).length < 2 ^ (prefixWord ++ tailWord_3852892).sum := by decide
  have hdescent : baseEnd_3852892 < baseStart_3852892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852927 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 4]
def baseStart_3852927 : Nat := 118140960795 + 3852927 * 2 ^ 59
def prefixEnd_3852927 : Nat := 4983230072969 + 3 ^ 40 * 3852927 * 2
def baseEnd_3852927 : Nat := 1978403477685752139093217

theorem tailTrace_3852927 : CollatzResearch.WordTrace tailWord_3852927 prefixEnd_3852927 1978403477685752139093217 := by
  unfold tailWord_3852927
  simp only [CollatzResearch.WordTrace]
  refine ⟨140527792512510981388461035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93685195008340654258974023 140527792512510981388461035)
  ·
    refine ⟨210791688768766472082691553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140527792512510981388461035 210791688768766472082691553)
    ·
      refine ⟨158093766576574854062018665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210791688768766472082691553 158093766576574854062018665)
      ·
        refine ⟨118570324932431140546513999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158093766576574854062018665 118570324932431140546513999)
        ·
          refine ⟨177855487398646710819770999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118570324932431140546513999 177855487398646710819770999)
          ·
            refine ⟨266783231097970066229656499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177855487398646710819770999 266783231097970066229656499)
            ·
              refine ⟨400174846646955099344484749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266783231097970066229656499 400174846646955099344484749)
              ·
                refine ⟨150065567492608162254181781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 400174846646955099344484749 150065567492608162254181781)
                ·
                  refine ⟨7034323476216007605664771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 150065567492608162254181781 7034323476216007605664771)
                  ·
                    refine ⟨10551485214324011408497157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7034323476216007605664771 10551485214324011408497157)
                    ·
                      refine ⟨1978403477685752139093217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10551485214324011408497157 1978403477685752139093217)
                      ·
                        rfl

theorem cell23_3852927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_3852927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852927 prefixEnd_3852927 := by exact prefixLift 3852927
  have htrace : WordTrace (prefixWord ++ tailWord_3852927) baseStart_3852927 baseEnd_3852927 := by
    simpa [prefixWord, tailWord_3852927, baseEnd_3852927] using wordTrace_append hprefix tailTrace_3852927
  have hstable : (prefixWord ++ tailWord_3852927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852927).length < 2 ^ (prefixWord ++ tailWord_3852927).sum := by decide
  have hdescent : baseEnd_3852927 < baseStart_3852927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852957 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 1, 3, 6]
def baseStart_3852957 : Nat := 118140960795 + 3852957 * 2 ^ 59
def prefixEnd_3852957 : Nat := 4983230072969 + 3 ^ 40 * 3852957 * 2
def baseEnd_3852957 : Nat := 1978418882105387021718079

theorem tailTrace_3852957 : CollatzResearch.WordTrace tailWord_3852957 prefixEnd_3852957 1978418882105387021718079 := by
  unfold tailWord_3852957
  simp only [CollatzResearch.WordTrace]
  refine ⟨140528886702402296512053125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93685924468268197674702083 140528886702402296512053125)
  ·
    refine ⟨26349166256700430596009961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140528886702402296512053125 26349166256700430596009961)
    ·
      refine ⟨19761874692525322947007471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26349166256700430596009961 19761874692525322947007471)
      ·
        refine ⟨29642812038787984420511207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19761874692525322947007471 29642812038787984420511207)
        ·
          refine ⟨44464218058181976630766811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29642812038787984420511207 44464218058181976630766811)
          ·
            refine ⟨66696327087272964946150217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44464218058181976630766811 66696327087272964946150217)
            ·
              refine ⟨50022245315454723709612663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66696327087272964946150217 50022245315454723709612663)
              ·
                refine ⟨75033367973182085564418995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50022245315454723709612663 75033367973182085564418995)
                ·
                  refine ⟨112550051959773128346628493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75033367973182085564418995 112550051959773128346628493)
                  ·
                    refine ⟨42206269484914923129985685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112550051959773128346628493 42206269484914923129985685)
                    ·
                      refine ⟨1978418882105387021718079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42206269484914923129985685 1978418882105387021718079)
                      ·
                        rfl

theorem cell23_3852957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_3852957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852957 prefixEnd_3852957 := by exact prefixLift 3852957
  have htrace : WordTrace (prefixWord ++ tailWord_3852957) baseStart_3852957 baseEnd_3852957 := by
    simpa [prefixWord, tailWord_3852957, baseEnd_3852957] using wordTrace_append hprefix tailTrace_3852957
  have hstable : (prefixWord ++ tailWord_3852957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852957).length < 2 ^ (prefixWord ++ tailWord_3852957).sum := by decide
  have hdescent : baseEnd_3852957 < baseStart_3852957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3852961 : List Nat := [1, 2, 3, 3, 3, 1, 1, 2, 2, 1, 4]
def baseStart_3852961 : Nat := 118140960795 + 3852961 * 2 ^ 59
def prefixEnd_3852961 : Nat := 4983230072969 + 3 ^ 40 * 3852961 * 2
def baseEnd_3852961 : Nat := 1978420936028005006068061

theorem tailTrace_3852961 : CollatzResearch.WordTrace tailWord_3852961 prefixEnd_3852961 1978420936028005006068061 := by
  unfold tailWord_3852961
  simp only [CollatzResearch.WordTrace]
  refine ⟨140529032594387805195198737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93686021729591870130132491 140529032594387805195198737)
  ·
    refine ⟨105396774445790853896399053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140529032594387805195198737 105396774445790853896399053)
    ·
      refine ⟨39523790417171570211149645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105396774445790853896399053 39523790417171570211149645)
      ·
        refine ⟨14821421406439338829181117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39523790417171570211149645 14821421406439338829181117)
        ·
          refine ⟨5558033027414752060942919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14821421406439338829181117 5558033027414752060942919)
          ·
            refine ⟨8337049541122128091414379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5558033027414752060942919 8337049541122128091414379)
            ·
              refine ⟨12505574311683192137121569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8337049541122128091414379 12505574311683192137121569)
              ·
                refine ⟨9379180733762394102841177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12505574311683192137121569 9379180733762394102841177)
                ·
                  refine ⟨7034385550321795577130883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9379180733762394102841177 7034385550321795577130883)
                  ·
                    refine ⟨10551578325482693365696325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7034385550321795577130883 10551578325482693365696325)
                    ·
                      refine ⟨1978420936028005006068061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10551578325482693365696325 1978420936028005006068061)
                      ·
                        rfl

theorem cell23_3852961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_3852961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3852961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3852961 prefixEnd_3852961 := by exact prefixLift 3852961
  have htrace : WordTrace (prefixWord ++ tailWord_3852961) baseStart_3852961 baseEnd_3852961 := by
    simpa [prefixWord, tailWord_3852961, baseEnd_3852961] using wordTrace_append hprefix tailTrace_3852961
  have hstable : (prefixWord ++ tailWord_3852961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3852961).length < 2 ^ (prefixWord ++ tailWord_3852961).sum := by decide
  have hdescent : baseEnd_3852961 < baseStart_3852961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3852961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853071 : List Nat := [1, 1, 2, 1, 1, 1, 7, 3, 1, 2, 3]
def baseStart_3853071 : Nat := 118140960795 + 3853071 * 2 ^ 59
def prefixEnd_3853071 : Nat := 4983230072969 + 3 ^ 40 * 3853071 * 2
def baseEnd_3853071 : Nat := 1978477418899999575692555

theorem tailTrace_3853071 : CollatzResearch.WordTrace tailWord_3853071 prefixEnd_3853071 1978477418899999575692555 := by
  unfold tailWord_3853071
  simp only [CollatzResearch.WordTrace]
  refine ⟨140533044623989293981703067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93688696415992862654468711 140533044623989293981703067)
  ·
    refine ⟨210799566935983940972554601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140533044623989293981703067 210799566935983940972554601)
    ·
      refine ⟨158099675201987955729415951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210799566935983940972554601 158099675201987955729415951)
      ·
        refine ⟨237149512802981933594123927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158099675201987955729415951 237149512802981933594123927)
        ·
          refine ⟨355724269204472900391185891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237149512802981933594123927 355724269204472900391185891)
          ·
            refine ⟨533586403806709350586778837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355724269204472900391185891 533586403806709350586778837)
            ·
              refine ⟨12505931339219750404377629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 533586403806709350586778837 12505931339219750404377629)
              ·
                refine ⟨4689724252207406401641611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12505931339219750404377629 4689724252207406401641611)
                ·
                  refine ⟨7034586378311109602462417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4689724252207406401641611 7034586378311109602462417)
                  ·
                    refine ⟨5275939783733332201846813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7034586378311109602462417 5275939783733332201846813)
                    ·
                      refine ⟨1978477418899999575692555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5275939783733332201846813 1978477418899999575692555)
                      ·
                        rfl

theorem cell23_3853071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 2, 3].length) (baseStart_3853071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853071 prefixEnd_3853071 := by exact prefixLift 3853071
  have htrace : WordTrace (prefixWord ++ tailWord_3853071) baseStart_3853071 baseEnd_3853071 := by
    simpa [prefixWord, tailWord_3853071, baseEnd_3853071] using wordTrace_append hprefix tailTrace_3853071
  have hstable : (prefixWord ++ tailWord_3853071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853071).length < 2 ^ (prefixWord ++ tailWord_3853071).sum := by decide
  have hdescent : baseEnd_3853071 < baseStart_3853071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853098 : List Nat := [3, 1, 4, 3, 1, 1, 1, 1, 1, 1, 6]
def baseStart_3853098 : Nat := 118140960795 + 3853098 * 2 ^ 59
def prefixEnd_3853098 : Nat := 4983230072969 + 3 ^ 40 * 3853098 * 2
def baseEnd_3853098 : Nat := 1978491282877670970054931

theorem tailTrace_3853098 : CollatzResearch.WordTrace tailWord_3853098 prefixEnd_3853098 1978491282877670970054931 := by
  unfold tailWord_3853098
  simp only [CollatzResearch.WordTrace]
  refine ⟨35133507348722869398233987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93689352929927651728623965 35133507348722869398233987)
  ·
    refine ⟨52700261023084304097350981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35133507348722869398233987 52700261023084304097350981)
    ·
      refine ⟨9881298941828307018253309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52700261023084304097350981 9881298941828307018253309)
      ·
        refine ⟨3705487103185615131844991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9881298941828307018253309 3705487103185615131844991)
        ·
          refine ⟨5558230654778422697767487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3705487103185615131844991 5558230654778422697767487)
          ·
            refine ⟨8337345982167634046651231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5558230654778422697767487 8337345982167634046651231)
            ·
              refine ⟨12506018973251451069976847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8337345982167634046651231 12506018973251451069976847)
              ·
                refine ⟨18759028459877176604965271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12506018973251451069976847 18759028459877176604965271)
                ·
                  refine ⟨28138542689815764907447907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18759028459877176604965271 28138542689815764907447907)
                  ·
                    refine ⟨42207814034723647361171861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28138542689815764907447907 42207814034723647361171861)
                    ·
                      refine ⟨1978491282877670970054931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42207814034723647361171861 1978491282877670970054931)
                      ·
                        rfl

theorem cell23_3853098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_3853098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853098 prefixEnd_3853098 := by exact prefixLift 3853098
  have htrace : WordTrace (prefixWord ++ tailWord_3853098) baseStart_3853098 baseEnd_3853098 := by
    simpa [prefixWord, tailWord_3853098, baseEnd_3853098] using wordTrace_append hprefix tailTrace_3853098
  have hstable : (prefixWord ++ tailWord_3853098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853098).length < 2 ^ (prefixWord ++ tailWord_3853098).sum := by decide
  have hdescent : baseEnd_3853098 < baseStart_3853098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853128 : List Nat := [2, 1, 3, 1, 1, 3, 1, 5, 1, 3, 2]
def baseStart_3853128 : Nat := 118140960795 + 3853128 * 2 ^ 59
def prefixEnd_3853128 : Nat := 4983230072969 + 3 ^ 40 * 3853128 * 2
def baseEnd_3853128 : Nat := 1978506687297305852679793

theorem tailTrace_3853128 : CollatzResearch.WordTrace tailWord_3853128 prefixEnd_3853128 1978506687297305852679793 := by
  unfold tailWord_3853128
  simp only [CollatzResearch.WordTrace]
  refine ⟨70267561792391396358264019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93690082389855195144352025 70267561792391396358264019)
  ·
    refine ⟨105401342688587094537396029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70267561792391396358264019 105401342688587094537396029)
    ·
      refine ⟨39525503508220160451523511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105401342688587094537396029 39525503508220160451523511)
      ·
        refine ⟨59288255262330240677285267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39525503508220160451523511 59288255262330240677285267)
        ·
          refine ⟨88932382893495361015927901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59288255262330240677285267 88932382893495361015927901)
          ·
            refine ⟨33349643585060760380972963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88932382893495361015927901 33349643585060760380972963)
            ·
              refine ⟨50024465377591140571459445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33349643585060760380972963 50024465377591140571459445)
              ·
                refine ⟨4689793629149169428574323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50024465377591140571459445 4689793629149169428574323)
                ·
                  refine ⟨7034690443723754142861485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4689793629149169428574323 7034690443723754142861485)
                  ·
                    refine ⟨2638008916396407803573057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7034690443723754142861485 2638008916396407803573057)
                    ·
                      refine ⟨1978506687297305852679793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2638008916396407803573057 1978506687297305852679793)
                      ·
                        rfl

theorem cell23_3853128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 1, 3, 2].length) (baseStart_3853128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853128 prefixEnd_3853128 := by exact prefixLift 3853128
  have htrace : WordTrace (prefixWord ++ tailWord_3853128) baseStart_3853128 baseEnd_3853128 := by
    simpa [prefixWord, tailWord_3853128, baseEnd_3853128] using wordTrace_append hprefix tailTrace_3853128
  have hstable : (prefixWord ++ tailWord_3853128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853128).length < 2 ^ (prefixWord ++ tailWord_3853128).sum := by decide
  have hdescent : baseEnd_3853128 < baseStart_3853128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853134 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 4, 6]
def baseStart_3853134 : Nat := 118140960795 + 3853134 * 2 ^ 59
def prefixEnd_3853134 : Nat := 4983230072969 + 3 ^ 40 * 3853134 * 2
def baseEnd_3853134 : Nat := 659503256060410943068255

theorem tailTrace_3853134 : CollatzResearch.WordTrace tailWord_3853134 prefixEnd_3853134 659503256060410943068255 := by
  unfold tailWord_3853134
  simp only [CollatzResearch.WordTrace]
  refine ⟨17566917802845131967655807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93690228281840703827497637 17566917802845131967655807)
  ·
    refine ⟨26350376704267697951483711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17566917802845131967655807 26350376704267697951483711)
    ·
      refine ⟨39525565056401546927225567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26350376704267697951483711 39525565056401546927225567)
      ·
        refine ⟨59288347584602320390838351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39525565056401546927225567 59288347584602320390838351)
        ·
          refine ⟨88932521376903480586257527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59288347584602320390838351 88932521376903480586257527)
          ·
            refine ⟨133398782065355220879386291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88932521376903480586257527 133398782065355220879386291)
            ·
              refine ⟨200098173098032831319079437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133398782065355220879386291 200098173098032831319079437)
              ·
                refine ⟨75036814911762311744654789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200098173098032831319079437 75036814911762311744654789)
                ·
                  refine ⟨14069402795955433452122773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75036814911762311744654789 14069402795955433452122773)
                  ·
                    refine ⟨659503256060410943068255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14069402795955433452122773 659503256060410943068255)
                    ·
                      rfl

theorem cell23_3853134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_3853134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853134 prefixEnd_3853134 := by exact prefixLift 3853134
  have htrace : WordTrace (prefixWord ++ tailWord_3853134) baseStart_3853134 baseEnd_3853134 := by
    simpa [prefixWord, tailWord_3853134, baseEnd_3853134] using wordTrace_append hprefix tailTrace_3853134
  have hstable : (prefixWord ++ tailWord_3853134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853134).length < 2 ^ (prefixWord ++ tailWord_3853134).sum := by decide
  have hdescent : baseEnd_3853134 < baseStart_3853134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853164 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 9]
def baseStart_3853164 : Nat := 118140960795 + 3853164 * 2 ^ 59
def prefixEnd_3853164 : Nat := 4983230072969 + 3 ^ 40 * 3853164 * 2
def baseEnd_3853164 : Nat := 219836130288985301314403

theorem tailTrace_3853164 : CollatzResearch.WordTrace tailWord_3853164 prefixEnd_3853164 219836130288985301314403 := by
  unfold tailWord_3853164
  simp only [CollatzResearch.WordTrace]
  refine ⟨70268218306326185432419273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93690957741768247243225697 70268218306326185432419273)
  ·
    refine ⟨52701163729744639074314455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70268218306326185432419273 52701163729744639074314455)
    ·
      refine ⟨79051745594616958611471683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52701163729744639074314455 79051745594616958611471683)
      ·
        refine ⟨118577618391925437917207525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79051745594616958611471683 118577618391925437917207525)
        ·
          refine ⟨22233303448486019609476411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118577618391925437917207525 22233303448486019609476411)
          ·
            refine ⟨33349955172729029414214617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22233303448486019609476411 33349955172729029414214617)
            ·
              refine ⟨25012466379546772060660963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33349955172729029414214617 25012466379546772060660963)
              ·
                refine ⟨37518699569320158090991445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25012466379546772060660963 37518699569320158090991445)
                ·
                  refine ⟨219836130288985301314403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37518699569320158090991445 219836130288985301314403)
                  ·
                    rfl

theorem cell23_3853164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 9].length) (baseStart_3853164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853164 prefixEnd_3853164 := by exact prefixLift 3853164
  have htrace : WordTrace (prefixWord ++ tailWord_3853164) baseStart_3853164 baseEnd_3853164 := by
    simpa [prefixWord, tailWord_3853164, baseEnd_3853164] using wordTrace_append hprefix tailTrace_3853164
  have hstable : (prefixWord ++ tailWord_3853164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853164).length < 2 ^ (prefixWord ++ tailWord_3853164).sum := by decide
  have hdescent : baseEnd_3853164 < baseStart_3853164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853192 : List Nat := [2, 1, 3, 3, 2, 2, 2, 2, 2, 2, 2]
def baseStart_3853192 : Nat := 118140960795 + 3853192 * 2 ^ 59
def prefixEnd_3853192 : Nat := 4983230072969 + 3 ^ 40 * 3853192 * 2
def baseEnd_3853192 : Nat := 1978539550059193602279499

theorem tailTrace_3853192 : CollatzResearch.WordTrace tailWord_3853192 prefixEnd_3853192 1978539550059193602279499 := by
  unfold tailWord_3853192
  simp only [CollatzResearch.WordTrace]
  refine ⟨70268728928275465823428915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93691638571033954431238553 70268728928275465823428915)
  ·
    refine ⟨105403093392413198735143373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70268728928275465823428915 105403093392413198735143373)
    ·
      refine ⟨39526160022154949525678765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105403093392413198735143373 39526160022154949525678765)
      ·
        refine ⟨14822310008308106072129537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39526160022154949525678765 14822310008308106072129537)
        ·
          refine ⟨11116732506231079554097153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14822310008308106072129537 11116732506231079554097153)
          ·
            refine ⟨8337549379673309665572865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11116732506231079554097153 8337549379673309665572865)
            ·
              refine ⟨6253162034754982249179649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8337549379673309665572865 6253162034754982249179649)
              ·
                refine ⟨4689871526066236686884737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6253162034754982249179649 4689871526066236686884737)
                ·
                  refine ⟨3517403644549677515163553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4689871526066236686884737 3517403644549677515163553)
                  ·
                    refine ⟨2638052733412258136372665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3517403644549677515163553 2638052733412258136372665)
                    ·
                      refine ⟨1978539550059193602279499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2638052733412258136372665 1978539550059193602279499)
                      ·
                        rfl

theorem cell23_3853192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_3853192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853192 prefixEnd_3853192 := by exact prefixLift 3853192
  have htrace : WordTrace (prefixWord ++ tailWord_3853192) baseStart_3853192 baseEnd_3853192 := by
    simpa [prefixWord, tailWord_3853192, baseEnd_3853192] using wordTrace_append hprefix tailTrace_3853192
  have hstable : (prefixWord ++ tailWord_3853192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853192).length < 2 ^ (prefixWord ++ tailWord_3853192).sum := by decide
  have hdescent : baseEnd_3853192 < baseStart_3853192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853231 : List Nat := [1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 4]
def baseStart_3853231 : Nat := 118140960795 + 3853231 * 2 ^ 59
def prefixEnd_3853231 : Nat := 4983230072969 + 3 ^ 40 * 3853231 * 2
def baseEnd_3853231 : Nat := 1978559575804718949691819

theorem tailTrace_3853231 : CollatzResearch.WordTrace tailWord_3853231 prefixEnd_3853231 1978559575804718949691819 := by
  unfold tailWord_3853231
  simp only [CollatzResearch.WordTrace]
  refine ⟨140538880303409641307527547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93692586868939760871685031 140538880303409641307527547)
  ·
    refine ⟨210808320455114461961291321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140538880303409641307527547 210808320455114461961291321)
    ·
      refine ⟨158106240341335846470968491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210808320455114461961291321 158106240341335846470968491)
      ·
        refine ⟨237159360512003769706452737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158106240341335846470968491 237159360512003769706452737)
        ·
          refine ⟨177869520384002827279839553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237159360512003769706452737 177869520384002827279839553)
          ·
            refine ⟨133402140288002120459879665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177869520384002827279839553 133402140288002120459879665)
            ·
              refine ⟨100051605216001590344909749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133402140288002120459879665 100051605216001590344909749)
              ·
                refine ⟨9379837989000149094835289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100051605216001590344909749 9379837989000149094835289)
                ·
                  refine ⟨7034878491750111821126467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9379837989000149094835289 7034878491750111821126467)
                  ·
                    refine ⟨10552317737625167731689701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7034878491750111821126467 10552317737625167731689701)
                    ·
                      refine ⟨1978559575804718949691819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10552317737625167731689701 1978559575804718949691819)
                      ·
                        rfl

theorem cell23_3853231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 4].length) (baseStart_3853231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853231 prefixEnd_3853231 := by exact prefixLift 3853231
  have htrace : WordTrace (prefixWord ++ tailWord_3853231) baseStart_3853231 baseEnd_3853231 := by
    simpa [prefixWord, tailWord_3853231, baseEnd_3853231] using wordTrace_append hprefix tailTrace_3853231
  have hstable : (prefixWord ++ tailWord_3853231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853231).length < 2 ^ (prefixWord ++ tailWord_3853231).sum := by decide
  have hdescent : baseEnd_3853231 < baseStart_3853231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853248 : List Nat := [2, 1, 1, 2, 3, 3, 1, 2, 2, 4, 2]
def baseStart_3853248 : Nat := 118140960795 + 3853248 * 2 ^ 59
def prefixEnd_3853248 : Nat := 4983230072969 + 3 ^ 40 * 3853248 * 2
def baseEnd_3853248 : Nat := 1978568304975845383179241

theorem tailTrace_3853248 : CollatzResearch.WordTrace tailWord_3853248 prefixEnd_3853248 1978568304975845383179241 := by
  unfold tailWord_3853248
  simp only [CollatzResearch.WordTrace]
  refine ⟨70269750172174026605448199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93693000229565368807264265 70269750172174026605448199)
  ·
    refine ⟨105404625258261039908172299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70269750172174026605448199 105404625258261039908172299)
    ·
      refine ⟨158106937887391559862258449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105404625258261039908172299 158106937887391559862258449)
      ·
        refine ⟨118580203415543669896693837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158106937887391559862258449 118580203415543669896693837)
        ·
          refine ⟨44467576280828876211260189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118580203415543669896693837 44467576280828876211260189)
          ·
            refine ⟨16675341105310828579222571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44467576280828876211260189 16675341105310828579222571)
            ·
              refine ⟨25013011657966242868833857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16675341105310828579222571 25013011657966242868833857)
              ·
                refine ⟨18759758743474682151625393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25013011657966242868833857 18759758743474682151625393)
                ·
                  refine ⟨14069819057606011613719045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18759758743474682151625393 14069819057606011613719045)
                  ·
                    refine ⟨2638091073301127177572321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14069819057606011613719045 2638091073301127177572321)
                    ·
                      refine ⟨1978568304975845383179241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2638091073301127177572321 1978568304975845383179241)
                      ·
                        rfl

theorem cell23_3853248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 2, 4, 2].length) (baseStart_3853248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853248 prefixEnd_3853248 := by exact prefixLift 3853248
  have htrace : WordTrace (prefixWord ++ tailWord_3853248) baseStart_3853248 baseEnd_3853248 := by
    simpa [prefixWord, tailWord_3853248, baseEnd_3853248] using wordTrace_append hprefix tailTrace_3853248
  have hstable : (prefixWord ++ tailWord_3853248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853248).length < 2 ^ (prefixWord ++ tailWord_3853248).sum := by decide
  have hdescent : baseEnd_3853248 < baseStart_3853248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853268 : List Nat := [2, 4, 1, 2, 1, 2, 1, 2, 1, 4, 3]
def baseStart_3853268 : Nat := 118140960795 + 3853268 * 2 ^ 59
def prefixEnd_3853268 : Nat := 4983230072969 + 3 ^ 40 * 3853268 * 2
def baseEnd_3853268 : Nat := 1978578574588935304929149

theorem tailTrace_3853268 : CollatzResearch.WordTrace tailWord_3853268 prefixEnd_3853268 1978578574588935304929149 := by
  unfold tailWord_3853268
  simp only [CollatzResearch.WordTrace]
  refine ⟨70270114902137798313312229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93693486536183731084416305 70270114902137798313312229)
  ·
    refine ⟨13175646544150837183746043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70270114902137798313312229 13175646544150837183746043)
    ·
      refine ⟨19763469816226255775619065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13175646544150837183746043 19763469816226255775619065)
      ·
        refine ⟨14822602362169691831714299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19763469816226255775619065 14822602362169691831714299)
        ·
          refine ⟨22233903543254537747571449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14822602362169691831714299 22233903543254537747571449)
          ·
            refine ⟨16675427657440903310678587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22233903543254537747571449 16675427657440903310678587)
            ·
              refine ⟨25013141486161354966017881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16675427657440903310678587 25013141486161354966017881)
              ·
                refine ⟨18759856114621016224513411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25013141486161354966017881 18759856114621016224513411)
                ·
                  refine ⟨28139784171931524336770117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18759856114621016224513411 28139784171931524336770117)
                  ·
                    refine ⟨5276209532237160813144397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28139784171931524336770117 5276209532237160813144397)
                    ·
                      refine ⟨1978578574588935304929149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5276209532237160813144397 1978578574588935304929149)
                      ·
                        rfl

theorem cell23_3853268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_3853268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853268 prefixEnd_3853268 := by exact prefixLift 3853268
  have htrace : WordTrace (prefixWord ++ tailWord_3853268) baseStart_3853268 baseEnd_3853268 := by
    simpa [prefixWord, tailWord_3853268, baseEnd_3853268] using wordTrace_append hprefix tailTrace_3853268
  have hstable : (prefixWord ++ tailWord_3853268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853268).length < 2 ^ (prefixWord ++ tailWord_3853268).sum := by decide
  have hdescent : baseEnd_3853268 < baseStart_3853268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853281 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 1, 7, 3]
def baseStart_3853281 : Nat := 118140960795 + 3853281 * 2 ^ 59
def prefixEnd_3853281 : Nat := 4983230072969 + 3 ^ 40 * 3853281 * 2
def baseEnd_3853281 : Nat := 1978585249837443754066589

theorem tailTrace_3853281 : CollatzResearch.WordTrace tailWord_3853281 prefixEnd_3853281 1978585249837443754066589 := by
  unfold tailWord_3853281
  simp only [CollatzResearch.WordTrace]
  refine ⟨140540703953228499846847697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93693802635485666564565131 140540703953228499846847697)
  ·
    refine ⟨105405527964921374885135773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140540703953228499846847697 105405527964921374885135773)
    ·
      refine ⟨39527072986845515581925915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105405527964921374885135773 39527072986845515581925915)
      ·
        refine ⟨59290609480268273372888873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39527072986845515581925915 59290609480268273372888873)
        ·
          refine ⟨44467957110201205029666655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59290609480268273372888873 44467957110201205029666655)
          ·
            refine ⟨66701935665301807544499983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44467957110201205029666655 66701935665301807544499983)
            ·
              refine ⟨100052903497952711316749975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66701935665301807544499983 100052903497952711316749975)
              ·
                refine ⟨150079355246929066975124963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100052903497952711316749975 150079355246929066975124963)
                ·
                  refine ⟨225119032870393600462687445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150079355246929066975124963 225119032870393600462687445)
                  ·
                    refine ⟨5276227332899850010844237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 225119032870393600462687445 5276227332899850010844237)
                    ·
                      refine ⟨1978585249837443754066589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5276227332899850010844237 1978585249837443754066589)
                      ·
                        rfl

theorem cell23_3853281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_3853281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853281 prefixEnd_3853281 := by exact prefixLift 3853281
  have htrace : WordTrace (prefixWord ++ tailWord_3853281) baseStart_3853281 baseEnd_3853281 := by
    simpa [prefixWord, tailWord_3853281, baseEnd_3853281] using wordTrace_append hprefix tailTrace_3853281
  have hstable : (prefixWord ++ tailWord_3853281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853281).length < 2 ^ (prefixWord ++ tailWord_3853281).sum := by decide
  have hdescent : baseEnd_3853281 < baseStart_3853281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853331 : List Nat := [1, 1, 1, 2, 1, 4, 1, 5, 1, 6]
def baseStart_3853331 : Nat := 118140960795 + 3853331 * 2 ^ 59
def prefixEnd_3853331 : Nat := 4983230072969 + 3 ^ 40 * 3853331 * 2
def baseEnd_3853331 : Nat := 659536974623389519480453

theorem tailTrace_3853331 : CollatzResearch.WordTrace tailWord_3853331 prefixEnd_3853331 659536974623389519480453 := by
  unfold tailWord_3853331
  simp only [CollatzResearch.WordTrace]
  refine ⟨140542527603047358386167847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93695018402031572257445231 140542527603047358386167847)
  ·
    refine ⟨210813791404571037579251771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140542527603047358386167847 210813791404571037579251771)
    ·
      refine ⟨316220687106856556368877657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210813791404571037579251771 316220687106856556368877657)
      ·
        refine ⟨237165515330142417276658243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316220687106856556368877657 237165515330142417276658243)
        ·
          refine ⟨355748272995213625914987365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237165515330142417276658243 355748272995213625914987365)
          ·
            refine ⟨66702801186602554859060131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 355748272995213625914987365 66702801186602554859060131)
            ·
              refine ⟨100054201779903832288590197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66702801186602554859060131 100054201779903832288590197)
              ·
                refine ⟨9380081416865984277055331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100054201779903832288590197 9380081416865984277055331)
                ·
                  refine ⟨14070122125298976415582997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9380081416865984277055331 14070122125298976415582997)
                  ·
                    refine ⟨659536974623389519480453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14070122125298976415582997 659536974623389519480453)
                    ·
                      rfl

theorem cell23_3853331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 6].length) (baseStart_3853331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853331 prefixEnd_3853331 := by exact prefixLift 3853331
  have htrace : WordTrace (prefixWord ++ tailWord_3853331) baseStart_3853331 baseEnd_3853331 := by
    simpa [prefixWord, tailWord_3853331, baseEnd_3853331] using wordTrace_append hprefix tailTrace_3853331
  have hstable : (prefixWord ++ tailWord_3853331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853331).length < 2 ^ (prefixWord ++ tailWord_3853331).sum := by decide
  have hdescent : baseEnd_3853331 < baseStart_3853331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853335 : List Nat := [1, 1, 3, 5, 1, 1, 3, 2, 1, 5]
def baseStart_3853335 : Nat := 118140960795 + 3853335 * 2 ^ 59
def prefixEnd_3853335 : Nat := 4983230072969 + 3 ^ 40 * 3853335 * 2
def baseEnd_3853335 : Nat := 659537659264262180930447

theorem tailTrace_3853335 : CollatzResearch.WordTrace tailWord_3853335 prefixEnd_3853335 659537659264262180930447 := by
  unfold tailWord_3853335
  simp only [CollatzResearch.WordTrace]
  refine ⟨140542673495032867069313459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93695115663355244712875639 140542673495032867069313459)
  ·
    refine ⟨210814010242549300603970189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140542673495032867069313459 210814010242549300603970189)
    ·
      refine ⟨79055253840955987726488821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210814010242549300603970189 79055253840955987726488821)
      ·
        refine ⟨7411430047589623849358327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79055253840955987726488821 7411430047589623849358327)
        ·
          refine ⟨11117145071384435774037491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7411430047589623849358327 11117145071384435774037491)
          ·
            refine ⟨16675717607076653661056237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11117145071384435774037491 16675717607076653661056237)
            ·
              refine ⟨6253394102653745122896089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16675717607076653661056237 6253394102653745122896089)
              ·
                refine ⟨4690045576990308842172067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6253394102653745122896089 4690045576990308842172067)
                ·
                  refine ⟨7035068365485463263258101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4690045576990308842172067 7035068365485463263258101)
                  ·
                    refine ⟨659537659264262180930447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7035068365485463263258101 659537659264262180930447)
                    ·
                      rfl

theorem cell23_3853335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 5].length) (baseStart_3853335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853335 prefixEnd_3853335 := by exact prefixLift 3853335
  have htrace : WordTrace (prefixWord ++ tailWord_3853335) baseStart_3853335 baseEnd_3853335 := by
    simpa [prefixWord, tailWord_3853335, baseEnd_3853335] using wordTrace_append hprefix tailTrace_3853335
  have hstable : (prefixWord ++ tailWord_3853335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853335).length < 2 ^ (prefixWord ++ tailWord_3853335).sum := by decide
  have hdescent : baseEnd_3853335 < baseStart_3853335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853338 : List Nat := [3, 1, 1, 3, 1, 2, 3, 1, 3, 1, 4]
def baseStart_3853338 : Nat := 118140960795 + 3853338 * 2 ^ 59
def prefixEnd_3853338 : Nat := 4983230072969 + 3 ^ 40 * 3853338 * 2
def baseEnd_3853338 : Nat := 1978614518234750031053827

theorem tailTrace_3853338 : CollatzResearch.WordTrace tailWord_3853338 prefixEnd_3853338 1978614518234750031053827 := by
  unfold tailWord_3853338
  simp only [CollatzResearch.WordTrace]
  refine ⟨35135695728505499645418167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93695188609347999054448445 35135695728505499645418167)
  ·
    refine ⟨52703543592758249468127251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35135695728505499645418167 52703543592758249468127251)
    ·
      refine ⟨79055315389137374202190877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52703543592758249468127251 79055315389137374202190877)
      ·
        refine ⟨29645743270926515325821579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79055315389137374202190877 29645743270926515325821579)
        ·
          refine ⟨44468614906389772988732369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29645743270926515325821579 44468614906389772988732369)
          ·
            refine ⟨33351461179792329741549277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44468614906389772988732369 33351461179792329741549277)
            ·
              refine ⟨12506797942422123653080979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33351461179792329741549277 12506797942422123653080979)
              ·
                refine ⟨18760196913633185479621469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12506797942422123653080979 18760196913633185479621469)
                ·
                  refine ⟨7035073842612444554858051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18760196913633185479621469 7035073842612444554858051)
                  ·
                    refine ⟨10552610763918666832287077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7035073842612444554858051 10552610763918666832287077)
                    ·
                      refine ⟨1978614518234750031053827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10552610763918666832287077 1978614518234750031053827)
                      ·
                        rfl

theorem cell23_3853338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_3853338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853338 prefixEnd_3853338 := by exact prefixLift 3853338
  have htrace : WordTrace (prefixWord ++ tailWord_3853338) baseStart_3853338 baseEnd_3853338 := by
    simpa [prefixWord, tailWord_3853338, baseEnd_3853338] using wordTrace_append hprefix tailTrace_3853338
  have hstable : (prefixWord ++ tailWord_3853338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853338).length < 2 ^ (prefixWord ++ tailWord_3853338).sum := by decide
  have hdescent : baseEnd_3853338 < baseStart_3853338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853348 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 3, 6]
def baseStart_3853348 : Nat := 118140960795 + 3853348 * 2 ^ 59
def prefixEnd_3853348 : Nat := 4983230072969 + 3 ^ 40 * 3853348 * 2
def baseEnd_3853348 : Nat := 659539884347098330642927

theorem tailTrace_3853348 : CollatzResearch.WordTrace tailWord_3853348 prefixEnd_3853348 659539884347098330642927 := by
  unfold tailWord_3853348
  simp only [CollatzResearch.WordTrace]
  refine ⟨70271573821992885144768349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93695431762657180193024465 70271573821992885144768349)
  ·
    refine ⟨26351840183247331929288131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70271573821992885144768349 26351840183247331929288131)
    ·
      refine ⟨39527760274870997893932197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26351840183247331929288131 39527760274870997893932197)
      ·
        refine ⟨7411455051538312105112287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39527760274870997893932197 7411455051538312105112287)
        ·
          refine ⟨11117182577307468157668431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7411455051538312105112287 11117182577307468157668431)
          ·
            refine ⟨16675773865961202236502647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11117182577307468157668431 16675773865961202236502647)
            ·
              refine ⟨25013660798941803354753971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16675773865961202236502647 25013660798941803354753971)
              ·
                refine ⟨37520491198412705032130957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25013660798941803354753971 37520491198412705032130957)
                ·
                  refine ⟨14070184199404764387049109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37520491198412705032130957 14070184199404764387049109)
                  ·
                    refine ⟨659539884347098330642927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14070184199404764387049109 659539884347098330642927)
                    ·
                      rfl

theorem cell23_3853348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_3853348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853348 prefixEnd_3853348 := by exact prefixLift 3853348
  have htrace : WordTrace (prefixWord ++ tailWord_3853348) baseStart_3853348 baseEnd_3853348 := by
    simpa [prefixWord, tailWord_3853348, baseEnd_3853348] using wordTrace_append hprefix tailTrace_3853348
  have hstable : (prefixWord ++ tailWord_3853348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853348).length < 2 ^ (prefixWord ++ tailWord_3853348).sum := by decide
  have hdescent : baseEnd_3853348 < baseStart_3853348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853355 : List Nat := [1, 1, 1, 1, 2, 1, 9, 1, 1, 1, 4]
def baseStart_3853355 : Nat := 118140960795 + 3853355 * 2 ^ 59
def prefixEnd_3853355 : Nat := 4983230072969 + 3 ^ 40 * 3853355 * 2
def baseEnd_3853355 : Nat := 1978623247405876464541249

theorem tailTrace_3853355 : CollatzResearch.WordTrace tailWord_3853355 prefixEnd_3853355 1978623247405876464541249 := by
  unfold tailWord_3853355
  simp only [CollatzResearch.WordTrace]
  refine ⟨140543402954960410485041519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93695601969973606990027679 140543402954960410485041519)
  ·
    refine ⟨210815104432440615727562279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140543402954960410485041519 210815104432440615727562279)
    ·
      refine ⟨316222656648660923591343419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210815104432440615727562279 316222656648660923591343419)
      ·
        refine ⟨474333984972991385387015129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316222656648660923591343419 474333984972991385387015129)
        ·
          refine ⟨355750488729743539040261347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 474333984972991385387015129 355750488729743539040261347)
          ·
            refine ⟨533625733094615308560392021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355750488729743539040261347 533625733094615308560392021)
            ·
              refine ⟨3126713279851261573596047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 533625733094615308560392021 3126713279851261573596047)
              ·
                refine ⟨4690069919776892360394071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3126713279851261573596047 4690069919776892360394071)
                ·
                  refine ⟨7035104879665338540591107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4690069919776892360394071 7035104879665338540591107)
                  ·
                    refine ⟨10552657319498007810886661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7035104879665338540591107 10552657319498007810886661)
                    ·
                      refine ⟨1978623247405876464541249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10552657319498007810886661 1978623247405876464541249)
                      ·
                        rfl

theorem cell23_3853355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 1, 1, 4].length) (baseStart_3853355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853355 prefixEnd_3853355 := by exact prefixLift 3853355
  have htrace : WordTrace (prefixWord ++ tailWord_3853355) baseStart_3853355 baseEnd_3853355 := by
    simpa [prefixWord, tailWord_3853355, baseEnd_3853355] using wordTrace_append hprefix tailTrace_3853355
  have hstable : (prefixWord ++ tailWord_3853355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853355).length < 2 ^ (prefixWord ++ tailWord_3853355).sum := by decide
  have hdescent : baseEnd_3853355 < baseStart_3853355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853366 : List Nat := [5, 1, 2, 1, 1, 2, 4, 2, 1, 1, 3]
def baseStart_3853366 : Nat := 118140960795 + 3853366 * 2 ^ 59
def prefixEnd_3853366 : Nat := 4983230072969 + 3 ^ 40 * 3853366 * 2
def baseEnd_3853366 : Nat := 1978628895693075921503699

theorem tailTrace_3853366 : CollatzResearch.WordTrace tailWord_3853366 prefixEnd_3853366 1978628895693075921503699 := by
  unfold tailWord_3853366
  simp only [CollatzResearch.WordTrace]
  refine ⟨8783987759870034960230747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93695869438613706242461301 8783987759870034960230747)
  ·
    refine ⟨13175981639805052440346121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8783987759870034960230747 13175981639805052440346121)
    ·
      refine ⟨9881986229853789330259591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13175981639805052440346121 9881986229853789330259591)
      ·
        refine ⟨14822979344780683995389387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9881986229853789330259591 14822979344780683995389387)
        ·
          refine ⟨22234469017171025993084081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14822979344780683995389387 22234469017171025993084081)
          ·
            refine ⟨16675851762878269494813061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22234469017171025993084081 16675851762878269494813061)
            ·
              refine ⟨3126722205539675530277449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16675851762878269494813061 3126722205539675530277449)
              ·
                refine ⟨2345041654154756647708087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3126722205539675530277449 2345041654154756647708087)
                ·
                  refine ⟨3517562481232134971562131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2345041654154756647708087 3517562481232134971562131)
                  ·
                    refine ⟨5276343721848202457343197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3517562481232134971562131 5276343721848202457343197)
                    ·
                      refine ⟨1978628895693075921503699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5276343721848202457343197 1978628895693075921503699)
                      ·
                        rfl

theorem cell23_3853366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_3853366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853366 prefixEnd_3853366 := by exact prefixLift 3853366
  have htrace : WordTrace (prefixWord ++ tailWord_3853366) baseStart_3853366 baseEnd_3853366 := by
    simpa [prefixWord, tailWord_3853366, baseEnd_3853366] using wordTrace_append hprefix tailTrace_3853366
  have hstable : (prefixWord ++ tailWord_3853366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853366).length < 2 ^ (prefixWord ++ tailWord_3853366).sum := by decide
  have hdescent : baseEnd_3853366 < baseStart_3853366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853381 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 2, 2, 6]
def baseStart_3853381 : Nat := 118140960795 + 3853381 * 2 ^ 59
def prefixEnd_3853381 : Nat := 4983230072969 + 3 ^ 40 * 3853381 * 2
def baseEnd_3853381 : Nat := 1978636597902893362816129

theorem tailTrace_3853381 : CollatzResearch.WordTrace tailWord_3853381 prefixEnd_3853381 1978636597902893362816129 := by
  unfold tailWord_3853381
  simp only [CollatzResearch.WordTrace]
  refine ⟨140544351252866216925487997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93696234168577477950325331 140544351252866216925487997)
  ·
    refine ⟨52704131719824831347057999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140544351252866216925487997 52704131719824831347057999)
    ·
      refine ⟨79056197579737247020586999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52704131719824831347057999 79056197579737247020586999)
      ·
        refine ⟨118584296369605870530880499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79056197579737247020586999 118584296369605870530880499)
        ·
          refine ⟨177876444554408805796320749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118584296369605870530880499 177876444554408805796320749)
          ·
            refine ⟨66703666707903302173620281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177876444554408805796320749 66703666707903302173620281)
            ·
              refine ⟨50027750030927476630215211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66703666707903302173620281 50027750030927476630215211)
              ·
                refine ⟨75041625046391214945322817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50027750030927476630215211 75041625046391214945322817)
                ·
                  refine ⟨56281218784793411208992113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75041625046391214945322817 56281218784793411208992113)
                  ·
                    refine ⟨42210914088595058406744085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56281218784793411208992113 42210914088595058406744085)
                    ·
                      refine ⟨1978636597902893362816129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42210914088595058406744085 1978636597902893362816129)
                      ·
                        rfl

theorem cell23_3853381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_3853381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853381 prefixEnd_3853381 := by exact prefixLift 3853381
  have htrace : WordTrace (prefixWord ++ tailWord_3853381) baseStart_3853381 baseEnd_3853381 := by
    simpa [prefixWord, tailWord_3853381, baseEnd_3853381] using wordTrace_append hprefix tailTrace_3853381
  have hstable : (prefixWord ++ tailWord_3853381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853381).length < 2 ^ (prefixWord ++ tailWord_3853381).sum := by decide
  have hdescent : baseEnd_3853381 < baseStart_3853381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853382 : List Nat := [6, 1, 1, 1, 1, 3, 2, 1, 1, 6]
def baseStart_3853382 : Nat := 118140960795 + 3853382 * 2 ^ 59
def prefixEnd_3853382 : Nat := 4983230072969 + 3 ^ 40 * 3853382 * 2
def baseEnd_3853382 : Nat := 659545703794515952967875

theorem tailTrace_3853382 : CollatzResearch.WordTrace tailWord_3853382 prefixEnd_3853382 659545703794515952967875 := by
  unfold tailWord_3853382
  simp only [CollatzResearch.WordTrace]
  refine ⟨4392012116433206065508575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 93696258483908396064182933 4392012116433206065508575)
  ·
    refine ⟨6588018174649809098262863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4392012116433206065508575 6588018174649809098262863)
    ·
      refine ⟨9882027261974713647394295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6588018174649809098262863 9882027261974713647394295)
      ·
        refine ⟨14823040892962070471091443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9882027261974713647394295 14823040892962070471091443)
        ·
          refine ⟨22234561339443105706637165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14823040892962070471091443 22234561339443105706637165)
          ·
            refine ⟨8337960502291164639988937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22234561339443105706637165 8337960502291164639988937)
            ·
              refine ⟨6253470376718373479991703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8337960502291164639988937 6253470376718373479991703)
              ·
                refine ⟨9380205565077560219987555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6253470376718373479991703 9380205565077560219987555)
                ·
                  refine ⟨14070308347616340329981333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9380205565077560219987555 14070308347616340329981333)
                  ·
                    refine ⟨659545703794515952967875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14070308347616340329981333 659545703794515952967875)
                    ·
                      rfl

theorem cell23_3853382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_3853382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853382 prefixEnd_3853382 := by exact prefixLift 3853382
  have htrace : WordTrace (prefixWord ++ tailWord_3853382) baseStart_3853382 baseEnd_3853382 := by
    simpa [prefixWord, tailWord_3853382, baseEnd_3853382] using wordTrace_append hprefix tailTrace_3853382
  have hstable : (prefixWord ++ tailWord_3853382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853382).length < 2 ^ (prefixWord ++ tailWord_3853382).sum := by decide
  have hdescent : baseEnd_3853382 < baseStart_3853382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853389 : List Nat := [1, 6, 1, 1, 1, 3, 1, 2, 3, 2, 2]
def baseStart_3853389 : Nat := 118140960795 + 3853389 * 2 ^ 59
def prefixEnd_3853389 : Nat := 4983230072969 + 3 ^ 40 * 3853389 * 2
def baseEnd_3853389 : Nat := 1978640705748129331516093

theorem tailTrace_3853389 : CollatzResearch.WordTrace tailWord_3853389 prefixEnd_3853389 1978640705748129331516093 := by
  unfold tailWord_3853389
  simp only [CollatzResearch.WordTrace]
  refine ⟨140544643036837234291779221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93696428691224822861186147 140544643036837234291779221)
  ·
    refine ⟨6588030142351745357427151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 140544643036837234291779221 6588030142351745357427151)
    ·
      refine ⟨9882045213527618036140727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6588030142351745357427151 9882045213527618036140727)
      ·
        refine ⟨14823067820291427054211091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9882045213527618036140727 14823067820291427054211091)
        ·
          refine ⟨22234601730437140581316637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14823067820291427054211091 22234601730437140581316637)
          ·
            refine ⟨8337975648913927717993739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22234601730437140581316637 8337975648913927717993739)
            ·
              refine ⟨12506963473370891576990609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8337975648913927717993739 12506963473370891576990609)
              ·
                refine ⟨9380222605028168682742957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12506963473370891576990609 9380222605028168682742957)
                ·
                  refine ⟨3517583476885563256028609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9380222605028168682742957 3517583476885563256028609)
                  ·
                    refine ⟨2638187607664172442021457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3517583476885563256028609 2638187607664172442021457)
                    ·
                      refine ⟨1978640705748129331516093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2638187607664172442021457 1978640705748129331516093)
                      ·
                        rfl

theorem cell23_3853389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_3853389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853389 prefixEnd_3853389 := by exact prefixLift 3853389
  have htrace : WordTrace (prefixWord ++ tailWord_3853389) baseStart_3853389 baseEnd_3853389 := by
    simpa [prefixWord, tailWord_3853389, baseEnd_3853389] using wordTrace_append hprefix tailTrace_3853389
  have hstable : (prefixWord ++ tailWord_3853389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853389).length < 2 ^ (prefixWord ++ tailWord_3853389).sum := by decide
  have hdescent : baseEnd_3853389 < baseStart_3853389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853406 : List Nat := [4, 4, 1, 1, 1, 1, 4, 1, 1, 1, 4]
def baseStart_3853406 : Nat := 118140960795 + 3853406 * 2 ^ 59
def prefixEnd_3853406 : Nat := 4983230072969 + 3 ^ 40 * 3853406 * 2
def baseEnd_3853406 : Nat := 1978649434919255765003515

theorem tailTrace_3853406 : CollatzResearch.WordTrace tailWord_3853406 prefixEnd_3853406 1978649434919255765003515 := by
  unfold tailWord_3853406
  simp only [CollatzResearch.WordTrace]
  refine ⟨17568157884721955774393509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93696842051850430796765381 17568157884721955774393509)
  ·
    refine ⟨3294029603385366707698783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17568157884721955774393509 3294029603385366707698783)
    ·
      refine ⟨4941044405078050061548175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3294029603385366707698783 4941044405078050061548175)
      ·
        refine ⟨7411566607617075092322263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4941044405078050061548175 7411566607617075092322263)
        ·
          refine ⟨11117349911425612638483395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7411566607617075092322263 11117349911425612638483395)
          ·
            refine ⟨16676024867138418957725093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11117349911425612638483395 16676024867138418957725093)
            ·
              refine ⟨3126754662588453554573455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16676024867138418957725093 3126754662588453554573455)
              ·
                refine ⟨4690131993882680331860183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3126754662588453554573455 4690131993882680331860183)
                ·
                  refine ⟨7035197990824020497790275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4690131993882680331860183 7035197990824020497790275)
                  ·
                    refine ⟨10552796986236030746685413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7035197990824020497790275 10552796986236030746685413)
                    ·
                      refine ⟨1978649434919255765003515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10552796986236030746685413 1978649434919255765003515)
                      ·
                        rfl

theorem cell23_3853406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_3853406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853406 prefixEnd_3853406 := by exact prefixLift 3853406
  have htrace : WordTrace (prefixWord ++ tailWord_3853406) baseStart_3853406 baseEnd_3853406 := by
    simpa [prefixWord, tailWord_3853406, baseEnd_3853406] using wordTrace_append hprefix tailTrace_3853406
  have hstable : (prefixWord ++ tailWord_3853406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853406).length < 2 ^ (prefixWord ++ tailWord_3853406).sum := by decide
  have hdescent : baseEnd_3853406 < baseStart_3853406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853416 : List Nat := [2, 1, 4, 4, 2, 1, 1, 2, 2, 4]
def baseStart_3853416 : Nat := 118140960795 + 3853416 * 2 ^ 59
def prefixEnd_3853416 : Nat := 4983230072969 + 3 ^ 40 * 3853416 * 2
def baseEnd_3853416 : Nat := 659551523241933575292823

theorem tailTrace_3853416 : CollatzResearch.WordTrace tailWord_3853416 prefixEnd_3853416 659551523241933575292823 := by
  unfold tailWord_3853416
  simp only [CollatzResearch.WordTrace]
  refine ⟨70272813903869708951506051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93697085205159611935341401 70272813903869708951506051)
  ·
    refine ⟨105409220855804563427259077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70272813903869708951506051 105409220855804563427259077)
    ·
      refine ⟨19764228910463355642611077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105409220855804563427259077 19764228910463355642611077)
      ·
        refine ⟨3705792920711879182989577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19764228910463355642611077 3705792920711879182989577)
        ·
          refine ⟨2779344690533909387242183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3705792920711879182989577 2779344690533909387242183)
          ·
            refine ⟨4169017035800864080863275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2779344690533909387242183 4169017035800864080863275)
            ·
              refine ⟨6253525553701296121294913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4169017035800864080863275 6253525553701296121294913)
              ·
                refine ⟨4690144165275972090971185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6253525553701296121294913 4690144165275972090971185)
                ·
                  refine ⟨3517608123956979068228389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4690144165275972090971185 3517608123956979068228389)
                  ·
                    refine ⟨659551523241933575292823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3517608123956979068228389 659551523241933575292823)
                    ·
                      rfl

theorem cell23_3853416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_3853416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853416 prefixEnd_3853416 := by exact prefixLift 3853416
  have htrace : WordTrace (prefixWord ++ tailWord_3853416) baseStart_3853416 baseEnd_3853416 := by
    simpa [prefixWord, tailWord_3853416, baseEnd_3853416] using wordTrace_append hprefix tailTrace_3853416
  have hstable : (prefixWord ++ tailWord_3853416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853416).length < 2 ^ (prefixWord ++ tailWord_3853416).sum := by decide
  have hdescent : baseEnd_3853416 < baseStart_3853416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853422 : List Nat := [4, 1, 2, 2, 1, 3, 1, 1, 4, 1, 3]
def baseStart_3853422 : Nat := 118140960795 + 3853422 * 2 ^ 59
def prefixEnd_3853422 : Nat := 4983230072969 + 3 ^ 40 * 3853422 * 2
def baseEnd_3853422 : Nat := 1978657650609727702403441

theorem tailTrace_3853422 : CollatzResearch.WordTrace tailWord_3853422 prefixEnd_3853422 1978657650609727702403441 := by
  unfold tailWord_3853422
  simp only [CollatzResearch.WordTrace]
  refine ⟨17568230830714710115966315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93697231097145120618487013 17568230830714710115966315)
  ·
    refine ⟨26352346246072065173949473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17568230830714710115966315 26352346246072065173949473)
    ·
      refine ⟨19764259684554048880462105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26352346246072065173949473 19764259684554048880462105)
      ·
        refine ⟨14823194763415536660346579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19764259684554048880462105 14823194763415536660346579)
        ·
          refine ⟨22234792145123304990519869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14823194763415536660346579 22234792145123304990519869)
          ·
            refine ⟨8338047054421239371444951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22234792145123304990519869 8338047054421239371444951)
            ·
              refine ⟨12507070581631859057167427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8338047054421239371444951 12507070581631859057167427)
              ·
                refine ⟨18760605872447788585751141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12507070581631859057167427 18760605872447788585751141)
                ·
                  refine ⟨3517613601083960359828339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18760605872447788585751141 3517613601083960359828339)
                  ·
                    refine ⟨5276420401625940539742509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3517613601083960359828339 5276420401625940539742509)
                    ·
                      refine ⟨1978657650609727702403441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5276420401625940539742509 1978657650609727702403441)
                      ·
                        rfl

theorem cell23_3853422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_3853422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853422 prefixEnd_3853422 := by exact prefixLift 3853422
  have htrace : WordTrace (prefixWord ++ tailWord_3853422) baseStart_3853422 baseEnd_3853422 := by
    simpa [prefixWord, tailWord_3853422, baseEnd_3853422] using wordTrace_append hprefix tailTrace_3853422
  have hstable : (prefixWord ++ tailWord_3853422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853422).length < 2 ^ (prefixWord ++ tailWord_3853422).sum := by decide
  have hdescent : baseEnd_3853422 < baseStart_3853422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853479 : List Nat := [1, 1, 6, 2, 1, 1, 2, 1, 4, 2, 2]
def baseStart_3853479 : Nat := 118140960795 + 3853479 * 2 ^ 59
def prefixEnd_3853479 : Nat := 4983230072969 + 3 ^ 40 * 3853479 * 2
def baseEnd_3853479 : Nat := 1978686919007033979390679

theorem tailTrace_3853479 : CollatzResearch.WordTrace tailWord_3853479 prefixEnd_3853479 1978686919007033979390679 := by
  unfold tailWord_3853479
  simp only [CollatzResearch.WordTrace]
  refine ⟨140547925606511179662555491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93698617071007453108370327 140547925606511179662555491)
  ·
    refine ⟨210821888409766769493833237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140547925606511179662555491 210821888409766769493833237)
    ·
      refine ⟨9882276019207817320023433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 210821888409766769493833237 9882276019207817320023433)
      ·
        refine ⟨7411707014405862990017575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9882276019207817320023433 7411707014405862990017575)
        ·
          refine ⟨11117560521608794485026363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7411707014405862990017575 11117560521608794485026363)
          ·
            refine ⟨16676340782413191727539545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11117560521608794485026363 16676340782413191727539545)
            ·
              refine ⟨12507255586809893795654659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16676340782413191727539545 12507255586809893795654659)
              ·
                refine ⟨18760883380214840693481989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12507255586809893795654659 18760883380214840693481989)
                ·
                  refine ⟨3517665633790282630027873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18760883380214840693481989 3517665633790282630027873)
                  ·
                    refine ⟨2638249225342711972520905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3517665633790282630027873 2638249225342711972520905)
                    ·
                      refine ⟨1978686919007033979390679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2638249225342711972520905 1978686919007033979390679)
                      ·
                        rfl

theorem cell23_3853479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_3853479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853479 prefixEnd_3853479 := by exact prefixLift 3853479
  have htrace : WordTrace (prefixWord ++ tailWord_3853479) baseStart_3853479 baseEnd_3853479 := by
    simpa [prefixWord, tailWord_3853479, baseEnd_3853479] using wordTrace_append hprefix tailTrace_3853479
  have hstable : (prefixWord ++ tailWord_3853479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853479).length < 2 ^ (prefixWord ++ tailWord_3853479).sum := by decide
  have hdescent : baseEnd_3853479 < baseStart_3853479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853498 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 6, 5]
def baseStart_3853498 : Nat := 118140960795 + 3853498 * 2 ^ 59
def prefixEnd_3853498 : Nat := 4983230072969 + 3 ^ 40 * 3853498 * 2
def baseEnd_3853498 : Nat := 659565558379823135017697

theorem tailTrace_3853498 : CollatzResearch.WordTrace tailWord_3853498 prefixEnd_3853498 659565558379823135017697 := by
  unfold tailWord_3853498
  simp only [CollatzResearch.WordTrace]
  refine ⟨35137154648360586476874287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93699079062294897271664765 35137154648360586476874287)
  ·
    refine ⟨52705731972540879715311431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35137154648360586476874287 52705731972540879715311431)
    ·
      refine ⟨79058597958811319572967147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52705731972540879715311431 79058597958811319572967147)
      ·
        refine ⟨118587896938216979359450721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79058597958811319572967147 118587896938216979359450721)
        ·
          refine ⟨88940922703662734519588041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118587896938216979359450721 88940922703662734519588041)
          ·
            refine ⟨66705692027747050889691031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88940922703662734519588041 66705692027747050889691031)
            ·
              refine ⟨100058538041620576334536547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66705692027747050889691031 100058538041620576334536547)
              ·
                refine ⟨150087807062430864501804821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100058538041620576334536547 150087807062430864501804821)
                ·
                  refine ⟨7035365956051446773522101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 150087807062430864501804821 7035365956051446773522101)
                  ·
                    refine ⟨659565558379823135017697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7035365956051446773522101 659565558379823135017697)
                    ·
                      rfl

theorem cell23_3853498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 6, 5].length) (baseStart_3853498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853498 prefixEnd_3853498 := by exact prefixLift 3853498
  have htrace : WordTrace (prefixWord ++ tailWord_3853498) baseStart_3853498 baseEnd_3853498 := by
    simpa [prefixWord, tailWord_3853498, baseEnd_3853498] using wordTrace_append hprefix tailTrace_3853498
  have hstable : (prefixWord ++ tailWord_3853498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853498).length < 2 ^ (prefixWord ++ tailWord_3853498).sum := by decide
  have hdescent : baseEnd_3853498 < baseStart_3853498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853525 : List Nat := [1, 3, 2, 4, 1, 1, 1, 2, 1, 2, 5]
def baseStart_3853525 : Nat := 118140960795 + 3853525 * 2 ^ 59
def prefixEnd_3853525 : Nat := 4983230072969 + 3 ^ 40 * 3853525 * 2
def baseEnd_3853525 : Nat := 1978710539117140799415467

theorem tailTrace_3853525 : CollatzResearch.WordTrace tailWord_3853525 prefixEnd_3853525 1978710539117140799415467 := by
  unfold tailWord_3853525
  simp only [CollatzResearch.WordTrace]
  refine ⟨140549603364344529518730029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93699735576229686345820019 140549603364344529518730029)
  ·
    refine ⟨52706101261629198569523761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140549603364344529518730029 52706101261629198569523761)
    ·
      refine ⟨39529575946221898927142821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52706101261629198569523761 39529575946221898927142821)
      ·
        refine ⟨7411795489916606048839279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39529575946221898927142821 7411795489916606048839279)
        ·
          refine ⟨11117693234874909073258919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7411795489916606048839279 11117693234874909073258919)
          ·
            refine ⟨16676539852312363609888379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11117693234874909073258919 16676539852312363609888379)
            ·
              refine ⟨25014809778468545414832569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16676539852312363609888379 25014809778468545414832569)
              ·
                refine ⟨18761107333851409061124427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25014809778468545414832569 18761107333851409061124427)
                ·
                  refine ⟨28141661000777113591686641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18761107333851409061124427 28141661000777113591686641)
                  ·
                    refine ⟨21106245750582835193764981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28141661000777113591686641 21106245750582835193764981)
                    ·
                      refine ⟨1978710539117140799415467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21106245750582835193764981 1978710539117140799415467)
                      ·
                        rfl

theorem cell23_3853525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_3853525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853525 prefixEnd_3853525 := by exact prefixLift 3853525
  have htrace : WordTrace (prefixWord ++ tailWord_3853525) baseStart_3853525 baseEnd_3853525 := by
    simpa [prefixWord, tailWord_3853525, baseEnd_3853525] using wordTrace_append hprefix tailTrace_3853525
  have hstable : (prefixWord ++ tailWord_3853525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853525).length < 2 ^ (prefixWord ++ tailWord_3853525).sum := by decide
  have hdescent : baseEnd_3853525 < baseStart_3853525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853535 : List Nat := [1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 4]
def baseStart_3853535 : Nat := 118140960795 + 3853535 * 2 ^ 59
def prefixEnd_3853535 : Nat := 4983230072969 + 3 ^ 40 * 3853535 * 2
def baseEnd_3853535 : Nat := 1978715673923685760290421

theorem tailTrace_3853535 : CollatzResearch.WordTrace tailWord_3853535 prefixEnd_3853535 1978715673923685760290421 := by
  unfold tailWord_3853535
  simp only [CollatzResearch.WordTrace]
  refine ⟨140549968094308301226594059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93699978729538867484396039 140549968094308301226594059)
  ·
    refine ⟨210824952141462451839891089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140549968094308301226594059 210824952141462451839891089)
    ·
      refine ⟨158118714106096838879918317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210824952141462451839891089 158118714106096838879918317)
      ·
        refine ⟨59294517789786314579969369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158118714106096838879918317 59294517789786314579969369)
        ·
          refine ⟨44470888342339735934977027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59294517789786314579969369 44470888342339735934977027)
          ·
            refine ⟨66706332513509603902465541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44470888342339735934977027 66706332513509603902465541)
            ·
              refine ⟨12507437346283050731712289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66706332513509603902465541 12507437346283050731712289)
              ·
                refine ⟨9380578009712288048784217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12507437346283050731712289 9380578009712288048784217)
                ·
                  refine ⟨7035433507284216036588163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9380578009712288048784217 7035433507284216036588163)
                  ·
                    refine ⟨10553150260926324054882245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7035433507284216036588163 10553150260926324054882245)
                    ·
                      refine ⟨1978715673923685760290421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10553150260926324054882245 1978715673923685760290421)
                      ·
                        rfl

theorem cell23_3853535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_3853535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853535 prefixEnd_3853535 := by exact prefixLift 3853535
  have htrace : WordTrace (prefixWord ++ tailWord_3853535) baseStart_3853535 baseEnd_3853535 := by
    simpa [prefixWord, tailWord_3853535, baseEnd_3853535] using wordTrace_append hprefix tailTrace_3853535
  have hstable : (prefixWord ++ tailWord_3853535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853535).length < 2 ^ (prefixWord ++ tailWord_3853535).sum := by decide
  have hdescent : baseEnd_3853535 < baseStart_3853535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853572 : List Nat := [2, 3, 2, 2, 2, 2, 1, 1, 1, 4, 3]
def baseStart_3853572 : Nat := 118140960795 + 3853572 * 2 ^ 59
def prefixEnd_3853572 : Nat := 4983230072969 + 3 ^ 40 * 3853572 * 2
def baseEnd_3853572 : Nat := 1978734672707902115527751

theorem tailTrace_3853572 : CollatzResearch.WordTrace tailWord_3853572 prefixEnd_3853572 1978734672707902115527751 := by
  unfold tailWord_3853572
  simp only [CollatzResearch.WordTrace]
  refine ⟨70275658797587128272845485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93700878396782837697127313 70275658797587128272845485)
  ·
    refine ⟨26353372049095173102317057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70275658797587128272845485 26353372049095173102317057)
    ·
      refine ⟨19765029036821379826737793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26353372049095173102317057 19765029036821379826737793)
      ·
        refine ⟨14823771777616034870053345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19765029036821379826737793 14823771777616034870053345)
        ·
          refine ⟨11117828833212026152540009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14823771777616034870053345 11117828833212026152540009)
          ·
            refine ⟨8338371624909019614405007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11117828833212026152540009 8338371624909019614405007)
            ·
              refine ⟨12507557437363529421607511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8338371624909019614405007 12507557437363529421607511)
              ·
                refine ⟨18761336156045294132411267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12507557437363529421607511 18761336156045294132411267)
                ·
                  refine ⟨28142004234067941198616901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18761336156045294132411267 28142004234067941198616901)
                  ·
                    refine ⟨5276625793887738974740669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28142004234067941198616901 5276625793887738974740669)
                    ·
                      refine ⟨1978734672707902115527751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5276625793887738974740669 1978734672707902115527751)
                      ·
                        rfl

theorem cell23_3853572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_3853572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853572 prefixEnd_3853572 := by exact prefixLift 3853572
  have htrace : WordTrace (prefixWord ++ tailWord_3853572) baseStart_3853572 baseEnd_3853572 := by
    simpa [prefixWord, tailWord_3853572, baseEnd_3853572] using wordTrace_append hprefix tailTrace_3853572
  have hstable : (prefixWord ++ tailWord_3853572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853572).length < 2 ^ (prefixWord ++ tailWord_3853572).sum := by decide
  have hdescent : baseEnd_3853572 < baseStart_3853572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853579 : List Nat := [1, 1, 1, 1, 5, 4, 2, 3, 1, 4]
def baseStart_3853579 : Nat := 118140960795 + 3853579 * 2 ^ 59
def prefixEnd_3853579 : Nat := 4983230072969 + 3 ^ 40 * 3853579 * 2
def baseEnd_3853579 : Nat := 659579422357494529380073

theorem tailTrace_3853579 : CollatzResearch.WordTrace tailWord_3853579 prefixEnd_3853579 659579422357494529380073 := by
  unfold tailWord_3853579
  simp only [CollatzResearch.WordTrace]
  refine ⟨140551572906148896741195791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93701048604099264494130527 140551572906148896741195791)
  ·
    refine ⟨210827359359223345111793687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140551572906148896741195791 210827359359223345111793687)
    ·
      refine ⟨316241039038835017667690531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210827359359223345111793687 316241039038835017667690531)
      ·
        refine ⟨474361558558252526501535797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316241039038835017667690531 474361558558252526501535797)
        ·
          refine ⟨44471396114836174359518981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 474361558558252526501535797 44471396114836174359518981)
          ·
            refine ⟨8338386771531782692409809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44471396114836174359518981 8338386771531782692409809)
            ·
              refine ⟨6253790078648837019307357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8338386771531782692409809 6253790078648837019307357)
              ·
                refine ⟨2345171279493313882240259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6253790078648837019307357 2345171279493313882240259)
                ·
                  refine ⟨3517756919239970823360389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2345171279493313882240259 3517756919239970823360389)
                  ·
                    refine ⟨659579422357494529380073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3517756919239970823360389 659579422357494529380073)
                    ·
                      rfl

theorem cell23_3853579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 3, 1, 4].length) (baseStart_3853579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853579 prefixEnd_3853579 := by exact prefixLift 3853579
  have htrace : WordTrace (prefixWord ++ tailWord_3853579) baseStart_3853579 baseEnd_3853579 := by
    simpa [prefixWord, tailWord_3853579, baseEnd_3853579] using wordTrace_append hprefix tailTrace_3853579
  have hstable : (prefixWord ++ tailWord_3853579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853579).length < 2 ^ (prefixWord ++ tailWord_3853579).sum := by decide
  have hdescent : baseEnd_3853579 < baseStart_3853579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853592 : List Nat := [2, 1, 2, 3, 1, 5, 1, 2, 6]
def baseStart_3853592 : Nat := 118140960795 + 3853592 * 2 ^ 59
def prefixEnd_3853592 : Nat := 4983230072969 + 3 ^ 40 * 3853592 * 2
def baseEnd_3853592 : Nat := 219860549146776893030851

theorem tailTrace_3853592 : CollatzResearch.WordTrace tailWord_3853592 prefixEnd_3853592 219860549146776893030851 := by
  unfold tailWord_3853592
  simp only [CollatzResearch.WordTrace]
  refine ⟨70276023527550899980709515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93701364703401199974279353 70276023527550899980709515)
  ·
    refine ⟨105414035291326349971064273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70276023527550899980709515 105414035291326349971064273)
    ·
      refine ⟨79060526468494762478298205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105414035291326349971064273 79060526468494762478298205)
      ·
        refine ⟨29647697425685535929361827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79060526468494762478298205 29647697425685535929361827)
        ·
          refine ⟨44471546138528303894042741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29647697425685535929361827 44471546138528303894042741)
          ·
            refine ⟨4169207450487028490066507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44471546138528303894042741 4169207450487028490066507)
            ·
              refine ⟨6253811175730542735099761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4169207450487028490066507 6253811175730542735099761)
              ·
                refine ⟨4690358381797907051324821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6253811175730542735099761 4690358381797907051324821)
                ·
                  refine ⟨219860549146776893030851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4690358381797907051324821 219860549146776893030851)
                  ·
                    rfl

theorem cell23_3853592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 6].length) (baseStart_3853592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853592 prefixEnd_3853592 := by exact prefixLift 3853592
  have htrace : WordTrace (prefixWord ++ tailWord_3853592) baseStart_3853592 baseEnd_3853592 := by
    simpa [prefixWord, tailWord_3853592, baseEnd_3853592] using wordTrace_append hprefix tailTrace_3853592
  have hstable : (prefixWord ++ tailWord_3853592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853592).length < 2 ^ (prefixWord ++ tailWord_3853592).sum := by decide
  have hdescent : baseEnd_3853592 < baseStart_3853592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853652 : List Nat := [2, 4, 1, 1, 2, 1, 1, 3, 4, 4]
def baseStart_3853652 : Nat := 118140960795 + 3853652 * 2 ^ 59
def prefixEnd_3853652 : Nat := 4983230072969 + 3 ^ 40 * 3853652 * 2
def baseEnd_3853652 : Nat := 659591917053420600842461

theorem tailTrace_3853652 : CollatzResearch.WordTrace tailWord_3853652 prefixEnd_3853652 659591917053420600842461 := by
  unfold tailWord_3853652
  simp only [CollatzResearch.WordTrace]
  refine ⟨70277117717442215104301605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93702823623256286805735473 70277117717442215104301605)
  ·
    refine ⟨13176959572020415332056551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70277117717442215104301605 13176959572020415332056551)
    ·
      refine ⟨19765439358030622998084827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13176959572020415332056551 19765439358030622998084827)
      ·
        refine ⟨29648159037045934497127241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19765439358030622998084827 29648159037045934497127241)
        ·
          refine ⟨22236119277784450872845431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29648159037045934497127241 22236119277784450872845431)
          ·
            refine ⟨33354178916676676309268147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22236119277784450872845431 33354178916676676309268147)
            ·
              refine ⟨50031268375015014463902221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33354178916676676309268147 50031268375015014463902221)
              ·
                refine ⟨18761725640630630423963333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50031268375015014463902221 18761725640630630423963333)
                ·
                  refine ⟨3517823557618243204493125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18761725640630630423963333 3517823557618243204493125)
                  ·
                    refine ⟨659591917053420600842461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3517823557618243204493125 659591917053420600842461)
                    ·
                      rfl

theorem cell23_3853652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_3853652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853652 prefixEnd_3853652 := by exact prefixLift 3853652
  have htrace : WordTrace (prefixWord ++ tailWord_3853652) baseStart_3853652 baseEnd_3853652 := by
    simpa [prefixWord, tailWord_3853652, baseEnd_3853652] using wordTrace_append hprefix tailTrace_3853652
  have hstable : (prefixWord ++ tailWord_3853652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853652).length < 2 ^ (prefixWord ++ tailWord_3853652).sum := by decide
  have hdescent : baseEnd_3853652 < baseStart_3853652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853653 : List Nat := [1, 3, 2, 2, 3, 2, 3, 2, 1, 1, 3]
def baseStart_3853653 : Nat := 118140960795 + 3853653 * 2 ^ 59
def prefixEnd_3853653 : Nat := 4983230072969 + 3 ^ 40 * 3853653 * 2
def baseEnd_3853653 : Nat := 1978776264640916298614879

theorem tailTrace_3853653 : CollatzResearch.WordTrace tailWord_3853653 prefixEnd_3853653 1978776264640916298614879 := by
  unfold tailWord_3853653
  simp only [CollatzResearch.WordTrace]
  refine ⟨140554271907880807379389613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93702847938587204919593075 140554271907880807379389613)
  ·
    refine ⟨52707851965455302767271105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140554271907880807379389613 52707851965455302767271105)
    ·
      refine ⟨39530888974091477075453329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52707851965455302767271105 39530888974091477075453329)
      ·
        refine ⟨29648166730568607806589997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39530888974091477075453329 29648166730568607806589997)
        ·
          refine ⟨11118062523963227927471249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29648166730568607806589997 11118062523963227927471249)
          ·
            refine ⟨8338546892972420945603437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11118062523963227927471249 8338546892972420945603437)
            ·
              refine ⟨3126955084864657854601289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8338546892972420945603437 3126955084864657854601289)
              ·
                refine ⟨2345216313648493390950967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3126955084864657854601289 2345216313648493390950967)
                ·
                  refine ⟨3517824470472740086426451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2345216313648493390950967 3517824470472740086426451)
                  ·
                    refine ⟨5276736705709110129639677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3517824470472740086426451 5276736705709110129639677)
                    ·
                      refine ⟨1978776264640916298614879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5276736705709110129639677 1978776264640916298614879)
                      ·
                        rfl

theorem cell23_3853653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_3853653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853653 prefixEnd_3853653 := by exact prefixLift 3853653
  have htrace : WordTrace (prefixWord ++ tailWord_3853653) baseStart_3853653 baseEnd_3853653 := by
    simpa [prefixWord, tailWord_3853653, baseEnd_3853653] using wordTrace_append hprefix tailTrace_3853653
  have hstable : (prefixWord ++ tailWord_3853653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853653).length < 2 ^ (prefixWord ++ tailWord_3853653).sum := by decide
  have hdescent : baseEnd_3853653 < baseStart_3853653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853655 : List Nat := [1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 6]
def baseStart_3853655 : Nat := 118140960795 + 3853655 * 2 ^ 59
def prefixEnd_3853655 : Nat := 4983230072969 + 3 ^ 40 * 3853655 * 2
def baseEnd_3853655 : Nat := 1978777291602225290789869

theorem tailTrace_3853655 : CollatzResearch.WordTrace tailWord_3853655 prefixEnd_3853655 1978777291602225290789869 := by
  unfold tailWord_3853655
  simp only [CollatzResearch.WordTrace]
  refine ⟨140554344853873561720962419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93702896569249041147308279 140554344853873561720962419)
  ·
    refine ⟨210831517280810342581443629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140554344853873561720962419 210831517280810342581443629)
    ·
      refine ⟨79061818980303878468041361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210831517280810342581443629 79061818980303878468041361)
      ·
        refine ⟨59296364235227908851031021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79061818980303878468041361 59296364235227908851031021)
        ·
          refine ⟨22236136588210465819136633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59296364235227908851031021 22236136588210465819136633)
          ·
            refine ⟨16677102441157849364352475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22236136588210465819136633 16677102441157849364352475)
            ·
              refine ⟨25015653661736774046528713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16677102441157849364352475 25015653661736774046528713)
              ·
                refine ⟨18761740246302580534896535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25015653661736774046528713 18761740246302580534896535)
                ·
                  refine ⟨28142610369453870802344803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18761740246302580534896535 28142610369453870802344803)
                  ·
                    refine ⟨42213915554180806203517205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28142610369453870802344803 42213915554180806203517205)
                    ·
                      refine ⟨1978777291602225290789869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42213915554180806203517205 1978777291602225290789869)
                      ·
                        rfl

theorem cell23_3853655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_3853655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853655 prefixEnd_3853655 := by exact prefixLift 3853655
  have htrace : WordTrace (prefixWord ++ tailWord_3853655) baseStart_3853655 baseEnd_3853655 := by
    simpa [prefixWord, tailWord_3853655, baseEnd_3853655] using wordTrace_append hprefix tailTrace_3853655
  have hstable : (prefixWord ++ tailWord_3853655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853655).length < 2 ^ (prefixWord ++ tailWord_3853655).sum := by decide
  have hdescent : baseEnd_3853655 < baseStart_3853655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853692 : List Nat := [2, 2, 2, 1, 1, 1, 5, 2, 1, 3, 3]
def baseStart_3853692 : Nat := 118140960795 + 3853692 * 2 ^ 59
def prefixEnd_3853692 : Nat := 4983230072969 + 3 ^ 40 * 3853692 * 2
def baseEnd_3853692 : Nat := 1978796290386441646027199

theorem tailTrace_3853692 : CollatzResearch.WordTrace tailWord_3853692 prefixEnd_3853692 1978796290386441646027199 := by
  unfold tailWord_3853692
  simp only [CollatzResearch.WordTrace]
  refine ⟨70277847177369758520029665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93703796236493011360039553 70277847177369758520029665)
  ·
    refine ⟨52708385383027318890022249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70277847177369758520029665 52708385383027318890022249)
    ·
      refine ⟨39531289037270489167516687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52708385383027318890022249 39531289037270489167516687)
      ·
        refine ⟨59296933555905733751275031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39531289037270489167516687 59296933555905733751275031)
        ·
          refine ⟨88945400333858600626912547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59296933555905733751275031 88945400333858600626912547)
          ·
            refine ⟨133418100500787900940368821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88945400333858600626912547 133418100500787900940368821)
            ·
              refine ⟨12507946921948865713159577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133418100500787900940368821 12507946921948865713159577)
              ·
                refine ⟨9380960191461649284869683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12507946921948865713159577 9380960191461649284869683)
                ·
                  refine ⟨14071440287192473927304525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9380960191461649284869683 14071440287192473927304525)
                  ·
                    refine ⟨5276790107697177722739197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14071440287192473927304525 5276790107697177722739197)
                    ·
                      refine ⟨1978796290386441646027199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5276790107697177722739197 1978796290386441646027199)
                      ·
                        rfl

theorem cell23_3853692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_3853692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853692 prefixEnd_3853692 := by exact prefixLift 3853692
  have htrace : WordTrace (prefixWord ++ tailWord_3853692) baseStart_3853692 baseEnd_3853692 := by
    simpa [prefixWord, tailWord_3853692, baseEnd_3853692] using wordTrace_append hprefix tailTrace_3853692
  have hstable : (prefixWord ++ tailWord_3853692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853692).length < 2 ^ (prefixWord ++ tailWord_3853692).sum := by decide
  have hdescent : baseEnd_3853692 < baseStart_3853692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853710 : List Nat := [4, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2]
def baseStart_3853710 : Nat := 118140960795 + 3853710 * 2 ^ 59
def prefixEnd_3853710 : Nat := 4983230072969 + 3 ^ 40 * 3853710 * 2
def baseEnd_3853710 : Nat := 1978805533038222575602117

theorem tailTrace_3853710 : CollatzResearch.WordTrace tailWord_3853710 prefixEnd_3853710 1978805533038222575602117 := by
  unfold tailWord_3853710
  simp only [CollatzResearch.WordTrace]
  refine ⟨17569543858584288264276823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93704233912449537409476389 17569543858584288264276823)
  ·
    refine ⟨26354315787876432396415235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17569543858584288264276823 26354315787876432396415235)
    ·
      refine ⟨39531473681814648594622853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26354315787876432396415235 39531473681814648594622853)
      ·
        refine ⟨7412151315340246611491785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39531473681814648594622853 7412151315340246611491785)
        ·
          refine ⟨5559113486505184958618839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7412151315340246611491785 5559113486505184958618839)
          ·
            refine ⟨8338670229757777437928259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5559113486505184958618839 8338670229757777437928259)
            ·
              refine ⟨12508005344636666156892389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8338670229757777437928259 12508005344636666156892389)
              ·
                refine ⟨2345251002119374904417323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12508005344636666156892389 2345251002119374904417323)
                ·
                  refine ⟨3517876503179062356625985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2345251002119374904417323 3517876503179062356625985)
                  ·
                    refine ⟨2638407377384296767469489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3517876503179062356625985 2638407377384296767469489)
                    ·
                      refine ⟨1978805533038222575602117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2638407377384296767469489 1978805533038222575602117)
                      ·
                        rfl

theorem cell23_3853710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_3853710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853710 prefixEnd_3853710 := by exact prefixLift 3853710
  have htrace : WordTrace (prefixWord ++ tailWord_3853710) baseStart_3853710 baseEnd_3853710 := by
    simpa [prefixWord, tailWord_3853710, baseEnd_3853710] using wordTrace_append hprefix tailTrace_3853710
  have hstable : (prefixWord ++ tailWord_3853710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853710).length < 2 ^ (prefixWord ++ tailWord_3853710).sum := by decide
  have hdescent : baseEnd_3853710 < baseStart_3853710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853772 : List Nat := [2, 2, 1, 4, 2, 1, 1, 3, 7]
def baseStart_3853772 : Nat := 118140960795 + 3853772 * 2 ^ 59
def prefixEnd_3853772 : Nat := 4983230072969 + 3 ^ 40 * 3853772 * 2
def baseEnd_3853772 : Nat := 219870818759866814780759

theorem tailTrace_3853772 : CollatzResearch.WordTrace tailWord_3853772 prefixEnd_3853772 219870818759866814780759 := by
  unfold tailWord_3853772
  simp only [CollatzResearch.WordTrace]
  refine ⟨70279306097224845351485785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93705741462966460468647713 70279306097224845351485785)
  ·
    refine ⟨52709479572918634013614339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70279306097224845351485785 52709479572918634013614339)
    ·
      refine ⟨79064219359377951020421509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52709479572918634013614339 79064219359377951020421509)
      ·
        refine ⟨14824541129883365816329033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79064219359377951020421509 14824541129883365816329033)
        ·
          refine ⟨11118405847412524362246775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14824541129883365816329033 11118405847412524362246775)
          ·
            refine ⟨16677608771118786543370163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11118405847412524362246775 16677608771118786543370163)
            ·
              refine ⟨25016413156678179815055245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16677608771118786543370163 25016413156678179815055245)
              ·
                refine ⟨9381154933754317430645717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25016413156678179815055245 9381154933754317430645717)
                ·
                  refine ⟨219870818759866814780759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9381154933754317430645717 219870818759866814780759)
                  ·
                    rfl

theorem cell23_3853772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 7].length) (baseStart_3853772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853772 prefixEnd_3853772 := by exact prefixLift 3853772
  have htrace : WordTrace (prefixWord ++ tailWord_3853772) baseStart_3853772 baseEnd_3853772 := by
    simpa [prefixWord, tailWord_3853772, baseEnd_3853772] using wordTrace_append hprefix tailTrace_3853772
  have hstable : (prefixWord ++ tailWord_3853772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853772).length < 2 ^ (prefixWord ++ tailWord_3853772).sum := by decide
  have hdescent : baseEnd_3853772 < baseStart_3853772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853856 : List Nat := [2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 4]
def baseStart_3853856 : Nat := 118140960795 + 3853856 * 2 ^ 59
def prefixEnd_3853856 : Nat := 4983230072969 + 3 ^ 40 * 3853856 * 2
def baseEnd_3853856 : Nat := 1978880501213779004376445

theorem tailTrace_3853856 : CollatzResearch.WordTrace tailWord_3853856 prefixEnd_3853856 1978880501213779004376445 := by
  unfold tailWord_3853856
  simp only [CollatzResearch.WordTrace]
  refine ⟨70280837963072686524514711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93707783950763582032686281 70280837963072686524514711)
  ·
    refine ⟨105421256944609029786772067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70280837963072686524514711 105421256944609029786772067)
    ·
      refine ⟨158131885416913544680158101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105421256944609029786772067 158131885416913544680158101)
      ·
        refine ⟨7412432128917822406882411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 158131885416913544680158101 7412432128917822406882411)
        ·
          refine ⟨11118648193376733610323617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7412432128917822406882411 11118648193376733610323617)
          ·
            refine ⟨8338986145032550207742713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11118648193376733610323617 8338986145032550207742713)
            ·
              refine ⟨6254239608774412655807035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8338986145032550207742713 6254239608774412655807035)
              ·
                refine ⟨9381359413161618983710553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6254239608774412655807035 9381359413161618983710553)
                ·
                  refine ⟨7036019559871214237782915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9381359413161618983710553 7036019559871214237782915)
                  ·
                    refine ⟨10554029339806821356674373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7036019559871214237782915 10554029339806821356674373)
                    ·
                      refine ⟨1978880501213779004376445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10554029339806821356674373 1978880501213779004376445)
                      ·
                        rfl

theorem cell23_3853856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_3853856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853856 prefixEnd_3853856 := by exact prefixLift 3853856
  have htrace : WordTrace (prefixWord ++ tailWord_3853856) baseStart_3853856 baseEnd_3853856 := by
    simpa [prefixWord, tailWord_3853856, baseEnd_3853856] using wordTrace_append hprefix tailTrace_3853856
  have hstable : (prefixWord ++ tailWord_3853856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853856).length < 2 ^ (prefixWord ++ tailWord_3853856).sum := by decide
  have hdescent : baseEnd_3853856 < baseStart_3853856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853879 : List Nat := [1, 1, 3, 1, 2, 5, 2, 2, 6]
def baseStart_3853879 : Nat := 118140960795 + 3853879 * 2 ^ 59
def prefixEnd_3853879 : Nat := 4983230072969 + 3 ^ 40 * 3853879 * 2
def baseEnd_3853879 : Nat := 219876923474314712709871

theorem tailTrace_3853879 : CollatzResearch.WordTrace tailWord_3853879 prefixEnd_3853879 219876923474314712709871 := by
  unfold tailWord_3853879
  simp only [CollatzResearch.WordTrace]
  refine ⟨140562514805062047977116691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93708343203374698651411127 140562514805062047977116691)
  ·
    refine ⟨210843772207593071965675037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140562514805062047977116691 210843772207593071965675037)
    ·
      refine ⟨79066414577847401987128139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210843772207593071965675037 79066414577847401987128139)
      ·
        refine ⟨118599621866771102980692209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79066414577847401987128139 118599621866771102980692209)
        ·
          refine ⟨88949716400078327235519157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118599621866771102980692209 88949716400078327235519157)
          ·
            refine ⟨8339035912507343178329921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88949716400078327235519157 8339035912507343178329921)
            ·
              refine ⟨6254276934380507383747441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8339035912507343178329921 6254276934380507383747441)
              ·
                refine ⟨4690707700785380537810581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6254276934380507383747441 4690707700785380537810581)
                ·
                  refine ⟨219876923474314712709871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4690707700785380537810581 219876923474314712709871)
                  ·
                    rfl

theorem cell23_3853879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 6].length) (baseStart_3853879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853879 prefixEnd_3853879 := by exact prefixLift 3853879
  have htrace : WordTrace (prefixWord ++ tailWord_3853879) baseStart_3853879 baseEnd_3853879 := by
    simpa [prefixWord, tailWord_3853879, baseEnd_3853879] using wordTrace_append hprefix tailTrace_3853879
  have hstable : (prefixWord ++ tailWord_3853879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853879).length < 2 ^ (prefixWord ++ tailWord_3853879).sum := by decide
  have hdescent : baseEnd_3853879 < baseStart_3853879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853882 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 1, 2, 6]
def baseStart_3853882 : Nat := 118140960795 + 3853882 * 2 ^ 59
def prefixEnd_3853882 : Nat := 4983230072969 + 3 ^ 40 * 3853882 * 2
def baseEnd_3853882 : Nat := 1978893851710795902651325

theorem tailTrace_3853882 : CollatzResearch.WordTrace tailWord_3853882 prefixEnd_3853882 1978893851710795902651325 := by
  unfold tailWord_3853882
  simp only [CollatzResearch.WordTrace]
  refine ⟨35140656056012794872368975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93708416149367452992983933 35140656056012794872368975)
  ·
    refine ⟨52710984084019192308553463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35140656056012794872368975 52710984084019192308553463)
    ·
      refine ⟨79066476126028788462830195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52710984084019192308553463 79066476126028788462830195)
      ·
        refine ⟨118599714189043182694245293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79066476126028788462830195 118599714189043182694245293)
        ·
          refine ⟨44474892820891193510341985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118599714189043182694245293 44474892820891193510341985)
          ·
            refine ⟨33356169615668395132756489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44474892820891193510341985 33356169615668395132756489)
            ·
              refine ⟨25017127211751296349567367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33356169615668395132756489 25017127211751296349567367)
              ·
                refine ⟨37525690817626944524351051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25017127211751296349567367 37525690817626944524351051)
                ·
                  refine ⟨56288536226440416786526577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37525690817626944524351051 56288536226440416786526577)
                  ·
                    refine ⟨42216402169830312589894933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56288536226440416786526577 42216402169830312589894933)
                    ·
                      refine ⟨1978893851710795902651325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42216402169830312589894933 1978893851710795902651325)
                      ·
                        rfl

theorem cell23_3853882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_3853882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853882 prefixEnd_3853882 := by exact prefixLift 3853882
  have htrace : WordTrace (prefixWord ++ tailWord_3853882) baseStart_3853882 baseEnd_3853882 := by
    simpa [prefixWord, tailWord_3853882, baseEnd_3853882] using wordTrace_append hprefix tailTrace_3853882
  have hstable : (prefixWord ++ tailWord_3853882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853882).length < 2 ^ (prefixWord ++ tailWord_3853882).sum := by decide
  have hdescent : baseEnd_3853882 < baseStart_3853882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853899 : List Nat := [1, 1, 1, 1, 3, 1, 3, 4, 1, 5, 2]
def baseStart_3853899 : Nat := 118140960795 + 3853899 * 2 ^ 59
def prefixEnd_3853899 : Nat := 4983230072969 + 3 ^ 40 * 3853899 * 2
def baseEnd_3853899 : Nat := 1978902580881922336138747

theorem tailTrace_3853899 : CollatzResearch.WordTrace tailWord_3853899 prefixEnd_3853899 1978902580881922336138747 := by
  unfold tailWord_3853899
  simp only [CollatzResearch.WordTrace]
  refine ⟨140563244264989591392844751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93708829509993060928563167 140563244264989591392844751)
  ·
    refine ⟨210844866397484387089267127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140563244264989591392844751 210844866397484387089267127)
    ·
      refine ⟨316267299596226580633900691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210844866397484387089267127 316267299596226580633900691)
      ·
        refine ⟨474400949394339870950851037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316267299596226580633900691 474400949394339870950851037)
        ·
          refine ⟨177900356022877451606569139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 474400949394339870950851037 177900356022877451606569139)
          ·
            refine ⟨266850534034316177409853709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177900356022877451606569139 266850534034316177409853709)
            ·
              refine ⟨100068950262868566528695141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 266850534034316177409853709 100068950262868566528695141)
              ·
                refine ⟨18762928174287856224130339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100068950262868566528695141 18762928174287856224130339)
                ·
                  refine ⟨28144392261431784336195509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18762928174287856224130339 28144392261431784336195509)
                  ·
                    refine ⟨2638536774509229781518329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28144392261431784336195509 2638536774509229781518329)
                    ·
                      refine ⟨1978902580881922336138747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2638536774509229781518329 1978902580881922336138747)
                      ·
                        rfl

theorem cell23_3853899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 5, 2].length) (baseStart_3853899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853899 prefixEnd_3853899 := by exact prefixLift 3853899
  have htrace : WordTrace (prefixWord ++ tailWord_3853899) baseStart_3853899 baseEnd_3853899 := by
    simpa [prefixWord, tailWord_3853899, baseEnd_3853899] using wordTrace_append hprefix tailTrace_3853899
  have hstable : (prefixWord ++ tailWord_3853899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853899).length < 2 ^ (prefixWord ++ tailWord_3853899).sum := by decide
  have hdescent : baseEnd_3853899 < baseStart_3853899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853902 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7]
def baseStart_3853902 : Nat := 118140960795 + 3853902 * 2 ^ 59
def prefixEnd_3853902 : Nat := 4983230072969 + 3 ^ 40 * 3853902 * 2
def baseEnd_3853902 : Nat := 1978904121323885824401233

theorem tailTrace_3853902 : CollatzResearch.WordTrace tailWord_3853902 prefixEnd_3853902 1978904121323885824401233 := by
  unfold tailWord_3853902
  simp only [CollatzResearch.WordTrace]
  refine ⟨17570419210497340363150495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93708902455985815270135973 17570419210497340363150495)
  ·
    refine ⟨26355628815746010544725743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17570419210497340363150495 26355628815746010544725743)
    ·
      refine ⟨39533443223619015817088615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26355628815746010544725743 39533443223619015817088615)
      ·
        refine ⟨59300164835428523725632923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39533443223619015817088615 59300164835428523725632923)
        ·
          refine ⟨88950247253142785588449385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59300164835428523725632923 88950247253142785588449385)
          ·
            refine ⟨66712685439857089191337039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88950247253142785588449385 66712685439857089191337039)
            ·
              refine ⟨100069028159785633787005559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66712685439857089191337039 100069028159785633787005559)
              ·
                refine ⟨150103542239678450680508339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100069028159785633787005559 150103542239678450680508339)
                ·
                  refine ⟨225155313359517676020762509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150103542239678450680508339 225155313359517676020762509)
                  ·
                    refine ⟨84433242509819128507785941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 225155313359517676020762509 84433242509819128507785941)
                    ·
                      refine ⟨1978904121323885824401233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84433242509819128507785941 1978904121323885824401233)
                      ·
                        rfl

theorem cell23_3853902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_3853902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853902 prefixEnd_3853902 := by exact prefixLift 3853902
  have htrace : WordTrace (prefixWord ++ tailWord_3853902) baseStart_3853902 baseEnd_3853902 := by
    simpa [prefixWord, tailWord_3853902, baseEnd_3853902] using wordTrace_append hprefix tailTrace_3853902
  have hstable : (prefixWord ++ tailWord_3853902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853902).length < 2 ^ (prefixWord ++ tailWord_3853902).sum := by decide
  have hdescent : baseEnd_3853902 < baseStart_3853902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853906 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 5, 1, 3]
def baseStart_3853906 : Nat := 118140960795 + 3853906 * 2 ^ 59
def prefixEnd_3853906 : Nat := 4983230072969 + 3 ^ 40 * 3853906 * 2
def baseEnd_3853906 : Nat := 1978906175246503808751215

theorem tailTrace_3853906 : CollatzResearch.WordTrace tailWord_3853906 prefixEnd_3853906 1978906175246503808751215 := by
  unfold tailWord_3853906
  simp only [CollatzResearch.WordTrace]
  refine ⟨35140874893991057897087393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93708999717309487725566381 35140874893991057897087393)
  ·
    refine ⟨26355656170493293422815545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35140874893991057897087393 26355656170493293422815545)
    ·
      refine ⟨19766742127869970067111659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26355656170493293422815545 19766742127869970067111659)
      ·
        refine ⟨29650113191804955100667489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19766742127869970067111659 29650113191804955100667489)
        ·
          refine ⟨22237584893853716325500617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29650113191804955100667489 22237584893853716325500617)
          ·
            refine ⟨16678188670390287244125463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22237584893853716325500617 16678188670390287244125463)
            ·
              refine ⟨25017283005585430866188195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16678188670390287244125463 25017283005585430866188195)
              ·
                refine ⟨37525924508378146299282293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25017283005585430866188195 37525924508378146299282293)
                ·
                  refine ⟨3518055422660451215557715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37525924508378146299282293 3518055422660451215557715)
                  ·
                    refine ⟨5277083133990676823336573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3518055422660451215557715 5277083133990676823336573)
                    ·
                      refine ⟨1978906175246503808751215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5277083133990676823336573 1978906175246503808751215)
                      ·
                        rfl

theorem cell23_3853906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_3853906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853906 prefixEnd_3853906 := by exact prefixLift 3853906
  have htrace : WordTrace (prefixWord ++ tailWord_3853906) baseStart_3853906 baseEnd_3853906 := by
    simpa [prefixWord, tailWord_3853906, baseEnd_3853906] using wordTrace_append hprefix tailTrace_3853906
  have hstable : (prefixWord ++ tailWord_3853906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853906).length < 2 ^ (prefixWord ++ tailWord_3853906).sum := by decide
  have hdescent : baseEnd_3853906 < baseStart_3853906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853909 : List Nat := [1, 3, 2, 2, 1, 1, 1, 6, 1, 5]
def baseStart_3853909 : Nat := 118140960795 + 3853909 * 2 ^ 59
def prefixEnd_3853909 : Nat := 4983230072969 + 3 ^ 40 * 3853909 * 2
def baseEnd_3853909 : Nat := 659635905229489099004567

theorem tailTrace_3853909 : CollatzResearch.WordTrace tailWord_3853909 prefixEnd_3853909 659635905229489099004567 := by
  unfold tailWord_3853909
  simp only [CollatzResearch.WordTrace]
  refine ⟨140563608994953363100708781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93709072663302242067139187 140563608994953363100708781)
  ·
    refine ⟨52711353373107511162765793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140563608994953363100708781 52711353373107511162765793)
    ·
      refine ⟨39533515029830633372074345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52711353373107511162765793 39533515029830633372074345)
      ·
        refine ⟨29650136272372975029055759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39533515029830633372074345 29650136272372975029055759)
        ·
          refine ⟨44475204408559462543583639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29650136272372975029055759 44475204408559462543583639)
          ·
            refine ⟨66712806612839193815375459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44475204408559462543583639 66712806612839193815375459)
            ·
              refine ⟨100069209919258790723063189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66712806612839193815375459 100069209919258790723063189)
              ·
                refine ⟨4690744214965255815143587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100069209919258790723063189 4690744214965255815143587)
                ·
                  refine ⟨7036116322447883722715381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4690744214965255815143587 7036116322447883722715381)
                  ·
                    refine ⟨659635905229489099004567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7036116322447883722715381 659635905229489099004567)
                    ·
                      rfl

theorem cell23_3853909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_3853909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853909 prefixEnd_3853909 := by exact prefixLift 3853909
  have htrace : WordTrace (prefixWord ++ tailWord_3853909) baseStart_3853909 baseEnd_3853909 := by
    simpa [prefixWord, tailWord_3853909, baseEnd_3853909] using wordTrace_append hprefix tailTrace_3853909
  have hstable : (prefixWord ++ tailWord_3853909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853909).length < 2 ^ (prefixWord ++ tailWord_3853909).sum := by decide
  have hdescent : baseEnd_3853909 < baseStart_3853909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853910 : List Nat := [5, 2, 2, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_3853910 : Nat := 118140960795 + 3853910 * 2 ^ 59
def prefixEnd_3853910 : Nat := 4983230072969 + 3 ^ 40 * 3853910 * 2
def baseEnd_3853910 : Nat := 1978908229169121793101197

theorem tailTrace_3853910 : CollatzResearch.WordTrace tailWord_3853910 prefixEnd_3853910 1978908229169121793101197 := by
  unfold tailWord_3853910
  simp only [CollatzResearch.WordTrace]
  refine ⟨8785227841746858766968449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93709096978633160180996789 8785227841746858766968449)
  ·
    refine ⟨6588920881310144075226337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8785227841746858766968449 6588920881310144075226337)
    ·
      refine ⟨4941690660982608056419753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6588920881310144075226337 4941690660982608056419753)
      ·
        refine ⟨3706267995736956042314815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4941690660982608056419753 3706267995736956042314815)
        ·
          refine ⟨5559401993605434063472223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3706267995736956042314815 5559401993605434063472223)
          ·
            refine ⟨8339102990408151095208335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5559401993605434063472223 8339102990408151095208335)
            ·
              refine ⟨12508654485612226642812503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8339102990408151095208335 12508654485612226642812503)
              ·
                refine ⟨18762981728418339964218755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12508654485612226642812503 18762981728418339964218755)
                ·
                  refine ⟨28144472592627509946328133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18762981728418339964218755 28144472592627509946328133)
                  ·
                    refine ⟨5277088611117658114936525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28144472592627509946328133 5277088611117658114936525)
                    ·
                      refine ⟨1978908229169121793101197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5277088611117658114936525 1978908229169121793101197)
                      ·
                        rfl

theorem cell23_3853910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_3853910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853910 prefixEnd_3853910 := by exact prefixLift 3853910
  have htrace : WordTrace (prefixWord ++ tailWord_3853910) baseStart_3853910 baseEnd_3853910 := by
    simpa [prefixWord, tailWord_3853910, baseEnd_3853910] using wordTrace_append hprefix tailTrace_3853910
  have hstable : (prefixWord ++ tailWord_3853910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853910).length < 2 ^ (prefixWord ++ tailWord_3853910).sum := by decide
  have hdescent : baseEnd_3853910 < baseStart_3853910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853917 : List Nat := [1, 4, 4, 2, 1, 1, 2, 3, 1, 4]
def baseStart_3853917 : Nat := 118140960795 + 3853917 * 2 ^ 59
def prefixEnd_3853917 : Nat := 4983230072969 + 3 ^ 40 * 3853917 * 2
def baseEnd_3853917 : Nat := 659637274511234421904555

theorem tailTrace_3853917 : CollatzResearch.WordTrace tailWord_3853917 prefixEnd_3853917 659637274511234421904555 := by
  unfold tailWord_3853917
  simp only [CollatzResearch.WordTrace]
  refine ⟨140563900778924380467000005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93709267185949586978000003 140563900778924380467000005)
  ·
    refine ⟨26355731396048321337562501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140563900778924380467000005 26355731396048321337562501)
    ·
      refine ⟨4941699636759060250792969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26355731396048321337562501 4941699636759060250792969)
      ·
        refine ⟨3706274727569295188094727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4941699636759060250792969 3706274727569295188094727)
        ·
          refine ⟨5559412091353942782142091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3706274727569295188094727 5559412091353942782142091)
          ·
            refine ⟨8339118137030914173213137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5559412091353942782142091 8339118137030914173213137)
            ·
              refine ⟨6254338602773185629909853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8339118137030914173213137 6254338602773185629909853)
              ·
                refine ⟨2345376976039944611216195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6254338602773185629909853 2345376976039944611216195)
                ·
                  refine ⟨3518065464059916916824293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2345376976039944611216195 3518065464059916916824293)
                  ·
                    refine ⟨659637274511234421904555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3518065464059916916824293 659637274511234421904555)
                    ·
                      rfl

theorem cell23_3853917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_3853917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853917 prefixEnd_3853917 := by exact prefixLift 3853917
  have htrace : WordTrace (prefixWord ++ tailWord_3853917) baseStart_3853917 baseEnd_3853917 := by
    simpa [prefixWord, tailWord_3853917, baseEnd_3853917] using wordTrace_append hprefix tailTrace_3853917
  have hstable : (prefixWord ++ tailWord_3853917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853917).length < 2 ^ (prefixWord ++ tailWord_3853917).sum := by decide
  have hdescent : baseEnd_3853917 < baseStart_3853917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853923 : List Nat := [1, 1, 1, 5, 1, 3, 1, 5, 1, 1, 3]
def baseStart_3853923 : Nat := 118140960795 + 3853923 * 2 ^ 59
def prefixEnd_3853923 : Nat := 4983230072969 + 3 ^ 40 * 3853923 * 2
def baseEnd_3853923 : Nat := 1978914904417630242238637

theorem tailTrace_3853923 : CollatzResearch.WordTrace tailWord_3853923 prefixEnd_3853923 1978914904417630242238637 := by
  unfold tailWord_3853923
  simp only [CollatzResearch.WordTrace]
  refine ⟨140564119616902643491718423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93709413077935095661145615 140564119616902643491718423)
  ·
    refine ⟨210846179425353965237577635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140564119616902643491718423 210846179425353965237577635)
    ·
      refine ⟨316269269138030947856366453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210846179425353965237577635 316269269138030947856366453)
      ·
        refine ⟨29650243981690401361534355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 316269269138030947856366453 29650243981690401361534355)
        ·
          refine ⟨44475365972535602042301533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29650243981690401361534355 44475365972535602042301533)
          ·
            refine ⟨16678262239700850765863075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44475365972535602042301533 16678262239700850765863075)
            ·
              refine ⟨25017393359551276148794613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16678262239700850765863075 25017393359551276148794613)
              ·
                refine ⟨2345380627457932138949495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25017393359551276148794613 2345380627457932138949495)
                ·
                  refine ⟨3518070941186898208424243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2345380627457932138949495 3518070941186898208424243)
                  ·
                    refine ⟨5277106411780347312636365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3518070941186898208424243 5277106411780347312636365)
                    ·
                      refine ⟨1978914904417630242238637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5277106411780347312636365 1978914904417630242238637)
                      ·
                        rfl

theorem cell23_3853923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_3853923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853923 prefixEnd_3853923 := by exact prefixLift 3853923
  have htrace : WordTrace (prefixWord ++ tailWord_3853923) baseStart_3853923 baseEnd_3853923 := by
    simpa [prefixWord, tailWord_3853923, baseEnd_3853923] using wordTrace_append hprefix tailTrace_3853923
  have hstable : (prefixWord ++ tailWord_3853923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853923).length < 2 ^ (prefixWord ++ tailWord_3853923).sum := by decide
  have hdescent : baseEnd_3853923 < baseStart_3853923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853949 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 3, 1, 5]
def baseStart_3853949 : Nat := 118140960795 + 3853949 * 2 ^ 59
def prefixEnd_3853949 : Nat := 4983230072969 + 3 ^ 40 * 3853949 * 2
def baseEnd_3853949 : Nat := 1978928254914647140513517

theorem tailTrace_3853949 : CollatzResearch.WordTrace tailWord_3853949 prefixEnd_3853949 1978928254914647140513517 := by
  unfold tailWord_3853949
  simp only [CollatzResearch.WordTrace]
  refine ⟨140565067914808449932164901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93710045276538966621443267 140565067914808449932164901)
  ·
    refine ⟨26355950234026584362280919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140565067914808449932164901 26355950234026584362280919)
    ·
      refine ⟨39533925351039876543421379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26355950234026584362280919 39533925351039876543421379)
      ·
        refine ⟨59300888026559814815132069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39533925351039876543421379 59300888026559814815132069)
        ·
          refine ⟨11118916504979965277837263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59300888026559814815132069 11118916504979965277837263)
          ·
            refine ⟨16678374757469947916755895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11118916504979965277837263 16678374757469947916755895)
            ·
              refine ⟨25017562136204921875133843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16678374757469947916755895 25017562136204921875133843)
              ·
                refine ⟨37526343204307382812700765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25017562136204921875133843 37526343204307382812700765)
                ·
                  refine ⟨14072378701615268554762787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37526343204307382812700765 14072378701615268554762787)
                  ·
                    refine ⟨21108568052422902832144181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14072378701615268554762787 21108568052422902832144181)
                    ·
                      refine ⟨1978928254914647140513517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21108568052422902832144181 1978928254914647140513517)
                      ·
                        rfl

theorem cell23_3853949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_3853949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853949 prefixEnd_3853949 := by exact prefixLift 3853949
  have htrace : WordTrace (prefixWord ++ tailWord_3853949) baseStart_3853949 baseEnd_3853949 := by
    simpa [prefixWord, tailWord_3853949, baseEnd_3853949] using wordTrace_append hprefix tailTrace_3853949
  have hstable : (prefixWord ++ tailWord_3853949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853949).length < 2 ^ (prefixWord ++ tailWord_3853949).sum := by decide
  have hdescent : baseEnd_3853949 < baseStart_3853949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853952 : List Nat := [2, 1, 1, 2, 1, 4, 2, 10]
def baseStart_3853952 : Nat := 118140960795 + 3853952 * 2 ^ 59
def prefixEnd_3853952 : Nat := 4983230072969 + 3 ^ 40 * 3853952 * 2
def baseEnd_3853952 : Nat := 73293696124318912176889

theorem tailTrace_3853952 : CollatzResearch.WordTrace tailWord_3853952 prefixEnd_3853952 73293696124318912176889 := by
  unfold tailWord_3853952
  simp only [CollatzResearch.WordTrace]
  refine ⟨70282588666898790722262055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93710118222531720963016073 70282588666898790722262055)
  ·
    refine ⟨105423883000348186083393083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70282588666898790722262055 105423883000348186083393083)
    ·
      refine ⟨158135824500522279125089625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105423883000348186083393083 158135824500522279125089625)
      ·
        refine ⟨118601868375391709343817219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158135824500522279125089625 118601868375391709343817219)
        ·
          refine ⟨177902802563087564015725829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118601868375391709343817219 177902802563087564015725829)
          ·
            refine ⟨33356775480578918252948593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177902802563087564015725829 33356775480578918252948593)
            ·
              refine ⟨25017581610434188689711445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33356775480578918252948593 25017581610434188689711445)
              ·
                refine ⟨73293696124318912176889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25017581610434188689711445 73293696124318912176889)
                ·
                  rfl

theorem cell23_3853952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 10].length) (baseStart_3853952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853952 prefixEnd_3853952 := by exact prefixLift 3853952
  have htrace : WordTrace (prefixWord ++ tailWord_3853952) baseStart_3853952 baseEnd_3853952 := by
    simpa [prefixWord, tailWord_3853952, baseEnd_3853952] using wordTrace_append hprefix tailTrace_3853952
  have hstable : (prefixWord ++ tailWord_3853952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853952).length < 2 ^ (prefixWord ++ tailWord_3853952).sum := by decide
  have hdescent : baseEnd_3853952 < baseStart_3853952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853959 : List Nat := [1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 6]
def baseStart_3853959 : Nat := 118140960795 + 3853959 * 2 ^ 59
def prefixEnd_3853959 : Nat := 4983230072969 + 3 ^ 40 * 3853959 * 2
def baseEnd_3853959 : Nat := 1978933389721192101388471

theorem tailTrace_3853959 : CollatzResearch.WordTrace tailWord_3853959 prefixEnd_3853959 1978933389721192101388471 := by
  unfold tailWord_3853959
  simp only [CollatzResearch.WordTrace]
  refine ⟨140565432644772221640028931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93710288429848147760019287 140565432644772221640028931)
  ·
    refine ⟨210848148967158332460043397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140565432644772221640028931 210848148967158332460043397)
    ·
      refine ⟨39534027931342187336258137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210848148967158332460043397 39534027931342187336258137)
      ·
        refine ⟨29650520948506640502193603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39534027931342187336258137 29650520948506640502193603)
        ·
          refine ⟨44475781422759960753290405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29650520948506640502193603 44475781422759960753290405)
          ·
            refine ⟨8339209016767492641241951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44475781422759960753290405 8339209016767492641241951)
            ·
              refine ⟨12508813525151238961862927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8339209016767492641241951 12508813525151238961862927)
              ·
                refine ⟨18763220287726858442794391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12508813525151238961862927 18763220287726858442794391)
                ·
                  refine ⟨28144830431590287664191587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18763220287726858442794391 28144830431590287664191587)
                  ·
                    refine ⟨42217245647385431496287381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28144830431590287664191587 42217245647385431496287381)
                    ·
                      refine ⟨1978933389721192101388471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42217245647385431496287381 1978933389721192101388471)
                      ·
                        rfl

theorem cell23_3853959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_3853959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853959 prefixEnd_3853959 := by exact prefixLift 3853959
  have htrace : WordTrace (prefixWord ++ tailWord_3853959) baseStart_3853959 baseEnd_3853959 := by
    simpa [prefixWord, tailWord_3853959, baseEnd_3853959] using wordTrace_append hprefix tailTrace_3853959
  have hstable : (prefixWord ++ tailWord_3853959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853959).length < 2 ^ (prefixWord ++ tailWord_3853959).sum := by decide
  have hdescent : baseEnd_3853959 < baseStart_3853959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3853983 : List Nat := [1, 1, 2, 7, 1, 1, 2, 1, 1, 1, 5]
def baseStart_3853983 : Nat := 118140960795 + 3853983 * 2 ^ 59
def prefixEnd_3853983 : Nat := 4983230072969 + 3 ^ 40 * 3853983 * 2
def baseEnd_3853983 : Nat := 1978945713256900007488361

theorem tailTrace_3853983 : CollatzResearch.WordTrace tailWord_3853983 prefixEnd_3853983 1978945713256900007488361 := by
  unfold tailWord_3853983
  simp only [CollatzResearch.WordTrace]
  refine ⟨140566307996685273738902603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93710871997790182492601735 140566307996685273738902603)
  ·
    refine ⟨210849461995027910608353905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140566307996685273738902603 210849461995027910608353905)
    ·
      refine ⟨158137096496270932956265429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210849461995027910608353905 158137096496270932956265429)
      ·
        refine ⟨3706338199131349991162471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 158137096496270932956265429 3706338199131349991162471)
        ·
          refine ⟨5559507298697024986743707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3706338199131349991162471 5559507298697024986743707)
          ·
            refine ⟨8339260948045537480115561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5559507298697024986743707 8339260948045537480115561)
            ·
              refine ⟨6254445711034153110086671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8339260948045537480115561 6254445711034153110086671)
              ·
                refine ⟨9381668566551229665130007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6254445711034153110086671 9381668566551229665130007)
                ·
                  refine ⟨14072502849826844497695011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9381668566551229665130007 14072502849826844497695011)
                  ·
                    refine ⟨21108754274740266746542517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14072502849826844497695011 21108754274740266746542517)
                    ·
                      refine ⟨1978945713256900007488361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21108754274740266746542517 1978945713256900007488361)
                      ·
                        rfl

theorem cell23_3853983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_3853983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3853983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3853983 prefixEnd_3853983 := by exact prefixLift 3853983
  have htrace : WordTrace (prefixWord ++ tailWord_3853983) baseStart_3853983 baseEnd_3853983 := by
    simpa [prefixWord, tailWord_3853983, baseEnd_3853983] using wordTrace_append hprefix tailTrace_3853983
  have hstable : (prefixWord ++ tailWord_3853983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3853983).length < 2 ^ (prefixWord ++ tailWord_3853983).sum := by decide
  have hdescent : baseEnd_3853983 < baseStart_3853983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3853983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854013 : List Nat := [1, 4, 1, 2, 1, 2, 3, 3, 2, 1, 3]
def baseStart_3854013 : Nat := 118140960795 + 3854013 * 2 ^ 59
def prefixEnd_3854013 : Nat := 4983230072969 + 3 ^ 40 * 3854013 * 2
def baseEnd_3854013 : Nat := 1978961117676534890113223

theorem tailTrace_3854013 : CollatzResearch.WordTrace tailWord_3854013 prefixEnd_3854013 1978961117676534890113223 := by
  unfold tailWord_3854013
  simp only [CollatzResearch.WordTrace]
  refine ⟨140567402186576588862494693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93711601457717725908329795 140567402186576588862494693)
  ·
    refine ⟨26356387909983110411717755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140567402186576588862494693 26356387909983110411717755)
    ·
      refine ⟨39534581864974665617576633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26356387909983110411717755 39534581864974665617576633)
      ·
        refine ⟨29650936398730999213182475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39534581864974665617576633 29650936398730999213182475)
        ·
          refine ⟨44476404598096498819773713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29650936398730999213182475 44476404598096498819773713)
          ·
            refine ⟨33357303448572374114830285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44476404598096498819773713 33357303448572374114830285)
            ·
              refine ⟨12508988793214640293061357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33357303448572374114830285 12508988793214640293061357)
              ·
                refine ⟨4690870797455490109898009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12508988793214640293061357 4690870797455490109898009)
                ·
                  refine ⟨3518153098091617582423507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4690870797455490109898009 3518153098091617582423507)
                  ·
                    refine ⟨5277229647137426373635261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3518153098091617582423507 5277229647137426373635261)
                    ·
                      refine ⟨1978961117676534890113223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5277229647137426373635261 1978961117676534890113223)
                      ·
                        rfl

theorem cell23_3854013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_3854013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854013 prefixEnd_3854013 := by exact prefixLift 3854013
  have htrace : WordTrace (prefixWord ++ tailWord_3854013) baseStart_3854013 baseEnd_3854013 := by
    simpa [prefixWord, tailWord_3854013, baseEnd_3854013] using wordTrace_append hprefix tailTrace_3854013
  have hstable : (prefixWord ++ tailWord_3854013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854013).length < 2 ^ (prefixWord ++ tailWord_3854013).sum := by decide
  have hdescent : baseEnd_3854013 < baseStart_3854013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854039 : List Nat := [1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 5]
def baseStart_3854039 : Nat := 118140960795 + 3854039 * 2 ^ 59
def prefixEnd_3854039 : Nat := 4983230072969 + 3 ^ 40 * 3854039 * 2
def baseEnd_3854039 : Nat := 1978974468173551788388103

theorem tailTrace_3854039 : CollatzResearch.WordTrace tailWord_3854039 prefixEnd_3854039 1978974468173551788388103 := by
  unfold tailWord_3854039
  simp only [CollatzResearch.WordTrace]
  refine ⟨140568350484482395302941171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93712233656321596868627447 140568350484482395302941171)
  ·
    refine ⟨210852525726723592954411757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140568350484482395302941171 210852525726723592954411757)
    ·
      refine ⟨79069697147521347357904409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210852525726723592954411757 79069697147521347357904409)
      ·
        refine ⟨59302272860641010518428307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79069697147521347357904409 59302272860641010518428307)
        ·
          refine ⟨88953409290961515777642461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59302272860641010518428307 88953409290961515777642461)
          ·
            refine ⟨33357528484110568416615923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88953409290961515777642461 33357528484110568416615923)
            ·
              refine ⟨50036292726165852624923885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33357528484110568416615923 50036292726165852624923885)
              ·
                refine ⟨18763609772312194734346457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50036292726165852624923885 18763609772312194734346457)
                ·
                  refine ⟨14072707329234146050759843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18763609772312194734346457 14072707329234146050759843)
                  ·
                    refine ⟨21109060993851219076139765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14072707329234146050759843 21109060993851219076139765)
                    ·
                      refine ⟨1978974468173551788388103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21109060993851219076139765 1978974468173551788388103)
                      ·
                        rfl

theorem cell23_3854039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_3854039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854039 prefixEnd_3854039 := by exact prefixLift 3854039
  have htrace : WordTrace (prefixWord ++ tailWord_3854039) baseStart_3854039 baseEnd_3854039 := by
    simpa [prefixWord, tailWord_3854039, baseEnd_3854039] using wordTrace_append hprefix tailTrace_3854039
  have hstable : (prefixWord ++ tailWord_3854039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854039).length < 2 ^ (prefixWord ++ tailWord_3854039).sum := by decide
  have hdescent : baseEnd_3854039 < baseStart_3854039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854040 : List Nat := [2, 1, 2, 2, 3, 1, 5, 1, 1, 3, 2]
def baseStart_3854040 : Nat := 118140960795 + 3854040 * 2 ^ 59
def prefixEnd_3854040 : Nat := 4983230072969 + 3 ^ 40 * 3854040 * 2
def baseEnd_3854040 : Nat := 1978974981654206284475599

theorem tailTrace_3854040 : CollatzResearch.WordTrace tailWord_3854040 prefixEnd_3854040 1978974981654206284475599 := by
  unfold tailWord_3854040
  simp only [CollatzResearch.WordTrace]
  refine ⟨70284193478739386236863787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93712257971652514982485049 70284193478739386236863787)
  ·
    refine ⟨105426290218109079355295681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70284193478739386236863787 105426290218109079355295681)
    ·
      refine ⟨79069717663581809516471761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105426290218109079355295681 79069717663581809516471761)
      ·
        refine ⟨59302288247686357137353821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79069717663581809516471761 59302288247686357137353821)
        ·
          refine ⟨22238358092882383926507683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59302288247686357137353821 22238358092882383926507683)
          ·
            refine ⟨33357537139323575889761525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22238358092882383926507683 33357537139323575889761525)
            ·
              refine ⟨3127269106811585239665143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33357537139323575889761525 3127269106811585239665143)
              ·
                refine ⟨4690903660217377859497715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3127269106811585239665143 4690903660217377859497715)
                ·
                  refine ⟨7036355490326066789246573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4690903660217377859497715 7036355490326066789246573)
                  ·
                    refine ⟨2638633308872275045967465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7036355490326066789246573 2638633308872275045967465)
                    ·
                      refine ⟨1978974981654206284475599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2638633308872275045967465 1978974981654206284475599)
                      ·
                        rfl

theorem cell23_3854040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 1, 3, 2].length) (baseStart_3854040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854040 prefixEnd_3854040 := by exact prefixLift 3854040
  have htrace : WordTrace (prefixWord ++ tailWord_3854040) baseStart_3854040 baseEnd_3854040 := by
    simpa [prefixWord, tailWord_3854040, baseEnd_3854040] using wordTrace_append hprefix tailTrace_3854040
  have hstable : (prefixWord ++ tailWord_3854040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854040).length < 2 ^ (prefixWord ++ tailWord_3854040).sum := by decide
  have hdescent : baseEnd_3854040 < baseStart_3854040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854056 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 2, 4, 3]
def baseStart_3854056 : Nat := 118140960795 + 3854056 * 2 ^ 59
def prefixEnd_3854056 : Nat := 4983230072969 + 3 ^ 40 * 3854056 * 2
def baseEnd_3854056 : Nat := 1978983197344678221875525

theorem tailTrace_3854056 : CollatzResearch.WordTrace tailWord_3854056 prefixEnd_3854056 1978983197344678221875525 := by
  unfold tailWord_3854056
  simp only [CollatzResearch.WordTrace]
  refine ⟨70284485262710403603155011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93712647016947204804206681 70284485262710403603155011)
  ·
    refine ⟨105426727894065605404732517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70284485262710403603155011 105426727894065605404732517)
    ·
      refine ⟨19767511480137301013387347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105426727894065605404732517 19767511480137301013387347)
      ·
        refine ⟨29651267220205951520081021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19767511480137301013387347 29651267220205951520081021)
        ·
          refine ⟨11119225207577231820030383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29651267220205951520081021 11119225207577231820030383)
          ·
            refine ⟨16678837811365847730045575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11119225207577231820030383 16678837811365847730045575)
            ·
              refine ⟨25018256717048771595068363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16678837811365847730045575 25018256717048771595068363)
              ·
                refine ⟨37527385075573157392602545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25018256717048771595068363 37527385075573157392602545)
                ·
                  refine ⟨28145538806679868044451909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37527385075573157392602545 28145538806679868044451909)
                  ·
                    refine ⟨5277288526252475258334733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28145538806679868044451909 5277288526252475258334733)
                    ·
                      refine ⟨1978983197344678221875525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5277288526252475258334733 1978983197344678221875525)
                      ·
                        rfl

theorem cell23_3854056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_3854056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854056 prefixEnd_3854056 := by exact prefixLift 3854056
  have htrace : WordTrace (prefixWord ++ tailWord_3854056) baseStart_3854056 baseEnd_3854056 := by
    simpa [prefixWord, tailWord_3854056, baseEnd_3854056] using wordTrace_append hprefix tailTrace_3854056
  have hstable : (prefixWord ++ tailWord_3854056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854056).length < 2 ^ (prefixWord ++ tailWord_3854056).sum := by decide
  have hdescent : baseEnd_3854056 < baseStart_3854056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854066 : List Nat := [3, 2, 1, 3, 1, 1, 3, 1, 2, 2, 4]
def baseStart_3854066 : Nat := 118140960795 + 3854066 * 2 ^ 59
def prefixEnd_3854066 : Nat := 4983230072969 + 3 ^ 40 * 3854066 * 2
def baseEnd_3854066 : Nat := 1978988332151223182750479

theorem tailTrace_3854066 : CollatzResearch.WordTrace tailWord_3854066 prefixEnd_3854066 1978988332151223182750479 := by
  unfold tailWord_3854066
  simp only [CollatzResearch.WordTrace]
  refine ⟨35142333813846144728543513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93712890170256385942782701 35142333813846144728543513)
  ·
    refine ⟨26356750360384608546407635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35142333813846144728543513 26356750360384608546407635)
    ·
      refine ⟨39535125540576912819611453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26356750360384608546407635 39535125540576912819611453)
      ·
        refine ⟨14825672077716342307354295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39535125540576912819611453 14825672077716342307354295)
        ·
          refine ⟨22238508116574513461031443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14825672077716342307354295 22238508116574513461031443)
          ·
            refine ⟨33357762174861770191547165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22238508116574513461031443 33357762174861770191547165)
            ·
              refine ⟨12509160815573163821830187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33357762174861770191547165 12509160815573163821830187)
              ·
                refine ⟨18763741223359745732745281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12509160815573163821830187 18763741223359745732745281)
                ·
                  refine ⟨14072805917519809299558961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18763741223359745732745281 14072805917519809299558961)
                  ·
                    refine ⟨10554604438139856974669221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14072805917519809299558961 10554604438139856974669221)
                    ·
                      refine ⟨1978988332151223182750479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10554604438139856974669221 1978988332151223182750479)
                      ·
                        rfl

theorem cell23_3854066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_3854066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854066 prefixEnd_3854066 := by exact prefixLift 3854066
  have htrace : WordTrace (prefixWord ++ tailWord_3854066) baseStart_3854066 baseEnd_3854066 := by
    simpa [prefixWord, tailWord_3854066, baseEnd_3854066] using wordTrace_append hprefix tailTrace_3854066
  have hstable : (prefixWord ++ tailWord_3854066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854066).length < 2 ^ (prefixWord ++ tailWord_3854066).sum := by decide
  have hdescent : baseEnd_3854066 < baseStart_3854066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854070 : List Nat := [5, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2]
def baseStart_3854070 : Nat := 118140960795 + 3854070 * 2 ^ 59
def prefixEnd_3854070 : Nat := 4983230072969 + 3 ^ 40 * 3854070 * 2
def baseEnd_3854070 : Nat := 1978990386073841167100461

theorem tailTrace_3854070 : CollatzResearch.WordTrace tailWord_3854070 prefixEnd_3854070 1978990386073841167100461 := by
  unfold tailWord_3854070
  simp only [CollatzResearch.WordTrace]
  refine ⟨8785592571710630474832479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93712987431580058398213109 8785592571710630474832479)
  ·
    refine ⟨13178388857565945712248719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8785592571710630474832479 13178388857565945712248719)
    ·
      refine ⟨19767583286348918568373079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13178388857565945712248719 19767583286348918568373079)
      ·
        refine ⟨29651374929523377852559619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19767583286348918568373079 29651374929523377852559619)
        ·
          refine ⟨44477062394285066778839429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29651374929523377852559619 44477062394285066778839429)
          ·
            refine ⟨8339449198928450021032393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44477062394285066778839429 8339449198928450021032393)
            ·
              refine ⟨6254586899196337515774295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8339449198928450021032393 6254586899196337515774295)
              ·
                refine ⟨9381880348794506273661443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6254586899196337515774295 9381880348794506273661443)
                ·
                  refine ⟨14072820523191759410492165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9381880348794506273661443 14072820523191759410492165)
                  ·
                    refine ⟨2638653848098454889467281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14072820523191759410492165 2638653848098454889467281)
                    ·
                      refine ⟨1978990386073841167100461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2638653848098454889467281 1978990386073841167100461)
                      ·
                        rfl

theorem cell23_3854070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_3854070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854070 prefixEnd_3854070 := by exact prefixLift 3854070
  have htrace : WordTrace (prefixWord ++ tailWord_3854070) baseStart_3854070 baseEnd_3854070 := by
    simpa [prefixWord, tailWord_3854070, baseEnd_3854070] using wordTrace_append hprefix tailTrace_3854070
  have hstable : (prefixWord ++ tailWord_3854070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854070).length < 2 ^ (prefixWord ++ tailWord_3854070).sum := by decide
  have hdescent : baseEnd_3854070 < baseStart_3854070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854099 : List Nat := [1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 5]
def baseStart_3854099 : Nat := 118140960795 + 3854099 * 2 ^ 59
def prefixEnd_3854099 : Nat := 4983230072969 + 3 ^ 40 * 3854099 * 2
def baseEnd_3854099 : Nat := 1979005277012821553637827

theorem tailTrace_3854099 : CollatzResearch.WordTrace tailWord_3854099 prefixEnd_3854099 1979005277012821553637827 := by
  unfold tailWord_3854099
  simp only [CollatzResearch.WordTrace]
  refine ⟨140570538864265025550125351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93713692576176683700083567 140570538864265025550125351)
  ·
    refine ⟨210855808296397538325188027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140570538864265025550125351 210855808296397538325188027)
    ·
      refine ⟨316283712444596307487782041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210855808296397538325188027 316283712444596307487782041)
      ·
        refine ⟨237212784333447230615836531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316283712444596307487782041 237212784333447230615836531)
        ·
          refine ⟨355819176500170845923754797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237212784333447230615836531 355819176500170845923754797)
          ·
            refine ⟨133432191187564067221408049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 355819176500170845923754797 133432191187564067221408049)
            ·
              refine ⟨100074143390673050416056037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133432191187564067221408049 100074143390673050416056037)
              ·
                refine ⟨18763901885751196953010507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100074143390673050416056037 18763901885751196953010507)
                ·
                  refine ⟨28145852828626795429515761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18763901885751196953010507 28145852828626795429515761)
                  ·
                    refine ⟨21109389621470096572136821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28145852828626795429515761 21109389621470096572136821)
                    ·
                      refine ⟨1979005277012821553637827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21109389621470096572136821 1979005277012821553637827)
                      ·
                        rfl

theorem cell23_3854099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 5].length) (baseStart_3854099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854099 prefixEnd_3854099 := by exact prefixLift 3854099
  have htrace : WordTrace (prefixWord ++ tailWord_3854099) baseStart_3854099 baseEnd_3854099 := by
    simpa [prefixWord, tailWord_3854099, baseEnd_3854099] using wordTrace_append hprefix tailTrace_3854099
  have hstable : (prefixWord ++ tailWord_3854099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854099).length < 2 ^ (prefixWord ++ tailWord_3854099).sum := by decide
  have hdescent : baseEnd_3854099 < baseStart_3854099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854149 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 10]
def baseStart_3854149 : Nat := 118140960795 + 3854149 * 2 ^ 59
def prefixEnd_3854149 : Nat := 4983230072969 + 3 ^ 40 * 3854149 * 2
def baseEnd_3854149 : Nat := 219892327893949595334733

theorem tailTrace_3854149 : CollatzResearch.WordTrace tailWord_3854149 prefixEnd_3854149 219892327893949595334733 := by
  unfold tailWord_3854149
  simp only [CollatzResearch.WordTrace]
  refine ⟨140572362514083884089445501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93714908342722589392963667 140572362514083884089445501)
  ·
    refine ⟨52714635942781456533542063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140572362514083884089445501 52714635942781456533542063)
    ·
      refine ⟨79071953914172184800313095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52714635942781456533542063 79071953914172184800313095)
      ·
        refine ⟨118607930871258277200469643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79071953914172184800313095 118607930871258277200469643)
        ·
          refine ⟨177911896306887415800704465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118607930871258277200469643 177911896306887415800704465)
          ·
            refine ⟨133433922230165561850528349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177911896306887415800704465 133433922230165561850528349)
            ·
              refine ⟨50037720836312085693948131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133433922230165561850528349 50037720836312085693948131)
              ·
                refine ⟨75056581254468128540922197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50037720836312085693948131 75056581254468128540922197)
                ·
                  refine ⟨219892327893949595334733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 75056581254468128540922197 219892327893949595334733)
                  ·
                    rfl

theorem cell23_3854149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 10].length) (baseStart_3854149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854149 prefixEnd_3854149 := by exact prefixLift 3854149
  have htrace : WordTrace (prefixWord ++ tailWord_3854149) baseStart_3854149 baseEnd_3854149 := by
    simpa [prefixWord, tailWord_3854149, baseEnd_3854149] using wordTrace_append hprefix tailTrace_3854149
  have hstable : (prefixWord ++ tailWord_3854149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854149).length < 2 ^ (prefixWord ++ tailWord_3854149).sum := by decide
  have hdescent : baseEnd_3854149 < baseStart_3854149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854193 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 5, 1, 3]
def baseStart_3854193 : Nat := 118140960795 + 3854193 * 2 ^ 59
def prefixEnd_3854193 : Nat := 4983230072969 + 3 ^ 40 * 3854193 * 2
def baseEnd_3854193 : Nat := 1979053544194344185862395

theorem tailTrace_3854193 : CollatzResearch.WordTrace tailWord_3854193 prefixEnd_3854193 1979053544194344185862395 := by
  unfold tailWord_3854193
  simp only [CollatzResearch.WordTrace]
  refine ⟨140573967325924479604047233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93715978217282986402698155 140573967325924479604047233)
  ·
    refine ⟨105430475494443359703035425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140573967325924479604047233 105430475494443359703035425)
    ·
      refine ⟨79072856620832519777276569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105430475494443359703035425 79072856620832519777276569)
      ·
        refine ⟨59304642465624389832957427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79072856620832519777276569 59304642465624389832957427)
        ·
          refine ⟨88956963698436584749436141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59304642465624389832957427 88956963698436584749436141)
          ·
            refine ⟨33358861386913719281038553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88956963698436584749436141 33358861386913719281038553)
            ·
              refine ⟨25019146040185289460778915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33358861386913719281038553 25019146040185289460778915)
              ·
                refine ⟨37528719060277934191168373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25019146040185289460778915 37528719060277934191168373)
                ·
                  refine ⟨3518317411901056330422035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37528719060277934191168373 3518317411901056330422035)
                  ·
                    refine ⟨5277476117851584495633053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3518317411901056330422035 5277476117851584495633053)
                    ·
                      refine ⟨1979053544194344185862395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5277476117851584495633053 1979053544194344185862395)
                      ·
                        rfl

theorem cell23_3854193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_3854193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854193 prefixEnd_3854193 := by exact prefixLift 3854193
  have htrace : WordTrace (prefixWord ++ tailWord_3854193) baseStart_3854193 baseEnd_3854193 := by
    simpa [prefixWord, tailWord_3854193, baseEnd_3854193] using wordTrace_append hprefix tailTrace_3854193
  have hstable : (prefixWord ++ tailWord_3854193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854193).length < 2 ^ (prefixWord ++ tailWord_3854193).sum := by decide
  have hdescent : baseEnd_3854193 < baseStart_3854193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854267 : List Nat := [1, 1, 1, 1, 1, 2, 2, 9, 1, 2, 2]
def baseStart_3854267 : Nat := 118140960795 + 3854267 * 2 ^ 59
def prefixEnd_3854267 : Nat := 4983230072969 + 3 ^ 40 * 3854267 * 2
def baseEnd_3854267 : Nat := 1979091541762776896337055

theorem tailTrace_3854267 : CollatzResearch.WordTrace tailWord_3854267 prefixEnd_3854267 1979091541762776896337055 := by
  unfold tailWord_3854267
  simp only [CollatzResearch.WordTrace]
  refine ⟨140576666327656390242241055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93717777551770926828160703 140576666327656390242241055)
  ·
    refine ⟨210864999491484585363361583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140576666327656390242241055 210864999491484585363361583)
    ·
      refine ⟨316297499237226878045042375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210864999491484585363361583 316297499237226878045042375)
      ·
        refine ⟨474446248855840317067563563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316297499237226878045042375 474446248855840317067563563)
        ·
          refine ⟨711669373283760475601345345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474446248855840317067563563 711669373283760475601345345)
          ·
            refine ⟨533752029962820356701009009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 711669373283760475601345345 533752029962820356701009009)
            ·
              refine ⟨400314022472115267525756757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 533752029962820356701009009 400314022472115267525756757)
              ·
                refine ⟨2345589975422550395658731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 400314022472115267525756757 2345589975422550395658731)
                ·
                  refine ⟨3518384963133825593488097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2345589975422550395658731 3518384963133825593488097)
                  ·
                    refine ⟨2638788722350369195116073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3518384963133825593488097 2638788722350369195116073)
                    ·
                      refine ⟨1979091541762776896337055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2638788722350369195116073 1979091541762776896337055)
                      ·
                        rfl

theorem cell23_3854267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9, 1, 2, 2].length) (baseStart_3854267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854267 prefixEnd_3854267 := by exact prefixLift 3854267
  have htrace : WordTrace (prefixWord ++ tailWord_3854267) baseStart_3854267 baseEnd_3854267 := by
    simpa [prefixWord, tailWord_3854267, baseEnd_3854267] using wordTrace_append hprefix tailTrace_3854267
  have hstable : (prefixWord ++ tailWord_3854267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854267).length < 2 ^ (prefixWord ++ tailWord_3854267).sum := by decide
  have hdescent : baseEnd_3854267 < baseStart_3854267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854284 : List Nat := [2, 2, 1, 4, 1, 2, 2, 4, 1, 2, 2]
def baseStart_3854284 : Nat := 118140960795 + 3854284 * 2 ^ 59
def prefixEnd_3854284 : Nat := 4983230072969 + 3 ^ 40 * 3854284 * 2
def baseEnd_3854284 : Nat := 1979100270933903329824477

theorem tailTrace_3854284 : CollatzResearch.WordTrace tailWord_3854284 prefixEnd_3854284 1979100270933903329824477 := by
  unfold tailWord_3854284
  simp only [CollatzResearch.WordTrace]
  refine ⟨70288643184297401072804953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93718190912396534763739937 70288643184297401072804953)
  ·
    refine ⟨52716482388223050804603715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70288643184297401072804953 52716482388223050804603715)
    ·
      refine ⟨79074723582334576206905573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52716482388223050804603715 79074723582334576206905573)
      ·
        refine ⟨14826510671687733038794795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79074723582334576206905573 14826510671687733038794795)
        ·
          refine ⟨22239766007531599558192193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14826510671687733038794795 22239766007531599558192193)
          ·
            refine ⟨16679824505648699668644145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22239766007531599558192193 16679824505648699668644145)
            ·
              refine ⟨12509868379236524751483109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16679824505648699668644145 12509868379236524751483109)
              ·
                refine ⟨2345600321106848390903083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12509868379236524751483109 2345600321106848390903083)
                ·
                  refine ⟨3518400481660272586354625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2345600321106848390903083 3518400481660272586354625)
                  ·
                    refine ⟨2638800361245204439765969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3518400481660272586354625 2638800361245204439765969)
                    ·
                      refine ⟨1979100270933903329824477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2638800361245204439765969 1979100270933903329824477)
                      ·
                        rfl

theorem cell23_3854284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_3854284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854284 prefixEnd_3854284 := by exact prefixLift 3854284
  have htrace : WordTrace (prefixWord ++ tailWord_3854284) baseStart_3854284 baseEnd_3854284 := by
    simpa [prefixWord, tailWord_3854284, baseEnd_3854284] using wordTrace_append hprefix tailTrace_3854284
  have hstable : (prefixWord ++ tailWord_3854284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854284).length < 2 ^ (prefixWord ++ tailWord_3854284).sum := by decide
  have hdescent : baseEnd_3854284 < baseStart_3854284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854294 : List Nat := [5, 2, 1, 1, 4, 1, 1, 1, 1, 6]
def baseStart_3854294 : Nat := 118140960795 + 3854294 * 2 ^ 59
def prefixEnd_3854294 : Nat := 4983230072969 + 3 ^ 40 * 3854294 * 2
def baseEnd_3854294 : Nat := 659701801913482763566477

theorem tailTrace_3854294 : CollatzResearch.WordTrace tailWord_3854294 prefixEnd_3854294 659701801913482763566477 := by
  unfold tailWord_3854294
  simp only [CollatzResearch.WordTrace]
  refine ⟨8786103193659910865842121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93718434065705715902315957 8786103193659910865842121)
  ·
    refine ⟨6589577395244933149381591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8786103193659910865842121 6589577395244933149381591)
    ·
      refine ⟨9884366092867399724072387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6589577395244933149381591 9884366092867399724072387)
      ·
        refine ⟨14826549139301099586108581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9884366092867399724072387 14826549139301099586108581)
        ·
          refine ⟨2779977963618956172395359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14826549139301099586108581 2779977963618956172395359)
          ·
            refine ⟨4169966945428434258593039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2779977963618956172395359 4169966945428434258593039)
            ·
              refine ⟨6254950418142651387889559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4169966945428434258593039 6254950418142651387889559)
              ·
                refine ⟨9382425627213977081834339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6254950418142651387889559 9382425627213977081834339)
                ·
                  refine ⟨14073638440820965622751509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9382425627213977081834339 14073638440820965622751509)
                  ·
                    refine ⟨659701801913482763566477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14073638440820965622751509 659701801913482763566477)
                    ·
                      rfl

theorem cell23_3854294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_3854294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854294 prefixEnd_3854294 := by exact prefixLift 3854294
  have htrace : WordTrace (prefixWord ++ tailWord_3854294) baseStart_3854294 baseEnd_3854294 := by
    simpa [prefixWord, tailWord_3854294, baseEnd_3854294] using wordTrace_append hprefix tailTrace_3854294
  have hstable : (prefixWord ++ tailWord_3854294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854294).length < 2 ^ (prefixWord ++ tailWord_3854294).sum := by decide
  have hdescent : baseEnd_3854294 < baseStart_3854294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854297 : List Nat := [1, 2, 1, 2, 7, 1, 1, 1, 1, 2, 4]
def baseStart_3854297 : Nat := 118140960795 + 3854297 * 2 ^ 59
def prefixEnd_3854297 : Nat := 4983230072969 + 3 ^ 40 * 3854297 * 2
def baseEnd_3854297 : Nat := 1979106946182411778961917

theorem tailTrace_3854297 : CollatzResearch.WordTrace tailWord_3854297 prefixEnd_3854297 1979106946182411778961917 := by
  unfold tailWord_3854297
  simp only [CollatzResearch.WordTrace]
  refine ⟨140577760517547705365833145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93718507011698470243888763 140577760517547705365833145)
  ·
    refine ⟨105433320388160779024374859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140577760517547705365833145 105433320388160779024374859)
    ·
      refine ⟨158149980582241168536562289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105433320388160779024374859 158149980582241168536562289)
      ·
        refine ⟨118612485436680876402421717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158149980582241168536562289 118612485436680876402421717)
        ·
          refine ⟨2779980127422208040681759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 118612485436680876402421717 2779980127422208040681759)
          ·
            refine ⟨4169970191133312061022639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2779980127422208040681759 4169970191133312061022639)
            ·
              refine ⟨6254955286699968091533959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4169970191133312061022639 6254955286699968091533959)
              ·
                refine ⟨9382432930049952137300939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6254955286699968091533959 9382432930049952137300939)
                ·
                  refine ⟨14073649395074928205951409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9382432930049952137300939 14073649395074928205951409)
                  ·
                    refine ⟨10555237046306196154463557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14073649395074928205951409 10555237046306196154463557)
                    ·
                      refine ⟨1979106946182411778961917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10555237046306196154463557 1979106946182411778961917)
                      ·
                        rfl

theorem cell23_3854297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 1, 2, 4].length) (baseStart_3854297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854297 prefixEnd_3854297 := by exact prefixLift 3854297
  have htrace : WordTrace (prefixWord ++ tailWord_3854297) baseStart_3854297 baseEnd_3854297 := by
    simpa [prefixWord, tailWord_3854297, baseEnd_3854297] using wordTrace_append hprefix tailTrace_3854297
  have hstable : (prefixWord ++ tailWord_3854297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854297).length < 2 ^ (prefixWord ++ tailWord_3854297).sum := by decide
  have hdescent : baseEnd_3854297 < baseStart_3854297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854316 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 1, 8]
def baseStart_3854316 : Nat := 118140960795 + 3854316 * 2 ^ 59
def prefixEnd_3854316 : Nat := 4983230072969 + 3 ^ 40 * 3854316 * 2
def baseEnd_3854316 : Nat := 659705567438282401541443

theorem tailTrace_3854316 : CollatzResearch.WordTrace tailWord_3854316 prefixEnd_3854316 659705567438282401541443 := by
  unfold tailWord_3854316
  simp only [CollatzResearch.WordTrace]
  refine ⟨70289226752239435805387401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93718969002985914407183201 70289226752239435805387401)
  ·
    refine ⟨52716920064179576854040551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70289226752239435805387401 52716920064179576854040551)
    ·
      refine ⟨79075380096269365281060827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52716920064179576854040551 79075380096269365281060827)
      ·
        refine ⟨118613070144404047921591241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79075380096269365281060827 118613070144404047921591241)
        ·
          refine ⟨88959802608303035941193431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118613070144404047921591241 88959802608303035941193431)
          ·
            refine ⟨133439703912454553911790147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88959802608303035941193431 133439703912454553911790147)
            ·
              refine ⟨200159555868681830867685221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133439703912454553911790147 200159555868681830867685221)
              ·
                refine ⟨37529916725377843287690979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200159555868681830867685221 37529916725377843287690979)
                ·
                  refine ⟨56294875088066764931536469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37529916725377843287690979 56294875088066764931536469)
                  ·
                    refine ⟨659705567438282401541443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56294875088066764931536469 659705567438282401541443)
                    ·
                      rfl

theorem cell23_3854316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 8].length) (baseStart_3854316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854316 prefixEnd_3854316 := by exact prefixLift 3854316
  have htrace : WordTrace (prefixWord ++ tailWord_3854316) baseStart_3854316 baseEnd_3854316 := by
    simpa [prefixWord, tailWord_3854316, baseEnd_3854316] using wordTrace_append hprefix tailTrace_3854316
  have hstable : (prefixWord ++ tailWord_3854316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854316).length < 2 ^ (prefixWord ++ tailWord_3854316).sum := by decide
  have hdescent : baseEnd_3854316 < baseStart_3854316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854336 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 6]
def baseStart_3854336 : Nat := 118140960795 + 3854336 * 2 ^ 59
def prefixEnd_3854336 : Nat := 4983230072969 + 3 ^ 40 * 3854336 * 2
def baseEnd_3854336 : Nat := 1979126971927937126374237

theorem tailTrace_3854336 : CollatzResearch.WordTrace tailWord_3854336 prefixEnd_3854336 1979126971927937126374237 := by
  unfold tailWord_3854336
  simp only [CollatzResearch.WordTrace]
  refine ⟨70289591482203207513251431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93719455309604276684335241 70289591482203207513251431)
  ·
    refine ⟨105434387223304811269877147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70289591482203207513251431 105434387223304811269877147)
    ·
      refine ⟨158151580834957216904815721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105434387223304811269877147 158151580834957216904815721)
      ·
        refine ⟨118613685626217912678611791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158151580834957216904815721 118613685626217912678611791)
        ·
          refine ⟨177920528439326869017917687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118613685626217912678611791 177920528439326869017917687)
          ·
            refine ⟨266880792658990303526876531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177920528439326869017917687 266880792658990303526876531)
            ·
              refine ⟨400321188988485455290314797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266880792658990303526876531 400321188988485455290314797)
              ·
                refine ⟨150120445870682045733868049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 400321188988485455290314797 150120445870682045733868049)
                ·
                  refine ⟨112590334403011534300401037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150120445870682045733868049 112590334403011534300401037)
                  ·
                    refine ⟨42221375401129325362650389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112590334403011534300401037 42221375401129325362650389)
                    ·
                      refine ⟨1979126971927937126374237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42221375401129325362650389 1979126971927937126374237)
                      ·
                        rfl

theorem cell23_3854336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_3854336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854336 prefixEnd_3854336 := by exact prefixLift 3854336
  have htrace : WordTrace (prefixWord ++ tailWord_3854336) baseStart_3854336 baseEnd_3854336 := by
    simpa [prefixWord, tailWord_3854336, baseEnd_3854336] using wordTrace_append hprefix tailTrace_3854336
  have hstable : (prefixWord ++ tailWord_3854336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854336).length < 2 ^ (prefixWord ++ tailWord_3854336).sum := by decide
  have hdescent : baseEnd_3854336 < baseStart_3854336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854400 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 2, 5, 2]
def baseStart_3854400 : Nat := 118140960795 + 3854400 * 2 ^ 59
def prefixEnd_3854400 : Nat := 4983230072969 + 3 ^ 40 * 3854400 * 2
def baseEnd_3854400 : Nat := 1979159834689824875973943

theorem tailTrace_3854400 : CollatzResearch.WordTrace tailWord_3854400 prefixEnd_3854400 1979159834689824875973943 := by
  unfold tailWord_3854400
  simp only [CollatzResearch.WordTrace]
  refine ⟨70290758618087276978416327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93721011490783035971221769 70290758618087276978416327)
  ·
    refine ⟨105436137927130915467624491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70290758618087276978416327 105436137927130915467624491)
    ·
      refine ⟨158154206890696373201436737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105436137927130915467624491 158154206890696373201436737)
      ·
        refine ⟨118615655168022279901077553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158154206890696373201436737 118615655168022279901077553)
        ·
          refine ⟨88961741376016709925808165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118615655168022279901077553 88961741376016709925808165)
          ·
            refine ⟨16680326508003133111089031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88961741376016709925808165 16680326508003133111089031)
            ·
              refine ⟨25020489762004699666633547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16680326508003133111089031 25020489762004699666633547)
              ·
                refine ⟨37530734643007049499950321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25020489762004699666633547 37530734643007049499950321)
                ·
                  refine ⟨28148050982255287124962741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37530734643007049499950321 28148050982255287124962741)
                  ·
                    refine ⟨2638879779586433167965257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28148050982255287124962741 2638879779586433167965257)
                    ·
                      refine ⟨1979159834689824875973943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2638879779586433167965257 1979159834689824875973943)
                      ·
                        rfl

theorem cell23_3854400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 2, 5, 2].length) (baseStart_3854400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854400 prefixEnd_3854400 := by exact prefixLift 3854400
  have htrace : WordTrace (prefixWord ++ tailWord_3854400) baseStart_3854400 baseEnd_3854400 := by
    simpa [prefixWord, tailWord_3854400, baseEnd_3854400] using wordTrace_append hprefix tailTrace_3854400
  have hstable : (prefixWord ++ tailWord_3854400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854400).length < 2 ^ (prefixWord ++ tailWord_3854400).sum := by decide
  have hdescent : baseEnd_3854400 < baseStart_3854400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854457 : List Nat := [1, 2, 1, 3, 4, 2, 2, 1, 3, 4]
def baseStart_3854457 : Nat := 118140960795 + 3854457 * 2 ^ 59
def prefixEnd_3854457 : Nat := 4983230072969 + 3 ^ 40 * 3854457 * 2
def baseEnd_3854457 : Nat := 659729701029043717653727

theorem tailTrace_3854457 : CollatzResearch.WordTrace tailWord_3854457 prefixEnd_3854457 659729701029043717653727 := by
  unfold tailWord_3854457
  simp only [CollatzResearch.WordTrace]
  refine ⟨140583596196968052691657625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93722397464645368461105083 140583596196968052691657625)
  ·
    refine ⟨105437697147726039518743219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140583596196968052691657625 105437697147726039518743219)
    ·
      refine ⟨158156545721589059278114829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105437697147726039518743219 158156545721589059278114829)
      ·
        refine ⟨59308704645595897229293061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158156545721589059278114829 59308704645595897229293061)
        ·
          refine ⟨11120382121049230730492449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59308704645595897229293061 11120382121049230730492449)
          ·
            refine ⟨8340286590786923047869337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11120382121049230730492449 8340286590786923047869337)
            ·
              refine ⟨6255214943090192285902003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8340286590786923047869337 6255214943090192285902003)
              ·
                refine ⟨9382822414635288428853005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6255214943090192285902003 9382822414635288428853005)
                ·
                  refine ⟨3518558405488233160819877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9382822414635288428853005 3518558405488233160819877)
                  ·
                    refine ⟨659729701029043717653727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3518558405488233160819877 659729701029043717653727)
                    ·
                      rfl

theorem cell23_3854457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 3, 4].length) (baseStart_3854457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854457 prefixEnd_3854457 := by exact prefixLift 3854457
  have htrace : WordTrace (prefixWord ++ tailWord_3854457) baseStart_3854457 baseEnd_3854457 := by
    simpa [prefixWord, tailWord_3854457, baseEnd_3854457] using wordTrace_append hprefix tailTrace_3854457
  have hstable : (prefixWord ++ tailWord_3854457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854457).length < 2 ^ (prefixWord ++ tailWord_3854457).sum := by decide
  have hdescent : baseEnd_3854457 < baseStart_3854457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854473 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 1, 2, 6]
def baseStart_3854473 : Nat := 118140960795 + 3854473 * 2 ^ 59
def prefixEnd_3854473 : Nat := 4983230072969 + 3 ^ 40 * 3854473 * 2
def baseEnd_3854473 : Nat := 1979197318777603090361107

theorem tailTrace_3854473 : CollatzResearch.WordTrace tailWord_3854473 prefixEnd_3854473 1979197318777603090361107 := by
  unfold tailWord_3854473
  simp only [CollatzResearch.WordTrace]
  refine ⟨140584179764910087424240073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93722786509940058282826715 140584179764910087424240073)
  ·
    refine ⟨105438134823682565568180055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140584179764910087424240073 105438134823682565568180055)
    ·
      refine ⟨158157202235523848352270083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105438134823682565568180055 158157202235523848352270083)
      ·
        refine ⟨237235803353285772528405125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158157202235523848352270083 237235803353285772528405125)
        ·
          refine ⟨44481713128741082349075961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237235803353285772528405125 44481713128741082349075961)
          ·
            refine ⟨33361284846555811761806971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44481713128741082349075961 33361284846555811761806971)
            ·
              refine ⟨50041927269833717642710457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33361284846555811761806971 50041927269833717642710457)
              ·
                refine ⟨37531445452375288232032843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50041927269833717642710457 37531445452375288232032843)
                ·
                  refine ⟨56297168178562932348049265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37531445452375288232032843 56297168178562932348049265)
                  ·
                    refine ⟨42222876133922199261036949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56297168178562932348049265 42222876133922199261036949)
                    ·
                      refine ⟨1979197318777603090361107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42222876133922199261036949 1979197318777603090361107)
                      ·
                        rfl

theorem cell23_3854473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 2, 6].length) (baseStart_3854473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854473 prefixEnd_3854473 := by exact prefixLift 3854473
  have htrace : WordTrace (prefixWord ++ tailWord_3854473) baseStart_3854473 baseEnd_3854473 := by
    simpa [prefixWord, tailWord_3854473, baseEnd_3854473] using wordTrace_append hprefix tailTrace_3854473
  have hstable : (prefixWord ++ tailWord_3854473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854473).length < 2 ^ (prefixWord ++ tailWord_3854473).sum := by decide
  have hdescent : baseEnd_3854473 < baseStart_3854473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854520 : List Nat := [2, 1, 2, 1, 2, 1, 4, 2, 3, 1, 4]
def baseStart_3854520 : Nat := 118140960795 + 3854520 * 2 ^ 59
def prefixEnd_3854520 : Nat := 4983230072969 + 3 ^ 40 * 3854520 * 2
def baseEnd_3854520 : Nat := 1979221452368364406473391

theorem tailTrace_3854520 : CollatzResearch.WordTrace tailWord_3854520 prefixEnd_3854520 1979221452368364406473391 := by
  unfold tailWord_3854520
  simp only [CollatzResearch.WordTrace]
  refine ⟨70292946997869907225600507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93723929330493209634134009 70292946997869907225600507)
  ·
    refine ⟨105439420496804860838400761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70292946997869907225600507 105439420496804860838400761)
    ·
      refine ⟨79079565372603645628800571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105439420496804860838400761 79079565372603645628800571)
      ·
        refine ⟨118619348058905468443200857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79079565372603645628800571 118619348058905468443200857)
        ·
          refine ⟨88964511044179101332400643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118619348058905468443200857 88964511044179101332400643)
          ·
            refine ⟨133446766566268651998600965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88964511044179101332400643 133446766566268651998600965)
            ·
              refine ⟨25021268731175372249737681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133446766566268651998600965 25021268731175372249737681)
              ·
                refine ⟨18765951548381529187303261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25021268731175372249737681 18765951548381529187303261)
                ·
                  refine ⟨7037231830643073445238723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18765951548381529187303261 7037231830643073445238723)
                  ·
                    refine ⟨10555847745964610167858085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7037231830643073445238723 10555847745964610167858085)
                    ·
                      refine ⟨1979221452368364406473391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10555847745964610167858085 1979221452368364406473391)
                      ·
                        rfl

theorem cell23_3854520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_3854520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854520 prefixEnd_3854520 := by exact prefixLift 3854520
  have htrace : WordTrace (prefixWord ++ tailWord_3854520) baseStart_3854520 baseEnd_3854520 := by
    simpa [prefixWord, tailWord_3854520, baseEnd_3854520] using wordTrace_append hprefix tailTrace_3854520
  have hstable : (prefixWord ++ tailWord_3854520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854520).length < 2 ^ (prefixWord ++ tailWord_3854520).sum := by decide
  have hdescent : baseEnd_3854520 < baseStart_3854520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854543 : List Nat := [1, 1, 2, 1, 1, 3, 3, 11]
def baseStart_3854543 : Nat := 118140960795 + 3854543 * 2 ^ 59
def prefixEnd_3854543 : Nat := 4983230072969 + 3 ^ 40 * 3854543 * 2
def baseEnd_3854543 : Nat := 73304935645311770980955

theorem tailTrace_3854543 : CollatzResearch.WordTrace tailWord_3854543 prefixEnd_3854543 73304935645311770980955 := by
  unfold tailWord_3854543
  simp only [CollatzResearch.WordTrace]
  refine ⟨140586732874656489379288283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93724488583104326252858855 140586732874656489379288283)
  ·
    refine ⟨210880099311984734068932425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140586732874656489379288283 210880099311984734068932425)
    ·
      refine ⟨158160074483988550551699319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210880099311984734068932425 158160074483988550551699319)
      ·
        refine ⟨237240111725982825827548979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158160074483988550551699319 237240111725982825827548979)
        ·
          refine ⟨355860167588974238741323469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237240111725982825827548979 355860167588974238741323469)
          ·
            refine ⟨133447562845865339527996301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 355860167588974238741323469 133447562845865339527996301)
            ·
              refine ⟨50042836067199502322998613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133447562845865339527996301 50042836067199502322998613)
              ·
                refine ⟨73304935645311770980955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 50042836067199502322998613 73304935645311770980955)
                ·
                  rfl

theorem cell23_3854543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 11].length) (baseStart_3854543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854543 prefixEnd_3854543 := by exact prefixLift 3854543
  have htrace : WordTrace (prefixWord ++ tailWord_3854543) baseStart_3854543 baseEnd_3854543 := by
    simpa [prefixWord, tailWord_3854543, baseEnd_3854543] using wordTrace_append hprefix tailTrace_3854543
  have hstable : (prefixWord ++ tailWord_3854543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854543).length < 2 ^ (prefixWord ++ tailWord_3854543).sum := by decide
  have hdescent : baseEnd_3854543 < baseStart_3854543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854571 : List Nat := [1, 1, 1, 1, 2, 5, 3, 4, 1, 2, 2]
def baseStart_3854571 : Nat := 118140960795 + 3854571 * 2 ^ 59
def prefixEnd_3854571 : Nat := 4983230072969 + 3 ^ 40 * 3854571 * 2
def baseEnd_3854571 : Nat := 1979247639881743706935657

theorem tailTrace_3854571 : CollatzResearch.WordTrace tailWord_3854571 prefixEnd_3854571 1979247639881743706935657 := by
  unfold tailWord_3854571
  simp only [CollatzResearch.WordTrace]
  refine ⟨140587754118555050161307567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93725169412370033440871711 140587754118555050161307567)
  ·
    refine ⟨210881631177832575241961351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140587754118555050161307567 210881631177832575241961351)
    ·
      refine ⟨316322446766748862862942027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210881631177832575241961351 316322446766748862862942027)
      ·
        refine ⟨474483670150123294294413041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316322446766748862862942027 474483670150123294294413041)
        ·
          refine ⟨355862752612592470720809781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 474483670150123294294413041 355862752612592470720809781)
          ·
            refine ⟨33362133057430544130075917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 355862752612592470720809781 33362133057430544130075917)
            ·
              refine ⟨12510799896536454048778469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33362133057430544130075917 12510799896536454048778469)
              ·
                refine ⟨2345774980600585134145963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12510799896536454048778469 2345774980600585134145963)
                ·
                  refine ⟨3518662470900877701218945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2345774980600585134145963 3518662470900877701218945)
                  ·
                    refine ⟨2638996853175658275914209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3518662470900877701218945 2638996853175658275914209)
                    ·
                      refine ⟨1979247639881743706935657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2638996853175658275914209 1979247639881743706935657)
                      ·
                        rfl

theorem cell23_3854571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 4, 1, 2, 2].length) (baseStart_3854571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854571 prefixEnd_3854571 := by exact prefixLift 3854571
  have htrace : WordTrace (prefixWord ++ tailWord_3854571) baseStart_3854571 baseEnd_3854571 := by
    simpa [prefixWord, tailWord_3854571, baseEnd_3854571] using wordTrace_append hprefix tailTrace_3854571
  have hstable : (prefixWord ++ tailWord_3854571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854571).length < 2 ^ (prefixWord ++ tailWord_3854571).sum := by decide
  have hdescent : baseEnd_3854571 < baseStart_3854571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854594 : List Nat := [3, 4, 1, 1, 2, 2, 3, 7]
def baseStart_3854594 : Nat := 118140960795 + 3854594 * 2 ^ 59
def prefixEnd_3854594 : Nat := 4983230072969 + 3 ^ 40 * 3854594 * 2
def baseEnd_3854594 : Nat := 73305905553214708035113

theorem tailTrace_3854594 : CollatzResearch.WordTrace tailWord_3854594 prefixEnd_3854594 73305905553214708035113 := by
  unfold tailWord_3854594
  simp only [CollatzResearch.WordTrace]
  refine ⟨35147148249367931272348709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93725728664981150059596557 35147148249367931272348709)
  ·
    refine ⟨6590090296756487113565383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35147148249367931272348709 6590090296756487113565383)
    ·
      refine ⟨9885135445134730670348075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6590090296756487113565383 9885135445134730670348075)
      ·
        refine ⟨14827703167702096005522113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9885135445134730670348075 14827703167702096005522113)
        ·
          refine ⟨11120777375776572004141585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14827703167702096005522113 11120777375776572004141585)
          ·
            refine ⟨8340583031832429003106189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11120777375776572004141585 8340583031832429003106189)
            ·
              refine ⟨3127718636937160876164821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8340583031832429003106189 3127718636937160876164821)
              ·
                refine ⟨73305905553214708035113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3127718636937160876164821 73305905553214708035113)
                ·
                  rfl

theorem cell23_3854594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 7].length) (baseStart_3854594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854594 prefixEnd_3854594 := by exact prefixLift 3854594
  have htrace : WordTrace (prefixWord ++ tailWord_3854594) baseStart_3854594 baseEnd_3854594 := by
    simpa [prefixWord, tailWord_3854594, baseEnd_3854594] using wordTrace_append hprefix tailTrace_3854594
  have hstable : (prefixWord ++ tailWord_3854594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854594).length < 2 ^ (prefixWord ++ tailWord_3854594).sum := by decide
  have hdescent : baseEnd_3854594 < baseStart_3854594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854621 : List Nat := [1, 4, 2, 3, 2, 1, 1, 1, 4, 1, 3]
def baseStart_3854621 : Nat := 118140960795 + 3854621 * 2 ^ 59
def prefixEnd_3854621 : Nat := 4983230072969 + 3 ^ 40 * 3854621 * 2
def baseEnd_3854621 : Nat := 1979273313914468511310427

theorem tailTrace_3854621 : CollatzResearch.WordTrace tailWord_3854621 prefixEnd_3854621 1979273313914468511310427 := by
  unfold tailWord_3854621
  simp only [CollatzResearch.WordTrace]
  refine ⟨140589577768373908700627717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93726385178915939133751811 140589577768373908700627717)
  ·
    refine ⟨26360545831570107881367697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140589577768373908700627717 26360545831570107881367697)
    ·
      refine ⟨19770409373677580911025773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26360545831570107881367697 19770409373677580911025773)
      ·
        refine ⟨7413903515129092841634665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19770409373677580911025773 7413903515129092841634665)
        ·
          refine ⟨5560427636346819631225999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7413903515129092841634665 5560427636346819631225999)
          ·
            refine ⟨8340641454520229446838999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5560427636346819631225999 8340641454520229446838999)
            ·
              refine ⟨12510962181780344170258499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8340641454520229446838999 12510962181780344170258499)
              ·
                refine ⟨18766443272670516255387749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12510962181780344170258499 18766443272670516255387749)
                ·
                  refine ⟨3518708113625721797885203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18766443272670516255387749 3518708113625721797885203)
                  ·
                    refine ⟨5278062170438582696827805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3518708113625721797885203 5278062170438582696827805)
                    ·
                      refine ⟨1979273313914468511310427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5278062170438582696827805 1979273313914468511310427)
                      ·
                        rfl

theorem cell23_3854621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_3854621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854621 prefixEnd_3854621 := by exact prefixLift 3854621
  have htrace : WordTrace (prefixWord ++ tailWord_3854621) baseStart_3854621 baseEnd_3854621 := by
    simpa [prefixWord, tailWord_3854621, baseEnd_3854621] using wordTrace_append hprefix tailTrace_3854621
  have hstable : (prefixWord ++ tailWord_3854621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854621).length < 2 ^ (prefixWord ++ tailWord_3854621).sum := by decide
  have hdescent : baseEnd_3854621 < baseStart_3854621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854638 : List Nat := [4, 1, 3, 3, 1, 2, 1, 1, 1, 3, 3]
def baseStart_3854638 : Nat := 118140960795 + 3854638 * 2 ^ 59
def prefixEnd_3854638 : Nat := 4983230072969 + 3 ^ 40 * 3854638 * 2
def baseEnd_3854638 : Nat := 1979282043085594944797849

theorem tailTrace_3854638 : CollatzResearch.WordTrace tailWord_3854638 prefixEnd_3854638 1979282043085594944797849 := by
  unfold tailWord_3854638
  simp only [CollatzResearch.WordTrace]
  refine ⟨17573774726164040075499571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93726798539541547069331045 17573774726164040075499571)
  ·
    refine ⟨26360662089246060113249357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17573774726164040075499571 26360662089246060113249357)
    ·
      refine ⟨9885248283467272542468509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26360662089246060113249357 9885248283467272542468509)
      ·
        refine ⟨3706968106300227203425691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9885248283467272542468509 3706968106300227203425691)
        ·
          refine ⟨5560452159450340805138537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3706968106300227203425691 5560452159450340805138537)
          ·
            refine ⟨4170339119587755603853903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5560452159450340805138537 4170339119587755603853903)
            ·
              refine ⟨6255508679381633405780855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4170339119587755603853903 6255508679381633405780855)
              ·
                refine ⟨9383263019072450108671283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6255508679381633405780855 9383263019072450108671283)
                ·
                  refine ⟨14074894528608675163006925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9383263019072450108671283 14074894528608675163006925)
                  ·
                    refine ⟨5278085448228253186127597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14074894528608675163006925 5278085448228253186127597)
                    ·
                      refine ⟨1979282043085594944797849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5278085448228253186127597 1979282043085594944797849)
                      ·
                        rfl

theorem cell23_3854638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_3854638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854638 prefixEnd_3854638 := by exact prefixLift 3854638
  have htrace : WordTrace (prefixWord ++ tailWord_3854638) baseStart_3854638 baseEnd_3854638 := by
    simpa [prefixWord, tailWord_3854638, baseEnd_3854638] using wordTrace_append hprefix tailTrace_3854638
  have hstable : (prefixWord ++ tailWord_3854638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854638).length < 2 ^ (prefixWord ++ tailWord_3854638).sum := by decide
  have hdescent : baseEnd_3854638 < baseStart_3854638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854640 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 4]
def baseStart_3854640 : Nat := 118140960795 + 3854640 * 2 ^ 59
def prefixEnd_3854640 : Nat := 4983230072969 + 3 ^ 40 * 3854640 * 2
def baseEnd_3854640 : Nat := 1979283070046903936972839

theorem tailTrace_3854640 : CollatzResearch.WordTrace tailWord_3854640 prefixEnd_3854640 1979283070046903936972839 := by
  unfold tailWord_3854640
  simp only [CollatzResearch.WordTrace]
  refine ⟨70295135377652537472784687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93726847170203383297046249 70295135377652537472784687)
  ·
    refine ⟨105442703066478806209177031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70295135377652537472784687 105442703066478806209177031)
    ·
      refine ⟨158164054599718209313765547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105442703066478806209177031 158164054599718209313765547)
      ·
        refine ⟨237246081899577313970648321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158164054599718209313765547 237246081899577313970648321)
        ·
          refine ⟨177934561424682985477986241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237246081899577313970648321 177934561424682985477986241)
          ·
            refine ⟨133450921068512239108489681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177934561424682985477986241 133450921068512239108489681)
            ·
              refine ⟨100088190801384179331367261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133450921068512239108489681 100088190801384179331367261)
              ·
                refine ⟨37533071550519067249262723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100088190801384179331367261 37533071550519067249262723)
                ·
                  refine ⟨56299607325778600873894085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37533071550519067249262723 56299607325778600873894085)
                  ·
                    refine ⟨10556176373583487663855141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56299607325778600873894085 10556176373583487663855141)
                    ·
                      refine ⟨1979283070046903936972839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10556176373583487663855141 1979283070046903936972839)
                      ·
                        rfl

theorem cell23_3854640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 4].length) (baseStart_3854640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854640 prefixEnd_3854640 := by exact prefixLift 3854640
  have htrace : WordTrace (prefixWord ++ tailWord_3854640) baseStart_3854640 baseEnd_3854640 := by
    simpa [prefixWord, tailWord_3854640, baseEnd_3854640] using wordTrace_append hprefix tailTrace_3854640
  have hstable : (prefixWord ++ tailWord_3854640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854640).length < 2 ^ (prefixWord ++ tailWord_3854640).sum := by decide
  have hdescent : baseEnd_3854640 < baseStart_3854640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854667 : List Nat := [1, 1, 1, 1, 3, 1, 1, 9, 5]
def baseStart_3854667 : Nat := 118140960795 + 3854667 * 2 ^ 59
def prefixEnd_3854667 : Nat := 4983230072969 + 3 ^ 40 * 3854667 * 2
def baseEnd_3854667 : Nat := 219921881558286147926135

theorem tailTrace_3854667 : CollatzResearch.WordTrace tailWord_3854667 prefixEnd_3854667 219921881558286147926135 := by
  unfold tailWord_3854667
  simp only [CollatzResearch.WordTrace]
  refine ⟨140591255526207258556802255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93727503684138172371201503 140591255526207258556802255)
  ·
    refine ⟨210886883289310887835203383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140591255526207258556802255 210886883289310887835203383)
    ·
      refine ⟨316330324933966331752805075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210886883289310887835203383 316330324933966331752805075)
      ·
        refine ⟨474495487400949497629207613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316330324933966331752805075 474495487400949497629207613)
        ·
          refine ⟨177935807775356061610952855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 474495487400949497629207613 177935807775356061610952855)
          ·
            refine ⟨266903711663034092416429283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177935807775356061610952855 266903711663034092416429283)
            ·
              refine ⟨400355567494551138624643925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266903711663034092416429283 400355567494551138624643925)
              ·
                refine ⟨2345833403288385577878773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 400355567494551138624643925 2345833403288385577878773)
                ·
                  refine ⟨219921881558286147926135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2345833403288385577878773 219921881558286147926135)
                  ·
                    rfl

theorem cell23_3854667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 9, 5].length) (baseStart_3854667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854667 prefixEnd_3854667 := by exact prefixLift 3854667
  have htrace : WordTrace (prefixWord ++ tailWord_3854667) baseStart_3854667 baseEnd_3854667 := by
    simpa [prefixWord, tailWord_3854667, baseEnd_3854667] using wordTrace_append hprefix tailTrace_3854667
  have hstable : (prefixWord ++ tailWord_3854667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854667).length < 2 ^ (prefixWord ++ tailWord_3854667).sum := by decide
  have hdescent : baseEnd_3854667 < baseStart_3854667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854680 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 3, 7]
def baseStart_3854680 : Nat := 118140960795 + 3854680 * 2 ^ 59
def prefixEnd_3854680 : Nat := 4983230072969 + 3 ^ 40 * 3854680 * 2
def baseEnd_3854680 : Nat := 659767869757694593490885

theorem tailTrace_3854680 : CollatzResearch.WordTrace tailWord_3854680 prefixEnd_3854680 659767869757694593490885 := by
  unfold tailWord_3854680
  simp only [CollatzResearch.WordTrace]
  refine ⟨70295864837580080888512747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93727819783440107851350329 70295864837580080888512747)
  ·
    refine ⟨105443797256370121332769121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70295864837580080888512747 105443797256370121332769121)
    ·
      refine ⟨79082847942277590999576841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105443797256370121332769121 79082847942277590999576841)
      ·
        refine ⟨59312135956708193249682631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79082847942277590999576841 59312135956708193249682631)
        ·
          refine ⟨88968203935062289874523947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59312135956708193249682631 88968203935062289874523947)
          ·
            refine ⟨133452305902593434811785921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88968203935062289874523947 133452305902593434811785921)
            ·
              refine ⟨100089229426945076108839441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133452305902593434811785921 100089229426945076108839441)
              ·
                refine ⟨75066922070208807081629581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100089229426945076108839441 75066922070208807081629581)
                ·
                  refine ⟨28150095776328302655611093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75066922070208807081629581 28150095776328302655611093)
                  ·
                    refine ⟨659767869757694593490885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28150095776328302655611093 659767869757694593490885)
                    ·
                      rfl

theorem cell23_3854680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 3, 7].length) (baseStart_3854680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854680 prefixEnd_3854680 := by exact prefixLift 3854680
  have htrace : WordTrace (prefixWord ++ tailWord_3854680) baseStart_3854680 baseEnd_3854680 := by
    simpa [prefixWord, tailWord_3854680, baseEnd_3854680] using wordTrace_append hprefix tailTrace_3854680
  have hstable : (prefixWord ++ tailWord_3854680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854680).length < 2 ^ (prefixWord ++ tailWord_3854680).sum := by decide
  have hdescent : baseEnd_3854680 < baseStart_3854680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854695 : List Nat := [1, 1, 5, 1, 3, 3, 2, 1, 2, 2, 2]
def baseStart_3854695 : Nat := 118140960795 + 3854695 * 2 ^ 59
def prefixEnd_3854695 : Nat := 4983230072969 + 3 ^ 40 * 3854695 * 2
def baseEnd_3854695 : Nat := 1979311311482901221785087

theorem tailTrace_3854695 : CollatzResearch.WordTrace tailWord_3854695 prefixEnd_3854695 1979311311482901221785087 := by
  unfold tailWord_3854695
  simp only [CollatzResearch.WordTrace]
  refine ⟨140592276770105819338821539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93728184513403879559214359 140592276770105819338821539)
  ·
    refine ⟨210888415155158729008232309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140592276770105819338821539 210888415155158729008232309)
    ·
      refine ⟨19770788920796130844521779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 210888415155158729008232309 19770788920796130844521779)
      ·
        refine ⟨29656183381194196266782669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19770788920796130844521779 29656183381194196266782669)
        ·
          refine ⟨11121068767947823600043501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29656183381194196266782669 11121068767947823600043501)
          ·
            refine ⟨4170400787980433850016313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11121068767947823600043501 4170400787980433850016313)
            ·
              refine ⟨3127800590985325387512235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4170400787980433850016313 3127800590985325387512235)
              ·
                refine ⟨4691700886477988081268353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3127800590985325387512235 4691700886477988081268353)
                ·
                  refine ⟨3518775664858491060951265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4691700886477988081268353 3518775664858491060951265)
                  ·
                    refine ⟨2639081748643868295713449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3518775664858491060951265 2639081748643868295713449)
                    ·
                      refine ⟨1979311311482901221785087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2639081748643868295713449 1979311311482901221785087)
                      ·
                        rfl

theorem cell23_3854695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_3854695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854695 prefixEnd_3854695 := by exact prefixLift 3854695
  have htrace : WordTrace (prefixWord ++ tailWord_3854695) baseStart_3854695 baseEnd_3854695 := by
    simpa [prefixWord, tailWord_3854695, baseEnd_3854695] using wordTrace_append hprefix tailTrace_3854695
  have hstable : (prefixWord ++ tailWord_3854695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854695).length < 2 ^ (prefixWord ++ tailWord_3854695).sum := by decide
  have hdescent : baseEnd_3854695 < baseStart_3854695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854720 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 9]
def baseStart_3854720 : Nat := 118140960795 + 3854720 * 2 ^ 59
def prefixEnd_3854720 : Nat := 4983230072969 + 3 ^ 40 * 3854720 * 2
def baseEnd_3854720 : Nat := 1979324148499263623972471

theorem tailTrace_3854720 : CollatzResearch.WordTrace tailWord_3854720 prefixEnd_3854720 1979324148499263623972471 := by
  unfold tailWord_3854720
  simp only [CollatzResearch.WordTrace]
  refine ⟨70296594297507624304240807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93728792396676832405654409 70296594297507624304240807)
  ·
    refine ⟨105444891446261436456361211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70296594297507624304240807 105444891446261436456361211)
    ·
      refine ⟨158167337169392154684541817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105444891446261436456361211 158167337169392154684541817)
      ·
        refine ⟨118625502877044116013406363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158167337169392154684541817 118625502877044116013406363)
        ·
          refine ⟨177938254315566174020109545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118625502877044116013406363 177938254315566174020109545)
          ·
            refine ⟨133453690736674630515082159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177938254315566174020109545 133453690736674630515082159)
            ·
              refine ⟨200180536105011945772623239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133453690736674630515082159 200180536105011945772623239)
              ·
                refine ⟨300270804157517918658934859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200180536105011945772623239 300270804157517918658934859)
                ·
                  refine ⟨450406206236276877988402289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 300270804157517918658934859 450406206236276877988402289)
                  ·
                    refine ⟨337804654677207658491301717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 450406206236276877988402289 337804654677207658491301717)
                    ·
                      refine ⟨1979324148499263623972471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 337804654677207658491301717 1979324148499263623972471)
                      ·
                        rfl

theorem cell23_3854720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_3854720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854720 prefixEnd_3854720 := by exact prefixLift 3854720
  have htrace : WordTrace (prefixWord ++ tailWord_3854720) baseStart_3854720 baseEnd_3854720 := by
    simpa [prefixWord, tailWord_3854720, baseEnd_3854720] using wordTrace_append hprefix tailTrace_3854720
  have hstable : (prefixWord ++ tailWord_3854720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854720).length < 2 ^ (prefixWord ++ tailWord_3854720).sum := by decide
  have hdescent : baseEnd_3854720 < baseStart_3854720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854754 : List Nat := [3, 3, 1, 2, 1, 1, 2, 2, 1, 4, 3]
def baseStart_3854754 : Nat := 118140960795 + 3854754 * 2 ^ 59
def prefixEnd_3854754 : Nat := 4983230072969 + 3 ^ 40 * 3854754 * 2
def baseEnd_3854754 : Nat := 1979341606841516490947315

theorem tailTrace_3854754 : CollatzResearch.WordTrace tailWord_3854754 prefixEnd_3854754 1979341606841516490947315 := by
  unfold tailWord_3854754
  simp only [CollatzResearch.WordTrace]
  refine ⟨35148607169223018103804829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93729619117928048276812877 35148607169223018103804829)
  ·
    refine ⟨13180727688458631788926811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35148607169223018103804829 13180727688458631788926811)
    ·
      refine ⟨19771091532687947683390217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13180727688458631788926811 19771091532687947683390217)
      ·
        refine ⟨14828318649515960762542663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19771091532687947683390217 14828318649515960762542663)
        ·
          refine ⟨22242477974273941143813995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14828318649515960762542663 22242477974273941143813995)
          ·
            refine ⟨33363716961410911715720993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22242477974273941143813995 33363716961410911715720993)
            ·
              refine ⟨25022787721058183786790745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33363716961410911715720993 25022787721058183786790745)
              ·
                refine ⟨18767090790793637840093059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25022787721058183786790745 18767090790793637840093059)
                ·
                  refine ⟨28150636186190456760139589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18767090790793637840093059 28150636186190456760139589)
                  ·
                    refine ⟨5278244284910710642526173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28150636186190456760139589 5278244284910710642526173)
                    ·
                      refine ⟨1979341606841516490947315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5278244284910710642526173 1979341606841516490947315)
                      ·
                        rfl

theorem cell23_3854754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_3854754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854754 prefixEnd_3854754 := by exact prefixLift 3854754
  have htrace : WordTrace (prefixWord ++ tailWord_3854754) baseStart_3854754 baseEnd_3854754 := by
    simpa [prefixWord, tailWord_3854754, baseEnd_3854754] using wordTrace_append hprefix tailTrace_3854754
  have hstable : (prefixWord ++ tailWord_3854754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854754).length < 2 ^ (prefixWord ++ tailWord_3854754).sum := by decide
  have hdescent : baseEnd_3854754 < baseStart_3854754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854757 : List Nat := [1, 3, 1, 2, 1, 1, 3, 5, 6]
def baseStart_3854757 : Nat := 118140960795 + 3854757 * 2 ^ 59
def prefixEnd_3854757 : Nat := 4983230072969 + 3 ^ 40 * 3854757 * 2
def baseEnd_3854757 : Nat := 219927016364831108801089

theorem tailTrace_3854757 : CollatzResearch.WordTrace tailWord_3854757 prefixEnd_3854757 219927016364831108801089 := by
  unfold tailWord_3854757
  simp only [CollatzResearch.WordTrace]
  refine ⟨140594538095881203927578525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93729692063920802618385683 140594538095881203927578525)
  ·
    refine ⟨52722951785955451472841947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140594538095881203927578525 52722951785955451472841947)
    ·
      refine ⟨79084427678933177209262921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52722951785955451472841947 79084427678933177209262921)
      ·
        refine ⟨59313320759199882906947191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79084427678933177209262921 59313320759199882906947191)
        ·
          refine ⟨88969981138799824360420787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59313320759199882906947191 88969981138799824360420787)
          ·
            refine ⟨133454971708199736540631181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88969981138799824360420787 133454971708199736540631181)
            ·
              refine ⟨50045614390574901202736693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133454971708199736540631181 50045614390574901202736693)
              ·
                refine ⟨4691776349116396987756565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50045614390574901202736693 4691776349116396987756565)
                ·
                  refine ⟨219927016364831108801089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4691776349116396987756565 219927016364831108801089)
                  ·
                    rfl

theorem cell23_3854757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 6].length) (baseStart_3854757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854757 prefixEnd_3854757 := by exact prefixLift 3854757
  have htrace : WordTrace (prefixWord ++ tailWord_3854757) baseStart_3854757 baseEnd_3854757 := by
    simpa [prefixWord, tailWord_3854757, baseEnd_3854757] using wordTrace_append hprefix tailTrace_3854757
  have hstable : (prefixWord ++ tailWord_3854757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854757).length < 2 ^ (prefixWord ++ tailWord_3854757).sum := by decide
  have hdescent : baseEnd_3854757 < baseStart_3854757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854784 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 7, 1, 3]
def baseStart_3854784 : Nat := 118140960795 + 3854784 * 2 ^ 59
def prefixEnd_3854784 : Nat := 4983230072969 + 3 ^ 40 * 3854784 * 2
def baseEnd_3854784 : Nat := 1979357011261151373572177

theorem tailTrace_3854784 : CollatzResearch.WordTrace tailWord_3854784 prefixEnd_3854784 1979357011261151373572177 := by
  unfold tailWord_3854784
  simp only [CollatzResearch.WordTrace]
  refine ⟨70297761433391693769405703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93730348577855591692540937 70297761433391693769405703)
  ·
    refine ⟨105446642150087540654108555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70297761433391693769405703 105446642150087540654108555)
    ·
      refine ⟨158169963225131310981162833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105446642150087540654108555 158169963225131310981162833)
      ·
        refine ⟨118627472418848483235872125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158169963225131310981162833 118627472418848483235872125)
        ·
          refine ⟨44485302157068181213452047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118627472418848483235872125 44485302157068181213452047)
          ·
            refine ⟨66727953235602271820178071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44485302157068181213452047 66727953235602271820178071)
            ·
              refine ⟨100091929853403407730267107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66727953235602271820178071 100091929853403407730267107)
              ·
                refine ⟨150137894780105111595400661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100091929853403407730267107 150137894780105111595400661)
                ·
                  refine ⟨3518856908908713553017203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 150137894780105111595400661 3518856908908713553017203)
                  ·
                    refine ⟨5278285363363070329525805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3518856908908713553017203 5278285363363070329525805)
                    ·
                      refine ⟨1979357011261151373572177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5278285363363070329525805 1979357011261151373572177)
                      ·
                        rfl

theorem cell23_3854784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 7, 1, 3].length) (baseStart_3854784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854784 prefixEnd_3854784 := by exact prefixLift 3854784
  have htrace : WordTrace (prefixWord ++ tailWord_3854784) baseStart_3854784 baseEnd_3854784 := by
    simpa [prefixWord, tailWord_3854784, baseEnd_3854784] using wordTrace_append hprefix tailTrace_3854784
  have hstable : (prefixWord ++ tailWord_3854784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854784).length < 2 ^ (prefixWord ++ tailWord_3854784).sum := by decide
  have hdescent : baseEnd_3854784 < baseStart_3854784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854827 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 5]
def baseStart_3854827 : Nat := 118140960795 + 3854827 * 2 ^ 59
def prefixEnd_3854827 : Nat := 4983230072969 + 3 ^ 40 * 3854827 * 2
def baseEnd_3854827 : Nat := 1979379090929294705334479

theorem tailTrace_3854827 : CollatzResearch.WordTrace tailWord_3854827 prefixEnd_3854827 1979379090929294705334479 := by
  unfold tailWord_3854827
  simp only [CollatzResearch.WordTrace]
  refine ⟨140597091205627605882626735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93731394137085070588417823 140597091205627605882626735)
  ·
    refine ⟨210895636808441408823940103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140597091205627605882626735 210895636808441408823940103)
    ·
      refine ⟨316343455212662113235910155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210895636808441408823940103 316343455212662113235910155)
      ·
        refine ⟨474515182818993169853865233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316343455212662113235910155 474515182818993169853865233)
        ·
          refine ⟨355886387114244877390398925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 474515182818993169853865233 355886387114244877390398925)
          ·
            refine ⟨133457395167841829021399597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 355886387114244877390398925 133457395167841829021399597)
            ·
              refine ⟨50046523187940685883024849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133457395167841829021399597 50046523187940685883024849)
              ·
                refine ⟨37534892390955514412268637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50046523187940685883024849 37534892390955514412268637)
                ·
                  refine ⟨14075584646608317904600739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37534892390955514412268637 14075584646608317904600739)
                  ·
                    refine ⟨21113376969912476856901109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14075584646608317904600739 21113376969912476856901109)
                    ·
                      refine ⟨1979379090929294705334479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21113376969912476856901109 1979379090929294705334479)
                      ·
                        rfl

theorem cell23_3854827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 5].length) (baseStart_3854827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854827 prefixEnd_3854827 := by exact prefixLift 3854827
  have htrace : WordTrace (prefixWord ++ tailWord_3854827) baseStart_3854827 baseEnd_3854827 := by
    simpa [prefixWord, tailWord_3854827, baseEnd_3854827] using wordTrace_append hprefix tailTrace_3854827
  have hstable : (prefixWord ++ tailWord_3854827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854827).length < 2 ^ (prefixWord ++ tailWord_3854827).sum := by decide
  have hdescent : baseEnd_3854827 < baseStart_3854827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854841 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 5, 2, 2]
def baseStart_3854841 : Nat := 118140960795 + 3854841 * 2 ^ 59
def prefixEnd_3854841 : Nat := 4983230072969 + 3 ^ 40 * 3854841 * 2
def baseEnd_3854841 : Nat := 1979386279658457650559415

theorem tailTrace_3854841 : CollatzResearch.WordTrace tailWord_3854841 prefixEnd_3854841 1979386279658457650559415 := by
  unfold tailWord_3854841
  simp only [CollatzResearch.WordTrace]
  refine ⟨140597601827576886273636377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93731734551717924182424251 140597601827576886273636377)
  ·
    refine ⟨105448201370682664705227283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140597601827576886273636377 105448201370682664705227283)
    ·
      refine ⟨158172302056023997057840925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105448201370682664705227283 158172302056023997057840925)
      ·
        refine ⟨59314613271008998896690347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158172302056023997057840925 59314613271008998896690347)
        ·
          refine ⟨88971919906513498345035521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59314613271008998896690347 88971919906513498345035521)
          ·
            refine ⟨66728939929885123758776641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88971919906513498345035521 66728939929885123758776641)
            ·
              refine ⟨50046704947413842819082481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66728939929885123758776641 50046704947413842819082481)
              ·
                refine ⟨37535028710560382114311861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50046704947413842819082481 37535028710560382114311861)
                ·
                  refine ⟨3518908941615035823216737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37535028710560382114311861 3518908941615035823216737)
                  ·
                    refine ⟨2639181706211276867412553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3518908941615035823216737 2639181706211276867412553)
                    ·
                      refine ⟨1979386279658457650559415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2639181706211276867412553 1979386279658457650559415)
                      ·
                        rfl

theorem cell23_3854841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 5, 2, 2].length) (baseStart_3854841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854841 prefixEnd_3854841 := by exact prefixLift 3854841
  have htrace : WordTrace (prefixWord ++ tailWord_3854841) baseStart_3854841 baseEnd_3854841 := by
    simpa [prefixWord, tailWord_3854841, baseEnd_3854841] using wordTrace_append hprefix tailTrace_3854841
  have hstable : (prefixWord ++ tailWord_3854841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854841).length < 2 ^ (prefixWord ++ tailWord_3854841).sum := by decide
  have hdescent : baseEnd_3854841 < baseStart_3854841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854844 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 5, 2, 3]
def baseStart_3854844 : Nat := 118140960795 + 3854844 * 2 ^ 59
def prefixEnd_3854844 : Nat := 4983230072969 + 3 ^ 40 * 3854844 * 2
def baseEnd_3854844 : Nat := 1979387820100421138821901

theorem tailTrace_3854844 : CollatzResearch.WordTrace tailWord_3854844 prefixEnd_3854844 1979387820100421138821901 := by
  unfold tailWord_3854844
  simp only [CollatzResearch.WordTrace]
  refine ⟨70298855623283008892997793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93731807497710678523997057 70298855623283008892997793)
  ·
    refine ⟨52724141717462256669748345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70298855623283008892997793 52724141717462256669748345)
    ·
      refine ⟨39543106288096692502311259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52724141717462256669748345 39543106288096692502311259)
      ·
        refine ⟨59314659432145038753466889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39543106288096692502311259 59314659432145038753466889)
        ·
          refine ⟨44485994574108779065100167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59314659432145038753466889 44485994574108779065100167)
          ·
            refine ⟨66728991861163168597650251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44485994574108779065100167 66728991861163168597650251)
            ·
              refine ⟨100093487791744752896475377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66728991861163168597650251 100093487791744752896475377)
              ·
                refine ⟨75070115843808564672356533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100093487791744752896475377 75070115843808564672356533)
                ·
                  refine ⟨7037823360357052938033425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75070115843808564672356533 7037823360357052938033425)
                  ·
                    refine ⟨5278367520267789703525069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7037823360357052938033425 5278367520267789703525069)
                    ·
                      refine ⟨1979387820100421138821901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5278367520267789703525069 1979387820100421138821901)
                      ·
                        rfl

theorem cell23_3854844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_3854844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854844 prefixEnd_3854844 := by exact prefixLift 3854844
  have htrace : WordTrace (prefixWord ++ tailWord_3854844) baseStart_3854844 baseEnd_3854844 := by
    simpa [prefixWord, tailWord_3854844, baseEnd_3854844] using wordTrace_append hprefix tailTrace_3854844
  have hstable : (prefixWord ++ tailWord_3854844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854844).length < 2 ^ (prefixWord ++ tailWord_3854844).sum := by decide
  have hdescent : baseEnd_3854844 < baseStart_3854844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854852 : List Nat := [2, 3, 2, 3, 1, 2, 3, 2, 1, 1, 3]
def baseStart_3854852 : Nat := 118140960795 + 3854852 * 2 ^ 59
def prefixEnd_3854852 : Nat := 4983230072969 + 3 ^ 40 * 3854852 * 2
def baseEnd_3854852 : Nat := 1979391927945657107521865

theorem tailTrace_3854852 : CollatzResearch.WordTrace tailWord_3854852 prefixEnd_3854852 1979391927945657107521865 := by
  unfold tailWord_3854852
  simp only [CollatzResearch.WordTrace]
  refine ⟨70299001515268517576143405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93732002020358023434857873 70299001515268517576143405)
  ·
    refine ⟨26362125568225694091053777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70299001515268517576143405 26362125568225694091053777)
    ·
      refine ⟨19771594176169270568290333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26362125568225694091053777 19771594176169270568290333)
      ·
        refine ⟨7414347816063476463108875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19771594176169270568290333 7414347816063476463108875)
        ·
          refine ⟨11121521724095214694663313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7414347816063476463108875 11121521724095214694663313)
          ·
            refine ⟨8341141293071411020997485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11121521724095214694663313 8341141293071411020997485)
            ·
              refine ⟨3127927984901779132874057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8341141293071411020997485 3127927984901779132874057)
              ·
                refine ⟨2345945988676334349655543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3127927984901779132874057 2345945988676334349655543)
                ·
                  refine ⟨3518918983014501524483315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2345945988676334349655543 3518918983014501524483315)
                  ·
                    refine ⟨5278378474521752286724973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3518918983014501524483315 5278378474521752286724973)
                    ·
                      refine ⟨1979391927945657107521865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5278378474521752286724973 1979391927945657107521865)
                      ·
                        rfl

theorem cell23_3854852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_3854852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854852 prefixEnd_3854852 := by exact prefixLift 3854852
  have htrace : WordTrace (prefixWord ++ tailWord_3854852) baseStart_3854852 baseEnd_3854852 := by
    simpa [prefixWord, tailWord_3854852, baseEnd_3854852] using wordTrace_append hprefix tailTrace_3854852
  have hstable : (prefixWord ++ tailWord_3854852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854852).length < 2 ^ (prefixWord ++ tailWord_3854852).sum := by decide
  have hdescent : baseEnd_3854852 < baseStart_3854852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854867 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 6]
def baseStart_3854867 : Nat := 118140960795 + 3854867 * 2 ^ 59
def prefixEnd_3854867 : Nat := 4983230072969 + 3 ^ 40 * 3854867 * 2
def baseEnd_3854867 : Nat := 1979399630155474548834295

theorem tailTrace_3854867 : CollatzResearch.WordTrace tailWord_3854867 prefixEnd_3854867 1979399630155474548834295 := by
  unfold tailWord_3854867
  simp only [CollatzResearch.WordTrace]
  refine ⟨140598550125482692714082855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93732366750321795142721903 140598550125482692714082855)
  ·
    refine ⟨210897825188224039071124283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140598550125482692714082855 210897825188224039071124283)
    ·
      refine ⟨316346737782336058606686425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210897825188224039071124283 316346737782336058606686425)
      ·
        refine ⟨237260053336752043955014819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316346737782336058606686425 237260053336752043955014819)
        ·
          refine ⟨355890080005128065932522229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237260053336752043955014819 355890080005128065932522229)
          ·
            refine ⟨33364695000480756181173959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 355890080005128065932522229 33364695000480756181173959)
            ·
              refine ⟨50047042500721134271760939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33364695000480756181173959 50047042500721134271760939)
              ·
                refine ⟨75070563751081701407641409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50047042500721134271760939 75070563751081701407641409)
                ·
                  refine ⟨56302922813311276055731057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75070563751081701407641409 56302922813311276055731057)
                  ·
                    refine ⟨42227192109983457041798293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56302922813311276055731057 42227192109983457041798293)
                    ·
                      refine ⟨1979399630155474548834295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42227192109983457041798293 1979399630155474548834295)
                      ·
                        rfl

theorem cell23_3854867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 6].length) (baseStart_3854867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854867 prefixEnd_3854867 := by exact prefixLift 3854867
  have htrace : WordTrace (prefixWord ++ tailWord_3854867) baseStart_3854867 baseEnd_3854867 := by
    simpa [prefixWord, tailWord_3854867, baseEnd_3854867] using wordTrace_append hprefix tailTrace_3854867
  have hstable : (prefixWord ++ tailWord_3854867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854867).length < 2 ^ (prefixWord ++ tailWord_3854867).sum := by decide
  have hdescent : baseEnd_3854867 < baseStart_3854867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854908 : List Nat := [2, 2, 2, 2, 3, 1, 1, 4, 2, 1, 3]
def baseStart_3854908 : Nat := 118140960795 + 3854908 * 2 ^ 59
def prefixEnd_3854908 : Nat := 4983230072969 + 3 ^ 40 * 3854908 * 2
def baseEnd_3854908 : Nat := 1979420682862308888421607

theorem tailTrace_3854908 : CollatzResearch.WordTrace tailWord_3854908 prefixEnd_3854908 1979420682862308888421607 := by
  unfold tailWord_3854908
  simp only [CollatzResearch.WordTrace]
  refine ⟨70300022759167078358162689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93733363678889437810883585 70300022759167078358162689)
  ·
    refine ⟨52725017069375308768622017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70300022759167078358162689 52725017069375308768622017)
    ·
      refine ⟨39543762802031481576466513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52725017069375308768622017 39543762802031481576466513)
      ·
        refine ⟨29657822101523611182349885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39543762802031481576466513 29657822101523611182349885)
        ·
          refine ⟨11121683288071354193381207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29657822101523611182349885 11121683288071354193381207)
          ·
            refine ⟨16682524932107031290071811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11121683288071354193381207 16682524932107031290071811)
            ·
              refine ⟨25023787398160546935107717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16682524932107031290071811 25023787398160546935107717)
              ·
                refine ⟨4691960137155102550332697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25023787398160546935107717 4691960137155102550332697)
                ·
                  refine ⟨3518970102866326912749523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4691960137155102550332697 3518970102866326912749523)
                  ·
                    refine ⟨5278455154299490369124285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3518970102866326912749523 5278455154299490369124285)
                    ·
                      refine ⟨1979420682862308888421607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5278455154299490369124285 1979420682862308888421607)
                      ·
                        rfl

theorem cell23_3854908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_3854908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854908 prefixEnd_3854908 := by exact prefixLift 3854908
  have htrace : WordTrace (prefixWord ++ tailWord_3854908) baseStart_3854908 baseEnd_3854908 := by
    simpa [prefixWord, tailWord_3854908, baseEnd_3854908] using wordTrace_append hprefix tailTrace_3854908
  have hstable : (prefixWord ++ tailWord_3854908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854908).length < 2 ^ (prefixWord ++ tailWord_3854908).sum := by decide
  have hdescent : baseEnd_3854908 < baseStart_3854908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854909 : List Nat := [1, 4, 1, 3, 2, 3, 2, 2, 1, 2, 2]
def baseStart_3854909 : Nat := 118140960795 + 3854909 * 2 ^ 59
def prefixEnd_3854909 : Nat := 4983230072969 + 3 ^ 40 * 3854909 * 2
def baseEnd_3854909 : Nat := 1979421196342963384509103

theorem tailTrace_3854909 : CollatzResearch.WordTrace tailWord_3854909 prefixEnd_3854909 1979421196342963384509103 := by
  unfold tailWord_3854909
  simp only [CollatzResearch.WordTrace]
  refine ⟨140600081991330533887111781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93733387994220355924741187 140600081991330533887111781)
  ·
    refine ⟨26362515373374475103833459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140600081991330533887111781 26362515373374475103833459)
    ·
      refine ⟨39543773060061712655750189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26362515373374475103833459 39543773060061712655750189)
      ·
        refine ⟨14828914897523142245906321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39543773060061712655750189 14828914897523142245906321)
        ·
          refine ⟨11121686173142356684429741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14828914897523142245906321 11121686173142356684429741)
          ·
            refine ⟨4170632314928383756661153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11121686173142356684429741 4170632314928383756661153)
            ·
              refine ⟨3127974236196287817495865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4170632314928383756661153 3127974236196287817495865)
              ·
                refine ⟨2345980677147215863121899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3127974236196287817495865 2345980677147215863121899)
                ·
                  refine ⟨3518971015720823794682849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2345980677147215863121899 3518971015720823794682849)
                  ·
                    refine ⟨2639228261790617846012137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3518971015720823794682849 2639228261790617846012137)
                    ·
                      refine ⟨1979421196342963384509103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2639228261790617846012137 1979421196342963384509103)
                      ·
                        rfl

theorem cell23_3854909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_3854909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854909 prefixEnd_3854909 := by exact prefixLift 3854909
  have htrace : WordTrace (prefixWord ++ tailWord_3854909) baseStart_3854909 baseEnd_3854909 := by
    simpa [prefixWord, tailWord_3854909, baseEnd_3854909] using wordTrace_append hprefix tailTrace_3854909
  have hstable : (prefixWord ++ tailWord_3854909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854909).length < 2 ^ (prefixWord ++ tailWord_3854909).sum := by decide
  have hdescent : baseEnd_3854909 < baseStart_3854909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854924 : List Nat := [2, 2, 1, 3, 1, 2, 3, 1, 2, 6]
def baseStart_3854924 : Nat := 118140960795 + 3854924 * 2 ^ 59
def prefixEnd_3854924 : Nat := 4983230072969 + 3 ^ 40 * 3854924 * 2
def baseEnd_3854924 : Nat := 659809632850926941940511

theorem tailTrace_3854924 : CollatzResearch.WordTrace tailWord_3854924 prefixEnd_3854924 659809632850926941940511 := by
  unfold tailWord_3854924
  simp only [CollatzResearch.WordTrace]
  refine ⟨70300314543138095724453913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93733752724184127632605217 70300314543138095724453913)
  ·
    refine ⟨52725235907353571793340435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70300314543138095724453913 52725235907353571793340435)
    ·
      refine ⟨79087853861030357690010653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52725235907353571793340435 79087853861030357690010653)
      ·
        refine ⟨29657945197886384133753995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79087853861030357690010653 29657945197886384133753995)
        ·
          refine ⟨44486917796829576200630993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29657945197886384133753995 44486917796829576200630993)
          ·
            refine ⟨33365188347622182150473245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44486917796829576200630993 33365188347622182150473245)
            ·
              refine ⟨12511945630358318306427467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33365188347622182150473245 12511945630358318306427467)
              ·
                refine ⟨18767918445537477459641201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12511945630358318306427467 18767918445537477459641201)
                ·
                  refine ⟨14075938834153108094730901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18767918445537477459641201 14075938834153108094730901)
                  ·
                    refine ⟨659809632850926941940511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14075938834153108094730901 659809632850926941940511)
                    ·
                      rfl

theorem cell23_3854924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 2, 6].length) (baseStart_3854924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854924 prefixEnd_3854924 := by exact prefixLift 3854924
  have htrace : WordTrace (prefixWord ++ tailWord_3854924) baseStart_3854924 baseEnd_3854924 := by
    simpa [prefixWord, tailWord_3854924, baseEnd_3854924] using wordTrace_append hprefix tailTrace_3854924
  have hstable : (prefixWord ++ tailWord_3854924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854924).length < 2 ^ (prefixWord ++ tailWord_3854924).sum := by decide
  have hdescent : baseEnd_3854924 < baseStart_3854924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854925 : List Nat := [1, 6, 1, 1, 2, 1, 2, 3, 2, 1, 3]
def baseStart_3854925 : Nat := 118140960795 + 3854925 * 2 ^ 59
def prefixEnd_3854925 : Nat := 4983230072969 + 3 ^ 40 * 3854925 * 2
def baseEnd_3854925 : Nat := 1979429412033435321909029

theorem tailTrace_3854925 : CollatzResearch.WordTrace tailWord_3854925 prefixEnd_3854925 1979429412033435321909029 := by
  unfold tailWord_3854925
  simp only [CollatzResearch.WordTrace]
  refine ⟨140600665559272568619694229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93733777039515045746462819 140600665559272568619694229)
  ·
    refine ⟨6590656198090901654048167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 140600665559272568619694229 6590656198090901654048167)
    ·
      refine ⟨9885984297136352481072251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6590656198090901654048167 9885984297136352481072251)
      ·
        refine ⟨14828976445704528721608377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9885984297136352481072251 14828976445704528721608377)
        ·
          refine ⟨11121732334278396541206283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14828976445704528721608377 11121732334278396541206283)
          ·
            refine ⟨16682598501417594811809425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11121732334278396541206283 16682598501417594811809425)
            ·
              refine ⟨12511948876063196108857069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16682598501417594811809425 12511948876063196108857069)
              ·
                refine ⟨4691980828523698540821401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12511948876063196108857069 4691980828523698540821401)
                ·
                  refine ⟨3518985621392773905616051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4691980828523698540821401 3518985621392773905616051)
                  ·
                    refine ⟨5278478432089160858424077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3518985621392773905616051 5278478432089160858424077)
                    ·
                      refine ⟨1979429412033435321909029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5278478432089160858424077 1979429412033435321909029)
                      ·
                        rfl

theorem cell23_3854925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_3854925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854925 prefixEnd_3854925 := by exact prefixLift 3854925
  have htrace : WordTrace (prefixWord ++ tailWord_3854925) baseStart_3854925 baseEnd_3854925 := by
    simpa [prefixWord, tailWord_3854925, baseEnd_3854925] using wordTrace_append hprefix tailTrace_3854925
  have hstable : (prefixWord ++ tailWord_3854925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854925).length < 2 ^ (prefixWord ++ tailWord_3854925).sum := by decide
  have hdescent : baseEnd_3854925 < baseStart_3854925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
