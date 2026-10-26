import V185TrunkScan23Chunk1413

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8376207 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 4, 8, 2]
def baseStart_8376207 : Nat := 118140960795 + 8376207 * 2 ^ 59
def prefixEnd_8376207 : Nat := 4983230072969 + 3 ^ 40 * 8376207 * 2
def baseEnd_8376207 : Nat := 4301020252554814785291031

theorem tailTrace_8376207 : CollatzResearch.WordTrace tailWord_8376207 prefixEnd_8376207 4301020252554814785291031 := by
  unfold tailWord_8376207
  simp only [CollatzResearch.WordTrace]
  refine ⟨305505367565440056109422875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203670245043626704072948583 305505367565440056109422875)
  ·
    refine ⟨458258051348160084164134313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305505367565440056109422875 458258051348160084164134313)
    ·
      refine ⟨343693538511120063123100735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458258051348160084164134313 343693538511120063123100735)
      ·
        refine ⟨515540307766680094684651103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343693538511120063123100735 515540307766680094684651103)
        ·
          refine ⟨773310461650020142026976655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515540307766680094684651103 773310461650020142026976655)
          ·
            refine ⟨1159965692475030213040464983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773310461650020142026976655 1159965692475030213040464983)
            ·
              refine ⟨1739948538712545319560697475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1159965692475030213040464983 1739948538712545319560697475)
              ·
                refine ⟨2609922808068817979341046213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1739948538712545319560697475 2609922808068817979341046213)
                ·
                  refine ⟨489360526512903371126446165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2609922808068817979341046213 489360526512903371126446165)
                  ·
                    refine ⟨5734693670073086380388041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 489360526512903371126446165 5734693670073086380388041)
                    ·
                      refine ⟨4301020252554814785291031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5734693670073086380388041 4301020252554814785291031)
                      ·
                        rfl

theorem cell23_8376207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 8, 2].length) (baseStart_8376207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376207 prefixEnd_8376207 := by exact prefixLift 8376207
  have htrace : WordTrace (prefixWord ++ tailWord_8376207) baseStart_8376207 baseEnd_8376207 := by
    simpa [prefixWord, tailWord_8376207, baseEnd_8376207] using wordTrace_append hprefix tailTrace_8376207
  have hstable : (prefixWord ++ tailWord_8376207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376207).length < 2 ^ (prefixWord ++ tailWord_8376207).sum := by decide
  have hdescent : baseEnd_8376207 < baseStart_8376207 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376218 : List Nat := [3, 1, 1, 4, 2, 3, 1, 2, 2, 1, 3]
def baseStart_8376218 : Nat := 118140960795 + 8376218 * 2 ^ 59
def prefixEnd_8376218 : Nat := 4983230072969 + 3 ^ 40 * 8376218 * 2
def baseEnd_8376218 : Nat := 4301025900842014242253481

theorem tailTrace_8376218 : CollatzResearch.WordTrace tailWord_8376218 prefixEnd_8376218 4301025900842014242253481 := by
  unfold tailWord_8376218
  simp only [CollatzResearch.WordTrace]
  refine ⟨76376442192100051247018327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203670512512266803325382205 76376442192100051247018327)
  ·
    refine ⟨114564663288150076870527491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76376442192100051247018327 114564663288150076870527491)
    ·
      refine ⟨171846994932225115305791237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114564663288150076870527491 171846994932225115305791237)
      ·
        refine ⟨32221311549792209119835857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171846994932225115305791237 32221311549792209119835857)
        ·
          refine ⟨24165983662344156839876893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32221311549792209119835857 24165983662344156839876893)
          ·
            refine ⟨9062243873379058814953835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24165983662344156839876893 9062243873379058814953835)
            ·
              refine ⟨13593365810068588222430753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9062243873379058814953835 13593365810068588222430753)
              ·
                refine ⟨10195024357551441166823065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13593365810068588222430753 10195024357551441166823065)
                ·
                  refine ⟨7646268268163580875117299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10195024357551441166823065 7646268268163580875117299)
                  ·
                    refine ⟨11469402402245371312675949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7646268268163580875117299 11469402402245371312675949)
                    ·
                      refine ⟨4301025900842014242253481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11469402402245371312675949 4301025900842014242253481)
                      ·
                        rfl

theorem cell23_8376218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_8376218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376218 prefixEnd_8376218 := by exact prefixLift 8376218
  have htrace : WordTrace (prefixWord ++ tailWord_8376218) baseStart_8376218 baseEnd_8376218 := by
    simpa [prefixWord, tailWord_8376218, baseEnd_8376218] using wordTrace_append hprefix tailTrace_8376218
  have hstable : (prefixWord ++ tailWord_8376218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376218).length < 2 ^ (prefixWord ++ tailWord_8376218).sum := by decide
  have hdescent : baseEnd_8376218 < baseStart_8376218 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376240 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 9]
def baseStart_8376240 : Nat := 118140960795 + 8376240 * 2 ^ 59
def prefixEnd_8376240 : Nat := 4983230072969 + 3 ^ 40 * 8376240 * 2
def baseEnd_8376240 : Nat := 4301037197416413156178379

theorem tailTrace_8376240 : CollatzResearch.WordTrace tailWord_8376240 prefixEnd_8376240 4301037197416413156178379 := by
  unfold tailWord_8376240
  simp only [CollatzResearch.WordTrace]
  refine ⟨152753285587160251372687087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203671047449547001830249449 152753285587160251372687087)
  ·
    refine ⟨229129928380740377059030631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152753285587160251372687087 229129928380740377059030631)
    ·
      refine ⟨343694892571110565588545947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229129928380740377059030631 343694892571110565588545947)
      ·
        refine ⟨515542338856665848382818921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343694892571110565588545947 515542338856665848382818921)
        ·
          refine ⟨386656754142499386287114191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515542338856665848382818921 386656754142499386287114191)
          ·
            refine ⟨579985131213749079430671287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386656754142499386287114191 579985131213749079430671287)
            ·
              refine ⟨869977696820623619146006931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579985131213749079430671287 869977696820623619146006931)
              ·
                refine ⟨1304966545230935428719010397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 869977696820623619146006931 1304966545230935428719010397)
                ·
                  refine ⟨489362454461600785769628899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1304966545230935428719010397 489362454461600785769628899)
                  ·
                    refine ⟨734043681692401178654443349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 489362454461600785769628899 734043681692401178654443349)
                    ·
                      refine ⟨4301037197416413156178379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 734043681692401178654443349 4301037197416413156178379)
                      ·
                        rfl

theorem cell23_8376240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 9].length) (baseStart_8376240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376240 prefixEnd_8376240 := by exact prefixLift 8376240
  have htrace : WordTrace (prefixWord ++ tailWord_8376240) baseStart_8376240 baseEnd_8376240 := by
    simpa [prefixWord, tailWord_8376240, baseEnd_8376240] using wordTrace_append hprefix tailTrace_8376240
  have hstable : (prefixWord ++ tailWord_8376240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376240).length < 2 ^ (prefixWord ++ tailWord_8376240).sum := by decide
  have hdescent : baseEnd_8376240 < baseStart_8376240 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376241 : List Nat := [1, 2, 2, 4, 2, 1, 3, 1, 1, 4, 2]
def baseStart_8376241 : Nat := 118140960795 + 8376241 * 2 ^ 59
def prefixEnd_8376241 : Nat := 4983230072969 + 3 ^ 40 * 8376241 * 2
def baseEnd_8376241 : Nat := 4301037710897067652265875

theorem tailTrace_8376241 : CollatzResearch.WordTrace tailWord_8376241 prefixEnd_8376241 4301037710897067652265875 := by
  unfold tailWord_8376241
  simp only [CollatzResearch.WordTrace]
  refine ⟨305506607647316879916160577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203671071764877919944107051 305506607647316879916160577)
  ·
    refine ⟨229129955735487659937120433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305506607647316879916160577 229129955735487659937120433)
    ·
      refine ⟨171847466801615744952840325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229129955735487659937120433 171847466801615744952840325)
      ·
        refine ⟨32221400025302952178657561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171847466801615744952840325 32221400025302952178657561)
        ·
          refine ⟨24166050018977214133993171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32221400025302952178657561 24166050018977214133993171)
          ·
            refine ⟨36249075028465821200989757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24166050018977214133993171 36249075028465821200989757)
            ·
              refine ⟨13593403135674682950371159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36249075028465821200989757 13593403135674682950371159)
              ·
                refine ⟨20390104703512024425556739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13593403135674682950371159 20390104703512024425556739)
                ·
                  refine ⟨30585157055268036638335109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20390104703512024425556739 30585157055268036638335109)
                  ·
                    refine ⟨5734716947862756869687833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30585157055268036638335109 5734716947862756869687833)
                    ·
                      refine ⟨4301037710897067652265875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5734716947862756869687833 4301037710897067652265875)
                      ·
                        rfl

theorem cell23_8376241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_8376241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376241 prefixEnd_8376241 := by exact prefixLift 8376241
  have htrace : WordTrace (prefixWord ++ tailWord_8376241) baseStart_8376241 baseEnd_8376241 := by
    simpa [prefixWord, tailWord_8376241, baseEnd_8376241] using wordTrace_append hprefix tailTrace_8376241
  have hstable : (prefixWord ++ tailWord_8376241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376241).length < 2 ^ (prefixWord ++ tailWord_8376241).sum := by decide
  have hdescent : baseEnd_8376241 < baseStart_8376241 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376281 : List Nat := [1, 2, 1, 2, 7, 1, 1, 1, 7]
def baseStart_8376281 : Nat := 118140960795 + 8376281 * 2 ^ 59
def prefixEnd_8376281 : Nat := 4983230072969 + 3 ^ 40 * 8376281 * 2
def baseEnd_8376281 : Nat := 477895361124805277307299

theorem tailTrace_8376281 : CollatzResearch.WordTrace tailWord_8376281 prefixEnd_8376281 477895361124805277307299 := by
  unfold tailWord_8376281
  simp only [CollatzResearch.WordTrace]
  refine ⟨305508066567171966747616697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203672044378114644498411131 305508066567171966747616697)
  ·
    refine ⟨229131049925378975060712523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305508066567171966747616697 229131049925378975060712523)
    ·
      refine ⟨343696574888068462591068785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229131049925378975060712523 343696574888068462591068785)
      ·
        refine ⟨257772431166051346943301589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343696574888068462591068785 257772431166051346943301589)
        ·
          refine ⟨6041541355454328443983631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 257772431166051346943301589 6041541355454328443983631)
          ·
            refine ⟨9062312033181492665975447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6041541355454328443983631 9062312033181492665975447)
            ·
              refine ⟨13593468049772238998963171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9062312033181492665975447 13593468049772238998963171)
              ·
                refine ⟨20390202074658358498444757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13593468049772238998963171 20390202074658358498444757)
                ·
                  refine ⟨477895361124805277307299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20390202074658358498444757 477895361124805277307299)
                  ·
                    rfl

theorem cell23_8376281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 7].length) (baseStart_8376281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376281 prefixEnd_8376281 := by exact prefixLift 8376281
  have htrace : WordTrace (prefixWord ++ tailWord_8376281) baseStart_8376281 baseEnd_8376281 := by
    simpa [prefixWord, tailWord_8376281, baseEnd_8376281] using wordTrace_append hprefix tailTrace_8376281
  have hstable : (prefixWord ++ tailWord_8376281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376281).length < 2 ^ (prefixWord ++ tailWord_8376281).sum := by decide
  have hdescent : baseEnd_8376281 < baseStart_8376281 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376287 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 7]
def baseStart_8376287 : Nat := 118140960795 + 8376287 * 2 ^ 59
def prefixEnd_8376287 : Nat := 4983230072969 + 3 ^ 40 * 8376287 * 2
def baseEnd_8376287 : Nat := 4301061331007174472290663

theorem tailTrace_8376287 : CollatzResearch.WordTrace tailWord_8376287 prefixEnd_8376287 4301061331007174472290663 := by
  unfold tailWord_8376287
  simp only [CollatzResearch.WordTrace]
  refine ⟨305508285405150229772335115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203672190270100153181556743 305508285405150229772335115)
  ·
    refine ⟨458262428107725344658502673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305508285405150229772335115 458262428107725344658502673)
    ·
      refine ⟨343696821080794008493877005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458262428107725344658502673 343696821080794008493877005)
      ·
        refine ⟨128886307905297753185203877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343696821080794008493877005 128886307905297753185203877)
        ·
          refine ⟨24166182732243328722225727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128886307905297753185203877 24166182732243328722225727)
          ·
            refine ⟨36249274098364993083338591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24166182732243328722225727 36249274098364993083338591)
            ·
              refine ⟨54373911147547489625007887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36249274098364993083338591 54373911147547489625007887)
              ·
                refine ⟨81560866721321234437511831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54373911147547489625007887 81560866721321234437511831)
                ·
                  refine ⟨122341300081981851656267747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81560866721321234437511831 122341300081981851656267747)
                  ·
                    refine ⟨183511950122972777484401621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 122341300081981851656267747 183511950122972777484401621)
                    ·
                      refine ⟨4301061331007174472290663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 183511950122972777484401621 4301061331007174472290663)
                      ·
                        rfl

theorem cell23_8376287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_8376287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376287 prefixEnd_8376287 := by exact prefixLift 8376287
  have htrace : WordTrace (prefixWord ++ tailWord_8376287) baseStart_8376287 baseEnd_8376287 := by
    simpa [prefixWord, tailWord_8376287, baseEnd_8376287] using wordTrace_append hprefix tailTrace_8376287
  have hstable : (prefixWord ++ tailWord_8376287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376287).length < 2 ^ (prefixWord ++ tailWord_8376287).sum := by decide
  have hdescent : baseEnd_8376287 < baseStart_8376287 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376314 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 6, 4, 2]
def baseStart_8376314 : Nat := 118140960795 + 8376314 * 2 ^ 59
def prefixEnd_8376314 : Nat := 4983230072969 + 3 ^ 40 * 8376314 * 2
def baseEnd_8376314 : Nat := 4301075194984845866653039

theorem tailTrace_8376314 : CollatzResearch.WordTrace tailWord_8376314 prefixEnd_8376314 4301075194984845866653039 := by
  unfold tailWord_8376314
  simp only [CollatzResearch.WordTrace]
  refine ⟨76377317544013103345891999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203672846784034942255711997 76377317544013103345891999)
  ·
    refine ⟨114565976316019655018837999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76377317544013103345891999 114565976316019655018837999)
    ·
      refine ⟨171848964474029482528256999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114565976316019655018837999 171848964474029482528256999)
      ·
        refine ⟨257773446711044223792385499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171848964474029482528256999 257773446711044223792385499)
        ·
          refine ⟨386660170066566335688578249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257773446711044223792385499 386660170066566335688578249)
          ·
            refine ⟨289995127549924751766433687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386660170066566335688578249 289995127549924751766433687)
            ·
              refine ⟨434992691324887127649650531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289995127549924751766433687 434992691324887127649650531)
              ·
                refine ⟨652489036987330691474475797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434992691324887127649650531 652489036987330691474475797)
                ·
                  refine ⟨30585423608781126162866053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 652489036987330691474475797 30585423608781126162866053)
                  ·
                    refine ⟨5734766926646461155537385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30585423608781126162866053 5734766926646461155537385)
                    ·
                      refine ⟨4301075194984845866653039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5734766926646461155537385 4301075194984845866653039)
                      ·
                        rfl

theorem cell23_8376314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 6, 4, 2].length) (baseStart_8376314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376314 prefixEnd_8376314 := by exact prefixLift 8376314
  have htrace : WordTrace (prefixWord ++ tailWord_8376314) baseStart_8376314 baseEnd_8376314 := by
    simpa [prefixWord, tailWord_8376314, baseEnd_8376314] using wordTrace_append hprefix tailTrace_8376314
  have hstable : (prefixWord ++ tailWord_8376314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376314).length < 2 ^ (prefixWord ++ tailWord_8376314).sum := by decide
  have hdescent : baseEnd_8376314 < baseStart_8376314 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376326 : List Nat := [6, 2, 1, 2, 1, 1, 2, 2, 2, 2, 2]
def baseStart_8376326 : Nat := 118140960795 + 8376326 * 2 ^ 59
def prefixEnd_8376326 : Nat := 4983230072969 + 3 ^ 40 * 8376326 * 2
def baseEnd_8376326 : Nat := 4301081356752699819702985

theorem tailTrace_8376326 : CollatzResearch.WordTrace tailWord_8376326 prefixEnd_8376326 4301081356752699819702985 := by
  unfold tailWord_8376326
  simp only [CollatzResearch.WordTrace]
  refine ⟨9547178370375279357281401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 203673138568005959622003221 9547178370375279357281401)
  ·
    refine ⟨7160383777781459517961051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9547178370375279357281401 7160383777781459517961051)
    ·
      refine ⟨10740575666672189276941577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7160383777781459517961051 10740575666672189276941577)
      ·
        refine ⟨8055431750004141957706183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10740575666672189276941577 8055431750004141957706183)
        ·
          refine ⟨12083147625006212936559275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8055431750004141957706183 12083147625006212936559275)
          ·
            refine ⟨18124721437509319404838913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12083147625006212936559275 18124721437509319404838913)
            ·
              refine ⟨13593541078131989553629185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18124721437509319404838913 13593541078131989553629185)
              ·
                refine ⟨10195155808598992165221889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13593541078131989553629185 10195155808598992165221889)
                ·
                  refine ⟨7646366856449244123916417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10195155808598992165221889 7646366856449244123916417)
                  ·
                    refine ⟨5734775142336933092937313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7646366856449244123916417 5734775142336933092937313)
                    ·
                      refine ⟨4301081356752699819702985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5734775142336933092937313 4301081356752699819702985)
                      ·
                        rfl

theorem cell23_8376326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_8376326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376326 prefixEnd_8376326 := by exact prefixLift 8376326
  have htrace : WordTrace (prefixWord ++ tailWord_8376326) baseStart_8376326 baseEnd_8376326 := by
    simpa [prefixWord, tailWord_8376326, baseEnd_8376326] using wordTrace_append hprefix tailTrace_8376326
  have hstable : (prefixWord ++ tailWord_8376326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376326).length < 2 ^ (prefixWord ++ tailWord_8376326).sum := by decide
  have hdescent : baseEnd_8376326 < baseStart_8376326 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376354 : List Nat := [3, 3, 1, 1, 1, 2, 1, 5, 6]
def baseStart_8376354 : Nat := 118140960795 + 8376354 * 2 ^ 59
def prefixEnd_8376354 : Nat := 4983230072969 + 3 ^ 40 * 8376354 * 2
def baseEnd_8376354 : Nat := 477899526023447301128095

theorem tailTrace_8376354 : CollatzResearch.WordTrace tailWord_8376354 prefixEnd_8376354 477899526023447301128095 := by
  unfold tailWord_8376354
  simp only [CollatzResearch.WordTrace]
  refine ⟨76377682273976875053756029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203673819397271666810016077 76377682273976875053756029)
  ·
    refine ⟨28641630852741328145158511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76377682273976875053756029 28641630852741328145158511)
    ·
      refine ⟨42962446279111992217737767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28641630852741328145158511 42962446279111992217737767)
      ·
        refine ⟨64443669418667988326606651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42962446279111992217737767 64443669418667988326606651)
        ·
          refine ⟨96665504128001982489909977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64443669418667988326606651 96665504128001982489909977)
          ·
            refine ⟨72499128096001486867432483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96665504128001982489909977 72499128096001486867432483)
            ·
              refine ⟨108748692144002230301148725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72499128096001486867432483 108748692144002230301148725)
              ·
                refine ⟨10195189888500209090732693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108748692144002230301148725 10195189888500209090732693)
                ·
                  refine ⟨477899526023447301128095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10195189888500209090732693 477899526023447301128095)
                  ·
                    rfl

theorem cell23_8376354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_8376354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376354 prefixEnd_8376354 := by exact prefixLift 8376354
  have htrace : WordTrace (prefixWord ++ tailWord_8376354) baseStart_8376354 baseEnd_8376354 := by
    simpa [prefixWord, tailWord_8376354, baseEnd_8376354] using wordTrace_append hprefix tailTrace_8376354
  have hstable : (prefixWord ++ tailWord_8376354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376354).length < 2 ^ (prefixWord ++ tailWord_8376354).sum := by decide
  have hdescent : baseEnd_8376354 < baseStart_8376354 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376381 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 5, 1, 3]
def baseStart_8376381 : Nat := 118140960795 + 8376381 * 2 ^ 59
def prefixEnd_8376381 : Nat := 4983230072969 + 3 ^ 40 * 8376381 * 2
def baseEnd_8376381 : Nat := 4301109598188697104515231

theorem tailTrace_8376381 : CollatzResearch.WordTrace tailWord_8376381 prefixEnd_8376381 4301109598188697104515231 := by
  unfold tailWord_8376381
  simp only [CollatzResearch.WordTrace]
  refine ⟨305511713866809683826256997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203674475911206455884171331 305511713866809683826256997)
  ·
    refine ⟨57283446350026815717423187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305511713866809683826256997 57283446350026815717423187)
    ·
      refine ⟨85925169525040223576134781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57283446350026815717423187 85925169525040223576134781)
      ·
        refine ⟨32221938571890083841050543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85925169525040223576134781 32221938571890083841050543)
        ·
          refine ⟨48332907857835125761575815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32221938571890083841050543 48332907857835125761575815)
          ·
            refine ⟨72499361786752688642363723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48332907857835125761575815 72499361786752688642363723)
            ·
              refine ⟨108749042680129032963545585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72499361786752688642363723 108749042680129032963545585)
              ·
                refine ⟨81561782010096774722659189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108749042680129032963545585 81561782010096774722659189)
                ·
                  refine ⟨7646417063446572630249299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81561782010096774722659189 7646417063446572630249299)
                  ·
                    refine ⟨11469625595169858945373949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7646417063446572630249299 11469625595169858945373949)
                    ·
                      refine ⟨4301109598188697104515231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11469625595169858945373949 4301109598188697104515231)
                      ·
                        rfl

theorem cell23_8376381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_8376381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376381 prefixEnd_8376381 := by exact prefixLift 8376381
  have htrace : WordTrace (prefixWord ++ tailWord_8376381) baseStart_8376381 baseEnd_8376381 := by
    simpa [prefixWord, tailWord_8376381, baseEnd_8376381] using wordTrace_append hprefix tailTrace_8376381
  have hstable : (prefixWord ++ tailWord_8376381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376381).length < 2 ^ (prefixWord ++ tailWord_8376381).sum := by decide
  have hdescent : baseEnd_8376381 < baseStart_8376381 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376391 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 4, 3, 2]
def baseStart_8376391 : Nat := 118140960795 + 8376391 * 2 ^ 59
def prefixEnd_8376391 : Nat := 4983230072969 + 3 ^ 40 * 8376391 * 2
def baseEnd_8376391 : Nat := 4301114732995242065390185

theorem tailTrace_8376391 : CollatzResearch.WordTrace tailWord_8376391 prefixEnd_8376391 4301114732995242065390185 := by
  unfold tailWord_8376391
  simp only [CollatzResearch.WordTrace]
  refine ⟨305512078596773455534121027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203674719064515637022747351 305512078596773455534121027)
  ·
    refine ⟨458268117895160183301181541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305512078596773455534121027 458268117895160183301181541)
    ·
      refine ⟨85925272105342534368971539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 458268117895160183301181541 85925272105342534368971539)
      ·
        refine ⟨128887908158013801553457309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85925272105342534368971539 128887908158013801553457309)
        ·
          refine ⟨48332965559255175582546491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128887908158013801553457309 48332965559255175582546491)
          ·
            refine ⟨72499448338882763373819737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48332965559255175582546491 72499448338882763373819737)
            ·
              refine ⟨54374586254162072530364803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72499448338882763373819737 54374586254162072530364803)
              ·
                refine ⟨81561879381243108795547205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54374586254162072530364803 81561879381243108795547205)
                ·
                  refine ⟨15292852383983082899165101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81561879381243108795547205 15292852383983082899165101)
                  ·
                    refine ⟨5734819643993656087186913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15292852383983082899165101 5734819643993656087186913)
                    ·
                      refine ⟨4301114732995242065390185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5734819643993656087186913 4301114732995242065390185)
                      ·
                        rfl

theorem cell23_8376391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 3, 2].length) (baseStart_8376391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376391 prefixEnd_8376391 := by exact prefixLift 8376391
  have htrace : WordTrace (prefixWord ++ tailWord_8376391) baseStart_8376391 baseEnd_8376391 := by
    simpa [prefixWord, tailWord_8376391, baseEnd_8376391] using wordTrace_append hprefix tailTrace_8376391
  have hstable : (prefixWord ++ tailWord_8376391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376391).length < 2 ^ (prefixWord ++ tailWord_8376391).sum := by decide
  have hdescent : baseEnd_8376391 < baseStart_8376391 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376398 : List Nat := [4, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3]
def baseStart_8376398 : Nat := 118140960795 + 8376398 * 2 ^ 59
def prefixEnd_8376398 : Nat := 4983230072969 + 3 ^ 40 * 8376398 * 2
def baseEnd_8376398 : Nat := 4301118327359823538002653

theorem tailTrace_8376398 : CollatzResearch.WordTrace tailWord_8376398 prefixEnd_8376398 4301118327359823538002653 := by
  unfold tailWord_8376398
  simp only [CollatzResearch.WordTrace]
  refine ⟨38189041738468511966203231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203674889271832063819750565 38189041738468511966203231)
  ·
    refine ⟨57283562607702767949304847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38189041738468511966203231 57283562607702767949304847)
    ·
      refine ⟨85925343911554151923957271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57283562607702767949304847 85925343911554151923957271)
      ·
        refine ⟨128888015867331227885935907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85925343911554151923957271 128888015867331227885935907)
        ·
          refine ⟨193332023800996841828903861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128888015867331227885935907 193332023800996841828903861)
          ·
            refine ⟨18124877231343453921459737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 193332023800996841828903861 18124877231343453921459737)
            ·
              refine ⟨13593657923507590441094803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18124877231343453921459737 13593657923507590441094803)
              ·
                refine ⟨20390486885261385661642205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13593657923507590441094803 20390486885261385661642205)
                ·
                  refine ⟨7646432581973019623115827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20390486885261385661642205 7646432581973019623115827)
                  ·
                    refine ⟨11469648872959529434673741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7646432581973019623115827 11469648872959529434673741)
                    ·
                      refine ⟨4301118327359823538002653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11469648872959529434673741 4301118327359823538002653)
                      ·
                        rfl

theorem cell23_8376398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_8376398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376398 prefixEnd_8376398 := by exact prefixLift 8376398
  have htrace : WordTrace (prefixWord ++ tailWord_8376398) baseStart_8376398 baseEnd_8376398 := by
    simpa [prefixWord, tailWord_8376398, baseEnd_8376398] using wordTrace_append hprefix tailTrace_8376398
  have hstable : (prefixWord ++ tailWord_8376398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376398).length < 2 ^ (prefixWord ++ tailWord_8376398).sum := by decide
  have hdescent : baseEnd_8376398 < baseStart_8376398 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376421 : List Nat := [1, 3, 1, 3, 2, 2, 1, 4, 1, 1, 4]
def baseStart_8376421 : Nat := 118140960795 + 8376421 * 2 ^ 59
def prefixEnd_8376421 : Nat := 4983230072969 + 3 ^ 40 * 8376421 * 2
def baseEnd_8376421 : Nat := 4301130137414876948015047

theorem tailTrace_8376421 : CollatzResearch.WordTrace tailWord_8376421 prefixEnd_8376421 4301130137414876948015047 := by
  unfold tailWord_8376421
  simp only [CollatzResearch.WordTrace]
  refine ⟨305513172786664770657713117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203675448524443180438475411 305513172786664770657713117)
  ·
    refine ⟨114567439794999288996642419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305513172786664770657713117 114567439794999288996642419)
    ·
      refine ⟨171851159692498933494963629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114567439794999288996642419 171851159692498933494963629)
      ·
        refine ⟨64444184884687100060611361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171851159692498933494963629 64444184884687100060611361)
        ·
          refine ⟨48333138663515325045458521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64444184884687100060611361 48333138663515325045458521)
          ·
            refine ⟨36249853997636493784093891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48333138663515325045458521 36249853997636493784093891)
            ·
              refine ⟨54374780996454740676140837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36249853997636493784093891 54374780996454740676140837)
              ·
                refine ⟨10195271436835263876776407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54374780996454740676140837 10195271436835263876776407)
                ·
                  refine ⟨15292907155252895815164611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10195271436835263876776407 15292907155252895815164611)
                  ·
                    refine ⟨22939360732879343722746917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15292907155252895815164611 22939360732879343722746917)
                    ·
                      refine ⟨4301130137414876948015047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22939360732879343722746917 4301130137414876948015047)
                      ·
                        rfl

theorem cell23_8376421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_8376421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376421 prefixEnd_8376421 := by exact prefixLift 8376421
  have htrace : WordTrace (prefixWord ++ tailWord_8376421) baseStart_8376421 baseEnd_8376421 := by
    simpa [prefixWord, tailWord_8376421, baseEnd_8376421] using wordTrace_append hprefix tailTrace_8376421
  have hstable : (prefixWord ++ tailWord_8376421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376421).length < 2 ^ (prefixWord ++ tailWord_8376421).sum := by decide
  have hdescent : baseEnd_8376421 < baseStart_8376421 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376438 : List Nat := [5, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4]
def baseStart_8376438 : Nat := 118140960795 + 8376438 * 2 ^ 59
def prefixEnd_8376438 : Nat := 4983230072969 + 3 ^ 40 * 8376438 * 2
def baseEnd_8376438 : Nat := 4301138866586003381502469

theorem tailTrace_8376438 : CollatzResearch.WordTrace tailWord_8376438 prefixEnd_8376438 4301138866586003381502469 := by
  unfold tailWord_8376438
  simp only [CollatzResearch.WordTrace]
  refine ⟨19094612051725198910067623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203675861885068788374054645 19094612051725198910067623)
  ·
    refine ⟨28641918077587798365101435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19094612051725198910067623 28641918077587798365101435)
    ·
      refine ⟨42962877116381697547652153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28641918077587798365101435 42962877116381697547652153)
      ·
        refine ⟨32222157837286273160739115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42962877116381697547652153 32222157837286273160739115)
        ·
          refine ⟨48333236755929409741108673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32222157837286273160739115 48333236755929409741108673)
          ·
            refine ⟨36249927566947057305831505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48333236755929409741108673 36249927566947057305831505)
            ·
              refine ⟨27187445675210292979373629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36249927566947057305831505 27187445675210292979373629)
              ·
                refine ⟨10195292128203859867265111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27187445675210292979373629 10195292128203859867265111)
                ·
                  refine ⟨15292938192305789800897667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10195292128203859867265111 15292938192305789800897667)
                  ·
                    refine ⟨22939407288458684701346501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15292938192305789800897667 22939407288458684701346501)
                    ·
                      refine ⟨4301138866586003381502469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22939407288458684701346501 4301138866586003381502469)
                      ·
                        rfl

theorem cell23_8376438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_8376438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376438 prefixEnd_8376438 := by exact prefixLift 8376438
  have htrace : WordTrace (prefixWord ++ tailWord_8376438) baseStart_8376438 baseEnd_8376438 := by
    simpa [prefixWord, tailWord_8376438, baseEnd_8376438] using wordTrace_append hprefix tailTrace_8376438
  have hstable : (prefixWord ++ tailWord_8376438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376438).length < 2 ^ (prefixWord ++ tailWord_8376438).sum := by decide
  have hdescent : baseEnd_8376438 < baseStart_8376438 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376441 : List Nat := [1, 2, 1, 3, 4, 2, 2, 1, 1, 1, 5]
def baseStart_8376441 : Nat := 118140960795 + 8376441 * 2 ^ 59
def prefixEnd_8376441 : Nat := 4983230072969 + 3 ^ 40 * 8376441 * 2
def baseEnd_8376441 : Nat := 4301140407027966869764955

theorem tailTrace_8376441 : CollatzResearch.WordTrace tailWord_8376441 prefixEnd_8376441 4301140407027966869764955 := by
  unfold tailWord_8376441
  simp only [CollatzResearch.WordTrace]
  refine ⟨305513902246592314073441177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203675934831061542715627451 305513902246592314073441177)
  ·
    refine ⟨229135426684944235555080883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305513902246592314073441177 229135426684944235555080883)
    ·
      refine ⟨343703140027416353332621325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229135426684944235555080883 343703140027416353332621325)
      ·
        refine ⟨128888677510281132499732997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343703140027416353332621325 128888677510281132499732997)
        ·
          refine ⟨24166627033177712343699937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128888677510281132499732997 24166627033177712343699937)
          ·
            refine ⟨18124970274883284257774953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24166627033177712343699937 18124970274883284257774953)
            ·
              refine ⟨13593727706162463193331215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18124970274883284257774953 13593727706162463193331215)
              ·
                refine ⟨20390591559243694789996823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13593727706162463193331215 20390591559243694789996823)
                ·
                  refine ⟨30585887338865542184995235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20390591559243694789996823 30585887338865542184995235)
                  ·
                    refine ⟨45878831008298313277492853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30585887338865542184995235 45878831008298313277492853)
                    ·
                      refine ⟨4301140407027966869764955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45878831008298313277492853 4301140407027966869764955)
                      ·
                        rfl

theorem cell23_8376441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_8376441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376441 prefixEnd_8376441 := by exact prefixLift 8376441
  have htrace : WordTrace (prefixWord ++ tailWord_8376441) baseStart_8376441 baseEnd_8376441 := by
    simpa [prefixWord, tailWord_8376441, baseEnd_8376441] using wordTrace_append hprefix tailTrace_8376441
  have hstable : (prefixWord ++ tailWord_8376441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376441).length < 2 ^ (prefixWord ++ tailWord_8376441).sum := by decide
  have hdescent : baseEnd_8376441 < baseStart_8376441 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376444 : List Nat := [2, 2, 2, 1, 1, 6, 9]
def baseStart_8376444 : Nat := 118140960795 + 8376444 * 2 ^ 59
def prefixEnd_8376444 : Nat := 4983230072969 + 3 ^ 40 * 8376444 * 2
def baseEnd_8376444 : Nat := 53100517869999140222561

theorem tailTrace_8376444 : CollatzResearch.WordTrace tailWord_8376444 prefixEnd_8376444 53100517869999140222561 := by
  unfold tailWord_8376444
  simp only [CollatzResearch.WordTrace]
  refine ⟨152757005832790722792900193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203676007777054297057200257 152757005832790722792900193)
  ·
    refine ⟨114567754374593042094675145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152757005832790722792900193 114567754374593042094675145)
    ·
      refine ⟨85925815780944781571006359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114567754374593042094675145 85925815780944781571006359)
      ·
        refine ⟨128888723671417172356509539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85925815780944781571006359 128888723671417172356509539)
        ·
          refine ⟨193333085507125758534764309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128888723671417172356509539 193333085507125758534764309)
          ·
            refine ⟨9062488383146519931317077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 193333085507125758534764309 9062488383146519931317077)
            ·
              refine ⟨53100517869999140222561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 9062488383146519931317077 53100517869999140222561)
              ·
                rfl

theorem cell23_8376444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 9].length) (baseStart_8376444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376444 prefixEnd_8376444 := by exact prefixLift 8376444
  have htrace : WordTrace (prefixWord ++ tailWord_8376444) baseStart_8376444 baseEnd_8376444 := by
    simpa [prefixWord, tailWord_8376444, baseEnd_8376444] using wordTrace_append hprefix tailTrace_8376444
  have hstable : (prefixWord ++ tailWord_8376444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376444).length < 2 ^ (prefixWord ++ tailWord_8376444).sum := by decide
  have hdescent : baseEnd_8376444 < baseStart_8376444 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376455 : List Nat := [1, 1, 4, 2, 1, 1, 2, 6, 1, 2, 2]
def baseStart_8376455 : Nat := 118140960795 + 8376455 * 2 ^ 59
def prefixEnd_8376455 : Nat := 4983230072969 + 3 ^ 40 * 8376455 * 2
def baseEnd_8376455 : Nat := 4301147595757129814989891

theorem tailTrace_8376455 : CollatzResearch.WordTrace tailWord_8376455 prefixEnd_8376455 4301147595757129814989891 := by
  unfold tailWord_8376455
  simp only [CollatzResearch.WordTrace]
  refine ⟨305514412868541594464450819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203676275245694396309633879 305514412868541594464450819)
  ·
    refine ⟨458271619302812391696676229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305514412868541594464450819 458271619302812391696676229)
    ·
      refine ⟨85925928619277323443126793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 458271619302812391696676229 85925928619277323443126793)
      ·
        refine ⟨64444446464457992582345095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85925928619277323443126793 64444446464457992582345095)
        ·
          refine ⟨96666669696686988873517643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64444446464457992582345095 96666669696686988873517643)
          ·
            refine ⟨145000004545030483310276465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96666669696686988873517643 145000004545030483310276465)
            ·
              refine ⟨108750003408772862482707349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145000004545030483310276465 108750003408772862482707349)
              ·
                refine ⟨5097656409786227928876907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108750003408772862482707349 5097656409786227928876907)
                ·
                  refine ⟨7646484614679341893315361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5097656409786227928876907 7646484614679341893315361)
                  ·
                    refine ⟨5734863461009506419986521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7646484614679341893315361 5734863461009506419986521)
                    ·
                      refine ⟨4301147595757129814989891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5734863461009506419986521 4301147595757129814989891)
                      ·
                        rfl

theorem cell23_8376455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_8376455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376455 prefixEnd_8376455 := by exact prefixLift 8376455
  have htrace : WordTrace (prefixWord ++ tailWord_8376455) baseStart_8376455 baseEnd_8376455 := by
    simpa [prefixWord, tailWord_8376455, baseEnd_8376455] using wordTrace_append hprefix tailTrace_8376455
  have hstable : (prefixWord ++ tailWord_8376455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376455).length < 2 ^ (prefixWord ++ tailWord_8376455).sum := by decide
  have hdescent : baseEnd_8376455 < baseStart_8376455 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376500 : List Nat := [2, 5, 3, 1, 2, 1, 2, 2, 1, 1, 3]
def baseStart_8376500 : Nat := 118140960795 + 8376500 * 2 ^ 59
def prefixEnd_8376500 : Nat := 4983230072969 + 3 ^ 40 * 8376500 * 2
def baseEnd_8376500 : Nat := 4301170702386582138927185

theorem tailTrace_8376500 : CollatzResearch.WordTrace tailWord_8376500 prefixEnd_8376500 4301170702386582138927185 := by
  unfold tailWord_8376500
  simp only [CollatzResearch.WordTrace]
  refine ⟨152758027076689283574919477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203677369435585711433225969 152758027076689283574919477)
  ·
    refine ⟨14321065038439620335148701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152758027076689283574919477 14321065038439620335148701)
    ·
      refine ⟨5370399389414857625680763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14321065038439620335148701 5370399389414857625680763)
      ·
        refine ⟨8055599084122286438521145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5370399389414857625680763 8055599084122286438521145)
        ·
          refine ⟨6041699313091714828890859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8055599084122286438521145 6041699313091714828890859)
          ·
            refine ⟨9062548969637572243336289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6041699313091714828890859 9062548969637572243336289)
            ·
              refine ⟨6796911727228179182502217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9062548969637572243336289 6796911727228179182502217)
              ·
                refine ⟨5097683795421134386876663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6796911727228179182502217 5097683795421134386876663)
                ·
                  refine ⟨7646525693131701580314995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5097683795421134386876663 7646525693131701580314995)
                  ·
                    refine ⟨11469788539697552370472493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7646525693131701580314995 11469788539697552370472493)
                    ·
                      refine ⟨4301170702386582138927185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11469788539697552370472493 4301170702386582138927185)
                      ·
                        rfl

theorem cell23_8376500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_8376500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376500 prefixEnd_8376500 := by exact prefixLift 8376500
  have htrace : WordTrace (prefixWord ++ tailWord_8376500) baseStart_8376500 baseEnd_8376500 := by
    simpa [prefixWord, tailWord_8376500, baseEnd_8376500] using wordTrace_append hprefix tailTrace_8376500
  have hstable : (prefixWord ++ tailWord_8376500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376500).length < 2 ^ (prefixWord ++ tailWord_8376500).sum := by decide
  have hdescent : baseEnd_8376500 < baseStart_8376500 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376504 : List Nat := [2, 1, 2, 1, 2, 1, 4, 2, 2, 6]
def baseStart_8376504 : Nat := 118140960795 + 8376504 * 2 ^ 59
def prefixEnd_8376504 : Nat := 4983230072969 + 3 ^ 40 * 8376504 * 2
def baseEnd_8376504 : Nat := 1433724252103066707759055

theorem tailTrace_8376504 : CollatzResearch.WordTrace tailWord_8376504 prefixEnd_8376504 1433724252103066707759055 := by
  unfold tailWord_8376504
  simp only [CollatzResearch.WordTrace]
  refine ⟨152758100022682037916492283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203677466696909383888656377 152758100022682037916492283)
  ·
    refine ⟨229137150034023056874738425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152758100022682037916492283 229137150034023056874738425)
    ·
      refine ⟨171852862525517292656053819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229137150034023056874738425 171852862525517292656053819)
      ·
        refine ⟨257779293788275938984080729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171852862525517292656053819 257779293788275938984080729)
        ·
          refine ⟨193334470341206954238060547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257779293788275938984080729 193334470341206954238060547)
          ·
            refine ⟨290001705511810431357090821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193334470341206954238060547 290001705511810431357090821)
            ·
              refine ⟨54375319783464455879454529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 290001705511810431357090821 54375319783464455879454529)
              ·
                refine ⟨40781489837598341909590897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54375319783464455879454529 40781489837598341909590897)
                ·
                  refine ⟨30586117378198756432193173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40781489837598341909590897 30586117378198756432193173)
                  ·
                    refine ⟨1433724252103066707759055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30586117378198756432193173 1433724252103066707759055)
                    ·
                      rfl

theorem cell23_8376504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 2, 6].length) (baseStart_8376504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376504 prefixEnd_8376504 := by exact prefixLift 8376504
  have htrace : WordTrace (prefixWord ++ tailWord_8376504) baseStart_8376504 baseEnd_8376504 := by
    simpa [prefixWord, tailWord_8376504, baseEnd_8376504] using wordTrace_append hprefix tailTrace_8376504
  have hstable : (prefixWord ++ tailWord_8376504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376504).length < 2 ^ (prefixWord ++ tailWord_8376504).sum := by decide
  have hdescent : baseEnd_8376504 < baseStart_8376504 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376511 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 5, 4, 2]
def baseStart_8376511 : Nat := 118140960795 + 8376511 * 2 ^ 59
def prefixEnd_8376511 : Nat := 4983230072969 + 3 ^ 40 * 8376511 * 2
def baseEnd_8376511 : Nat := 4301176350673781595889633

theorem tailTrace_8376511 : CollatzResearch.WordTrace tailWord_8376511 prefixEnd_8376511 4301176350673781595889633 := by
  unfold tailWord_8376511
  simp only [CollatzResearch.WordTrace]
  refine ⟨305516455356338716028489387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203677636904225810685659591 305516455356338716028489387)
  ·
    refine ⟨458274683034508074042734081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305516455356338716028489387 458274683034508074042734081)
    ·
      refine ⟨343706012275881055532050561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458274683034508074042734081 343706012275881055532050561)
      ·
        refine ⟨257779509206910791649037921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343706012275881055532050561 257779509206910791649037921)
        ·
          refine ⟨193334631905183093736778441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257779509206910791649037921 193334631905183093736778441)
          ·
            refine ⟨145000973928887320302583831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193334631905183093736778441 145000973928887320302583831)
            ·
              refine ⟨217501460893330980453875747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145000973928887320302583831 217501460893330980453875747)
              ·
                refine ⟨326252191339996470680813621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217501460893330980453875747 326252191339996470680813621)
                ·
                  refine ⟨30586142938124669126326277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 326252191339996470680813621 30586142938124669126326277)
                  ·
                    refine ⟨5734901800898375461186177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30586142938124669126326277 5734901800898375461186177)
                    ·
                      refine ⟨4301176350673781595889633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5734901800898375461186177 4301176350673781595889633)
                      ·
                        rfl

theorem cell23_8376511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 4, 2].length) (baseStart_8376511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376511 prefixEnd_8376511 := by exact prefixLift 8376511
  have htrace : WordTrace (prefixWord ++ tailWord_8376511) baseStart_8376511 baseEnd_8376511 := by
    simpa [prefixWord, tailWord_8376511, baseEnd_8376511] using wordTrace_append hprefix tailTrace_8376511
  have hstable : (prefixWord ++ tailWord_8376511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376511).length < 2 ^ (prefixWord ++ tailWord_8376511).sum := by decide
  have hdescent : baseEnd_8376511 < baseStart_8376511 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376561 : List Nat := [1, 2, 2, 2, 2, 1, 3, 2, 2, 3, 3]
def baseStart_8376561 : Nat := 118140960795 + 8376561 * 2 ^ 59
def prefixEnd_8376561 : Nat := 4983230072969 + 3 ^ 40 * 8376561 * 2
def baseEnd_8376561 : Nat := 4301202024706506400264403

theorem tailTrace_8376561 : CollatzResearch.WordTrace tailWord_8376561 prefixEnd_8376561 4301202024706506400264403 := by
  unfold tailWord_8376561
  simp only [CollatzResearch.WordTrace]
  refine ⟨305518279006157574567809537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203678852670771716378539691 305518279006157574567809537)
  ·
    refine ⟨229138709254618180925857153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305518279006157574567809537 229138709254618180925857153)
    ·
      refine ⟨171854031940963635694392865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229138709254618180925857153 171854031940963635694392865)
      ·
        refine ⟨128890523955722726770794649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171854031940963635694392865 128890523955722726770794649)
        ·
          refine ⟨96667892966792045078095987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128890523955722726770794649 96667892966792045078095987)
          ·
            refine ⟨145001839450188067617143981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96667892966792045078095987 145001839450188067617143981)
            ·
              refine ⟨54375689793820525356428993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145001839450188067617143981 54375689793820525356428993)
              ·
                refine ⟨40781767345365394017321745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54375689793820525356428993 40781767345365394017321745)
                ·
                  refine ⟨30586325509024045512991309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40781767345365394017321745 30586325509024045512991309)
                  ·
                    refine ⟨11469872065884017067371741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30586325509024045512991309 11469872065884017067371741)
                    ·
                      refine ⟨4301202024706506400264403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11469872065884017067371741 4301202024706506400264403)
                      ·
                        rfl

theorem cell23_8376561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_8376561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376561 prefixEnd_8376561 := by exact prefixLift 8376561
  have htrace : WordTrace (prefixWord ++ tailWord_8376561) baseStart_8376561 baseEnd_8376561 := by
    simpa [prefixWord, tailWord_8376561, baseEnd_8376561] using wordTrace_append hprefix tailTrace_8376561
  have hstable : (prefixWord ++ tailWord_8376561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376561).length < 2 ^ (prefixWord ++ tailWord_8376561).sum := by decide
  have hdescent : baseEnd_8376561 < baseStart_8376561 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376562 : List Nat := [3, 2, 1, 3, 2, 1, 3, 2, 2, 2, 2]
def baseStart_8376562 : Nat := 118140960795 + 8376562 * 2 ^ 59
def prefixEnd_8376562 : Nat := 4983230072969 + 3 ^ 40 * 8376562 * 2
def baseEnd_8376562 : Nat := 4301202538187160896351899

theorem tailTrace_8376562 : CollatzResearch.WordTrace tailWord_8376562 prefixEnd_8376562 4301202538187160896351899 := by
  unfold tailWord_8376562
  simp only [CollatzResearch.WordTrace]
  refine ⟨76379578869788487934648985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203678876986102634492397293 76379578869788487934648985)
  ·
    refine ⟨57284684152341365950986739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76379578869788487934648985 57284684152341365950986739)
    ·
      refine ⟨85927026228512048926480109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57284684152341365950986739 85927026228512048926480109)
      ·
        refine ⟨32222634835692018347430041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85927026228512048926480109 32222634835692018347430041)
        ·
          refine ⟨24166976126769013760572531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32222634835692018347430041 24166976126769013760572531)
          ·
            refine ⟨36250464190153520640858797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24166976126769013760572531 36250464190153520640858797)
            ·
              refine ⟨13593924071307570240322049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36250464190153520640858797 13593924071307570240322049)
              ·
                refine ⟨10195443053480677680241537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13593924071307570240322049 10195443053480677680241537)
                ·
                  refine ⟨7646582290110508260181153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10195443053480677680241537 7646582290110508260181153)
                  ·
                    refine ⟨5734936717582881195135865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7646582290110508260181153 5734936717582881195135865)
                    ·
                      refine ⟨4301202538187160896351899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5734936717582881195135865 4301202538187160896351899)
                      ·
                        rfl

theorem cell23_8376562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_8376562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376562 prefixEnd_8376562 := by exact prefixLift 8376562
  have htrace : WordTrace (prefixWord ++ tailWord_8376562) baseStart_8376562 baseEnd_8376562 := by
    simpa [prefixWord, tailWord_8376562, baseEnd_8376562] using wordTrace_append hprefix tailTrace_8376562
  have hstable : (prefixWord ++ tailWord_8376562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376562).length < 2 ^ (prefixWord ++ tailWord_8376562).sum := by decide
  have hdescent : baseEnd_8376562 < baseStart_8376562 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376602 : List Nat := [3, 1, 1, 3, 5, 1, 1, 3, 5]
def baseStart_8376602 : Nat := 118140960795 + 8376602 * 2 ^ 59
def prefixEnd_8376602 : Nat := 4983230072969 + 3 ^ 40 * 8376602 * 2
def baseEnd_8376602 : Nat := 477913675268148971094635

theorem tailTrace_8376602 : CollatzResearch.WordTrace tailWord_8376602 prefixEnd_8376602 477913675268148971094635 := by
  unfold tailWord_8376602
  simp only [CollatzResearch.WordTrace]
  refine ⟨76379943599752259642513015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203679849599339359046701373 76379943599752259642513015)
  ·
    refine ⟨114569915399628389463769523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76379943599752259642513015 114569915399628389463769523)
    ·
      refine ⟨171854873099442584195654285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114569915399628389463769523 171854873099442584195654285)
      ·
        refine ⟨64445577412290969073370357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171854873099442584195654285 64445577412290969073370357)
        ·
          refine ⟨6041772882402278350628471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64445577412290969073370357 6041772882402278350628471)
          ·
            refine ⟨9062659323603417525942707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6041772882402278350628471 9062659323603417525942707)
            ·
              refine ⟨13593988985405126288914061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9062659323603417525942707 13593988985405126288914061)
              ·
                refine ⟨5097745869526922358342773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13593988985405126288914061 5097745869526922358342773)
                ·
                  refine ⟨477913675268148971094635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5097745869526922358342773 477913675268148971094635)
                  ·
                    rfl

theorem cell23_8376602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 3, 5].length) (baseStart_8376602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376602 prefixEnd_8376602 := by exact prefixLift 8376602
  have htrace : WordTrace (prefixWord ++ tailWord_8376602) baseStart_8376602 baseEnd_8376602 := by
    simpa [prefixWord, tailWord_8376602, baseEnd_8376602] using wordTrace_append hprefix tailTrace_8376602
  have hstable : (prefixWord ++ tailWord_8376602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376602).length < 2 ^ (prefixWord ++ tailWord_8376602).sum := by decide
  have hdescent : baseEnd_8376602 < baseStart_8376602 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376670 : List Nat := [4, 4, 2, 1, 2, 1, 2, 2, 5]
def baseStart_8376670 : Nat := 118140960795 + 8376670 * 2 ^ 59
def prefixEnd_8376670 : Nat := 4983230072969 + 3 ^ 40 * 8376670 * 2
def baseEnd_8376670 : Nat := 477917554899760719311267

theorem tailTrace_8376670 : CollatzResearch.WordTrace tailWord_8376670 prefixEnd_8376670 477917554899760719311267 := by
  unfold tailWord_8376670
  simp only [CollatzResearch.WordTrace]
  refine ⟨38190281820345335772940933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203681503041841790789018309 38190281820345335772940933)
  ·
    refine ⟨7160677841314750457426425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38190281820345335772940933 7160677841314750457426425)
    ·
      refine ⟨5370508380986062843069819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7160677841314750457426425 5370508380986062843069819)
      ·
        refine ⟨8055762571479094264604729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5370508380986062843069819 8055762571479094264604729)
        ·
          refine ⟨6041821928609320698453547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8055762571479094264604729 6041821928609320698453547)
          ·
            refine ⟨9062732892913981047680321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6041821928609320698453547 9062732892913981047680321)
            ·
              refine ⟨6797049669685485785760241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9062732892913981047680321 6797049669685485785760241)
              ·
                refine ⟨5097787252264114339320181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6797049669685485785760241 5097787252264114339320181)
                ·
                  refine ⟨477917554899760719311267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5097787252264114339320181 477917554899760719311267)
                  ·
                    rfl

theorem cell23_8376670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_8376670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376670 prefixEnd_8376670 := by exact prefixLift 8376670
  have htrace : WordTrace (prefixWord ++ tailWord_8376670) baseStart_8376670 baseEnd_8376670 := by
    simpa [prefixWord, tailWord_8376670, baseEnd_8376670] using wordTrace_append hprefix tailTrace_8376670
  have hstable : (prefixWord ++ tailWord_8376670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376670).length < 2 ^ (prefixWord ++ tailWord_8376670).sum := by decide
  have hdescent : baseEnd_8376670 < baseStart_8376670 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376679 : List Nat := [1, 1, 5, 1, 3, 3, 2, 2, 1, 4]
def baseStart_8376679 : Nat := 118140960795 + 8376679 * 2 ^ 59
def prefixEnd_8376679 : Nat := 4983230072969 + 3 ^ 40 * 8376679 * 2
def baseEnd_8376679 : Nat := 1433754205141245646196287

theorem tailTrace_8376679 : CollatzResearch.WordTrace tailWord_8376679 prefixEnd_8376679 1433754205141245646196287 := by
  unfold tailWord_8376679
  simp only [CollatzResearch.WordTrace]
  refine ⟨305522582819730080720605091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203681721879820053813736727 305522582819730080720605091)
  ·
    refine ⟨458283874229595121080907637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305522582819730080720605091 458283874229595121080907637)
    ·
      refine ⟨42964113209024542601335091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 458283874229595121080907637 42964113209024542601335091)
      ·
        refine ⟨64446169813536813902002637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42964113209024542601335091 64446169813536813902002637)
        ·
          refine ⟨24167313680076305213250989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64446169813536813902002637 24167313680076305213250989)
          ·
            refine ⟨9062742630028614454969121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24167313680076305213250989 9062742630028614454969121)
            ·
              refine ⟨6797056972521460841226841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9062742630028614454969121 6797056972521460841226841)
              ·
                refine ⟨5097792729391095630920131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6797056972521460841226841 5097792729391095630920131)
                ·
                  refine ⟨7646689094086643446380197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5097792729391095630920131 7646689094086643446380197)
                  ·
                    refine ⟨1433754205141245646196287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7646689094086643446380197 1433754205141245646196287)
                    ·
                      rfl

theorem cell23_8376679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_8376679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376679 prefixEnd_8376679 := by exact prefixLift 8376679
  have htrace : WordTrace (prefixWord ++ tailWord_8376679) baseStart_8376679 baseEnd_8376679 := by
    simpa [prefixWord, tailWord_8376679, baseEnd_8376679] using wordTrace_append hprefix tailTrace_8376679
  have hstable : (prefixWord ++ tailWord_8376679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376679).length < 2 ^ (prefixWord ++ tailWord_8376679).sum := by decide
  have hdescent : baseEnd_8376679 < baseStart_8376679 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376685 : List Nat := [1, 5, 1, 1, 1, 2, 2, 3, 3, 1, 3]
def baseStart_8376685 : Nat := 118140960795 + 8376685 * 2 ^ 59
def prefixEnd_8376685 : Nat := 4983230072969 + 3 ^ 40 * 8376685 * 2
def baseEnd_8376685 : Nat := 4301265696307663915113833

theorem tailTrace_8376685 : CollatzResearch.WordTrace tailWord_8376685 prefixEnd_8376685 4301265696307663915113833 := by
  unfold tailWord_8376685
  simp only [CollatzResearch.WordTrace]
  refine ⟨305522801657708343745323509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203681867771805562496882339 305522801657708343745323509)
  ·
    refine ⟨28642762655410157226124079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 305522801657708343745323509 28642762655410157226124079)
    ·
      refine ⟨42964143983115235839186119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28642762655410157226124079 42964143983115235839186119)
      ·
        refine ⟨64446215974672853758779179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42964143983115235839186119 64446215974672853758779179)
        ·
          refine ⟨96669323962009280638168769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64446215974672853758779179 96669323962009280638168769)
          ·
            refine ⟨72501992971506960478626577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96669323962009280638168769 72501992971506960478626577)
            ·
              refine ⟨54376494728630220358969933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72501992971506960478626577 54376494728630220358969933)
              ·
                refine ⟨20391185523236332634613725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54376494728630220358969933 20391185523236332634613725)
                ·
                  refine ⟨7646694571213624737980147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20391185523236332634613725 7646694571213624737980147)
                  ·
                    refine ⟨11470041856820437106970221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7646694571213624737980147 11470041856820437106970221)
                    ·
                      refine ⟨4301265696307663915113833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11470041856820437106970221 4301265696307663915113833)
                      ·
                        rfl

theorem cell23_8376685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_8376685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376685 prefixEnd_8376685 := by exact prefixLift 8376685
  have htrace : WordTrace (prefixWord ++ tailWord_8376685) baseStart_8376685 baseEnd_8376685 := by
    simpa [prefixWord, tailWord_8376685, baseEnd_8376685] using wordTrace_append hprefix tailTrace_8376685
  have hstable : (prefixWord ++ tailWord_8376685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376685).length < 2 ^ (prefixWord ++ tailWord_8376685).sum := by decide
  have hdescent : baseEnd_8376685 < baseStart_8376685 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376706 : List Nat := [3, 4, 2, 1, 3, 1, 1, 1, 2, 2, 3]
def baseStart_8376706 : Nat := 118140960795 + 8376706 * 2 ^ 59
def prefixEnd_8376706 : Nat := 4983230072969 + 3 ^ 40 * 8376706 * 2
def baseEnd_8376706 : Nat := 4301276479401408332951237

theorem tailTrace_8376706 : CollatzResearch.WordTrace tailWord_8376706 prefixEnd_8376706 4301276479401408332951237 := by
  unfold tailWord_8376706
  simp only [CollatzResearch.WordTrace]
  refine ⟨76380891897658066082959493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203682378393754842887891981 76380891897658066082959493)
  ·
    refine ⟨14321417230810887390554905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76380891897658066082959493 14321417230810887390554905)
    ·
      refine ⟨10741062923108165542916179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14321417230810887390554905 10741062923108165542916179)
      ·
        refine ⟨16111594384662248314374269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10741062923108165542916179 16111594384662248314374269)
        ·
          refine ⟨6041847894248343117890351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16111594384662248314374269 6041847894248343117890351)
          ·
            refine ⟨9062771841372514676835527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6041847894248343117890351 9062771841372514676835527)
            ·
              refine ⟨13594157762058772015253291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9062771841372514676835527 13594157762058772015253291)
              ·
                refine ⟨20391236643088158022879937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13594157762058772015253291 20391236643088158022879937)
                ·
                  refine ⟨15293427482316118517159953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20391236643088158022879937 15293427482316118517159953)
                  ·
                    refine ⟨11470070611737088887869965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15293427482316118517159953 11470070611737088887869965)
                    ·
                      refine ⟨4301276479401408332951237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11470070611737088887869965 4301276479401408332951237)
                      ·
                        rfl

theorem cell23_8376706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_8376706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376706 prefixEnd_8376706 := by exact prefixLift 8376706
  have htrace : WordTrace (prefixWord ++ tailWord_8376706) baseStart_8376706 baseEnd_8376706 := by
    simpa [prefixWord, tailWord_8376706, baseEnd_8376706] using wordTrace_append hprefix tailTrace_8376706
  have hstable : (prefixWord ++ tailWord_8376706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376706).length < 2 ^ (prefixWord ++ tailWord_8376706).sum := by decide
  have hdescent : baseEnd_8376706 < baseStart_8376706 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376708 : List Nat := [2, 3, 2, 1, 1, 2, 1, 3, 3, 1, 4]
def baseStart_8376708 : Nat := 118140960795 + 8376708 * 2 ^ 59
def prefixEnd_8376708 : Nat := 4983230072969 + 3 ^ 40 * 8376708 * 2
def baseEnd_8376708 : Nat := 4301277506362717325126227

theorem tailTrace_8376708 : CollatzResearch.WordTrace tailWord_8376708 prefixEnd_8376708 4301277506362717325126227 := by
  unfold tailWord_8376708
  simp only [CollatzResearch.WordTrace]
  refine ⟨152761820268312509336705389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203682427024416679115607185 152761820268312509336705389)
  ·
    refine ⟨57285682600617191001264521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152761820268312509336705389 57285682600617191001264521)
    ·
      refine ⟨42964261950462893250948391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57285682600617191001264521 42964261950462893250948391)
      ·
        refine ⟨64446392925694339876422587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42964261950462893250948391 64446392925694339876422587)
        ·
          refine ⟨96669589388541509814633881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64446392925694339876422587 96669589388541509814633881)
          ·
            refine ⟨72502192041406132360975411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96669589388541509814633881 72502192041406132360975411)
            ·
              refine ⟨108753288062109198541463117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72502192041406132360975411 108753288062109198541463117)
              ·
                refine ⟨40782483023290949453048669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108753288062109198541463117 40782483023290949453048669)
                ·
                  refine ⟨15293431133734106044893251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40782483023290949453048669 15293431133734106044893251)
                  ·
                    refine ⟨22940146700601159067339877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15293431133734106044893251 22940146700601159067339877)
                    ·
                      refine ⟨4301277506362717325126227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22940146700601159067339877 4301277506362717325126227)
                      ·
                        rfl

theorem cell23_8376708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_8376708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376708 prefixEnd_8376708 := by exact prefixLift 8376708
  have htrace : WordTrace (prefixWord ++ tailWord_8376708) baseStart_8376708 baseEnd_8376708 := by
    simpa [prefixWord, tailWord_8376708, baseEnd_8376708] using wordTrace_append hprefix tailTrace_8376708
  have hstable : (prefixWord ++ tailWord_8376708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376708).length < 2 ^ (prefixWord ++ tailWord_8376708).sum := by decide
  have hdescent : baseEnd_8376708 < baseStart_8376708 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376725 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 7, 2, 2]
def baseStart_8376725 : Nat := 118140960795 + 8376725 * 2 ^ 59
def prefixEnd_8376725 : Nat := 4983230072969 + 3 ^ 40 * 8376725 * 2
def baseEnd_8376725 : Nat := 4301286235533843758613649

theorem tailTrace_8376725 : CollatzResearch.WordTrace tailWord_8376725 prefixEnd_8376725 4301286235533843758613649 := by
  unfold tailWord_8376725
  simp only [CollatzResearch.WordTrace]
  refine ⟨305524260577563430576779629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203682840385042287051186419 305524260577563430576779629)
  ·
    refine ⟨114571597716586286466292361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305524260577563430576779629 114571597716586286466292361)
    ·
      refine ⟨85928698287439714849719271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114571597716586286466292361 85928698287439714849719271)
      ·
        refine ⟨128893047431159572274578907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85928698287439714849719271 128893047431159572274578907)
        ·
          refine ⟨193339571146739358411868361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128893047431159572274578907 193339571146739358411868361)
          ·
            refine ⟨145004678360054518808901271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193339571146739358411868361 145004678360054518808901271)
            ·
              refine ⟨217507017540081778213351907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145004678360054518808901271 217507017540081778213351907)
              ·
                refine ⟨326260526310122667320027861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217507017540081778213351907 326260526310122667320027861)
                ·
                  refine ⟨7646731085393500015313153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 326260526310122667320027861 7646731085393500015313153)
                  ·
                    refine ⟨5735048314045125011484865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7646731085393500015313153 5735048314045125011484865)
                    ·
                      refine ⟨4301286235533843758613649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5735048314045125011484865 4301286235533843758613649)
                      ·
                        rfl

theorem cell23_8376725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 7, 2, 2].length) (baseStart_8376725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376725 prefixEnd_8376725 := by exact prefixLift 8376725
  have htrace : WordTrace (prefixWord ++ tailWord_8376725) baseStart_8376725 baseEnd_8376725 := by
    simpa [prefixWord, tailWord_8376725, baseEnd_8376725] using wordTrace_append hprefix tailTrace_8376725
  have hstable : (prefixWord ++ tailWord_8376725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376725).length < 2 ^ (prefixWord ++ tailWord_8376725).sum := by decide
  have hdescent : baseEnd_8376725 < baseStart_8376725 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376726 : List Nat := [5, 3, 1, 2, 1, 2, 1, 2, 6]
def baseStart_8376726 : Nat := 118140960795 + 8376726 * 2 ^ 59
def prefixEnd_8376726 : Nat := 4983230072969 + 3 ^ 40 * 8376726 * 2
def baseEnd_8376726 : Nat := 477920749890499806077905

theorem tailTrace_8376726 : CollatzResearch.WordTrace tailWord_8376726 prefixEnd_8376726 477920749890499806077905 := by
  unfold tailWord_8376726
  simp only [CollatzResearch.WordTrace]
  refine ⟨19095268565659987984222877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203682864700373205165044021 19095268565659987984222877)
  ·
    refine ⟨7160725712122495494083579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19095268565659987984222877 7160725712122495494083579)
    ·
      refine ⟨10741088568183743241125369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7160725712122495494083579 10741088568183743241125369)
      ·
        refine ⟨8055816426137807430844027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10741088568183743241125369 8055816426137807430844027)
        ·
          refine ⟨12083724639206711146266041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8055816426137807430844027 12083724639206711146266041)
          ·
            refine ⟨9062793479405033359699531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12083724639206711146266041 9062793479405033359699531)
            ·
              refine ⟨13594190219107550039549297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9062793479405033359699531 13594190219107550039549297)
              ·
                refine ⟨10195642664330662529661973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13594190219107550039549297 10195642664330662529661973)
                ·
                  refine ⟨477920749890499806077905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10195642664330662529661973 477920749890499806077905)
                  ·
                    rfl

theorem cell23_8376726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_8376726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376726 prefixEnd_8376726 := by exact prefixLift 8376726
  have htrace : WordTrace (prefixWord ++ tailWord_8376726) baseStart_8376726 baseEnd_8376726 := by
    simpa [prefixWord, tailWord_8376726, baseEnd_8376726] using wordTrace_append hprefix tailTrace_8376726
  have hstable : (prefixWord ++ tailWord_8376726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376726).length < 2 ^ (prefixWord ++ tailWord_8376726).sum := by decide
  have hdescent : baseEnd_8376726 < baseStart_8376726 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376738 : List Nat := [3, 3, 1, 2, 1, 1, 2, 2, 1, 1, 6]
def baseStart_8376738 : Nat := 118140960795 + 8376738 * 2 ^ 59
def prefixEnd_8376738 : Nat := 4983230072969 + 3 ^ 40 * 8376738 * 2
def baseEnd_8376738 : Nat := 4301292910782352207751089

theorem tailTrace_8376738 : CollatzResearch.WordTrace tailWord_8376738 prefixEnd_8376738 4301292910782352207751089 := by
  unfold tailWord_8376738
  simp only [CollatzResearch.WordTrace]
  refine ⟨76381183681629083449250717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203683156484344222531335245 76381183681629083449250717)
  ·
    refine ⟨28642943880610906293469019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76381183681629083449250717 28642943880610906293469019)
    ·
      refine ⟨42964415820916359440203529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28642943880610906293469019 42964415820916359440203529)
      ·
        refine ⟨32223311865687269580152647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42964415820916359440203529 32223311865687269580152647)
        ·
          refine ⟨48334967798530904370228971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32223311865687269580152647 48334967798530904370228971)
          ·
            refine ⟨72502451697796356555343457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48334967798530904370228971 72502451697796356555343457)
            ·
              refine ⟨54376838773347267416507593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72502451697796356555343457 54376838773347267416507593)
              ·
                refine ⟨40782629080010450562380695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54376838773347267416507593 40782629080010450562380695)
                ·
                  refine ⟨61173943620015675843571043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40782629080010450562380695 61173943620015675843571043)
                  ·
                    refine ⟨91760915430023513765356565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61173943620015675843571043 91760915430023513765356565)
                    ·
                      refine ⟨4301292910782352207751089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91760915430023513765356565 4301292910782352207751089)
                      ·
                        rfl

theorem cell23_8376738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_8376738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376738 prefixEnd_8376738 := by exact prefixLift 8376738
  have htrace : WordTrace (prefixWord ++ tailWord_8376738) baseStart_8376738 baseEnd_8376738 := by
    simpa [prefixWord, tailWord_8376738, baseEnd_8376738] using wordTrace_append hprefix tailTrace_8376738
  have hstable : (prefixWord ++ tailWord_8376738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376738).length < 2 ^ (prefixWord ++ tailWord_8376738).sum := by decide
  have hdescent : baseEnd_8376738 < baseStart_8376738 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376765 : List Nat := [1, 4, 1, 2, 2, 4, 2, 7]
def baseStart_8376765 : Nat := 118140960795 + 8376765 * 2 ^ 59
def prefixEnd_8376765 : Nat := 4983230072969 + 3 ^ 40 * 8376765 * 2
def baseEnd_8376765 : Nat := 159307658324445318596795

theorem tailTrace_8376765 : CollatzResearch.WordTrace tailWord_8376765 prefixEnd_8376765 159307658324445318596795 := by
  unfold tailWord_8376765
  simp only [CollatzResearch.WordTrace]
  refine ⟨305525719497418517408235749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203683812998279011605490499 305525719497418517408235749)
  ·
    refine ⟨57286072405765972014044203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305525719497418517408235749 57286072405765972014044203)
    ·
      refine ⟨85929108608648958021066305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57286072405765972014044203 85929108608648958021066305)
      ·
        refine ⟨64446831456486718515799729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85929108608648958021066305 64446831456486718515799729)
        ·
          refine ⟨48335123592365038886849797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64446831456486718515799729 48335123592365038886849797)
          ·
            refine ⟨9062835673568444791284337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48335123592365038886849797 9062835673568444791284337)
            ·
              refine ⟨6797126755176333593463253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9062835673568444791284337 6797126755176333593463253)
              ·
                refine ⟨159307658324445318596795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6797126755176333593463253 159307658324445318596795)
                ·
                  rfl

theorem cell23_8376765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 7].length) (baseStart_8376765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376765 prefixEnd_8376765 := by exact prefixLift 8376765
  have htrace : WordTrace (prefixWord ++ tailWord_8376765) baseStart_8376765 baseEnd_8376765 := by
    simpa [prefixWord, tailWord_8376765, baseEnd_8376765] using wordTrace_append hprefix tailTrace_8376765
  have hstable : (prefixWord ++ tailWord_8376765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376765).length < 2 ^ (prefixWord ++ tailWord_8376765).sum := by decide
  have hdescent : baseEnd_8376765 < baseStart_8376765 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376775 : List Nat := [1, 1, 4, 1, 1, 4, 1, 2, 4, 1, 3]
def baseStart_8376775 : Nat := 118140960795 + 8376775 * 2 ^ 59
def prefixEnd_8376775 : Nat := 4983230072969 + 3 ^ 40 * 8376775 * 2
def baseEnd_8376775 : Nat := 4301311909566568562988419

theorem tailTrace_8376775 : CollatzResearch.WordTrace tailWord_8376775 prefixEnd_8376775 4301311909566568562988419 := by
  unfold tailWord_8376775
  simp only [CollatzResearch.WordTrace]
  refine ⟨305526084227382289116099779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203684056151588192744066519 305526084227382289116099779)
  ·
    refine ⟨458289126341073433674149669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305526084227382289116099779 458289126341073433674149669)
    ·
      refine ⟨85929211188951268813903063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 458289126341073433674149669 85929211188951268813903063)
      ·
        refine ⟨128893816783426903220854595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85929211188951268813903063 128893816783426903220854595)
        ·
          refine ⟨193340725175140354831281893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128893816783426903220854595 193340725175140354831281893)
          ·
            refine ⟨36251385970338816530865355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193340725175140354831281893 36251385970338816530865355)
            ·
              refine ⟨54377078955508224796298033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36251385970338816530865355 54377078955508224796298033)
              ·
                refine ⟨40782809216631168597223525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54377078955508224796298033 40782809216631168597223525)
                ·
                  refine ⟨7646776728118344111979411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40782809216631168597223525 7646776728118344111979411)
                  ·
                    refine ⟨11470165092177516167969117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7646776728118344111979411 11470165092177516167969117)
                    ·
                      refine ⟨4301311909566568562988419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11470165092177516167969117 4301311909566568562988419)
                      ·
                        rfl

theorem cell23_8376775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_8376775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376775 prefixEnd_8376775 := by exact prefixLift 8376775
  have htrace : WordTrace (prefixWord ++ tailWord_8376775) baseStart_8376775 baseEnd_8376775 := by
    simpa [prefixWord, tailWord_8376775, baseEnd_8376775] using wordTrace_append hprefix tailTrace_8376775
  have hstable : (prefixWord ++ tailWord_8376775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376775).length < 2 ^ (prefixWord ++ tailWord_8376775).sum := by decide
  have hdescent : baseEnd_8376775 < baseStart_8376775 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376776 : List Nat := [2, 1, 3, 1, 3, 4, 1, 3, 1, 2, 2]
def baseStart_8376776 : Nat := 118140960795 + 8376776 * 2 ^ 59
def prefixEnd_8376776 : Nat := 4983230072969 + 3 ^ 40 * 8376776 * 2
def baseEnd_8376776 : Nat := 4301312423047223059075915

theorem tailTrace_8376776 : CollatzResearch.WordTrace tailWord_8376776 prefixEnd_8376776 4301312423047223059075915 := by
  unfold tailWord_8376776
  simp only [CollatzResearch.WordTrace]
  refine ⟨152763060350189333143443091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203684080466919110857924121 152763060350189333143443091)
  ·
    refine ⟨229144590525283999715164637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152763060350189333143443091 229144590525283999715164637)
    ·
      refine ⟨85929221446981499893186739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229144590525283999715164637 85929221446981499893186739)
      ·
        refine ⟨128893832170472249839780109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85929221446981499893186739 128893832170472249839780109)
        ·
          refine ⟨48335187063927093689917541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128893832170472249839780109 48335187063927093689917541)
          ·
            refine ⟨9062847574486330066859539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48335187063927093689917541 9062847574486330066859539)
            ·
              refine ⟨13594271361729495100289309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9062847574486330066859539 13594271361729495100289309)
              ·
                refine ⟨5097851760648560662608491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13594271361729495100289309 5097851760648560662608491)
                ·
                  refine ⟨7646777640972840993912737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5097851760648560662608491 7646777640972840993912737)
                  ·
                    refine ⟨5735083230729630745434553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7646777640972840993912737 5735083230729630745434553)
                    ·
                      refine ⟨4301312423047223059075915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5735083230729630745434553 4301312423047223059075915)
                      ·
                        rfl

theorem cell23_8376776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 3, 1, 2, 2].length) (baseStart_8376776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376776 prefixEnd_8376776 := by exact prefixLift 8376776
  have htrace : WordTrace (prefixWord ++ tailWord_8376776) baseStart_8376776 baseEnd_8376776 := by
    simpa [prefixWord, tailWord_8376776, baseEnd_8376776] using wordTrace_append hprefix tailTrace_8376776
  have hstable : (prefixWord ++ tailWord_8376776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376776).length < 2 ^ (prefixWord ++ tailWord_8376776).sum := by decide
  have hdescent : baseEnd_8376776 < baseStart_8376776 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376815 : List Nat := [1, 1, 2, 1, 4, 1, 1, 5, 1, 4, 2]
def baseStart_8376815 : Nat := 118140960795 + 8376815 * 2 ^ 59
def prefixEnd_8376815 : Nat := 4983230072969 + 3 ^ 40 * 8376815 * 2
def baseEnd_8376815 : Nat := 4301332448792748406488235

theorem tailTrace_8376815 : CollatzResearch.WordTrace tailWord_8376815 prefixEnd_8376815 4301332448792748406488235 := by
  unfold tailWord_8376815
  simp only [CollatzResearch.WordTrace]
  refine ⟨305527543147237375947555899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203685028764824917298370599 305527543147237375947555899)
  ·
    refine ⟨458291314720856063921333849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305527543147237375947555899 458291314720856063921333849)
    ·
      refine ⟨343718486040642047941000387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458291314720856063921333849 343718486040642047941000387)
      ·
        refine ⟨515577729060963071911500581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343718486040642047941000387 515577729060963071911500581)
        ·
          refine ⟨96670824198930575983406359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 515577729060963071911500581 96670824198930575983406359)
          ·
            refine ⟨145006236298395863975109539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96670824198930575983406359 145006236298395863975109539)
            ·
              refine ⟨217509354447593795962664309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145006236298395863975109539 217509354447593795962664309)
              ·
                refine ⟨20391501979461918371499779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 217509354447593795962664309 20391501979461918371499779)
                ·
                  refine ⟨30587252969192877557249669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20391501979461918371499779 30587252969192877557249669)
                  ·
                    refine ⟨5735109931723664541984313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30587252969192877557249669 5735109931723664541984313)
                    ·
                      refine ⟨4301332448792748406488235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5735109931723664541984313 4301332448792748406488235)
                      ·
                        rfl

theorem cell23_8376815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 4, 2].length) (baseStart_8376815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376815 prefixEnd_8376815 := by exact prefixLift 8376815
  have htrace : WordTrace (prefixWord ++ tailWord_8376815) baseStart_8376815 baseEnd_8376815 := by
    simpa [prefixWord, tailWord_8376815, baseEnd_8376815] using wordTrace_append hprefix tailTrace_8376815
  have hstable : (prefixWord ++ tailWord_8376815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376815).length < 2 ^ (prefixWord ++ tailWord_8376815).sum := by decide
  have hdescent : baseEnd_8376815 < baseStart_8376815 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376828 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 4, 2, 4]
def baseStart_8376828 : Nat := 118140960795 + 8376828 * 2 ^ 59
def prefixEnd_8376828 : Nat := 4983230072969 + 3 ^ 40 * 8376828 * 2
def baseEnd_8376828 : Nat := 4301339124041256855625675

theorem tailTrace_8376828 : CollatzResearch.WordTrace tailWord_8376828 prefixEnd_8376828 4301339124041256855625675 := by
  unfold tailWord_8376828
  simp only [CollatzResearch.WordTrace]
  refine ⟨152764008648095139583889569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203685344864126852778519425 152764008648095139583889569)
  ·
    refine ⟨114573006486071354687917177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152764008648095139583889569 114573006486071354687917177)
    ·
      refine ⟨85929754864553516015937883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114573006486071354687917177 85929754864553516015937883)
      ·
        refine ⟨128894632296830274023906825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85929754864553516015937883 128894632296830274023906825)
        ·
          refine ⟨96670974222622705517930119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128894632296830274023906825 96670974222622705517930119)
          ·
            refine ⟨145006461333934058276895179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96670974222622705517930119 145006461333934058276895179)
            ·
              refine ⟨217509692000901087415342769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145006461333934058276895179 217509692000901087415342769)
              ·
                refine ⟨163132269000675815561507077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217509692000901087415342769 163132269000675815561507077)
                ·
                  refine ⟨30587300437626715417782577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 163132269000675815561507077 30587300437626715417782577)
                  ·
                    refine ⟨22940475328220036563336933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30587300437626715417782577 22940475328220036563336933)
                    ·
                      refine ⟨4301339124041256855625675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22940475328220036563336933 4301339124041256855625675)
                      ·
                        rfl

theorem cell23_8376828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_8376828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376828 prefixEnd_8376828 := by exact prefixLift 8376828
  have htrace : WordTrace (prefixWord ++ tailWord_8376828) baseStart_8376828 baseEnd_8376828 := by
    simpa [prefixWord, tailWord_8376828, baseEnd_8376828] using wordTrace_append hprefix tailTrace_8376828
  have hstable : (prefixWord ++ tailWord_8376828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376828).length < 2 ^ (prefixWord ++ tailWord_8376828).sum := by decide
  have hdescent : baseEnd_8376828 < baseStart_8376828 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376836 : List Nat := [2, 3, 2, 3, 1, 2, 3, 1, 1, 3, 2]
def baseStart_8376836 : Nat := 118140960795 + 8376836 * 2 ^ 59
def prefixEnd_8376836 : Nat := 4983230072969 + 3 ^ 40 * 8376836 * 2
def baseEnd_8376836 : Nat := 4301343231886492824325639

theorem tailTrace_8376836 : CollatzResearch.WordTrace tailWord_8376836 prefixEnd_8376836 4301343231886492824325639 := by
  unfold tailWord_8376836
  simp only [CollatzResearch.WordTrace]
  refine ⟨152764154540080648267035181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203685539386774197689380241 152764154540080648267035181)
  ·
    refine ⟨57286557952530243100138193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152764154540080648267035181 57286557952530243100138193)
    ·
      refine ⟨42964918464397682325103645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57286557952530243100138193 42964918464397682325103645)
      ·
        refine ⟨16111844424149130871913867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42964918464397682325103645 16111844424149130871913867)
        ·
          refine ⟨24167766636223696307870801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16111844424149130871913867 24167766636223696307870801)
          ·
            refine ⟨18125824977167772230903101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24167766636223696307870801 18125824977167772230903101)
            ·
              refine ⟨6797184366437914586588663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18125824977167772230903101 6797184366437914586588663)
              ·
                refine ⟨10195776549656871879882995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6797184366437914586588663 10195776549656871879882995)
                ·
                  refine ⟨15293664824485307819824493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10195776549656871879882995 15293664824485307819824493)
                  ·
                    refine ⟨5735124309181990432434185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15293664824485307819824493 5735124309181990432434185)
                    ·
                      refine ⟨4301343231886492824325639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5735124309181990432434185 4301343231886492824325639)
                      ·
                        rfl

theorem cell23_8376836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_8376836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376836 prefixEnd_8376836 := by exact prefixLift 8376836
  have htrace : WordTrace (prefixWord ++ tailWord_8376836) baseStart_8376836 baseEnd_8376836 := by
    simpa [prefixWord, tailWord_8376836, baseEnd_8376836] using wordTrace_append hprefix tailTrace_8376836
  have hstable : (prefixWord ++ tailWord_8376836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376836).length < 2 ^ (prefixWord ++ tailWord_8376836).sum := by decide
  have hdescent : baseEnd_8376836 < baseStart_8376836 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376852 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_8376852 : Nat := 118140960795 + 8376852 * 2 ^ 59
def prefixEnd_8376852 : Nat := 4983230072969 + 3 ^ 40 * 8376852 * 2
def baseEnd_8376852 : Nat := 4301351447576964761725565

theorem tailTrace_8376852 : CollatzResearch.WordTrace tailWord_8376852 prefixEnd_8376852 4301351447576964761725565 := by
  unfold tailWord_8376852
  simp only [CollatzResearch.WordTrace]
  refine ⟨152764446324051665633326405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203685928432068887511101873 152764446324051665633326405)
  ·
    refine ⟨28643333685759687306248701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152764446324051665633326405 28643333685759687306248701)
    ·
      refine ⟨10741250132159882739843263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28643333685759687306248701 10741250132159882739843263)
      ·
        refine ⟨16111875198239824109764895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10741250132159882739843263 16111875198239824109764895)
        ·
          refine ⟨24167812797359736164647343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16111875198239824109764895 24167812797359736164647343)
          ·
            refine ⟨36251719196039604246971015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24167812797359736164647343 36251719196039604246971015)
            ·
              refine ⟨54377578794059406370456523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36251719196039604246971015 54377578794059406370456523)
              ·
                refine ⟨81566368191089109555684785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54377578794059406370456523 81566368191089109555684785)
                ·
                  refine ⟨61174776143316832166763589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81566368191089109555684785 61174776143316832166763589)
                  ·
                    refine ⟨11470270526871906031268173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61174776143316832166763589 11470270526871906031268173)
                    ·
                      refine ⟨4301351447576964761725565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11470270526871906031268173 4301351447576964761725565)
                      ·
                        rfl

theorem cell23_8376852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_8376852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376852 prefixEnd_8376852 := by exact prefixLift 8376852
  have htrace : WordTrace (prefixWord ++ tailWord_8376852) baseStart_8376852 baseEnd_8376852 := by
    simpa [prefixWord, tailWord_8376852, baseEnd_8376852] using wordTrace_append hprefix tailTrace_8376852
  have hstable : (prefixWord ++ tailWord_8376852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376852).length < 2 ^ (prefixWord ++ tailWord_8376852).sum := by decide
  have hdescent : baseEnd_8376852 < baseStart_8376852 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376865 : List Nat := [1, 2, 3, 2, 2, 1, 3, 1, 2, 3, 3]
def baseStart_8376865 : Nat := 118140960795 + 8376865 * 2 ^ 59
def prefixEnd_8376865 : Nat := 4983230072969 + 3 ^ 40 * 8376865 * 2
def baseEnd_8376865 : Nat := 4301358122825473210863005

theorem tailTrace_8376865 : CollatzResearch.WordTrace tailWord_8376865 prefixEnd_8376865 4301358122825473210863005 := by
  unfold tailWord_8376865
  simp only [CollatzResearch.WordTrace]
  refine ⟨305529366797056234486876049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203686244531370822991250699 305529366797056234486876049)
  ·
    refine ⟨229147025097792175865157037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305529366797056234486876049 229147025097792175865157037)
    ·
      refine ⟨85930134411672065949433889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229147025097792175865157037 85930134411672065949433889)
      ·
        refine ⟨64447600808754049462075417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85930134411672065949433889 64447600808754049462075417)
        ·
          refine ⟨48335700606565537096556563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64447600808754049462075417 48335700606565537096556563)
          ·
            refine ⟨72503550909848305644834845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48335700606565537096556563 72503550909848305644834845)
            ·
              refine ⟨27188831591193114616813067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72503550909848305644834845 27188831591193114616813067)
              ·
                refine ⟨40783247386789671925219601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27188831591193114616813067 40783247386789671925219601)
                ·
                  refine ⟨30587435540092253943914701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40783247386789671925219601 30587435540092253943914701)
                  ·
                    refine ⟨11470288327534595228968013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30587435540092253943914701 11470288327534595228968013)
                    ·
                      refine ⟨4301358122825473210863005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11470288327534595228968013 4301358122825473210863005)
                      ·
                        rfl

theorem cell23_8376865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_8376865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376865 prefixEnd_8376865 := by exact prefixLift 8376865
  have htrace : WordTrace (prefixWord ++ tailWord_8376865) baseStart_8376865 baseEnd_8376865 := by
    simpa [prefixWord, tailWord_8376865, baseEnd_8376865] using wordTrace_append hprefix tailTrace_8376865
  have hstable : (prefixWord ++ tailWord_8376865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376865).length < 2 ^ (prefixWord ++ tailWord_8376865).sum := by decide
  have hdescent : baseEnd_8376865 < baseStart_8376865 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376942 : List Nat := [4, 1, 2, 2, 2, 1, 2, 1, 1, 4, 3]
def baseStart_8376942 : Nat := 118140960795 + 8376942 * 2 ^ 59
def prefixEnd_8376942 : Nat := 4983230072969 + 3 ^ 40 * 8376942 * 2
def baseEnd_8376942 : Nat := 4301397660835869409600151

theorem tailTrace_8376942 : CollatzResearch.WordTrace tailWord_8376942 prefixEnd_8376942 4301397660835869409600151 := by
  unfold tailWord_8376942
  simp only [CollatzResearch.WordTrace]
  refine ⟨38191521902222159579678635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203688116811851517758286053 38191521902222159579678635)
  ·
    refine ⟨57287282853333239369517953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38191521902222159579678635 57287282853333239369517953)
    ·
      refine ⟨42965462139999929527138465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57287282853333239369517953 42965462139999929527138465)
      ·
        refine ⟨32224096604999947145353849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42965462139999929527138465 32224096604999947145353849)
        ·
          refine ⟨24168072453749960359015387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32224096604999947145353849 24168072453749960359015387)
          ·
            refine ⟨36252108680624940538523081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24168072453749960359015387 36252108680624940538523081)
            ·
              refine ⟨27189081510468705403892311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36252108680624940538523081 27189081510468705403892311)
              ·
                refine ⟨40783622265703058105838467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27189081510468705403892311 40783622265703058105838467)
                ·
                  refine ⟨61175433398554587158757701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40783622265703058105838467 61175433398554587158757701)
                  ·
                    refine ⟨11470393762228985092267069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61175433398554587158757701 11470393762228985092267069)
                    ·
                      refine ⟨4301397660835869409600151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11470393762228985092267069 4301397660835869409600151)
                      ·
                        rfl

theorem cell23_8376942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_8376942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376942 prefixEnd_8376942 := by exact prefixLift 8376942
  have htrace : WordTrace (prefixWord ++ tailWord_8376942) baseStart_8376942 baseEnd_8376942 := by
    simpa [prefixWord, tailWord_8376942, baseEnd_8376942] using wordTrace_append hprefix tailTrace_8376942
  have hstable : (prefixWord ++ tailWord_8376942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376942).length < 2 ^ (prefixWord ++ tailWord_8376942).sum := by decide
  have hdescent : baseEnd_8376942 < baseStart_8376942 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376972 : List Nat := [2, 2, 1, 2, 1, 1, 2, 5, 3, 1, 3]
def baseStart_8376972 : Nat := 118140960795 + 8376972 * 2 ^ 59
def prefixEnd_8376972 : Nat := 4983230072969 + 3 ^ 40 * 8376972 * 2
def baseEnd_8376972 : Nat := 4301413065255504292225013

theorem tailTrace_8376972 : CollatzResearch.WordTrace tailWord_8376972 prefixEnd_8376972 4301413065255504292225013 := by
  unfold tailWord_8376972
  simp only [CollatzResearch.WordTrace]
  refine ⟨152766634703834295880510585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203688846271779061174014113 152766634703834295880510585)
  ·
    refine ⟨114574976027875721910382939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152766634703834295880510585 114574976027875721910382939)
    ·
      refine ⟨171862464041813582865574409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114574976027875721910382939 171862464041813582865574409)
      ·
        refine ⟨128896848031360187149180807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171862464041813582865574409 128896848031360187149180807)
        ·
          refine ⟨193345272047040280723771211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128896848031360187149180807 193345272047040280723771211)
          ·
            refine ⟨290017908070560421085656817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193345272047040280723771211 290017908070560421085656817)
            ·
              refine ⟨217513431052920315814242613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290017908070560421085656817 217513431052920315814242613)
              ·
                refine ⟨20391884161211279607585245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 217513431052920315814242613 20391884161211279607585245)
                ·
                  refine ⟨7646956560454229852844467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20391884161211279607585245 7646956560454229852844467)
                  ·
                    refine ⟨11470434840681344779266701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7646956560454229852844467 11470434840681344779266701)
                    ·
                      refine ⟨4301413065255504292225013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11470434840681344779266701 4301413065255504292225013)
                      ·
                        rfl

theorem cell23_8376972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_8376972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376972 prefixEnd_8376972 := by exact prefixLift 8376972
  have htrace : WordTrace (prefixWord ++ tailWord_8376972) baseStart_8376972 baseEnd_8376972 := by
    simpa [prefixWord, tailWord_8376972, baseEnd_8376972] using wordTrace_append hprefix tailTrace_8376972
  have hstable : (prefixWord ++ tailWord_8376972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376972).length < 2 ^ (prefixWord ++ tailWord_8376972).sum := by decide
  have hdescent : baseEnd_8376972 < baseStart_8376972 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376992 : List Nat := [2, 1, 1, 4, 4, 1, 1, 1, 3, 5]
def baseStart_8376992 : Nat := 118140960795 + 8376992 * 2 ^ 59
def prefixEnd_8376992 : Nat := 4983230072969 + 3 ^ 40 * 8376992 * 2
def baseEnd_8376992 : Nat := 1433807778289531404658307

theorem tailTrace_8376992 : CollatzResearch.WordTrace tailWord_8376992 prefixEnd_8376992 1433807778289531404658307 := by
  unfold tailWord_8376992
  simp only [CollatzResearch.WordTrace]
  refine ⟨152766999433798067588374615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203689332578397423451166153 152766999433798067588374615)
  ·
    refine ⟨229150499150697101382561923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152766999433798067588374615 229150499150697101382561923)
    ·
      refine ⟨343725748726045652073842885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229150499150697101382561923 343725748726045652073842885)
      ·
        refine ⟨64448577886133559763845541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 343725748726045652073842885 64448577886133559763845541)
        ·
          refine ⟨12084108353650042455721039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64448577886133559763845541 12084108353650042455721039)
          ·
            refine ⟨18126162530475063683581559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12084108353650042455721039 18126162530475063683581559)
            ·
              refine ⟨27189243795712595525372339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18126162530475063683581559 27189243795712595525372339)
              ·
                refine ⟨40783865693568893288058509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27189243795712595525372339 40783865693568893288058509)
                ·
                  refine ⟨15293949635088334983021941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40783865693568893288058509 15293949635088334983021941)
                  ·
                    refine ⟨1433807778289531404658307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15293949635088334983021941 1433807778289531404658307)
                    ·
                      rfl

theorem cell23_8376992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 3, 5].length) (baseStart_8376992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376992 prefixEnd_8376992 := by exact prefixLift 8376992
  have htrace : WordTrace (prefixWord ++ tailWord_8376992) baseStart_8376992 baseEnd_8376992 := by
    simpa [prefixWord, tailWord_8376992, baseEnd_8376992] using wordTrace_append hprefix tailTrace_8376992
  have hstable : (prefixWord ++ tailWord_8376992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376992).length < 2 ^ (prefixWord ++ tailWord_8376992).sum := by decide
  have hdescent : baseEnd_8376992 < baseStart_8376992 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377023 : List Nat := [1, 1, 2, 2, 2, 6, 2, 2, 1, 1, 3]
def baseStart_8377023 : Nat := 118140960795 + 8377023 * 2 ^ 59
def prefixEnd_8377023 : Nat := 4983230072969 + 3 ^ 40 * 8377023 * 2
def baseEnd_8377023 : Nat := 4301439252768883592687279

theorem tailTrace_8377023 : CollatzResearch.WordTrace tailWord_8377023 prefixEnd_8377023 4301439252768883592687279 := by
  unfold tailWord_8377023
  simp only [CollatzResearch.WordTrace]
  refine ⟨305535129530483827471127723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203690086353655884980751815 305535129530483827471127723)
  ·
    refine ⟨458302694295725741206691585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305535129530483827471127723 458302694295725741206691585)
    ·
      refine ⟨343727020721794305905018689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458302694295725741206691585 343727020721794305905018689)
      ·
        refine ⟨257795265541345729428764017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343727020721794305905018689 257795265541345729428764017)
        ·
          refine ⟨193346449156009297071573013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257795265541345729428764017 193346449156009297071573013)
          ·
            refine ⟨9063114804187935800229985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 193346449156009297071573013 9063114804187935800229985)
            ·
              refine ⟨6797336103140951850172489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9063114804187935800229985 6797336103140951850172489)
              ·
                refine ⟨5098002077355713887629367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6797336103140951850172489 5098002077355713887629367)
                ·
                  refine ⟨7647003116033570831444051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5098002077355713887629367 7647003116033570831444051)
                  ·
                    refine ⟨11470504674050356247166077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7647003116033570831444051 11470504674050356247166077)
                    ·
                      refine ⟨4301439252768883592687279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11470504674050356247166077 4301439252768883592687279)
                      ·
                        rfl

theorem cell23_8377023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 2, 1, 1, 3].length) (baseStart_8377023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377023 prefixEnd_8377023 := by exact prefixLift 8377023
  have htrace : WordTrace (prefixWord ++ tailWord_8377023) baseStart_8377023 baseEnd_8377023 := by
    simpa [prefixWord, tailWord_8377023, baseEnd_8377023] using wordTrace_append hprefix tailTrace_8377023
  have hstable : (prefixWord ++ tailWord_8377023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377023).length < 2 ^ (prefixWord ++ tailWord_8377023).sum := by decide
  have hdescent : baseEnd_8377023 < baseStart_8377023 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377032 : List Nat := [2, 1, 3, 1, 2, 3, 1, 2, 3, 2, 3]
def baseStart_8377032 : Nat := 118140960795 + 8377032 * 2 ^ 59
def prefixEnd_8377032 : Nat := 4983230072969 + 3 ^ 40 * 8377032 * 2
def baseEnd_8377032 : Nat := 4301443874094774057474737

theorem tailTrace_8377032 : CollatzResearch.WordTrace tailWord_8377032 prefixEnd_8377032 4301443874094774057474737 := by
  unfold tailWord_8377032
  simp only [CollatzResearch.WordTrace]
  refine ⟨152767728893725611004102675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203690305191634148005470233 152767728893725611004102675)
  ·
    refine ⟨229151593340588416506154013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152767728893725611004102675 229151593340588416506154013)
    ·
      refine ⟨85931847502720656189807755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229151593340588416506154013 85931847502720656189807755)
      ·
        refine ⟨128897771254080984284711633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85931847502720656189807755 128897771254080984284711633)
        ·
          refine ⟨96673328440560738213533725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128897771254080984284711633 96673328440560738213533725)
          ·
            refine ⟨36252498165210276830075147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96673328440560738213533725 36252498165210276830075147)
            ·
              refine ⟨54378747247815415245112721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36252498165210276830075147 54378747247815415245112721)
              ·
                refine ⟨40784060435861561433834541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54378747247815415245112721 40784060435861561433834541)
                ·
                  refine ⟨15294022663448085537687953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40784060435861561433834541 15294022663448085537687953)
                  ·
                    refine ⟨11470516997586064153265965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15294022663448085537687953 11470516997586064153265965)
                    ·
                      refine ⟨4301443874094774057474737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11470516997586064153265965 4301443874094774057474737)
                      ·
                        rfl

theorem cell23_8377032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_8377032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377032 prefixEnd_8377032 := by exact prefixLift 8377032
  have htrace : WordTrace (prefixWord ++ tailWord_8377032) baseStart_8377032 baseEnd_8377032 := by
    simpa [prefixWord, tailWord_8377032, baseEnd_8377032] using wordTrace_append hprefix tailTrace_8377032
  have hstable : (prefixWord ++ tailWord_8377032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377032).length < 2 ^ (prefixWord ++ tailWord_8377032).sum := by decide
  have hdescent : baseEnd_8377032 < baseStart_8377032 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377122 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5]
def baseStart_8377122 : Nat := 118140960795 + 8377122 * 2 ^ 59
def prefixEnd_8377122 : Nat := 4983230072969 + 3 ^ 40 * 8377122 * 2
def baseEnd_8377122 : Nat := 4301490087353678705349323

theorem tailTrace_8377122 : CollatzResearch.WordTrace tailWord_8377122 prefixEnd_8377122 4301490087353678705349323 := by
  unfold tailWord_8377122
  simp only [CollatzResearch.WordTrace]
  refine ⟨76384685089281291844745405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203692493571416778252654413 76384685089281291844745405)
  ·
    refine ⟨28644256908480484441779527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76384685089281291844745405 28644256908480484441779527)
    ·
      refine ⟨42966385362720726662669291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28644256908480484441779527 42966385362720726662669291)
      ·
        refine ⟨64449578044081089994003937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42966385362720726662669291 64449578044081089994003937)
        ·
          refine ⟨48337183533060817495502953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64449578044081089994003937 48337183533060817495502953)
          ·
            refine ⟨36252887649795613121627215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48337183533060817495502953 36252887649795613121627215)
            ·
              refine ⟨54379331474693419682440823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36252887649795613121627215 54379331474693419682440823)
              ·
                refine ⟨81568997212040129523661235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54379331474693419682440823 81568997212040129523661235)
                ·
                  refine ⟨122353495818060194285491853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81568997212040129523661235 122353495818060194285491853)
                  ·
                    refine ⟨45882560931772572857059445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 122353495818060194285491853 45882560931772572857059445)
                    ·
                      refine ⟨4301490087353678705349323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45882560931772572857059445 4301490087353678705349323)
                      ·
                        rfl

theorem cell23_8377122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_8377122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377122 prefixEnd_8377122 := by exact prefixLift 8377122
  have htrace : WordTrace (prefixWord ++ tailWord_8377122) baseStart_8377122 baseEnd_8377122 := by
    simpa [prefixWord, tailWord_8377122, baseEnd_8377122] using wordTrace_append hprefix tailTrace_8377122
  have hstable : (prefixWord ++ tailWord_8377122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377122).length < 2 ^ (prefixWord ++ tailWord_8377122).sum := by decide
  have hdescent : baseEnd_8377122 < baseStart_8377122 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377152 : List Nat := [2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 3]
def baseStart_8377152 : Nat := 118140960795 + 8377152 * 2 ^ 59
def prefixEnd_8377152 : Nat := 4983230072969 + 3 ^ 40 * 8377152 * 2
def baseEnd_8377152 : Nat := 4301505491773313587974185

theorem tailTrace_8377152 : CollatzResearch.WordTrace tailWord_8377152 prefixEnd_8377152 4301505491773313587974185 := by
  unfold tailWord_8377152
  simp only [CollatzResearch.WordTrace]
  refine ⟨152769917273508241251286855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203693223031344321668382473 152769917273508241251286855)
  ·
    refine ⟨229154875910262361876930283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152769917273508241251286855 229154875910262361876930283)
    ·
      refine ⟨343732313865393542815395425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229154875910262361876930283 343732313865393542815395425)
      ·
        refine ⟨257799235399045157111546569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343732313865393542815395425 257799235399045157111546569)
        ·
          refine ⟨193349426549283867833659927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257799235399045157111546569 193349426549283867833659927)
          ·
            refine ⟨290024139823925801750489891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193349426549283867833659927 290024139823925801750489891)
            ·
              refine ⟨435036209735888702625734837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290024139823925801750489891 435036209735888702625734837)
              ·
                refine ⟨40784644662739565871162641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 435036209735888702625734837 40784644662739565871162641)
                ·
                  refine ⟨30588483497054674403371981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40784644662739565871162641 30588483497054674403371981)
                  ·
                    refine ⟨11470681311395502901264493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30588483497054674403371981 11470681311395502901264493)
                    ·
                      refine ⟨4301505491773313587974185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11470681311395502901264493 4301505491773313587974185)
                      ·
                        rfl

theorem cell23_8377152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 3].length) (baseStart_8377152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377152 prefixEnd_8377152 := by exact prefixLift 8377152
  have htrace : WordTrace (prefixWord ++ tailWord_8377152) baseStart_8377152 baseEnd_8377152 := by
    simpa [prefixWord, tailWord_8377152, baseEnd_8377152] using wordTrace_append hprefix tailTrace_8377152
  have hstable : (prefixWord ++ tailWord_8377152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377152).length < 2 ^ (prefixWord ++ tailWord_8377152).sum := by decide
  have hdescent : baseEnd_8377152 < baseStart_8377152 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377209 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 1, 6, 2]
def baseStart_8377209 : Nat := 118140960795 + 8377209 * 2 ^ 59
def prefixEnd_8377209 : Nat := 4983230072969 + 3 ^ 40 * 8377209 * 2
def baseEnd_8377209 : Nat := 4301534760170619864961423

theorem tailTrace_8377209 : CollatzResearch.WordTrace tailWord_8377209 prefixEnd_8377209 4301534760170619864961423 := by
  unfold tailWord_8377209
  simp only [CollatzResearch.WordTrace]
  refine ⟨305541913507809981237398681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203694609005206654158265787 305541913507809981237398681)
  ·
    refine ⟨229156435130857485928049011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305541913507809981237398681 229156435130857485928049011)
    ·
      refine ⟨343734652696286228892073517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229156435130857485928049011 343734652696286228892073517)
      ·
        refine ⟨128900494761107335834527569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343734652696286228892073517 128900494761107335834527569)
        ·
          refine ⟨96675371070830501875895677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128900494761107335834527569 96675371070830501875895677)
          ·
            refine ⟨36253264151561438203460879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96675371070830501875895677 36253264151561438203460879)
            ·
              refine ⟨54379896227342157305191319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36253264151561438203460879 54379896227342157305191319)
              ·
                refine ⟨81569844341013235957786979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54379896227342157305191319 81569844341013235957786979)
                ·
                  refine ⟨122354766511519853936680469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81569844341013235957786979 122354766511519853936680469)
                  ·
                    refine ⟨5735379680227493153281897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 122354766511519853936680469 5735379680227493153281897)
                    ·
                      refine ⟨4301534760170619864961423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5735379680227493153281897 4301534760170619864961423)
                      ·
                        rfl

theorem cell23_8377209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 6, 2].length) (baseStart_8377209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377209 prefixEnd_8377209 := by exact prefixLift 8377209
  have htrace : WordTrace (prefixWord ++ tailWord_8377209) baseStart_8377209 baseEnd_8377209 := by
    simpa [prefixWord, tailWord_8377209, baseEnd_8377209] using wordTrace_append hprefix tailTrace_8377209
  have hstable : (prefixWord ++ tailWord_8377209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377209).length < 2 ^ (prefixWord ++ tailWord_8377209).sum := by decide
  have hdescent : baseEnd_8377209 < baseStart_8377209 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377219 : List Nat := [1, 1, 1, 3, 4, 1, 3, 2, 3, 4]
def baseStart_8377219 : Nat := 118140960795 + 8377219 * 2 ^ 59
def prefixEnd_8377219 : Nat := 4983230072969 + 3 ^ 40 * 8377219 * 2
def baseEnd_8377219 : Nat := 1433846631659054941945459

theorem tailTrace_8377219 : CollatzResearch.WordTrace tailWord_8377219 prefixEnd_8377219 1433846631659054941945459 := by
  unfold tailWord_8377219
  simp only [CollatzResearch.WordTrace]
  refine ⟨305542278237773752945262711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203694852158515835296841807 305542278237773752945262711)
  ·
    refine ⟨458313417356660629417894067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305542278237773752945262711 458313417356660629417894067)
    ·
      refine ⟨687470126034990944126841101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458313417356660629417894067 687470126034990944126841101)
      ·
        refine ⟨257801297263121604047565413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 687470126034990944126841101 257801297263121604047565413)
        ·
          refine ⟨48337743236835300758918515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257801297263121604047565413 48337743236835300758918515)
          ·
            refine ⟨72506614855252951138377773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48337743236835300758918515 72506614855252951138377773)
            ·
              refine ⟨27189980570719856676891665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72506614855252951138377773 27189980570719856676891665)
              ·
                refine ⟨20392485428039892507668749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27189980570719856676891665 20392485428039892507668749)
                ·
                  refine ⟨7647182035514959690375781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20392485428039892507668749 7647182035514959690375781)
                  ·
                    refine ⟨1433846631659054941945459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7647182035514959690375781 1433846631659054941945459)
                    ·
                      rfl

theorem cell23_8377219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 3, 4].length) (baseStart_8377219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377219 prefixEnd_8377219 := by exact prefixLift 8377219
  have htrace : WordTrace (prefixWord ++ tailWord_8377219) baseStart_8377219 baseEnd_8377219 := by
    simpa [prefixWord, tailWord_8377219, baseEnd_8377219] using wordTrace_append hprefix tailTrace_8377219
  have hstable : (prefixWord ++ tailWord_8377219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377219).length < 2 ^ (prefixWord ++ tailWord_8377219).sum := by decide
  have hdescent : baseEnd_8377219 < baseStart_8377219 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377226 : List Nat := [3, 1, 2, 4, 1, 1, 3, 1, 2, 1, 4]
def baseStart_8377226 : Nat := 118140960795 + 8377226 * 2 ^ 59
def prefixEnd_8377226 : Nat := 4983230072969 + 3 ^ 40 * 8377226 * 2
def baseEnd_8377226 : Nat := 4301543489341746298448845

theorem tailTrace_8377226 : CollatzResearch.WordTrace tailWord_8377226 prefixEnd_8377226 4301543489341746298448845 := by
  unfold tailWord_8377226
  simp only [CollatzResearch.WordTrace]
  refine ⟨76385633387187098285191883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203695022365832262093845021 76385633387187098285191883)
  ·
    refine ⟨114578450080780647427787825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76385633387187098285191883 114578450080780647427787825)
    ·
      refine ⟨85933837560585485570840869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114578450080780647427787825 85933837560585485570840869)
      ·
        refine ⟨16112594542609778544532663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85933837560585485570840869 16112594542609778544532663)
        ·
          refine ⟨24168891813914667816798995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16112594542609778544532663 24168891813914667816798995)
          ·
            refine ⟨36253337720872001725198493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24168891813914667816798995 36253337720872001725198493)
            ·
              refine ⟨13595001645327000646949435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36253337720872001725198493 13595001645327000646949435)
              ·
                refine ⟨20392502467990500970424153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13595001645327000646949435 20392502467990500970424153)
                ·
                  refine ⟨15294376850992875727818115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20392502467990500970424153 15294376850992875727818115)
                  ·
                    refine ⟨22941565276489313591727173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15294376850992875727818115 22941565276489313591727173)
                    ·
                      refine ⟨4301543489341746298448845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22941565276489313591727173 4301543489341746298448845)
                      ·
                        rfl

theorem cell23_8377226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_8377226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377226 prefixEnd_8377226 := by exact prefixLift 8377226
  have htrace : WordTrace (prefixWord ++ tailWord_8377226) baseStart_8377226 baseEnd_8377226 := by
    simpa [prefixWord, tailWord_8377226, baseEnd_8377226] using wordTrace_append hprefix tailTrace_8377226
  have hstable : (prefixWord ++ tailWord_8377226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377226).length < 2 ^ (prefixWord ++ tailWord_8377226).sum := by decide
  have hdescent : baseEnd_8377226 < baseStart_8377226 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377249 : List Nat := [1, 2, 3, 4, 1, 2, 1, 1, 8]
def baseStart_8377249 : Nat := 118140960795 + 8377249 * 2 ^ 59
def prefixEnd_8377249 : Nat := 4983230072969 + 3 ^ 40 * 8377249 * 2
def baseEnd_8377249 : Nat := 477950588821866634273471

theorem tailTrace_8377249 : CollatzResearch.WordTrace tailWord_8377249 prefixEnd_8377249 477950588821866634273471 := by
  unfold tailWord_8377249
  simp only [CollatzResearch.WordTrace]
  refine ⟨305543372427665068068854801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203695581618443378712569867 305543372427665068068854801)
  ·
    refine ⟨229157529320748801051641101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305543372427665068068854801 229157529320748801051641101)
    ·
      refine ⟨85934073495280800394365413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229157529320748801051641101 85934073495280800394365413)
      ·
        refine ⟨16112638780365150073943515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85934073495280800394365413 16112638780365150073943515)
        ·
          refine ⟨24168958170547725110915273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16112638780365150073943515 24168958170547725110915273)
          ·
            refine ⟨18126718627910793833186455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24168958170547725110915273 18126718627910793833186455)
            ·
              refine ⟨27190077941866190749779683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18126718627910793833186455 27190077941866190749779683)
              ·
                refine ⟨40785116912799286124669525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27190077941866190749779683 40785116912799286124669525)
                ·
                  refine ⟨477950588821866634273471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40785116912799286124669525 477950588821866634273471)
                  ·
                    rfl

theorem cell23_8377249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 8].length) (baseStart_8377249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377249 prefixEnd_8377249 := by exact prefixLift 8377249
  have htrace : WordTrace (prefixWord ++ tailWord_8377249) baseStart_8377249 baseEnd_8377249 := by
    simpa [prefixWord, tailWord_8377249, baseEnd_8377249] using wordTrace_append hprefix tailTrace_8377249
  have hstable : (prefixWord ++ tailWord_8377249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377249).length < 2 ^ (prefixWord ++ tailWord_8377249).sum := by decide
  have hdescent : baseEnd_8377249 < baseStart_8377249 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377252 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 1, 1, 8]
def baseStart_8377252 : Nat := 118140960795 + 8377252 * 2 ^ 59
def prefixEnd_8377252 : Nat := 4983230072969 + 3 ^ 40 * 8377252 * 2
def baseEnd_8377252 : Nat := 4301556839838763196723725

theorem tailTrace_8377252 : CollatzResearch.WordTrace tailWord_8377252 prefixEnd_8377252 4301556839838763196723725 := by
  unfold tailWord_8377252
  simp only [CollatzResearch.WordTrace]
  refine ⟨152771740923327099790607005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203695654564436133054142673 152771740923327099790607005)
  ·
    refine ⟨57289402846247662421477627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152771740923327099790607005 57289402846247662421477627)
    ·
      refine ⟨85934104269371493632216441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57289402846247662421477627 85934104269371493632216441)
      ·
        refine ⟨64450578202028620224162331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85934104269371493632216441 64450578202028620224162331)
        ·
          refine ⟨96675867303042930336243497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64450578202028620224162331 96675867303042930336243497)
          ·
            refine ⟨72506900477282197752182623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96675867303042930336243497 72506900477282197752182623)
            ·
              refine ⟨108760350715923296628273935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72506900477282197752182623 108760350715923296628273935)
              ·
                refine ⟨163140526073884944942410903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108760350715923296628273935 163140526073884944942410903)
                ·
                  refine ⟨244710789110827417413616355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163140526073884944942410903 244710789110827417413616355)
                  ·
                    refine ⟨367066183666241126120424533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 244710789110827417413616355 367066183666241126120424533)
                    ·
                      refine ⟨4301556839838763196723725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 367066183666241126120424533 4301556839838763196723725)
                      ·
                        rfl

theorem cell23_8377252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_8377252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377252 prefixEnd_8377252 := by exact prefixLift 8377252
  have htrace : WordTrace (prefixWord ++ tailWord_8377252) baseStart_8377252 baseEnd_8377252 := by
    simpa [prefixWord, tailWord_8377252, baseEnd_8377252] using wordTrace_append hprefix tailTrace_8377252
  have hstable : (prefixWord ++ tailWord_8377252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377252).length < 2 ^ (prefixWord ++ tailWord_8377252).sum := by decide
  have hdescent : baseEnd_8377252 < baseStart_8377252 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377259 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 7, 1, 3]
def baseStart_8377259 : Nat := 118140960795 + 8377259 * 2 ^ 59
def prefixEnd_8377259 : Nat := 4983230072969 + 3 ^ 40 * 8377259 * 2
def baseEnd_8377259 : Nat := 4301560434203344669336193

theorem tailTrace_8377259 : CollatzResearch.WordTrace tailWord_8377259 prefixEnd_8377259 4301560434203344669336193 := by
  unfold tailWord_8377259
  simp only [CollatzResearch.WordTrace]
  refine ⟨305543737157628839776718831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203695824771752559851145887 305543737157628839776718831)
  ·
    refine ⟨458315605736443259665078247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305543737157628839776718831 458315605736443259665078247)
    ·
      refine ⟨687473408604664889497617371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458315605736443259665078247 687473408604664889497617371)
      ·
        refine ⟨1031210112906997334246426057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687473408604664889497617371 1031210112906997334246426057)
        ·
          refine ⟨773407584680248000684819543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1031210112906997334246426057 773407584680248000684819543)
          ·
            refine ⟨1160111377020372001027229315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773407584680248000684819543 1160111377020372001027229315)
            ·
              refine ⟨1740167065530558001540843973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1160111377020372001027229315 1740167065530558001540843973)
              ·
                refine ⟨326281324786979625288908245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1740167065530558001540843973 326281324786979625288908245)
                ·
                  refine ⟨7647218549694834967708787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 326281324786979625288908245 7647218549694834967708787)
                  ·
                    refine ⟨11470827824542252451563181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7647218549694834967708787 11470827824542252451563181)
                    ·
                      refine ⟨4301560434203344669336193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11470827824542252451563181 4301560434203344669336193)
                      ·
                        rfl

theorem cell23_8377259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 7, 1, 3].length) (baseStart_8377259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377259 prefixEnd_8377259 := by exact prefixLift 8377259
  have htrace : WordTrace (prefixWord ++ tailWord_8377259) baseStart_8377259 baseEnd_8377259 := by
    simpa [prefixWord, tailWord_8377259, baseEnd_8377259] using wordTrace_append hprefix tailTrace_8377259
  have hstable : (prefixWord ++ tailWord_8377259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377259).length < 2 ^ (prefixWord ++ tailWord_8377259).sum := by decide
  have hdescent : baseEnd_8377259 < baseStart_8377259 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377329 : List Nat := [1, 2, 2, 2, 4, 1, 2, 1, 1, 1, 6]
def baseStart_8377329 : Nat := 118140960795 + 8377329 * 2 ^ 59
def prefixEnd_8377329 : Nat := 4983230072969 + 3 ^ 40 * 8377329 * 2
def baseEnd_8377329 : Nat := 4301596377849159395460871

theorem tailTrace_8377329 : CollatzResearch.WordTrace tailWord_8377329 prefixEnd_8377329 4301596377849159395460871 := by
  unfold tailWord_8377329
  simp only [CollatzResearch.WordTrace]
  refine ⟨305546290267375241731767041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203697526844916827821178027 305546290267375241731767041)
  ·
    refine ⟨229159717700531431298825281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305546290267375241731767041 229159717700531431298825281)
    ·
      refine ⟨171869788275398573474118961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229159717700531431298825281 171869788275398573474118961)
      ·
        refine ⟨128902341206548930105589221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171869788275398573474118961 128902341206548930105589221)
        ·
          refine ⟨24169188976227924394797979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128902341206548930105589221 24169188976227924394797979)
          ·
            refine ⟨36253783464341886592196969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24169188976227924394797979 36253783464341886592196969)
            ·
              refine ⟨27190337598256414944147727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36253783464341886592196969 27190337598256414944147727)
              ·
                refine ⟨40785506397384622416221591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27190337598256414944147727 40785506397384622416221591)
                ·
                  refine ⟨61178259596076933624332387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40785506397384622416221591 61178259596076933624332387)
                  ·
                    refine ⟨91767389394115400436498581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61178259596076933624332387 91767389394115400436498581)
                    ·
                      refine ⟨4301596377849159395460871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91767389394115400436498581 4301596377849159395460871)
                      ·
                        rfl

theorem cell23_8377329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_8377329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377329 prefixEnd_8377329 := by exact prefixLift 8377329
  have htrace : WordTrace (prefixWord ++ tailWord_8377329) baseStart_8377329 baseEnd_8377329 := by
    simpa [prefixWord, tailWord_8377329, baseEnd_8377329] using wordTrace_append hprefix tailTrace_8377329
  have hstable : (prefixWord ++ tailWord_8377329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377329).length < 2 ^ (prefixWord ++ tailWord_8377329).sum := by decide
  have hdescent : baseEnd_8377329 < baseStart_8377329 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377330 : List Nat := [3, 2, 1, 5, 1, 2, 1, 2, 1, 5]
def baseStart_8377330 : Nat := 118140960795 + 8377330 * 2 ^ 59
def prefixEnd_8377330 : Nat := 4983230072969 + 3 ^ 40 * 8377330 * 2
def baseEnd_8377330 : Nat := 1433865630443271297182789

theorem tailTrace_8377330 : CollatzResearch.WordTrace tailWord_8377330 prefixEnd_8377330 1433865630443271297182789 := by
  unfold tailWord_8377330
  simp only [CollatzResearch.WordTrace]
  refine ⟨76386581685092904725638361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203697551160247745935035629 76386581685092904725638361)
  ·
    refine ⟨57289936263819678544228771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76386581685092904725638361 57289936263819678544228771)
    ·
      refine ⟨85934904395729517816343157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57289936263819678544228771 85934904395729517816343157)
      ·
        refine ⟨8056397287099642295282171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85934904395729517816343157 8056397287099642295282171)
        ·
          refine ⟨12084595930649463442923257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8056397287099642295282171 12084595930649463442923257)
          ·
            refine ⟨9063446947987097582192443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12084595930649463442923257 9063446947987097582192443)
            ·
              refine ⟨13595170421980646373288665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9063446947987097582192443 13595170421980646373288665)
              ·
                refine ⟨10196377816485484779966499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13595170421980646373288665 10196377816485484779966499)
                ·
                  refine ⟨15294566724728227169949749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10196377816485484779966499 15294566724728227169949749)
                  ·
                    refine ⟨1433865630443271297182789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15294566724728227169949749 1433865630443271297182789)
                    ·
                      rfl

theorem cell23_8377330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_8377330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377330 prefixEnd_8377330 := by exact prefixLift 8377330
  have htrace : WordTrace (prefixWord ++ tailWord_8377330) baseStart_8377330 baseEnd_8377330 := by
    simpa [prefixWord, tailWord_8377330, baseEnd_8377330] using wordTrace_append hprefix tailTrace_8377330
  have hstable : (prefixWord ++ tailWord_8377330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377330).length < 2 ^ (prefixWord ++ tailWord_8377330).sum := by decide
  have hdescent : baseEnd_8377330 < baseStart_8377330 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377367 : List Nat := [1, 1, 3, 5, 1, 2, 1, 4, 1, 2, 2]
def baseStart_8377367 : Nat := 118140960795 + 8377367 * 2 ^ 59
def prefixEnd_8377367 : Nat := 4983230072969 + 3 ^ 40 * 8377367 * 2
def baseEnd_8377367 : Nat := 4301615890114030246785697

theorem tailTrace_8377367 : CollatzResearch.WordTrace tailWord_8377367 prefixEnd_8377367 4301615890114030246785697 := by
  unfold tailWord_8377367
  simp only [CollatzResearch.WordTrace]
  refine ⟨305547676241237574221650355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203698450827491716147766903 305547676241237574221650355)
  ·
    refine ⟨458321514361856361332475533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305547676241237574221650355 458321514361856361332475533)
    ·
      refine ⟨171870567885696135499678325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 458321514361856361332475533 171870567885696135499678325)
      ·
        refine ⟨16112865739284012703094843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171870567885696135499678325 16112865739284012703094843)
        ·
          refine ⟨24169298608926019054642265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16112865739284012703094843 24169298608926019054642265)
          ·
            refine ⟨18126973956694514290981699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24169298608926019054642265 18126973956694514290981699)
            ·
              refine ⟨27190460935041771436472549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18126973956694514290981699 27190460935041771436472549)
              ·
                refine ⟨5098211425320332144338603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27190460935041771436472549 5098211425320332144338603)
                ·
                  refine ⟨7647317137980498216507905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5098211425320332144338603 7647317137980498216507905)
                  ·
                    refine ⟨5735487853485373662380929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7647317137980498216507905 5735487853485373662380929)
                    ·
                      refine ⟨4301615890114030246785697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5735487853485373662380929 4301615890114030246785697)
                      ·
                        rfl

theorem cell23_8377367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_8377367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377367 prefixEnd_8377367 := by exact prefixLift 8377367
  have htrace : WordTrace (prefixWord ++ tailWord_8377367) baseStart_8377367 baseEnd_8377367 := by
    simpa [prefixWord, tailWord_8377367, baseEnd_8377367] using wordTrace_append hprefix tailTrace_8377367
  have hstable : (prefixWord ++ tailWord_8377367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377367).length < 2 ^ (prefixWord ++ tailWord_8377367).sum := by decide
  have hdescent : baseEnd_8377367 < baseStart_8377367 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377373 : List Nat := [1, 4, 2, 2, 4, 1, 1, 8]
def baseStart_8377373 : Nat := 118140960795 + 8377373 * 2 ^ 59
def prefixEnd_8377373 : Nat := 4983230072969 + 3 ^ 40 * 8377373 * 2
def baseEnd_8377373 : Nat := 159319221148072489752247

theorem tailTrace_8377373 : CollatzResearch.WordTrace tailWord_8377373 prefixEnd_8377373 159319221148072489752247 := by
  unfold tailWord_8377373
  simp only [CollatzResearch.WordTrace]
  refine ⟨305547895079215837246368773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203698596719477224830912515 305547895079215837246368773)
  ·
    refine ⟨57290230327352969483694145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305547895079215837246368773 57290230327352969483694145)
    ·
      refine ⟨42967672745514727112770609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57290230327352969483694145 42967672745514727112770609)
      ·
        refine ⟨32225754559136045334577957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42967672745514727112770609 32225754559136045334577957)
        ·
          refine ⟨6042328979838008500233367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32225754559136045334577957 6042328979838008500233367)
          ·
            refine ⟨9063493469757012750350051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6042328979838008500233367 9063493469757012750350051)
            ·
              refine ⟨13595240204635519125525077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9063493469757012750350051 13595240204635519125525077)
              ·
                refine ⟨159319221148072489752247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13595240204635519125525077 159319221148072489752247)
                ·
                  rfl

theorem cell23_8377373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 8].length) (baseStart_8377373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377373 prefixEnd_8377373 := by exact prefixLift 8377373
  have htrace : WordTrace (prefixWord ++ tailWord_8377373) baseStart_8377373 baseEnd_8377373 := by
    simpa [prefixWord, tailWord_8377373, baseEnd_8377373] using wordTrace_append hprefix tailTrace_8377373
  have hstable : (prefixWord ++ tailWord_8377373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377373).length < 2 ^ (prefixWord ++ tailWord_8377373).sum := by decide
  have hdescent : baseEnd_8377373 < baseStart_8377373 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377383 : List Nat := [1, 1, 7, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_8377383 : Nat := 118140960795 + 8377383 * 2 ^ 59
def prefixEnd_8377383 : Nat := 4983230072969 + 3 ^ 40 * 8377383 * 2
def baseEnd_8377383 : Nat := 4301624105804502184185623

theorem tailTrace_8377383 : CollatzResearch.WordTrace tailWord_8377383 prefixEnd_8377383 4301624105804502184185623 := by
  unfold tailWord_8377383
  simp only [CollatzResearch.WordTrace]
  refine ⟨305548259809179608954232803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203698839872786405969488535 305548259809179608954232803)
  ·
    refine ⟨458322389713769413431349205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305548259809179608954232803 458322389713769413431349205)
    ·
      refine ⟨10741931008916470627297247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 458322389713769413431349205 10741931008916470627297247)
      ·
        refine ⟨16112896513374705940945871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10741931008916470627297247 16112896513374705940945871)
        ·
          refine ⟨24169344770062058911418807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16112896513374705940945871 24169344770062058911418807)
          ·
            refine ⟨36254017155093088367128211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24169344770062058911418807 36254017155093088367128211)
            ·
              refine ⟨54381025732639632550692317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36254017155093088367128211 54381025732639632550692317)
              ·
                refine ⟨20392884649739862206509619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54381025732639632550692317 20392884649739862206509619)
                ·
                  refine ⟨30589326974609793309764429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20392884649739862206509619 30589326974609793309764429)
                  ·
                    refine ⟨11470997615478672491161661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30589326974609793309764429 11470997615478672491161661)
                    ·
                      refine ⟨4301624105804502184185623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11470997615478672491161661 4301624105804502184185623)
                      ·
                        rfl

theorem cell23_8377383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_8377383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377383 prefixEnd_8377383 := by exact prefixLift 8377383
  have htrace : WordTrace (prefixWord ++ tailWord_8377383) baseStart_8377383 baseEnd_8377383 := by
    simpa [prefixWord, tailWord_8377383, baseEnd_8377383] using wordTrace_append hprefix tailTrace_8377383
  have hstable : (prefixWord ++ tailWord_8377383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377383).length < 2 ^ (prefixWord ++ tailWord_8377383).sum := by decide
  have hdescent : baseEnd_8377383 < baseStart_8377383 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377393 : List Nat := [1, 2, 2, 3, 1, 2, 2, 4, 1, 3, 2]
def baseStart_8377393 : Nat := 118140960795 + 8377393 * 2 ^ 59
def prefixEnd_8377393 : Nat := 4983230072969 + 3 ^ 40 * 8377393 * 2
def baseEnd_8377393 : Nat := 4301629240611047145060577

theorem tailTrace_8377393 : CollatzResearch.WordTrace tailWord_8377393 prefixEnd_8377393 4301629240611047145060577 := by
  unfold tailWord_8377393
  simp only [CollatzResearch.WordTrace]
  refine ⟨305548624539143380662096833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203699083026095587108064555 305548624539143380662096833)
  ·
    refine ⟨229161468404357535496572625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305548624539143380662096833 229161468404357535496572625)
    ·
      refine ⟨171871101303268151622429469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229161468404357535496572625 171871101303268151622429469)
      ·
        refine ⟨64451662988725556858411051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171871101303268151622429469 64451662988725556858411051)
        ·
          refine ⟨96677494483088335287616577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64451662988725556858411051 96677494483088335287616577)
          ·
            refine ⟨72508120862316251465712433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96677494483088335287616577 72508120862316251465712433)
            ·
              refine ⟨54381090646737188599284325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72508120862316251465712433 54381090646737188599284325)
              ·
                refine ⟨10196454496263222862365811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54381090646737188599284325 10196454496263222862365811)
                ·
                  refine ⟨15294681744394834293548717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10196454496263222862365811 15294681744394834293548717)
                  ·
                    refine ⟨5735505654148062860080769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15294681744394834293548717 5735505654148062860080769)
                    ·
                      refine ⟨4301629240611047145060577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5735505654148062860080769 4301629240611047145060577)
                      ·
                        rfl

theorem cell23_8377393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_8377393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377393 prefixEnd_8377393 := by exact prefixLift 8377393
  have htrace : WordTrace (prefixWord ++ tailWord_8377393) baseStart_8377393 baseEnd_8377393 := by
    simpa [prefixWord, tailWord_8377393, baseEnd_8377393] using wordTrace_append hprefix tailTrace_8377393
  have hstable : (prefixWord ++ tailWord_8377393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377393).length < 2 ^ (prefixWord ++ tailWord_8377393).sum := by decide
  have hdescent : baseEnd_8377393 < baseStart_8377393 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377436 : List Nat := [2, 2, 4, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_8377436 : Nat := 118140960795 + 8377436 * 2 ^ 59
def prefixEnd_8377436 : Nat := 4983230072969 + 3 ^ 40 * 8377436 * 2
def baseEnd_8377436 : Nat := 4301651320279190476822879

theorem tailTrace_8377436 : CollatzResearch.WordTrace tailWord_8377436 prefixEnd_8377436 4301651320279190476822879 := by
  unfold tailWord_8377436
  simp only [CollatzResearch.WordTrace]
  refine ⟨152775096438993799502956081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203700128585325066003941441 152775096438993799502956081)
  ·
    refine ⟨114581322329245349627217061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152775096438993799502956081 114581322329245349627217061)
    ·
      refine ⟨21483997936733503055103199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114581322329245349627217061 21483997936733503055103199)
      ·
        refine ⟨32225996905100254582654799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21483997936733503055103199 32225996905100254582654799)
        ·
          refine ⟨48338995357650381873982199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32225996905100254582654799 48338995357650381873982199)
          ·
            refine ⟨72508493036475572810973299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48338995357650381873982199 72508493036475572810973299)
            ·
              refine ⟨108762739554713359216459949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72508493036475572810973299 108762739554713359216459949)
              ·
                refine ⟨40786027333017509706172481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108762739554713359216459949 40786027333017509706172481)
                ·
                  refine ⟨30589520499763132279629361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40786027333017509706172481 30589520499763132279629361)
                  ·
                    refine ⟨22942140374822349209722021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30589520499763132279629361 22942140374822349209722021)
                    ·
                      refine ⟨4301651320279190476822879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22942140374822349209722021 4301651320279190476822879)
                      ·
                        rfl

theorem cell23_8377436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_8377436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377436 prefixEnd_8377436 := by exact prefixLift 8377436
  have htrace : WordTrace (prefixWord ++ tailWord_8377436) baseStart_8377436 baseEnd_8377436 := by
    simpa [prefixWord, tailWord_8377436, baseEnd_8377436] using wordTrace_append hprefix tailTrace_8377436
  have hstable : (prefixWord ++ tailWord_8377436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377436).length < 2 ^ (prefixWord ++ tailWord_8377436).sum := by decide
  have hdescent : baseEnd_8377436 < baseStart_8377436 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377459 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 8, 5]
def baseStart_8377459 : Nat := 118140960795 + 8377459 * 2 ^ 59
def prefixEnd_8377459 : Nat := 4983230072969 + 3 ^ 40 * 8377459 * 2
def baseEnd_8377459 : Nat := 1433887710111414628945091

theorem tailTrace_8377459 : CollatzResearch.WordTrace tailWord_8377459 prefixEnd_8377459 1433887710111414628945091 := by
  unfold tailWord_8377459
  simp only [CollatzResearch.WordTrace]
  refine ⟨305551031756904273933999431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203700687837936182622666287 305551031756904273933999431)
  ·
    refine ⟨458326547635356410900999147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305551031756904273933999431 458326547635356410900999147)
    ·
      refine ⟨687489821453034616351498721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458326547635356410900999147 687489821453034616351498721)
      ·
        refine ⟨515617366089775962263624041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 687489821453034616351498721 515617366089775962263624041)
        ·
          refine ⟨386713024567331971697718031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515617366089775962263624041 386713024567331971697718031)
          ·
            refine ⟨580069536850997957546577047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386713024567331971697718031 580069536850997957546577047)
            ·
              refine ⟨870104305276496936319865571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580069536850997957546577047 870104305276496936319865571)
              ·
                refine ⟨1305156457914745404479798357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 870104305276496936319865571 1305156457914745404479798357)
                ·
                  refine ⟨15294802241188422708747637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1305156457914745404479798357 15294802241188422708747637)
                  ·
                    refine ⟨1433887710111414628945091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15294802241188422708747637 1433887710111414628945091)
                    ·
                      rfl

theorem cell23_8377459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 5].length) (baseStart_8377459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377459 prefixEnd_8377459 := by exact prefixLift 8377459
  have htrace : WordTrace (prefixWord ++ tailWord_8377459) baseStart_8377459 baseEnd_8377459 := by
    simpa [prefixWord, tailWord_8377459, baseEnd_8377459] using wordTrace_append hprefix tailTrace_8377459
  have hstable : (prefixWord ++ tailWord_8377459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377459).length < 2 ^ (prefixWord ++ tailWord_8377459).sum := by decide
  have hdescent : baseEnd_8377459 < baseStart_8377459 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377476 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 4, 5]
def baseStart_8377476 : Nat := 118140960795 + 8377476 * 2 ^ 59
def prefixEnd_8377476 : Nat := 4983230072969 + 3 ^ 40 * 8377476 * 2
def baseEnd_8377476 : Nat := 1433890619835123440107565

theorem tailTrace_8377476 : CollatzResearch.WordTrace tailWord_8377476 prefixEnd_8377476 1433890619835123440107565 := by
  unfold tailWord_8377476
  simp only [CollatzResearch.WordTrace]
  refine ⟨152775825898921342918684141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203701101198561790558245521 152775825898921342918684141)
  ·
    refine ⟨57290934712095503594506553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152775825898921342918684141 57290934712095503594506553)
    ·
      refine ⟨42968201034071627695879915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57290934712095503594506553 42968201034071627695879915)
      ·
        refine ⟨64452301551107441543819873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42968201034071627695879915 64452301551107441543819873)
        ·
          refine ⟨48339226163330581157864905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64452301551107441543819873 48339226163330581157864905)
          ·
            refine ⟨36254419622497935868398679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48339226163330581157864905 36254419622497935868398679)
            ·
              refine ⟨54381629433746903802598019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36254419622497935868398679 54381629433746903802598019)
              ·
                refine ⟨81572444150620355703897029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54381629433746903802598019 81572444150620355703897029)
                ·
                  refine ⟨15294833278241316694480693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81572444150620355703897029 15294833278241316694480693)
                  ·
                    refine ⟨1433890619835123440107565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15294833278241316694480693 1433890619835123440107565)
                    ·
                      rfl

theorem cell23_8377476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_8377476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377476 prefixEnd_8377476 := by exact prefixLift 8377476
  have htrace : WordTrace (prefixWord ++ tailWord_8377476) baseStart_8377476 baseEnd_8377476 := by
    simpa [prefixWord, tailWord_8377476, baseEnd_8377476] using wordTrace_append hprefix tailTrace_8377476
  have hstable : (prefixWord ++ tailWord_8377476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377476).length < 2 ^ (prefixWord ++ tailWord_8377476).sum := by decide
  have hdescent : baseEnd_8377476 < baseStart_8377476 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377480 : List Nat := [2, 1, 3, 4, 3, 1, 1, 1, 7]
def baseStart_8377480 : Nat := 118140960795 + 8377480 * 2 ^ 59
def prefixEnd_8377480 : Nat := 4983230072969 + 3 ^ 40 * 8377480 * 2
def baseEnd_8377480 : Nat := 477963768158665367185853

theorem tailTrace_8377480 : CollatzResearch.WordTrace tailWord_8377480 prefixEnd_8377480 477963768158665367185853 := by
  unfold tailWord_8377480
  simp only [CollatzResearch.WordTrace]
  refine ⟨152775898844914097260256947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203701198459885463013675929 152775898844914097260256947)
  ·
    refine ⟨229163848267371145890385421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152775898844914097260256947 229163848267371145890385421)
    ·
      refine ⟨85936443100264179708894533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229163848267371145890385421 85936443100264179708894533)
      ·
        refine ⟨16113083081299533695417725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85936443100264179708894533 16113083081299533695417725)
        ·
          refine ⟨6042406155487325135781647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16113083081299533695417725 6042406155487325135781647)
          ·
            refine ⟨9063609233230987703672471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6042406155487325135781647 9063609233230987703672471)
            ·
              refine ⟨13595413849846481555508707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9063609233230987703672471 13595413849846481555508707)
              ·
                refine ⟨20393120774769722333263061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13595413849846481555508707 20393120774769722333263061)
                ·
                  refine ⟨477963768158665367185853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20393120774769722333263061 477963768158665367185853)
                  ·
                    rfl

theorem cell23_8377480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 7].length) (baseStart_8377480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377480 prefixEnd_8377480 := by exact prefixLift 8377480
  have htrace : WordTrace (prefixWord ++ tailWord_8377480) baseStart_8377480 baseEnd_8377480 := by
    simpa [prefixWord, tailWord_8377480, baseEnd_8377480] using wordTrace_append hprefix tailTrace_8377480
  have hstable : (prefixWord ++ tailWord_8377480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377480).length < 2 ^ (prefixWord ++ tailWord_8377480).sum := by decide
  have hdescent : baseEnd_8377480 < baseStart_8377480 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377486 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7]
def baseStart_8377486 : Nat := 118140960795 + 8377486 * 2 ^ 59
def prefixEnd_8377486 : Nat := 4983230072969 + 3 ^ 40 * 8377486 * 2
def baseEnd_8377486 : Nat := 4301676994311915281197649

theorem tailTrace_8377486 : CollatzResearch.WordTrace tailWord_8377486 prefixEnd_8377486 4301676994311915281197649 := by
  unfold tailWord_8377486
  simp only [CollatzResearch.WordTrace]
  refine ⟨38194002065975807193154039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203701344351870971696821541 38194002065975807193154039)
  ·
    refine ⟨57291003098963710789731059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38194002065975807193154039 57291003098963710789731059)
    ·
      refine ⟨85936504648445566184596589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57291003098963710789731059 85936504648445566184596589)
      ·
        refine ⟨32226189243167087319223721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85936504648445566184596589 32226189243167087319223721)
        ·
          refine ⟨24169641932375315489417791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32226189243167087319223721 24169641932375315489417791)
          ·
            refine ⟨36254462898562973234126687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24169641932375315489417791 36254462898562973234126687)
            ·
              refine ⟨54381694347844459851190031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36254462898562973234126687 54381694347844459851190031)
              ·
                refine ⟨81572541521766689776785047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54381694347844459851190031 81572541521766689776785047)
                ·
                  refine ⟨122358812282650034665177571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81572541521766689776785047 122358812282650034665177571)
                  ·
                    refine ⟨183538218423975051997766357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 122358812282650034665177571 183538218423975051997766357)
                    ·
                      refine ⟨4301676994311915281197649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 183538218423975051997766357 4301676994311915281197649)
                      ·
                        rfl

theorem cell23_8377486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_8377486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377486 prefixEnd_8377486 := by exact prefixLift 8377486
  have htrace : WordTrace (prefixWord ++ tailWord_8377486) baseStart_8377486 baseEnd_8377486 := by
    simpa [prefixWord, tailWord_8377486, baseEnd_8377486] using wordTrace_append hprefix tailTrace_8377486
  have hstable : (prefixWord ++ tailWord_8377486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377486).length < 2 ^ (prefixWord ++ tailWord_8377486).sum := by decide
  have hdescent : baseEnd_8377486 < baseStart_8377486 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377519 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 10]
def baseStart_8377519 : Nat := 118140960795 + 8377519 * 2 ^ 59
def prefixEnd_8377519 : Nat := 4983230072969 + 3 ^ 40 * 8377519 * 2
def baseEnd_8377519 : Nat := 477965993241501516898333

theorem tailTrace_8377519 : CollatzResearch.WordTrace tailWord_8377519 prefixEnd_8377519 477965993241501516898333 := by
  unfold tailWord_8377519
  simp only [CollatzResearch.WordTrace]
  refine ⟨305553220136686904181183611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203702146757791269454122407 305553220136686904181183611)
  ·
    refine ⟨458329830205030356271775417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305553220136686904181183611 458329830205030356271775417)
    ·
      refine ⟨343747372653772767203831563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458329830205030356271775417 343747372653772767203831563)
      ·
        refine ⟨515621058980659150805747345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343747372653772767203831563 515621058980659150805747345)
        ·
          refine ⟨386715794235494363104310509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515621058980659150805747345 386715794235494363104310509)
          ·
            refine ⟨145018422838310386164116441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 386715794235494363104310509 145018422838310386164116441)
            ·
              refine ⟨108763817128732789623087331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145018422838310386164116441 108763817128732789623087331)
              ·
                refine ⟨163145725693099184434630997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108763817128732789623087331 163145725693099184434630997)
                ·
                  refine ⟨477965993241501516898333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 163145725693099184434630997 477965993241501516898333)
                  ·
                    rfl

theorem cell23_8377519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 10].length) (baseStart_8377519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377519 prefixEnd_8377519 := by exact prefixLift 8377519
  have htrace : WordTrace (prefixWord ++ tailWord_8377519) baseStart_8377519 baseEnd_8377519 := by
    simpa [prefixWord, tailWord_8377519, baseEnd_8377519] using wordTrace_append hprefix tailTrace_8377519
  have hstable : (prefixWord ++ tailWord_8377519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377519).length < 2 ^ (prefixWord ++ tailWord_8377519).sum := by decide
  have hdescent : baseEnd_8377519 < baseStart_8377519 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377533 : List Nat := [1, 4, 1, 2, 1, 1, 4, 2, 2, 2, 3]
def baseStart_8377533 : Nat := 118140960795 + 8377533 * 2 ^ 59
def prefixEnd_8377533 : Nat := 4983230072969 + 3 ^ 40 * 8377533 * 2
def baseEnd_8377533 : Nat := 4301701127902676597309933

theorem tailTrace_8377533 : CollatzResearch.WordTrace tailWord_8377533 prefixEnd_8377533 4301701127902676597309933 := by
  unfold tailWord_8377533
  simp only [CollatzResearch.WordTrace]
  refine ⟨305553730758636184572193253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203702487172424123048128835 305553730758636184572193253)
  ·
    refine ⟨57291324517244284607286235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305553730758636184572193253 57291324517244284607286235)
    ·
      refine ⟨85936986775866426910929353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57291324517244284607286235 85936986775866426910929353)
      ·
        refine ⟨64452740081899820183197015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85936986775866426910929353 64452740081899820183197015)
        ·
          refine ⟨96679110122849730274795523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64452740081899820183197015 96679110122849730274795523)
          ·
            refine ⟨145018665184274595412193285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96679110122849730274795523 145018665184274595412193285)
            ·
              refine ⟨27190999722051486639786241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145018665184274595412193285 27190999722051486639786241)
              ·
                refine ⟨20393249791538614979839681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27190999722051486639786241 20393249791538614979839681)
                ·
                  refine ⟨15294937343653961234879761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20393249791538614979839681 15294937343653961234879761)
                  ·
                    refine ⟨11471203007740470926159821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15294937343653961234879761 11471203007740470926159821)
                    ·
                      refine ⟨4301701127902676597309933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11471203007740470926159821 4301701127902676597309933)
                      ·
                        rfl

theorem cell23_8377533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_8377533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377533 prefixEnd_8377533 := by exact prefixLift 8377533
  have htrace : WordTrace (prefixWord ++ tailWord_8377533) baseStart_8377533 baseEnd_8377533 := by
    simpa [prefixWord, tailWord_8377533, baseEnd_8377533] using wordTrace_append hprefix tailTrace_8377533
  have hstable : (prefixWord ++ tailWord_8377533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377533).length < 2 ^ (prefixWord ++ tailWord_8377533).sum := by decide
  have hdescent : baseEnd_8377533 < baseStart_8377533 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377590 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2]
def baseStart_8377590 : Nat := 118140960795 + 8377590 * 2 ^ 59
def prefixEnd_8377590 : Nat := 4983230072969 + 3 ^ 40 * 8377590 * 2
def baseEnd_8377590 : Nat := 4301730396299982874297171

theorem tailTrace_8377590 : CollatzResearch.WordTrace tailWord_8377590 prefixEnd_8377590 4301730396299982874297171 := by
  unfold tailWord_8377590
  simp only [CollatzResearch.WordTrace]
  refine ⟨19097238107464355206688639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203703873146286455538012149 19097238107464355206688639)
  ·
    refine ⟨28645857161196532810032959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19097238107464355206688639 28645857161196532810032959)
    ·
      refine ⟨42968785741794799215049439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28645857161196532810032959 42968785741794799215049439)
      ·
        refine ⟨64453178612692198822574159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42968785741794799215049439 64453178612692198822574159)
        ·
          refine ⟨96679767919038298233861239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64453178612692198822574159 96679767919038298233861239)
          ·
            refine ⟨145019651878557447350791859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96679767919038298233861239 145019651878557447350791859)
            ·
              refine ⟨217529477817836171026187789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145019651878557447350791859 217529477817836171026187789)
              ·
                refine ⟨81573554181688564134820421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217529477817836171026187789 81573554181688564134820421)
                ·
                  refine ⟨15295041409066605775278829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81573554181688564134820421 15295041409066605775278829)
                  ·
                    refine ⟨5735640528399977165729561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15295041409066605775278829 5735640528399977165729561)
                    ·
                      refine ⟨4301730396299982874297171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5735640528399977165729561 4301730396299982874297171)
                      ·
                        rfl

theorem cell23_8377590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_8377590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377590 prefixEnd_8377590 := by exact prefixLift 8377590
  have htrace : WordTrace (prefixWord ++ tailWord_8377590) baseStart_8377590 baseEnd_8377590 := by
    simpa [prefixWord, tailWord_8377590, baseEnd_8377590] using wordTrace_append hprefix tailTrace_8377590
  have hstable : (prefixWord ++ tailWord_8377590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377590).length < 2 ^ (prefixWord ++ tailWord_8377590).sum := by decide
  have hdescent : baseEnd_8377590 < baseStart_8377590 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377631 : List Nat := [1, 1, 2, 4, 5, 1, 1, 3, 1, 1, 3]
def baseStart_8377631 : Nat := 118140960795 + 8377631 * 2 ^ 59
def prefixEnd_8377631 : Nat := 4983230072969 + 3 ^ 40 * 8377631 * 2
def baseEnd_8377631 : Nat := 4301751449006817213884483

theorem tailTrace_8377631 : CollatzResearch.WordTrace tailWord_8377631 prefixEnd_8377631 4301751449006817213884483 := by
  unfold tailWord_8377631
  simp only [CollatzResearch.WordTrace]
  refine ⟨305557305112281147309260747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203704870074854098206173831 305557305112281147309260747)
  ·
    refine ⟨458335957668421720963891121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305557305112281147309260747 458335957668421720963891121)
    ·
      refine ⟨343751968251316290722918341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458335957668421720963891121 343751968251316290722918341)
      ·
        refine ⟨64453494047121804510547189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 343751968251316290722918341 64453494047121804510547189)
        ·
          refine ⟨6042515066917669172863799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64453494047121804510547189 6042515066917669172863799)
          ·
            refine ⟨9063772600376503759295699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6042515066917669172863799 9063772600376503759295699)
            ·
              refine ⟨13595658900564755638943549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9063772600376503759295699 13595658900564755638943549)
              ·
                refine ⟨5098372087711783364603831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13595658900564755638943549 5098372087711783364603831)
                ·
                  refine ⟨7647558131567675046905747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5098372087711783364603831 7647558131567675046905747)
                  ·
                    refine ⟨11471337197351512570358621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7647558131567675046905747 11471337197351512570358621)
                    ·
                      refine ⟨4301751449006817213884483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11471337197351512570358621 4301751449006817213884483)
                      ·
                        rfl

theorem cell23_8377631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_8377631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377631 prefixEnd_8377631 := by exact prefixLift 8377631
  have htrace : WordTrace (prefixWord ++ tailWord_8377631) baseStart_8377631 baseEnd_8377631 := by
    simpa [prefixWord, tailWord_8377631, baseEnd_8377631] using wordTrace_append hprefix tailTrace_8377631
  have hstable : (prefixWord ++ tailWord_8377631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377631).length < 2 ^ (prefixWord ++ tailWord_8377631).sum := by decide
  have hdescent : baseEnd_8377631 < baseStart_8377631 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377640 : List Nat := [2, 1, 5, 1, 2, 2, 2, 1, 1, 1, 5]
def baseStart_8377640 : Nat := 118140960795 + 8377640 * 2 ^ 59
def prefixEnd_8377640 : Nat := 4983230072969 + 3 ^ 40 * 8377640 * 2
def baseEnd_8377640 : Nat := 4301756070332707678671941

theorem tailTrace_8377640 : CollatzResearch.WordTrace tailWord_8377640 prefixEnd_8377640 4301756070332707678671941 := by
  unfold tailWord_8377640
  simp only [CollatzResearch.WordTrace]
  refine ⟨152778816684624270923169187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203705088912832361230892249 152778816684624270923169187)
  ·
    refine ⟨229168225026936406384753781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152778816684624270923169187 229168225026936406384753781)
    ·
      refine ⟨21484521096275288098570667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 229168225026936406384753781 21484521096275288098570667)
      ·
        refine ⟨32226781644412932147856001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21484521096275288098570667 32226781644412932147856001)
        ·
          refine ⟨24170086233309699110892001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32226781644412932147856001 24170086233309699110892001)
          ·
            refine ⟨18127564674982274333169001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24170086233309699110892001 18127564674982274333169001)
            ·
              refine ⟨13595673506236705749876751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18127564674982274333169001 13595673506236705749876751)
              ·
                refine ⟨20393510259355058624815127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13595673506236705749876751 20393510259355058624815127)
                ·
                  refine ⟨30590265389032587937222691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20393510259355058624815127 30590265389032587937222691)
                  ·
                    refine ⟨45885398083548881905834037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30590265389032587937222691 45885398083548881905834037)
                    ·
                      refine ⟨4301756070332707678671941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45885398083548881905834037 4301756070332707678671941)
                      ·
                        rfl

theorem cell23_8377640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_8377640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377640 prefixEnd_8377640 := by exact prefixLift 8377640
  have htrace : WordTrace (prefixWord ++ tailWord_8377640) baseStart_8377640 baseEnd_8377640 := by
    simpa [prefixWord, tailWord_8377640, baseEnd_8377640] using wordTrace_append hprefix tailTrace_8377640
  have hstable : (prefixWord ++ tailWord_8377640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377640).length < 2 ^ (prefixWord ++ tailWord_8377640).sum := by decide
  have hdescent : baseEnd_8377640 < baseStart_8377640 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377656 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 2, 7]
def baseStart_8377656 : Nat := 118140960795 + 8377656 * 2 ^ 59
def prefixEnd_8377656 : Nat := 4983230072969 + 3 ^ 40 * 8377656 * 2
def baseEnd_8377656 : Nat := 1433921428674393205357289

theorem tailTrace_8377656 : CollatzResearch.WordTrace tailWord_8377656 prefixEnd_8377656 1433921428674393205357289 := by
  unfold tailWord_8377656
  simp only [CollatzResearch.WordTrace]
  refine ⟨152779108468595288289460411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203705477958127051052613881 152779108468595288289460411)
  ·
    refine ⟨229168662702892932434190617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152779108468595288289460411 229168662702892932434190617)
    ·
      refine ⟨171876497027169699325642963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229168662702892932434190617 171876497027169699325642963)
      ·
        refine ⟨257814745540754548988464445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171876497027169699325642963 257814745540754548988464445)
        ·
          refine ⟨96680529577782955870674167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257814745540754548988464445 96680529577782955870674167)
          ·
            refine ⟨145020794366674433806011251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96680529577782955870674167 145020794366674433806011251)
            ·
              refine ⟨217531191550011650709016877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145020794366674433806011251 217531191550011650709016877)
              ·
                refine ⟨81574196831254369015881329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217531191550011650709016877 81574196831254369015881329)
                ·
                  refine ⟨61180647623440776761910997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81574196831254369015881329 61180647623440776761910997)
                  ·
                    refine ⟨1433921428674393205357289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61180647623440776761910997 1433921428674393205357289)
                    ·
                      rfl

theorem cell23_8377656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 2, 7].length) (baseStart_8377656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377656 prefixEnd_8377656 := by exact prefixLift 8377656
  have htrace : WordTrace (prefixWord ++ tailWord_8377656) baseStart_8377656 baseEnd_8377656 := by
    simpa [prefixWord, tailWord_8377656, baseEnd_8377656] using wordTrace_append hprefix tailTrace_8377656
  have hstable : (prefixWord ++ tailWord_8377656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377656).length < 2 ^ (prefixWord ++ tailWord_8377656).sum := by decide
  have hdescent : baseEnd_8377656 < baseStart_8377656 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377680 : List Nat := [2, 1, 1, 1, 1, 5, 3, 1, 3, 3, 2]
def baseStart_8377680 : Nat := 118140960795 + 8377680 * 2 ^ 59
def prefixEnd_8377680 : Nat := 4983230072969 + 3 ^ 40 * 8377680 * 2
def baseEnd_8377680 : Nat := 4301776609558887522171757

theorem tailTrace_8377680 : CollatzResearch.WordTrace tailWord_8377680 prefixEnd_8377680 4301776609558887522171757 := by
  unfold tailWord_8377680
  simp only [CollatzResearch.WordTrace]
  refine ⟨152779546144551814338897247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203706061526069085785196329 152779546144551814338897247)
  ·
    refine ⟨229169319216827721508345871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152779546144551814338897247 229169319216827721508345871)
    ·
      refine ⟨343753978825241582262518807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229169319216827721508345871 343753978825241582262518807)
      ·
        refine ⟨515630968237862373393778211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343753978825241582262518807 515630968237862373393778211)
        ·
          refine ⟨773446452356793560090667317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515630968237862373393778211 773446452356793560090667317)
          ·
            refine ⟨72510604908449396258500061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 773446452356793560090667317 72510604908449396258500061)
            ·
              refine ⟨27191476840668523596937523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72510604908449396258500061 27191476840668523596937523)
              ·
                refine ⟨40787215261002785395406285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27191476840668523596937523 40787215261002785395406285)
                ·
                  refine ⟨15295205722876044523277357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40787215261002785395406285 15295205722876044523277357)
                  ·
                    refine ⟨5735702146078516696229009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15295205722876044523277357 5735702146078516696229009)
                    ·
                      refine ⟨4301776609558887522171757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5735702146078516696229009 4301776609558887522171757)
                      ·
                        rfl

theorem cell23_8377680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 3, 3, 2].length) (baseStart_8377680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377680 prefixEnd_8377680 := by exact prefixLift 8377680
  have htrace : WordTrace (prefixWord ++ tailWord_8377680) baseStart_8377680 baseEnd_8377680 := by
    simpa [prefixWord, tailWord_8377680, baseEnd_8377680] using wordTrace_append hprefix tailTrace_8377680
  have hstable : (prefixWord ++ tailWord_8377680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377680).length < 2 ^ (prefixWord ++ tailWord_8377680).sum := by decide
  have hdescent : baseEnd_8377680 < baseStart_8377680 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377704 : List Nat := [2, 1, 4, 2, 3, 1, 2, 2, 2, 1, 3]
def baseStart_8377704 : Nat := 118140960795 + 8377704 * 2 ^ 59
def prefixEnd_8377704 : Nat := 4983230072969 + 3 ^ 40 * 8377704 * 2
def baseEnd_8377704 : Nat := 4301788933094595428271647

theorem tailTrace_8377704 : CollatzResearch.WordTrace tailWord_8377704 prefixEnd_8377704 4301788933094595428271647 := by
  unfold tailWord_8377704
  simp only [CollatzResearch.WordTrace]
  refine ⟨152779983820508340388334083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203706645094011120517778777 152779983820508340388334083)
  ·
    refine ⟨229169975730762510582501125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152779983820508340388334083 229169975730762510582501125)
    ·
      refine ⟨42969370449517970734218961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 229169975730762510582501125 42969370449517970734218961)
      ·
        refine ⟨32227027837138478050664221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42969370449517970734218961 32227027837138478050664221)
        ·
          refine ⟨12085135438926929268999083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32227027837138478050664221 12085135438926929268999083)
          ·
            refine ⟨18127703158390393903498625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12085135438926929268999083 18127703158390393903498625)
            ·
              refine ⟨13595777368792795427623969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18127703158390393903498625 13595777368792795427623969)
              ·
                refine ⟨10196833026594596570717977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13595777368792795427623969 10196833026594596570717977)
                ·
                  refine ⟨7647624769945947428038483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10196833026594596570717977 7647624769945947428038483)
                  ·
                    refine ⟨11471437154918921142057725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7647624769945947428038483 11471437154918921142057725)
                    ·
                      refine ⟨4301788933094595428271647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11471437154918921142057725 4301788933094595428271647)
                      ·
                        rfl

theorem cell23_8377704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_8377704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377704 prefixEnd_8377704 := by exact prefixLift 8377704
  have htrace : WordTrace (prefixWord ++ tailWord_8377704) baseStart_8377704 baseEnd_8377704 := by
    simpa [prefixWord, tailWord_8377704, baseEnd_8377704] using wordTrace_append hprefix tailTrace_8377704
  have hstable : (prefixWord ++ tailWord_8377704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377704).length < 2 ^ (prefixWord ++ tailWord_8377704).sum := by decide
  have hdescent : baseEnd_8377704 < baseStart_8377704 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377713 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 2, 4, 3]
def baseStart_8377713 : Nat := 118140960795 + 8377713 * 2 ^ 59
def prefixEnd_8377713 : Nat := 4983230072969 + 3 ^ 40 * 8377713 * 2
def baseEnd_8377713 : Nat := 4301793554420485893059105

theorem tailTrace_8377713 : CollatzResearch.WordTrace tailWord_8377713 prefixEnd_8377713 4301793554420485893059105 := by
  unfold tailWord_8377713
  simp only [CollatzResearch.WordTrace]
  refine ⟨305560295897984075313745793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203706863931989383542497195 305560295897984075313745793)
  ·
    refine ⟨229170221923488056485309345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305560295897984075313745793 229170221923488056485309345)
    ·
      refine ⟨171877666442616042363982009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229170221923488056485309345 171877666442616042363982009)
      ·
        refine ⟨128908249831962031772986507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171877666442616042363982009 128908249831962031772986507)
        ·
          refine ⟨193362374747943047659479761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128908249831962031772986507 193362374747943047659479761)
          ·
            refine ⟨145021781060957285744609821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193362374747943047659479761 145021781060957285744609821)
            ·
              refine ⟨54383167897858982154228683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145021781060957285744609821 54383167897858982154228683)
              ·
                refine ⟨81574751846788473231343025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54383167897858982154228683 81574751846788473231343025)
                ·
                  refine ⟨61181063885091354923507269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81574751846788473231343025 61181063885091354923507269)
                  ·
                    refine ⟨11471449478454629048157613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61181063885091354923507269 11471449478454629048157613)
                    ·
                      refine ⟨4301793554420485893059105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11471449478454629048157613 4301793554420485893059105)
                      ·
                        rfl

theorem cell23_8377713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_8377713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377713 prefixEnd_8377713 := by exact prefixLift 8377713
  have htrace : WordTrace (prefixWord ++ tailWord_8377713) baseStart_8377713 baseEnd_8377713 := by
    simpa [prefixWord, tailWord_8377713, baseEnd_8377713] using wordTrace_append hprefix tailTrace_8377713
  have hstable : (prefixWord ++ tailWord_8377713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377713).length < 2 ^ (prefixWord ++ tailWord_8377713).sum := by decide
  have hdescent : baseEnd_8377713 < baseStart_8377713 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377723 : List Nat := [1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 4]
def baseStart_8377723 : Nat := 118140960795 + 8377723 * 2 ^ 59
def prefixEnd_8377723 : Nat := 4983230072969 + 3 ^ 40 * 8377723 * 2
def baseEnd_8377723 : Nat := 4301798689227030853934059

theorem tailTrace_8377723 : CollatzResearch.WordTrace tailWord_8377723 prefixEnd_8377723 4301798689227030853934059 := by
  unfold tailWord_8377723
  simp only [CollatzResearch.WordTrace]
  refine ⟨305560660627947847021609823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203707107085298564681073215 305560660627947847021609823)
  ·
    refine ⟨458340990941921770532414735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305560660627947847021609823 458340990941921770532414735)
    ·
      refine ⟨687511486412882655798622103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458340990941921770532414735 687511486412882655798622103)
      ·
        refine ⟨1031267229619323983697933155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687511486412882655798622103 1031267229619323983697933155)
        ·
          refine ⟨1546900844428985975546899733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1031267229619323983697933155 1546900844428985975546899733)
          ·
            refine ⟨72510977082608717603760925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1546900844428985975546899733 72510977082608717603760925)
            ·
              refine ⟨27191616405978269101410347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72510977082608717603760925 27191616405978269101410347)
              ·
                refine ⟨40787424608967403652115521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27191616405978269101410347 40787424608967403652115521)
                ·
                  refine ⟨30590568456725552739086641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40787424608967403652115521 30590568456725552739086641)
                  ·
                    refine ⟨22942926342544164554314981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30590568456725552739086641 22942926342544164554314981)
                    ·
                      refine ⟨4301798689227030853934059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22942926342544164554314981 4301798689227030853934059)
                      ·
                        rfl

theorem cell23_8377723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 4].length) (baseStart_8377723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377723 prefixEnd_8377723 := by exact prefixLift 8377723
  have htrace : WordTrace (prefixWord ++ tailWord_8377723) baseStart_8377723 baseEnd_8377723 := by
    simpa [prefixWord, tailWord_8377723, baseEnd_8377723] using wordTrace_append hprefix tailTrace_8377723
  have hstable : (prefixWord ++ tailWord_8377723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377723).length < 2 ^ (prefixWord ++ tailWord_8377723).sum := by decide
  have hdescent : baseEnd_8377723 < baseStart_8377723 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377763 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 4, 5]
def baseStart_8377763 : Nat := 118140960795 + 8377763 * 2 ^ 59
def prefixEnd_8377763 : Nat := 4983230072969 + 3 ^ 40 * 8377763 * 2
def baseEnd_8377763 : Nat := 1433939742817736899144625

theorem tailTrace_8377763 : CollatzResearch.WordTrace tailWord_8377763 prefixEnd_8377763 1433939742817736899144625 := by
  unfold tailWord_8377763
  simp only [CollatzResearch.WordTrace]
  refine ⟨305562119547802933853065943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203708079698535289235377295 305562119547802933853065943)
  ·
    refine ⟨458343179321704400779598915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305562119547802933853065943 458343179321704400779598915)
    ·
      refine ⟨687514768982556601169398373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458343179321704400779598915 687514768982556601169398373)
      ·
        refine ⟨128909019184229362719262195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 687514768982556601169398373 128909019184229362719262195)
        ·
          refine ⟨193363528776344044078893293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128909019184229362719262195 193363528776344044078893293)
          ·
            refine ⟨72511323291129016529584985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193363528776344044078893293 72511323291129016529584985)
            ·
              refine ⟨54383492468346762397188739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72511323291129016529584985 54383492468346762397188739)
              ·
                refine ⟨81575238702520143595783109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54383492468346762397188739 81575238702520143595783109)
                ·
                  refine ⟨15295357256722526924209333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81575238702520143595783109 15295357256722526924209333)
                  ·
                    refine ⟨1433939742817736899144625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15295357256722526924209333 1433939742817736899144625)
                    ·
                      rfl

theorem cell23_8377763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 5].length) (baseStart_8377763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377763 prefixEnd_8377763 := by exact prefixLift 8377763
  have htrace : WordTrace (prefixWord ++ tailWord_8377763) baseStart_8377763 baseEnd_8377763 := by
    simpa [prefixWord, tailWord_8377763, baseEnd_8377763] using wordTrace_append hprefix tailTrace_8377763
  have hstable : (prefixWord ++ tailWord_8377763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377763).length < 2 ^ (prefixWord ++ tailWord_8377763).sum := by decide
  have hdescent : baseEnd_8377763 < baseStart_8377763 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377783 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 4]
def baseStart_8377783 : Nat := 118140960795 + 8377783 * 2 ^ 59
def prefixEnd_8377783 : Nat := 4983230072969 + 3 ^ 40 * 8377783 * 2
def baseEnd_8377783 : Nat := 4301829498066300619183783

theorem tailTrace_8377783 : CollatzResearch.WordTrace tailWord_8377783 prefixEnd_8377783 4301829498066300619183783 := by
  unfold tailWord_8377783
  simp only [CollatzResearch.WordTrace]
  refine ⟨305562849007730477268794003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203708566005153651512529335 305562849007730477268794003)
  ·
    refine ⟨458344273511595715903191005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305562849007730477268794003 458344273511595715903191005)
    ·
      refine ⟨171879102566848393463696627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 458344273511595715903191005 171879102566848393463696627)
      ·
        refine ⟨257818653850272590195544941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171879102566848393463696627 257818653850272590195544941)
        ·
          refine ⟨96681995193852221323329353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257818653850272590195544941 96681995193852221323329353)
          ·
            refine ⟨72511496395389165992497015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96681995193852221323329353 72511496395389165992497015)
            ·
              refine ⟨108767244593083748988745523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72511496395389165992497015 108767244593083748988745523)
              ·
                refine ⟨163150866889625623483118285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108767244593083748988745523 163150866889625623483118285)
                ·
                  refine ⟨61181575083609608806169357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163150866889625623483118285 61181575083609608806169357)
                  ·
                    refine ⟨22943090656353603302313509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61181575083609608806169357 22943090656353603302313509)
                    ·
                      refine ⟨4301829498066300619183783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22943090656353603302313509 4301829498066300619183783)
                      ·
                        rfl

theorem cell23_8377783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_8377783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377783 prefixEnd_8377783 := by exact prefixLift 8377783
  have htrace : WordTrace (prefixWord ++ tailWord_8377783) baseStart_8377783 baseEnd_8377783 := by
    simpa [prefixWord, tailWord_8377783, baseEnd_8377783] using wordTrace_append hprefix tailTrace_8377783
  have hstable : (prefixWord ++ tailWord_8377783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377783).length < 2 ^ (prefixWord ++ tailWord_8377783).sum := by decide
  have hdescent : baseEnd_8377783 < baseStart_8377783 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377800 : List Nat := [2, 1, 3, 1, 3, 1, 2, 3, 2, 1, 4]
def baseStart_8377800 : Nat := 118140960795 + 8377800 * 2 ^ 59
def prefixEnd_8377800 : Nat := 4983230072969 + 3 ^ 40 * 8377800 * 2
def baseEnd_8377800 : Nat := 4301838227237427052671205

theorem tailTrace_8377800 : CollatzResearch.WordTrace tailWord_8377800 prefixEnd_8377800 4301838227237427052671205 := by
  unfold tailWord_8377800
  simp only [CollatzResearch.WordTrace]
  refine ⟨152781734524334444586081427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203708979365779259448108569 152781734524334444586081427)
  ·
    refine ⟨229172601786501666879122141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152781734524334444586081427 229172601786501666879122141)
    ·
      refine ⟨85939725669938125079670803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229172601786501666879122141 85939725669938125079670803)
      ·
        refine ⟨128909588504907187619506205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85939725669938125079670803 128909588504907187619506205)
        ·
          refine ⟨48341095689340195357314827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128909588504907187619506205 48341095689340195357314827)
          ·
            refine ⟨72511643534010293035972241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48341095689340195357314827 72511643534010293035972241)
            ·
              refine ⟨54383732650507719776979181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72511643534010293035972241 54383732650507719776979181)
              ·
                refine ⟨20393899743940394916367193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54383732650507719776979181 20393899743940394916367193)
                ·
                  refine ⟨15295424807955296187275395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20393899743940394916367193 15295424807955296187275395)
                  ·
                    refine ⟨22943137211932944280913093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15295424807955296187275395 22943137211932944280913093)
                    ·
                      refine ⟨4301838227237427052671205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22943137211932944280913093 4301838227237427052671205)
                      ·
                        rfl

theorem cell23_8377800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_8377800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377800 prefixEnd_8377800 := by exact prefixLift 8377800
  have htrace : WordTrace (prefixWord ++ tailWord_8377800) baseStart_8377800 baseEnd_8377800 := by
    simpa [prefixWord, tailWord_8377800, baseEnd_8377800] using wordTrace_append hprefix tailTrace_8377800
  have hstable : (prefixWord ++ tailWord_8377800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377800).length < 2 ^ (prefixWord ++ tailWord_8377800).sum := by decide
  have hdescent : baseEnd_8377800 < baseStart_8377800 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377823 : List Nat := [1, 1, 2, 3, 3, 1, 1, 3, 8]
def baseStart_8377823 : Nat := 118140960795 + 8377823 * 2 ^ 59
def prefixEnd_8377823 : Nat := 4983230072969 + 3 ^ 40 * 8377823 * 2
def baseEnd_8377823 : Nat := 477983337476942273631511

theorem tailTrace_8377823 : CollatzResearch.WordTrace tailWord_8377823 prefixEnd_8377823 477983337476942273631511 := by
  unfold tailWord_8377823
  simp only [CollatzResearch.WordTrace]
  refine ⟨305564307927585564100250123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203709538618390376066833415 305564307927585564100250123)
  ·
    refine ⟨458346461891378346150375185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305564307927585564100250123 458346461891378346150375185)
    ·
      refine ⟨343759846418533759612781389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458346461891378346150375185 343759846418533759612781389)
      ·
        refine ⟨128909942406950159854793021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343759846418533759612781389 128909942406950159854793021)
        ·
          refine ⟨48341228402606309945547383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128909942406950159854793021 48341228402606309945547383)
          ·
            refine ⟨72511842603909464918321075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48341228402606309945547383 72511842603909464918321075)
            ·
              refine ⟨108767763905864197377481613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72511842603909464918321075 108767763905864197377481613)
              ·
                refine ⟨40787911464699074016555605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108767763905864197377481613 40787911464699074016555605)
                ·
                  refine ⟨477983337476942273631511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40787911464699074016555605 477983337476942273631511)
                  ·
                    rfl

theorem cell23_8377823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 8].length) (baseStart_8377823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377823 prefixEnd_8377823 := by exact prefixLift 8377823
  have htrace : WordTrace (prefixWord ++ tailWord_8377823) baseStart_8377823 baseEnd_8377823 := by
    simpa [prefixWord, tailWord_8377823, baseEnd_8377823] using wordTrace_append hprefix tailTrace_8377823
  have hstable : (prefixWord ++ tailWord_8377823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377823).length < 2 ^ (prefixWord ++ tailWord_8377823).sum := by decide
  have hdescent : baseEnd_8377823 < baseStart_8377823 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377827 : List Nat := [1, 1, 1, 6, 2, 1, 3, 1, 3, 4]
def baseStart_8377827 : Nat := 118140960795 + 8377827 * 2 ^ 59
def prefixEnd_8377827 : Nat := 4983230072969 + 3 ^ 40 * 8377827 * 2
def baseEnd_8377827 : Nat := 1433950697071699482344527

theorem tailTrace_8377827 : CollatzResearch.WordTrace tailWord_8377827 prefixEnd_8377827 1433950697071699482344527 := by
  unfold tailWord_8377827
  simp only [CollatzResearch.WordTrace]
  refine ⟨305564453819571072783395735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203709635879714048522263823 305564453819571072783395735)
  ·
    refine ⟨458346680729356609175093603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305564453819571072783395735 458346680729356609175093603)
    ·
      refine ⟨687520021094034913762640405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458346680729356609175093603 687520021094034913762640405)
      ·
        refine ⟨32227500988782886582623769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 687520021094034913762640405 32227500988782886582623769)
        ·
          refine ⟨24170625741587164936967827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32227500988782886582623769 24170625741587164936967827)
          ·
            refine ⟨36255938612380747405451741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24170625741587164936967827 36255938612380747405451741)
            ·
              refine ⟨13595976979642780277044403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36255938612380747405451741 13595976979642780277044403)
              ·
                refine ⟨20393965469464170415566605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13595976979642780277044403 20393965469464170415566605)
                ·
                  refine ⟨7647737051049063905837477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20393965469464170415566605 7647737051049063905837477)
                  ·
                    refine ⟨1433950697071699482344527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7647737051049063905837477 1433950697071699482344527)
                    ·
                      rfl

theorem cell23_8377827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 3, 4].length) (baseStart_8377827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377827 prefixEnd_8377827 := by exact prefixLift 8377827
  have htrace : WordTrace (prefixWord ++ tailWord_8377827) baseStart_8377827 baseEnd_8377827 := by
    simpa [prefixWord, tailWord_8377827, baseEnd_8377827] using wordTrace_append hprefix tailTrace_8377827
  have hstable : (prefixWord ++ tailWord_8377827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377827).length < 2 ^ (prefixWord ++ tailWord_8377827).sum := by decide
  have hdescent : baseEnd_8377827 < baseStart_8377827 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377840 : List Nat := [2, 1, 1, 1, 3, 5, 1, 3, 6]
def baseStart_8377840 : Nat := 118140960795 + 8377840 * 2 ^ 59
def prefixEnd_8377840 : Nat := 4983230072969 + 3 ^ 40 * 8377840 * 2
def baseEnd_8377840 : Nat := 477984307384845210685669

theorem tailTrace_8377840 : CollatzResearch.WordTrace tailWord_8377840 prefixEnd_8377840 477984307384845210685669 := by
  unfold tailWord_8377840
  simp only [CollatzResearch.WordTrace]
  refine ⟨152782463984261988001809487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203709951979015984002412649 152782463984261988001809487)
  ·
    refine ⟨229173695976392982002714231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152782463984261988001809487 229173695976392982002714231)
    ·
      refine ⟨343760543964589473004071347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229173695976392982002714231 343760543964589473004071347)
      ·
        refine ⟨515640815946884209506107021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343760543964589473004071347 515640815946884209506107021)
        ·
          refine ⟨193365305980081578564790133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 515640815946884209506107021 193365305980081578564790133)
          ·
            refine ⟨18127997435632647990449075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 193365305980081578564790133 18127997435632647990449075)
            ·
              refine ⟨27191996153448971985673613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18127997435632647990449075 27191996153448971985673613)
              ·
                refine ⟨10196998557543364494627605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27191996153448971985673613 10196998557543364494627605)
                ·
                  refine ⟨477984307384845210685669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10196998557543364494627605 477984307384845210685669)
                  ·
                    rfl

theorem cell23_8377840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 6].length) (baseStart_8377840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377840 prefixEnd_8377840 := by exact prefixLift 8377840
  have htrace : WordTrace (prefixWord ++ tailWord_8377840) baseStart_8377840 baseEnd_8377840 := by
    simpa [prefixWord, tailWord_8377840, baseEnd_8377840] using wordTrace_append hprefix tailTrace_8377840
  have hstable : (prefixWord ++ tailWord_8377840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377840).length < 2 ^ (prefixWord ++ tailWord_8377840).sum := by decide
  have hdescent : baseEnd_8377840 < baseStart_8377840 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377900 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 8, 4]
def baseStart_8377900 : Nat := 118140960795 + 8377900 * 2 ^ 59
def prefixEnd_8377900 : Nat := 4983230072969 + 3 ^ 40 * 8377900 * 2
def baseEnd_8377900 : Nat := 1433963191767625553806915

theorem tailTrace_8377900 : CollatzResearch.WordTrace tailWord_8377900 prefixEnd_8377900 1433963191767625553806915 := by
  unfold tailWord_8377900
  simp only [CollatzResearch.WordTrace]
  refine ⟨152783558174153303125401577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203711410898871070833868769 152783558174153303125401577)
  ·
    refine ⟨114587668630614977344051183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152783558174153303125401577 114587668630614977344051183)
    ·
      refine ⟨171881502945922466016076775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114587668630614977344051183 171881502945922466016076775)
      ·
        refine ⟨257822254418883699024115163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171881502945922466016076775 257822254418883699024115163)
        ·
          refine ⟨386733381628325548536172745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257822254418883699024115163 386733381628325548536172745)
          ·
            refine ⟨290050036221244161402129559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386733381628325548536172745 290050036221244161402129559)
            ·
              refine ⟨435075054331866242103194339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290050036221244161402129559 435075054331866242103194339)
              ·
                refine ⟨652612581497799363154791509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 435075054331866242103194339 652612581497799363154791509)
                ·
                  refine ⟨7647803689427336286970213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 652612581497799363154791509 7647803689427336286970213)
                  ·
                    refine ⟨1433963191767625553806915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7647803689427336286970213 1433963191767625553806915)
                    ·
                      rfl

theorem cell23_8377900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 4].length) (baseStart_8377900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377900 prefixEnd_8377900 := by exact prefixLift 8377900
  have htrace : WordTrace (prefixWord ++ tailWord_8377900) baseStart_8377900 baseEnd_8377900 := by
    simpa [prefixWord, tailWord_8377900, baseEnd_8377900] using wordTrace_append hprefix tailTrace_8377900
  have hstable : (prefixWord ++ tailWord_8377900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377900).length < 2 ^ (prefixWord ++ tailWord_8377900).sum := by decide
  have hdescent : baseEnd_8377900 < baseStart_8377900 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377980 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 1, 5, 4]
def baseStart_8377980 : Nat := 118140960795 + 8377980 * 2 ^ 59
def prefixEnd_8377980 : Nat := 4983230072969 + 3 ^ 40 * 8377980 * 2
def baseEnd_8377980 : Nat := 4301930653755236348420377

theorem tailTrace_8377980 : CollatzResearch.WordTrace tailWord_8377980 prefixEnd_8377980 4301930653755236348420377 := by
  unfold tailWord_8377980
  simp only [CollatzResearch.WordTrace]
  refine ⟨152785017094008389956857697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203713356125344519942476929 152785017094008389956857697)
  ·
    refine ⟨114588762820506292467643273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152785017094008389956857697 114588762820506292467643273)
    ·
      refine ⟨85941572115379719350732455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114588762820506292467643273 85941572115379719350732455)
      ·
        refine ⟨128912358173069579026098683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85941572115379719350732455 128912358173069579026098683)
        ·
          refine ⟨193368537259604368539148025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128912358173069579026098683 193368537259604368539148025)
          ·
            refine ⟨145026402944703276404361019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193368537259604368539148025 145026402944703276404361019)
            ·
              refine ⟨217539604417054914606541529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145026402944703276404361019 217539604417054914606541529)
              ·
                refine ⟨163154703312791185954906147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217539604417054914606541529 163154703312791185954906147)
                ·
                  refine ⟨244732054969186778932359221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163154703312791185954906147 244732054969186778932359221)
                  ·
                    refine ⟨22943630153361260524908677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 244732054969186778932359221 22943630153361260524908677)
                    ·
                      refine ⟨4301930653755236348420377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22943630153361260524908677 4301930653755236348420377)
                      ·
                        rfl

theorem cell23_8377980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_8377980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377980 prefixEnd_8377980 := by exact prefixLift 8377980
  have htrace : WordTrace (prefixWord ++ tailWord_8377980) baseStart_8377980 baseEnd_8377980 := by
    simpa [prefixWord, tailWord_8377980, baseEnd_8377980] using wordTrace_append hprefix tailTrace_8377980
  have hstable : (prefixWord ++ tailWord_8377980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377980).length < 2 ^ (prefixWord ++ tailWord_8377980).sum := by decide
  have hdescent : baseEnd_8377980 < baseStart_8377980 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377984 : List Nat := [2, 1, 1, 2, 1, 4, 1, 5, 1, 3, 2]
def baseStart_8377984 : Nat := 118140960795 + 8377984 * 2 ^ 59
def prefixEnd_8377984 : Nat := 4983230072969 + 3 ^ 40 * 8377984 * 2
def baseEnd_8377984 : Nat := 4301932707677854332770359

theorem tailTrace_8377984 : CollatzResearch.WordTrace tailWord_8377984 prefixEnd_8377984 4301932707677854332770359 := by
  unfold tailWord_8377984
  simp only [CollatzResearch.WordTrace]
  refine ⟨152785090040001144298430503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203713453386668192397907337 152785090040001144298430503)
  ·
    refine ⟨229177635060001716447645755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152785090040001144298430503 229177635060001716447645755)
    ·
      refine ⟨343766452590002574671468633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229177635060001716447645755 343766452590002574671468633)
      ·
        refine ⟨257824839442501931003601475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343766452590002574671468633 257824839442501931003601475)
        ·
          refine ⟨386737259163752896505402213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257824839442501931003601475 386737259163752896505402213)
          ·
            refine ⟨72513236093203668094762915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 386737259163752896505402213 72513236093203668094762915)
            ·
              refine ⟨108769854139805502142144373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72513236093203668094762915 108769854139805502142144373)
              ·
                refine ⟨10197173825606765825826035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108769854139805502142144373 10197173825606765825826035)
                ·
                  refine ⟨15295760738410148738739053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10197173825606765825826035 15295760738410148738739053)
                  ·
                    refine ⟨5735910276903805777027145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15295760738410148738739053 5735910276903805777027145)
                    ·
                      refine ⟨4301932707677854332770359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5735910276903805777027145 4301932707677854332770359)
                      ·
                        rfl

theorem cell23_8377984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 1, 3, 2].length) (baseStart_8377984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377984 prefixEnd_8377984 := by exact prefixLift 8377984
  have htrace : WordTrace (prefixWord ++ tailWord_8377984) baseStart_8377984 baseEnd_8377984 := by
    simpa [prefixWord, tailWord_8377984, baseEnd_8377984] using wordTrace_append hprefix tailTrace_8377984
  have hstable : (prefixWord ++ tailWord_8377984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377984).length < 2 ^ (prefixWord ++ tailWord_8377984).sum := by decide
  have hdescent : baseEnd_8377984 < baseStart_8377984 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8377992 : List Nat := [2, 1, 3, 5, 1, 1, 3, 2, 1, 2, 2]
def baseStart_8377992 : Nat := 118140960795 + 8377992 * 2 ^ 59
def prefixEnd_8377992 : Nat := 4983230072969 + 3 ^ 40 * 8377992 * 2
def baseEnd_8377992 : Nat := 4301936815523090301470323

theorem tailTrace_8377992 : CollatzResearch.WordTrace tailWord_8377992 prefixEnd_8377992 4301936815523090301470323 := by
  unfold tailWord_8377992
  simp only [CollatzResearch.WordTrace]
  refine ⟨152785235931986652981576115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203713647909315537308768153 152785235931986652981576115)
  ·
    refine ⟨229177853897979979472364173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152785235931986652981576115 229177853897979979472364173)
    ·
      refine ⟨85941695211742492302136565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229177853897979979472364173 85941695211742492302136565)
      ·
        refine ⟨8057033926100858653325303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85941695211742492302136565 8057033926100858653325303)
        ·
          refine ⟨12085550889151287979987955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8057033926100858653325303 12085550889151287979987955)
          ·
            refine ⟨18128326333726931969981933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12085550889151287979987955 18128326333726931969981933)
            ·
              refine ⟨6798122375147599488743225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18128326333726931969981933 6798122375147599488743225)
              ·
                refine ⟨5098591781360699616557419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6798122375147599488743225 5098591781360699616557419)
                ·
                  refine ⟨7647887672041049424836129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5098591781360699616557419 7647887672041049424836129)
                  ·
                    refine ⟨5735915754030787068627097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7647887672041049424836129 5735915754030787068627097)
                    ·
                      refine ⟨4301936815523090301470323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5735915754030787068627097 4301936815523090301470323)
                      ·
                        rfl

theorem cell23_8377992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_8377992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8377992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8377992 prefixEnd_8377992 := by exact prefixLift 8377992
  have htrace : WordTrace (prefixWord ++ tailWord_8377992) baseStart_8377992 baseEnd_8377992 := by
    simpa [prefixWord, tailWord_8377992, baseEnd_8377992] using wordTrace_append hprefix tailTrace_8377992
  have hstable : (prefixWord ++ tailWord_8377992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8377992).length < 2 ^ (prefixWord ++ tailWord_8377992).sum := by decide
  have hdescent : baseEnd_8377992 < baseStart_8377992 := by decide
  rcases family_descends (prefixWord ++ tailWord_8377992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378008 : List Nat := [2, 1, 2, 4, 1, 4, 2, 1, 2, 1, 3]
def baseStart_8378008 : Nat := 118140960795 + 8378008 * 2 ^ 59
def prefixEnd_8378008 : Nat := 4983230072969 + 3 ^ 40 * 8378008 * 2
def baseEnd_8378008 : Nat := 4301945031213562238870249

theorem tailTrace_8378008 : CollatzResearch.WordTrace tailWord_8378008 prefixEnd_8378008 4301945031213562238870249 := by
  unfold tailWord_8378008
  simp only [CollatzResearch.WordTrace]
  refine ⟨152785527715957670347867339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203714036954610227130489785 152785527715957670347867339)
  ·
    refine ⟨229178291573936505521801009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152785527715957670347867339 229178291573936505521801009)
    ·
      refine ⟨171883718680452379141350757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229178291573936505521801009 171883718680452379141350757)
      ·
        refine ⟨32228197252584821089003267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171883718680452379141350757 32228197252584821089003267)
        ·
          refine ⟨48342295878877231633504901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32228197252584821089003267 48342295878877231633504901)
          ·
            refine ⟨9064180477289480931282169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48342295878877231633504901 9064180477289480931282169)
            ·
              refine ⟨6798135357967110698461627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9064180477289480931282169 6798135357967110698461627)
              ·
                refine ⟨10197203036950666047692441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6798135357967110698461627 10197203036950666047692441)
                ·
                  refine ⟨7647902277712999535769331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10197203036950666047692441 7647902277712999535769331)
                  ·
                    refine ⟨11471853416569499303653997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7647902277712999535769331 11471853416569499303653997)
                    ·
                      refine ⟨4301945031213562238870249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11471853416569499303653997 4301945031213562238870249)
                      ·
                        rfl

theorem cell23_8378008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_8378008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378008 prefixEnd_8378008 := by exact prefixLift 8378008
  have htrace : WordTrace (prefixWord ++ tailWord_8378008) baseStart_8378008 baseEnd_8378008 := by
    simpa [prefixWord, tailWord_8378008, baseEnd_8378008] using wordTrace_append hprefix tailTrace_8378008
  have hstable : (prefixWord ++ tailWord_8378008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378008).length < 2 ^ (prefixWord ++ tailWord_8378008).sum := by decide
  have hdescent : baseEnd_8378008 < baseStart_8378008 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378017 : List Nat := [1, 2, 3, 3, 2, 1, 1, 2, 2, 1, 5]
def baseStart_8378017 : Nat := 118140960795 + 8378017 * 2 ^ 59
def prefixEnd_8378017 : Nat := 4983230072969 + 3 ^ 40 * 8378017 * 2
def baseEnd_8378017 : Nat := 4301949652539452703657707

theorem tailTrace_8378017 : CollatzResearch.WordTrace tailWord_8378017 prefixEnd_8378017 4301949652539452703657707 := by
  unfold tailWord_8378017
  simp only [CollatzResearch.WordTrace]
  refine ⟨305571383688882735232812305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203714255792588490155208203 305571383688882735232812305)
  ·
    refine ⟨229178537766662051424609229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305571383688882735232812305 229178537766662051424609229)
    ·
      refine ⟨85941951662498269284228461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229178537766662051424609229 85941951662498269284228461)
      ·
        refine ⟨32228231873436850981585673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85941951662498269284228461 32228231873436850981585673)
        ·
          refine ⟨24171173905077638236189255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32228231873436850981585673 24171173905077638236189255)
          ·
            refine ⟨36256760857616457354283883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24171173905077638236189255 36256760857616457354283883)
            ·
              refine ⟨54385141286424686031425825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36256760857616457354283883 54385141286424686031425825)
              ·
                refine ⟨40788855964818514523569369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54385141286424686031425825 40788855964818514523569369)
                ·
                  refine ⟨30591641973613885892677027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40788855964818514523569369 30591641973613885892677027)
                  ·
                    refine ⟨45887462960420828839015541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30591641973613885892677027 45887462960420828839015541)
                    ·
                      refine ⟨4301949652539452703657707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45887462960420828839015541 4301949652539452703657707)
                      ·
                        rfl

theorem cell23_8378017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_8378017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378017 prefixEnd_8378017 := by exact prefixLift 8378017
  have htrace : WordTrace (prefixWord ++ tailWord_8378017) baseStart_8378017 baseEnd_8378017 := by
    simpa [prefixWord, tailWord_8378017, baseEnd_8378017] using wordTrace_append hprefix tailTrace_8378017
  have hstable : (prefixWord ++ tailWord_8378017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378017).length < 2 ^ (prefixWord ++ tailWord_8378017).sum := by decide
  have hdescent : baseEnd_8378017 < baseStart_8378017 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378018 : List Nat := [3, 3, 1, 4, 1, 1, 1, 1, 3, 3, 2]
def baseStart_8378018 : Nat := 118140960795 + 8378018 * 2 ^ 59
def prefixEnd_8378018 : Nat := 4983230072969 + 3 ^ 40 * 8378018 * 2
def baseEnd_8378018 : Nat := 4301950166020107199745203

theorem tailTrace_8378018 : CollatzResearch.WordTrace tailWord_8378018 prefixEnd_8378018 4301950166020107199745203 := by
  unfold tailWord_8378018
  simp only [CollatzResearch.WordTrace]
  refine ⟨76392855040469778100899677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203714280107919408269065805 76392855040469778100899677)
  ·
    refine ⟨28647320640176166787837379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76392855040469778100899677 28647320640176166787837379)
    ·
      refine ⟨42970980960264250181756069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28647320640176166787837379 42970980960264250181756069)
      ·
        refine ⟨8057058930049546909079263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42970980960264250181756069 8057058930049546909079263)
        ·
          refine ⟨12085588395074320363618895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8057058930049546909079263 12085588395074320363618895)
          ·
            refine ⟨18128382592611480545428343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12085588395074320363618895 18128382592611480545428343)
            ·
              refine ⟨27192573888917220818142515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18128382592611480545428343 27192573888917220818142515)
              ·
                refine ⟨40788860833375831227213773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27192573888917220818142515 40788860833375831227213773)
                ·
                  refine ⟨15295822812515936710205165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40788860833375831227213773 15295822812515936710205165)
                  ·
                    refine ⟨5735933554693476266326937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15295822812515936710205165 5735933554693476266326937)
                    ·
                      refine ⟨4301950166020107199745203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5735933554693476266326937 4301950166020107199745203)
                      ·
                        rfl

theorem cell23_8378018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_8378018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378018 prefixEnd_8378018 := by exact prefixLift 8378018
  have htrace : WordTrace (prefixWord ++ tailWord_8378018) baseStart_8378018 baseEnd_8378018 := by
    simpa [prefixWord, tailWord_8378018, baseEnd_8378018] using wordTrace_append hprefix tailTrace_8378018
  have hstable : (prefixWord ++ tailWord_8378018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378018).length < 2 ^ (prefixWord ++ tailWord_8378018).sum := by decide
  have hdescent : baseEnd_8378018 < baseStart_8378018 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378047 : List Nat := [1, 1, 2, 2, 2, 3, 2, 2, 2, 3, 3]
def baseStart_8378047 : Nat := 118140960795 + 8378047 * 2 ^ 59
def prefixEnd_8378047 : Nat := 4983230072969 + 3 ^ 40 * 8378047 * 2
def baseEnd_8378047 : Nat := 4301965056959087586282569

theorem tailTrace_8378047 : CollatzResearch.WordTrace tailWord_8378047 prefixEnd_8378047 4301965056959087586282569 := by
  unfold tailWord_8378047
  simp only [CollatzResearch.WordTrace]
  refine ⟨305572477878774050356404395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203714985252516033570936263 305572477878774050356404395)
  ·
    refine ⟨458358716818161075534606593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305572477878774050356404395 458358716818161075534606593)
    ·
      refine ⟨343769037613620806650954945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458358716818161075534606593 343769037613620806650954945)
      ·
        refine ⟨257826778210215604988216209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343769037613620806650954945 257826778210215604988216209)
        ·
          refine ⟨193370083657661703741162157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257826778210215604988216209 193370083657661703741162157)
          ·
            refine ⟨72513781371623138902935809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193370083657661703741162157 72513781371623138902935809)
            ·
              refine ⟨54385336028717354177201857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72513781371623138902935809 54385336028717354177201857)
              ·
                refine ⟨40789002021538015632901393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54385336028717354177201857 40789002021538015632901393)
                ·
                  refine ⟨30591751516153511724676045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40789002021538015632901393 30591751516153511724676045)
                  ·
                    refine ⟨11471906818557566896753517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30591751516153511724676045 11471906818557566896753517)
                    ·
                      refine ⟨4301965056959087586282569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11471906818557566896753517 4301965056959087586282569)
                      ·
                        rfl

theorem cell23_8378047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 3, 3].length) (baseStart_8378047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378047 prefixEnd_8378047 := by exact prefixLift 8378047
  have htrace : WordTrace (prefixWord ++ tailWord_8378047) baseStart_8378047 baseEnd_8378047 := by
    simpa [prefixWord, tailWord_8378047, baseEnd_8378047] using wordTrace_append hprefix tailTrace_8378047
  have hstable : (prefixWord ++ tailWord_8378047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378047).length < 2 ^ (prefixWord ++ tailWord_8378047).sum := by decide
  have hdescent : baseEnd_8378047 < baseStart_8378047 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378061 : List Nat := [1, 6, 2, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_8378061 : Nat := 118140960795 + 8378061 * 2 ^ 59
def prefixEnd_8378061 : Nat := 4983230072969 + 3 ^ 40 * 8378061 * 2
def baseEnd_8378061 : Nat := 4301972245688250531507505

theorem tailTrace_8378061 : CollatzResearch.WordTrace tailWord_8378061 prefixEnd_8378061 4301972245688250531507505 := by
  unfold tailWord_8378061
  simp only [CollatzResearch.WordTrace]
  refine ⟨305572988500723330747414037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203715325667148887164942691 305572988500723330747414037)
  ·
    refine ⟨14323733835971406128785033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 305572988500723330747414037 14323733835971406128785033)
    ·
      refine ⟨10742800376978554596588775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14323733835971406128785033 10742800376978554596588775)
      ·
        refine ⟨16114200565467831894883163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10742800376978554596588775 16114200565467831894883163)
        ·
          refine ⟨24171300848201747842324745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16114200565467831894883163 24171300848201747842324745)
          ·
            refine ⟨18128475636151310881743559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24171300848201747842324745 18128475636151310881743559)
            ·
              refine ⟨27192713454226966322615339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18128475636151310881743559 27192713454226966322615339)
              ·
                refine ⟨40789070181340449483923009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27192713454226966322615339 40789070181340449483923009)
                ·
                  refine ⟨30591802636005337112942257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40789070181340449483923009 30591802636005337112942257)
                  ·
                    refine ⟨22943851977004002834706693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30591802636005337112942257 22943851977004002834706693)
                    ·
                      refine ⟨4301972245688250531507505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22943851977004002834706693 4301972245688250531507505)
                      ·
                        rfl

theorem cell23_8378061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_8378061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378061 prefixEnd_8378061 := by exact prefixLift 8378061
  have htrace : WordTrace (prefixWord ++ tailWord_8378061) baseStart_8378061 baseEnd_8378061 := by
    simpa [prefixWord, tailWord_8378061, baseEnd_8378061] using wordTrace_append hprefix tailTrace_8378061
  have hstable : (prefixWord ++ tailWord_8378061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378061).length < 2 ^ (prefixWord ++ tailWord_8378061).sum := by decide
  have hdescent : baseEnd_8378061 < baseStart_8378061 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378148 : List Nat := [2, 3, 1, 3, 2, 1, 3, 3, 1, 4]
def baseStart_8378148 : Nat := 118140960795 + 8378148 * 2 ^ 59
def prefixEnd_8378148 : Nat := 4983230072969 + 3 ^ 40 * 8378148 * 2
def baseEnd_8378148 : Nat := 1434005639501730563706535

theorem tailTrace_8378148 : CollatzResearch.WordTrace tailWord_8378148 prefixEnd_8378148 1434005639501730563706535 := by
  unfold tailWord_8378148
  simp only [CollatzResearch.WordTrace]
  refine ⟨152788080825704072302915549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203717441100938763070554065 152788080825704072302915549)
  ·
    refine ⟨57295530309639027113593331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152788080825704072302915549 57295530309639027113593331)
    ·
      refine ⟨85943295464458540670389997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57295530309639027113593331 85943295464458540670389997)
      ·
        refine ⟨32228735799171952751396249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85943295464458540670389997 32228735799171952751396249)
        ·
          refine ⟨24171551849378964563547187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32228735799171952751396249 24171551849378964563547187)
          ·
            refine ⟨36257327774068446845320781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24171551849378964563547187 36257327774068446845320781)
            ·
              refine ⟨13596497915275667566995293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36257327774068446845320781 13596497915275667566995293)
              ·
                refine ⟨5098686718228375337623235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13596497915275667566995293 5098686718228375337623235)
                ·
                  refine ⟨7648030077342563006434853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5098686718228375337623235 7648030077342563006434853)
                  ·
                    refine ⟨1434005639501730563706535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7648030077342563006434853 1434005639501730563706535)
                    ·
                      rfl

theorem cell23_8378148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_8378148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378148 prefixEnd_8378148 := by exact prefixLift 8378148
  have htrace : WordTrace (prefixWord ++ tailWord_8378148) baseStart_8378148 baseEnd_8378148 := by
    simpa [prefixWord, tailWord_8378148, baseEnd_8378148] using wordTrace_append hprefix tailTrace_8378148
  have hstable : (prefixWord ++ tailWord_8378148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378148).length < 2 ^ (prefixWord ++ tailWord_8378148).sum := by decide
  have hdescent : baseEnd_8378148 < baseStart_8378148 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378158 : List Nat := [4, 1, 3, 2, 2, 1, 1, 2, 2, 2, 3]
def baseStart_8378158 : Nat := 118140960795 + 8378158 * 2 ^ 59
def prefixEnd_8378158 : Nat := 4983230072969 + 3 ^ 40 * 8378158 * 2
def baseEnd_8378158 : Nat := 4302022053311736651994559

theorem tailTrace_8378158 : CollatzResearch.WordTrace tailWord_8378158 prefixEnd_8378158 4302022053311736651994559 := by
  unfold tailWord_8378158
  simp only [CollatzResearch.WordTrace]
  refine ⟨38197065797671489539211891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203717684254247944209130085 38197065797671489539211891)
  ·
    refine ⟨57295598696507234308817837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38197065797671489539211891 57295598696507234308817837)
    ·
      refine ⟨21485849511190212865806689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57295598696507234308817837 21485849511190212865806689)
      ·
        refine ⟨16114387133392659649355017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21485849511190212865806689 16114387133392659649355017)
        ·
          refine ⟨12085790350044494737016263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16114387133392659649355017 12085790350044494737016263)
          ·
            refine ⟨18128685525066742105524395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12085790350044494737016263 18128685525066742105524395)
            ·
              refine ⟨27193028287600113158286593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18128685525066742105524395 27193028287600113158286593)
              ·
                refine ⟨20394771215700084868714945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27193028287600113158286593 20394771215700084868714945)
                ·
                  refine ⟨15296078411775063651536209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20394771215700084868714945 15296078411775063651536209)
                  ·
                    refine ⟨11472058808831297738652157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15296078411775063651536209 11472058808831297738652157)
                    ·
                      refine ⟨4302022053311736651994559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11472058808831297738652157 4302022053311736651994559)
                      ·
                        rfl

theorem cell23_8378158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_8378158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378158 prefixEnd_8378158 := by exact prefixLift 8378158
  have htrace : WordTrace (prefixWord ++ tailWord_8378158) baseStart_8378158 baseEnd_8378158 := by
    simpa [prefixWord, tailWord_8378158, baseEnd_8378158] using wordTrace_append hprefix tailTrace_8378158
  have hstable : (prefixWord ++ tailWord_8378158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378158).length < 2 ^ (prefixWord ++ tailWord_8378158).sum := by decide
  have hdescent : baseEnd_8378158 < baseStart_8378158 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378165 : List Nat := [1, 3, 3, 1, 4, 1, 3, 2, 1, 4]
def baseStart_8378165 : Nat := 118140960795 + 8378165 * 2 ^ 59
def prefixEnd_8378165 : Nat := 4983230072969 + 3 ^ 40 * 8378165 * 2
def baseEnd_8378165 : Nat := 1434008549225439374869009

theorem tailTrace_8378165 : CollatzResearch.WordTrace tailWord_8378165 prefixEnd_8378165 1434008549225439374869009 := by
  unfold tailWord_8378165
  simp only [CollatzResearch.WordTrace]
  refine ⟨305576781692346556509199949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203717854461564371006133299 305576781692346556509199949)
  ·
    refine ⟨114591293134629958690949981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305576781692346556509199949 114591293134629958690949981)
    ·
      refine ⟨42971734925486234509106243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114591293134629958690949981 42971734925486234509106243)
      ·
        refine ⟨64457602388229351763659365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42971734925486234509106243 64457602388229351763659365)
        ·
          refine ⟨12085800447793003455686131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64457602388229351763659365 12085800447793003455686131)
          ·
            refine ⟨18128700671689505183529197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12085800447793003455686131 18128700671689505183529197)
            ·
              refine ⟨6798262751883564443823449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18128700671689505183529197 6798262751883564443823449)
              ·
                refine ⟨5098697063912673332867587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6798262751883564443823449 5098697063912673332867587)
                ·
                  refine ⟨7648045595869009999301381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5098697063912673332867587 7648045595869009999301381)
                  ·
                    refine ⟨1434008549225439374869009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7648045595869009999301381 1434008549225439374869009)
                    ·
                      rfl

theorem cell23_8378165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_8378165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378165 prefixEnd_8378165 := by exact prefixLift 8378165
  have htrace : WordTrace (prefixWord ++ tailWord_8378165) baseStart_8378165 baseEnd_8378165 := by
    simpa [prefixWord, tailWord_8378165, baseEnd_8378165] using wordTrace_append hprefix tailTrace_8378165
  have hstable : (prefixWord ++ tailWord_8378165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378165).length < 2 ^ (prefixWord ++ tailWord_8378165).sum := by decide
  have hdescent : baseEnd_8378165 < baseStart_8378165 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378221 : List Nat := [1, 5, 1, 1, 1, 1, 3, 4, 2, 4]
def baseStart_8378221 : Nat := 118140960795 + 8378221 * 2 ^ 59
def prefixEnd_8378221 : Nat := 4983230072969 + 3 ^ 40 * 8378221 * 2
def baseEnd_8378221 : Nat := 1434018134197656635168923

theorem tailTrace_8378221 : CollatzResearch.WordTrace tailWord_8378221 prefixEnd_8378221 1434018134197656635168923 := by
  unfold tailWord_8378221
  simp only [CollatzResearch.WordTrace]
  refine ⟨305578824180143678073238517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203719216120095785382159011 305578824180143678073238517)
  ·
    refine ⟨28648014766888469819366111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 305578824180143678073238517 28648014766888469819366111)
    ·
      refine ⟨42972022150332704729049167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28648014766888469819366111 42972022150332704729049167)
      ·
        refine ⟨64458033225499057093573751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42972022150332704729049167 64458033225499057093573751)
        ·
          refine ⟨96687049838248585640360627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64458033225499057093573751 96687049838248585640360627)
          ·
            refine ⟨145030574757372878460540941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96687049838248585640360627 145030574757372878460540941)
            ·
              refine ⟨54386465534014829422702853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145030574757372878460540941 54386465534014829422702853)
              ·
                refine ⟨10197462287627780516756785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54386465534014829422702853 10197462287627780516756785)
                ·
                  refine ⟨7648096715720835387567589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10197462287627780516756785 7648096715720835387567589)
                  ·
                    refine ⟨1434018134197656635168923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7648096715720835387567589 1434018134197656635168923)
                    ·
                      rfl

theorem cell23_8378221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_8378221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378221 prefixEnd_8378221 := by exact prefixLift 8378221
  have htrace : WordTrace (prefixWord ++ tailWord_8378221) baseStart_8378221 baseEnd_8378221 := by
    simpa [prefixWord, tailWord_8378221, baseEnd_8378221] using wordTrace_append hprefix tailTrace_8378221
  have hstable : (prefixWord ++ tailWord_8378221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378221).length < 2 ^ (prefixWord ++ tailWord_8378221).sum := by decide
  have hdescent : baseEnd_8378221 < baseStart_8378221 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378222 : List Nat := [4, 1, 2, 3, 1, 1, 4, 2, 1, 1, 3]
def baseStart_8378222 : Nat := 118140960795 + 8378222 * 2 ^ 59
def prefixEnd_8378222 : Nat := 4983230072969 + 3 ^ 40 * 8378222 * 2
def baseEnd_8378222 : Nat := 4302054916073624401594265

theorem tailTrace_8378222 : CollatzResearch.WordTrace tailWord_8378222 prefixEnd_8378222 4302054916073624401594265 := by
  unfold tailWord_8378222
  simp only [CollatzResearch.WordTrace]
  refine ⟨38197357581642506905503115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203719240435426703496016613 38197357581642506905503115)
  ·
    refine ⟨57296036372463760358254673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38197357581642506905503115 57296036372463760358254673)
    ·
      refine ⟨42972027279347820268691005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57296036372463760358254673 42972027279347820268691005)
      ·
        refine ⟨16114510229755432600759127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42972027279347820268691005 16114510229755432600759127)
        ·
          refine ⟨24171765344633148901138691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16114510229755432600759127 24171765344633148901138691)
          ·
            refine ⟨36257648016949723351708037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24171765344633148901138691 36257648016949723351708037)
            ·
              refine ⟨6798309003178073128445257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36257648016949723351708037 6798309003178073128445257)
              ·
                refine ⟨5098731752383554846333943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6798309003178073128445257 5098731752383554846333943)
                ·
                  refine ⟨7648097628575332269500915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5098731752383554846333943 7648097628575332269500915)
                  ·
                    refine ⟨11472146442862998404251373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7648097628575332269500915 11472146442862998404251373)
                    ·
                      refine ⟨4302054916073624401594265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11472146442862998404251373 4302054916073624401594265)
                      ·
                        rfl

theorem cell23_8378222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_8378222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378222 prefixEnd_8378222 := by exact prefixLift 8378222
  have htrace : WordTrace (prefixWord ++ tailWord_8378222) baseStart_8378222 baseEnd_8378222 := by
    simpa [prefixWord, tailWord_8378222, baseEnd_8378222] using wordTrace_append hprefix tailTrace_8378222
  have hstable : (prefixWord ++ tailWord_8378222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378222).length < 2 ^ (prefixWord ++ tailWord_8378222).sum := by decide
  have hdescent : baseEnd_8378222 < baseStart_8378222 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378238 : List Nat := [4, 2, 3, 1, 1, 2, 2, 1, 1, 6]
def baseStart_8378238 : Nat := 118140960795 + 8378238 * 2 ^ 59
def prefixEnd_8378238 : Nat := 4983230072969 + 3 ^ 40 * 8378238 * 2
def baseEnd_8378238 : Nat := 1434021043921365446331397

theorem tailTrace_8378238 : CollatzResearch.WordTrace tailWord_8378238 prefixEnd_8378238 1434021043921365446331397 := by
  unfold tailWord_8378238
  simp only [CollatzResearch.WordTrace]
  refine ⟨38197430527635261247075921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203719629480721393317738245 38197430527635261247075921)
  ·
    refine ⟨28648072895726445935306941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38197430527635261247075921 28648072895726445935306941)
    ·
      refine ⟨10743027335897417225740103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28648072895726445935306941 10743027335897417225740103)
      ·
        refine ⟨16114541003846125838610155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10743027335897417225740103 16114541003846125838610155)
        ·
          refine ⟨24171811505769188757915233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16114541003846125838610155 24171811505769188757915233)
          ·
            refine ⟨18128858629326891568436425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24171811505769188757915233 18128858629326891568436425)
            ·
              refine ⟨13596643971995168676327319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18128858629326891568436425 13596643971995168676327319)
              ·
                refine ⟨20394965957992753014490979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13596643971995168676327319 20394965957992753014490979)
                ·
                  refine ⟨30592448936989129521736469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20394965957992753014490979 30592448936989129521736469)
                  ·
                    refine ⟨1434021043921365446331397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30592448936989129521736469 1434021043921365446331397)
                    ·
                      rfl

theorem cell23_8378238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_8378238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378238 prefixEnd_8378238 := by exact prefixLift 8378238
  have htrace : WordTrace (prefixWord ++ tailWord_8378238) baseStart_8378238 baseEnd_8378238 := by
    simpa [prefixWord, tailWord_8378238, baseEnd_8378238] using wordTrace_append hprefix tailTrace_8378238
  have hstable : (prefixWord ++ tailWord_8378238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378238).length < 2 ^ (prefixWord ++ tailWord_8378238).sum := by decide
  have hdescent : baseEnd_8378238 < baseStart_8378238 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378261 : List Nat := [1, 3, 2, 1, 1, 3, 2, 2, 4, 1, 3]
def baseStart_8378261 : Nat := 118140960795 + 8378261 * 2 ^ 59
def prefixEnd_8378261 : Nat := 4983230072969 + 3 ^ 40 * 8378261 * 2
def baseEnd_8378261 : Nat := 4302074941819149749006585

theorem tailTrace_8378261 : CollatzResearch.WordTrace tailWord_8378261 prefixEnd_8378261 4302074941819149749006585 := by
  unfold tailWord_8378261
  simp only [CollatzResearch.WordTrace]
  refine ⟨305580283099998764904694637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203720188733332509936463091 305580283099998764904694637)
  ·
    refine ⟨114592606162499536839260489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305580283099998764904694637 114592606162499536839260489)
    ·
      refine ⟨85944454621874652629445367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114592606162499536839260489 85944454621874652629445367)
      ·
        refine ⟨128916681932811978944168051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85944454621874652629445367 128916681932811978944168051)
        ·
          refine ⟨193375022899217968416252077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128916681932811978944168051 193375022899217968416252077)
          ·
            refine ⟨72515633587206738156094529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193375022899217968416252077 72515633587206738156094529)
            ·
              refine ⟨54386725190405053617070897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72515633587206738156094529 54386725190405053617070897)
              ·
                refine ⟨40790043892803790212803173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54386725190405053617070897 40790043892803790212803173)
                ·
                  refine ⟨7648133229900710664900595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40790043892803790212803173 7648133229900710664900595)
                  ·
                    refine ⟨11472199844851065997350893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7648133229900710664900595 11472199844851065997350893)
                    ·
                      refine ⟨4302074941819149749006585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11472199844851065997350893 4302074941819149749006585)
                      ·
                        rfl

theorem cell23_8378261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_8378261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378261 prefixEnd_8378261 := by exact prefixLift 8378261
  have htrace : WordTrace (prefixWord ++ tailWord_8378261) baseStart_8378261 baseEnd_8378261 := by
    simpa [prefixWord, tailWord_8378261, baseEnd_8378261] using wordTrace_append hprefix tailTrace_8378261
  have hstable : (prefixWord ++ tailWord_8378261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378261).length < 2 ^ (prefixWord ++ tailWord_8378261).sum := by decide
  have hdescent : baseEnd_8378261 < baseStart_8378261 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378262 : List Nat := [5, 3, 1, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_8378262 : Nat := 118140960795 + 8378262 * 2 ^ 59
def prefixEnd_8378262 : Nat := 4983230072969 + 3 ^ 40 * 8378262 * 2
def baseEnd_8378262 : Nat := 4302075455299804245094081

theorem tailTrace_8378262 : CollatzResearch.WordTrace tailWord_8378262 prefixEnd_8378262 4302075455299804245094081 := by
  unfold tailWord_8378262
  simp only [CollatzResearch.WordTrace]
  refine ⟨19098769973312196379717565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203720213048663428050320693 19098769973312196379717565)
  ·
    refine ⟨7162038739992073642394087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19098769973312196379717565 7162038739992073642394087)
    ·
      refine ⟨10743058109988110463591131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7162038739992073642394087 10743058109988110463591131)
      ·
        refine ⟨16114587164982165695386697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10743058109988110463591131 16114587164982165695386697)
        ·
          refine ⟨12085940373736624271540023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16114587164982165695386697 12085940373736624271540023)
          ·
            refine ⟨18128910560604936407310035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12085940373736624271540023 18128910560604936407310035)
            ·
              refine ⟨27193365840907404610965053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18128910560604936407310035 27193365840907404610965053)
              ·
                refine ⟨10197512190340276729111895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27193365840907404610965053 10197512190340276729111895)
                ·
                  refine ⟨15296268285510415093667843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10197512190340276729111895 15296268285510415093667843)
                  ·
                    refine ⟨22944402428265622640501765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15296268285510415093667843 22944402428265622640501765)
                    ·
                      refine ⟨4302075455299804245094081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22944402428265622640501765 4302075455299804245094081)
                      ·
                        rfl

theorem cell23_8378262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_8378262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378262 prefixEnd_8378262 := by exact prefixLift 8378262
  have htrace : WordTrace (prefixWord ++ tailWord_8378262) baseStart_8378262 baseEnd_8378262 := by
    simpa [prefixWord, tailWord_8378262, baseEnd_8378262] using wordTrace_append hprefix tailTrace_8378262
  have hstable : (prefixWord ++ tailWord_8378262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378262).length < 2 ^ (prefixWord ++ tailWord_8378262).sum := by decide
  have hdescent : baseEnd_8378262 < baseStart_8378262 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378292 : List Nat := [2, 5, 2, 1, 3, 1, 1, 1, 1, 2, 4]
def baseStart_8378292 : Nat := 118140960795 + 8378292 * 2 ^ 59
def prefixEnd_8378292 : Nat := 4983230072969 + 3 ^ 40 * 8378292 * 2
def baseEnd_8378292 : Nat := 4302090859719439127718943

theorem tailTrace_8378292 : CollatzResearch.WordTrace tailWord_8378292 prefixEnd_8378292 4302090859719439127718943 := by
  unfold tailWord_8378292
  simp only [CollatzResearch.WordTrace]
  refine ⟨152790706881443228599536565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203720942508590971466048753 152790706881443228599536565)
  ·
    refine ⟨14324128770135302681206553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152790706881443228599536565 14324128770135302681206553)
    ·
      refine ⟨10743096577601477010904915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14324128770135302681206553 10743096577601477010904915)
      ·
        refine ⟨16114644866402215516357373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10743096577601477010904915 16114644866402215516357373)
        ·
          refine ⟨6042991824900830818634015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16114644866402215516357373 6042991824900830818634015)
          ·
            refine ⟨9064487737351246227951023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6042991824900830818634015 9064487737351246227951023)
            ·
              refine ⟨13596731606026869341926535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9064487737351246227951023 13596731606026869341926535)
              ·
                refine ⟨20395097409040304012889803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13596731606026869341926535 20395097409040304012889803)
                ·
                  refine ⟨30592646113560456019334705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20395097409040304012889803 30592646113560456019334705)
                  ·
                    refine ⟨22944484585170342014501029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30592646113560456019334705 22944484585170342014501029)
                    ·
                      refine ⟨4302090859719439127718943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22944484585170342014501029 4302090859719439127718943)
                      ·
                        rfl

theorem cell23_8378292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_8378292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378292 prefixEnd_8378292 := by exact prefixLift 8378292
  have htrace : WordTrace (prefixWord ++ tailWord_8378292) baseStart_8378292 baseEnd_8378292 := by
    simpa [prefixWord, tailWord_8378292, baseEnd_8378292] using wordTrace_append hprefix tailTrace_8378292
  have hstable : (prefixWord ++ tailWord_8378292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378292).length < 2 ^ (prefixWord ++ tailWord_8378292).sum := by decide
  have hdescent : baseEnd_8378292 < baseStart_8378292 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378304 : List Nat := [2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 5]
def baseStart_8378304 : Nat := 118140960795 + 8378304 * 2 ^ 59
def prefixEnd_8378304 : Nat := 4983230072969 + 3 ^ 40 * 8378304 * 2
def baseEnd_8378304 : Nat := 4302097021487293080768887

theorem tailTrace_8378304 : CollatzResearch.WordTrace tailWord_8378304 prefixEnd_8378304 4302097021487293080768887 := by
  unfold tailWord_8378304
  simp only [CollatzResearch.WordTrace]
  refine ⟨152790925719421491624254983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203721234292561988832339977 152790925719421491624254983)
  ·
    refine ⟨229186388579132237436382475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152790925719421491624254983 229186388579132237436382475)
    ·
      refine ⟨343779582868698356154573713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229186388579132237436382475 343779582868698356154573713)
      ·
        refine ⟨257834687151523767115930285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343779582868698356154573713 257834687151523767115930285)
        ·
          refine ⟨96688007681821412668473857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257834687151523767115930285 96688007681821412668473857)
          ·
            refine ⟨72516005761366059501355393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96688007681821412668473857 72516005761366059501355393)
            ·
              refine ⟨54387004321024544626016545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72516005761366059501355393 54387004321024544626016545)
              ·
                refine ⟨40790253240768408469512409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54387004321024544626016545 40790253240768408469512409)
                ·
                  refine ⟨30592689930576306352134307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40790253240768408469512409 30592689930576306352134307)
                  ·
                    refine ⟨45889034895864459528201461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30592689930576306352134307 45889034895864459528201461)
                    ·
                      refine ⟨4302097021487293080768887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45889034895864459528201461 4302097021487293080768887)
                      ·
                        rfl

theorem cell23_8378304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_8378304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378304 prefixEnd_8378304 := by exact prefixLift 8378304
  have htrace : WordTrace (prefixWord ++ tailWord_8378304) baseStart_8378304 baseEnd_8378304 := by
    simpa [prefixWord, tailWord_8378304, baseEnd_8378304] using wordTrace_append hprefix tailTrace_8378304
  have hstable : (prefixWord ++ tailWord_8378304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378304).length < 2 ^ (prefixWord ++ tailWord_8378304).sum := by decide
  have hdescent : baseEnd_8378304 < baseStart_8378304 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378314 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 1, 4, 4]
def baseStart_8378314 : Nat := 118140960795 + 8378314 * 2 ^ 59
def prefixEnd_8378314 : Nat := 4983230072969 + 3 ^ 40 * 8378314 * 2
def baseEnd_8378314 : Nat := 4302102156293838041643841

theorem tailTrace_8378314 : CollatzResearch.WordTrace tailWord_8378314 prefixEnd_8378314 4302102156293838041643841 := by
  unfold tailWord_8378314
  simp only [CollatzResearch.WordTrace]
  refine ⟨76395554042201688739093499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203721477445871169970915997 76395554042201688739093499)
  ·
    refine ⟨114593331063302533108640249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76395554042201688739093499 114593331063302533108640249)
    ·
      refine ⟨85944998297476899831480187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114593331063302533108640249 85944998297476899831480187)
      ·
        refine ⟨128917497446215349747220281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85944998297476899831480187 128917497446215349747220281)
        ·
          refine ⟨96688123084661512310415211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128917497446215349747220281 96688123084661512310415211)
          ·
            refine ⟨145032184626992268465622817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96688123084661512310415211 145032184626992268465622817)
            ·
              refine ⟨108774138470244201349217113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145032184626992268465622817 108774138470244201349217113)
              ·
                refine ⟨81580603852683151011912835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108774138470244201349217113 81580603852683151011912835)
                ·
                  refine ⟨122370905779024726517869253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81580603852683151011912835 122370905779024726517869253)
                  ·
                    refine ⟨22944544833567136222100485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 122370905779024726517869253 22944544833567136222100485)
                    ·
                      refine ⟨4302102156293838041643841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22944544833567136222100485 4302102156293838041643841)
                      ·
                        rfl

theorem cell23_8378314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_8378314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378314 prefixEnd_8378314 := by exact prefixLift 8378314
  have htrace : WordTrace (prefixWord ++ tailWord_8378314) baseStart_8378314 baseEnd_8378314 := by
    simpa [prefixWord, tailWord_8378314, baseEnd_8378314] using wordTrace_append hprefix tailTrace_8378314
  have hstable : (prefixWord ++ tailWord_8378314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378314).length < 2 ^ (prefixWord ++ tailWord_8378314).sum := by decide
  have hdescent : baseEnd_8378314 < baseStart_8378314 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378318 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2]
def baseStart_8378318 : Nat := 118140960795 + 8378318 * 2 ^ 59
def prefixEnd_8378318 : Nat := 4983230072969 + 3 ^ 40 * 8378318 * 2
def baseEnd_8378318 : Nat := 4302104210216456025993823

theorem tailTrace_8378318 : CollatzResearch.WordTrace tailWord_8378318 prefixEnd_8378318 4302104210216456025993823 := by
  unfold tailWord_8378318
  simp only [CollatzResearch.WordTrace]
  refine ⟨38197795257599032954939951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203721574707194842426346405 38197795257599032954939951)
  ·
    refine ⟨57296692886398549432409927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38197795257599032954939951 57296692886398549432409927)
    ·
      refine ⟨85945039329597824148614891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57296692886398549432409927 85945039329597824148614891)
      ·
        refine ⟨128917558994396736222922337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85945039329597824148614891 128917558994396736222922337)
        ·
          refine ⟨96688169245797552167191753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128917558994396736222922337 96688169245797552167191753)
          ·
            refine ⟨72516126934348164125393815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96688169245797552167191753 72516126934348164125393815)
            ·
              refine ⟨108774190401522246188090723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72516126934348164125393815 108774190401522246188090723)
              ·
                refine ⟨163161285602283369282136085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108774190401522246188090723 163161285602283369282136085)
                ·
                  refine ⟨7648185262607032935100129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 163161285602283369282136085 7648185262607032935100129)
                  ·
                    refine ⟨5736138946955274701325097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7648185262607032935100129 5736138946955274701325097)
                    ·
                      refine ⟨4302104210216456025993823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5736138946955274701325097 4302104210216456025993823)
                      ·
                        rfl

theorem cell23_8378318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2].length) (baseStart_8378318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378318 prefixEnd_8378318 := by exact prefixLift 8378318
  have htrace : WordTrace (prefixWord ++ tailWord_8378318) baseStart_8378318 baseEnd_8378318 := by
    simpa [prefixWord, tailWord_8378318, baseEnd_8378318] using wordTrace_append hprefix tailTrace_8378318
  have hstable : (prefixWord ++ tailWord_8378318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378318).length < 2 ^ (prefixWord ++ tailWord_8378318).sum := by decide
  have hdescent : baseEnd_8378318 < baseStart_8378318 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378364 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 1, 1, 7]
def baseStart_8378364 : Nat := 118140960795 + 8378364 * 2 ^ 59
def prefixEnd_8378364 : Nat := 4983230072969 + 3 ^ 40 * 8378364 * 2
def baseEnd_8378364 : Nat := 4302127830326562846018611

theorem tailTrace_8378364 : CollatzResearch.WordTrace tailWord_8378364 prefixEnd_8378364 4302127830326562846018611 := by
  unfold tailWord_8378364
  simp only [CollatzResearch.WordTrace]
  refine ⟨152792019909312806747847073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203722693212417075663796097 152792019909312806747847073)
  ·
    refine ⟨114594014931984605060885305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152792019909312806747847073 114594014931984605060885305)
    ·
      refine ⟨85945511198988453795663979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114594014931984605060885305 85945511198988453795663979)
      ·
        refine ⟨128918266798482680693495969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85945511198988453795663979 128918266798482680693495969)
        ·
          refine ⟨96688700098862010520121977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128918266798482680693495969 96688700098862010520121977)
          ·
            refine ⟨72516525074146507890091483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96688700098862010520121977 72516525074146507890091483)
            ·
              refine ⟨108774787611219761835137225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72516525074146507890091483 108774787611219761835137225)
              ·
                refine ⟨81581090708414821376352919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108774787611219761835137225 81581090708414821376352919)
                ·
                  refine ⟨122371636062622232064529379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81581090708414821376352919 122371636062622232064529379)
                  ·
                    refine ⟨183557454093933348096794069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 122371636062622232064529379 183557454093933348096794069)
                    ·
                      refine ⟨4302127830326562846018611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 183557454093933348096794069 4302127830326562846018611)
                      ·
                        rfl

theorem cell23_8378364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_8378364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378364 prefixEnd_8378364 := by exact prefixLift 8378364
  have htrace : WordTrace (prefixWord ++ tailWord_8378364) baseStart_8378364 baseEnd_8378364 := by
    simpa [prefixWord, tailWord_8378364, baseEnd_8378364] using wordTrace_append hprefix tailTrace_8378364
  have hstable : (prefixWord ++ tailWord_8378364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378364).length < 2 ^ (prefixWord ++ tailWord_8378364).sum := by decide
  have hdescent : baseEnd_8378364 < baseStart_8378364 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378418 : List Nat := [3, 2, 1, 1, 2, 4, 1, 2, 3, 4]
def baseStart_8378418 : Nat := 118140960795 + 8378418 * 2 ^ 59
def prefixEnd_8378418 : Nat := 4983230072969 + 3 ^ 40 * 8378418 * 2
def baseEnd_8378418 : Nat := 1434051852760635211581121

theorem tailTrace_8378418 : CollatzResearch.WordTrace tailWord_8378418 prefixEnd_8378418 1434051852760635211581121 := by
  unfold tailWord_8378418
  simp only [CollatzResearch.WordTrace]
  refine ⟨76396502340107495179539977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203724006240286653812106605 76396502340107495179539977)
  ·
    refine ⟨57297376755080621384654983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76396502340107495179539977 57297376755080621384654983)
    ·
      refine ⟨85946065132620932076982475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57297376755080621384654983 85946065132620932076982475)
      ·
        refine ⟨128919097698931398115473713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85946065132620932076982475 128919097698931398115473713)
        ·
          refine ⟨96689323274198548586605285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128919097698931398115473713 96689323274198548586605285)
          ·
            refine ⟨18129248113912227859988491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96689323274198548586605285 18129248113912227859988491)
            ·
              refine ⟨27193872170868341789982737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18129248113912227859988491 27193872170868341789982737)
              ·
                refine ⟨20395404128151256342487053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27193872170868341789982737 20395404128151256342487053)
                ·
                  refine ⟨7648276548056721128432645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20395404128151256342487053 7648276548056721128432645)
                  ·
                    refine ⟨1434051852760635211581121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7648276548056721128432645 1434051852760635211581121)
                    ·
                      rfl

theorem cell23_8378418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_8378418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378418 prefixEnd_8378418 := by exact prefixLift 8378418
  have htrace : WordTrace (prefixWord ++ tailWord_8378418) baseStart_8378418 baseEnd_8378418 := by
    simpa [prefixWord, tailWord_8378418, baseEnd_8378418] using wordTrace_append hprefix tailTrace_8378418
  have hstable : (prefixWord ++ tailWord_8378418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378418).length < 2 ^ (prefixWord ++ tailWord_8378418).sum := by decide
  have hdescent : baseEnd_8378418 < baseStart_8378418 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378425 : List Nat := [1, 2, 1, 5, 3, 2, 1, 1, 2, 1, 4]
def baseStart_8378425 : Nat := 118140960795 + 8378425 * 2 ^ 59
def prefixEnd_8378425 : Nat := 4983230072969 + 3 ^ 40 * 8378425 * 2
def baseEnd_8378425 : Nat := 4302159152646487107355831

theorem tailTrace_8378425 : CollatzResearch.WordTrace tailWord_8378425 prefixEnd_8378425 4302159152646487107355831 := by
  unfold tailWord_8378425
  simp only [CollatzResearch.WordTrace]
  refine ⟨305586264671404620913664729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203724176447603080609109819 305586264671404620913664729)
  ·
    refine ⟨229189698503553465685248547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305586264671404620913664729 229189698503553465685248547)
    ·
      refine ⟨343784547755330198527872821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229189698503553465685248547 343784547755330198527872821)
      ·
        refine ⟨32229801352062206111988077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 343784547755330198527872821 32229801352062206111988077)
        ·
          refine ⟨12086175507023327291995529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32229801352062206111988077 12086175507023327291995529)
          ·
            refine ⟨9064631630267495468996647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12086175507023327291995529 9064631630267495468996647)
            ·
              refine ⟨13596947445401243203494971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9064631630267495468996647 13596947445401243203494971)
              ·
                refine ⟨20395421168101864805242457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13596947445401243203494971 20395421168101864805242457)
                ·
                  refine ⟨15296565876076398603931843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20395421168101864805242457 15296565876076398603931843)
                  ·
                    refine ⟨22944848814114597905897765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15296565876076398603931843 22944848814114597905897765)
                    ·
                      refine ⟨4302159152646487107355831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22944848814114597905897765 4302159152646487107355831)
                      ·
                        rfl

theorem cell23_8378425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_8378425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378425 prefixEnd_8378425 := by exact prefixLift 8378425
  have htrace : WordTrace (prefixWord ++ tailWord_8378425) baseStart_8378425 baseEnd_8378425 := by
    simpa [prefixWord, tailWord_8378425, baseEnd_8378425] using wordTrace_append hprefix tailTrace_8378425
  have hstable : (prefixWord ++ tailWord_8378425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378425).length < 2 ^ (prefixWord ++ tailWord_8378425).sum := by decide
  have hdescent : baseEnd_8378425 < baseStart_8378425 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378438 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_8378438 : Nat := 118140960795 + 8378438 * 2 ^ 59
def prefixEnd_8378438 : Nat := 4983230072969 + 3 ^ 40 * 8378438 * 2
def baseEnd_8378438 : Nat := 4302165827894995556493271

theorem tailTrace_8378438 : CollatzResearch.WordTrace tailWord_8378438 prefixEnd_8378438 4302165827894995556493271 := by
  unfold tailWord_8378438
  simp only [CollatzResearch.WordTrace]
  refine ⟨9549585588136172629183999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 203724492546905016089258645 9549585588136172629183999)
  ·
    refine ⟨14324378382204258943775999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9549585588136172629183999 14324378382204258943775999)
    ·
      refine ⟨21486567573306388415663999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14324378382204258943775999 21486567573306388415663999)
      ·
        refine ⟨32229851359959582623495999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21486567573306388415663999 32229851359959582623495999)
        ·
          refine ⟨48344777039939373935243999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32229851359959582623495999 48344777039939373935243999)
          ·
            refine ⟨72517165559909060902865999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48344777039939373935243999 72517165559909060902865999)
            ·
              refine ⟨108775748339863591354298999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72517165559909060902865999 108775748339863591354298999)
              ·
                refine ⟨163163622509795387031448499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108775748339863591354298999 163163622509795387031448499)
                ·
                  refine ⟨244745433764693080547172749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163163622509795387031448499 244745433764693080547172749)
                  ·
                    refine ⟨91779537661759905205189781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 244745433764693080547172749 91779537661759905205189781)
                    ·
                      refine ⟨4302165827894995556493271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91779537661759905205189781 4302165827894995556493271)
                      ·
                        rfl

theorem cell23_8378438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_8378438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378438 prefixEnd_8378438 := by exact prefixLift 8378438
  have htrace : WordTrace (prefixWord ++ tailWord_8378438) baseStart_8378438 baseEnd_8378438 := by
    simpa [prefixWord, tailWord_8378438, baseEnd_8378438] using wordTrace_append hprefix tailTrace_8378438
  have hstable : (prefixWord ++ tailWord_8378438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378438).length < 2 ^ (prefixWord ++ tailWord_8378438).sum := by decide
  have hdescent : baseEnd_8378438 < baseStart_8378438 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378468 : List Nat := [2, 3, 1, 1, 2, 1, 3, 2, 1, 5, 2]
def baseStart_8378468 : Nat := 118140960795 + 8378468 * 2 ^ 59
def prefixEnd_8378468 : Nat := 4983230072969 + 3 ^ 40 * 8378468 * 2
def baseEnd_8378468 : Nat := 4302181232314630439118133

theorem tailTrace_8378468 : CollatzResearch.WordTrace tailWord_8378468 prefixEnd_8378468 4302181232314630439118133 := by
  unfold tailWord_8378468
  simp only [CollatzResearch.WordTrace]
  refine ⟨152793916505124419628740029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203725222006832559504986705 152793916505124419628740029)
  ·
    refine ⟨57297718689421657360777511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152793916505124419628740029 57297718689421657360777511)
    ·
      refine ⟨85946578034132486041166267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57297718689421657360777511 85946578034132486041166267)
      ·
        refine ⟨128919867051198729061749401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85946578034132486041166267 128919867051198729061749401)
        ·
          refine ⟨96689900288399046796312051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128919867051198729061749401 96689900288399046796312051)
          ·
            refine ⟨145034850432598570194468077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96689900288399046796312051 145034850432598570194468077)
            ·
              refine ⟨54388068912224463822925529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145034850432598570194468077 54388068912224463822925529)
              ·
                refine ⟨40791051684168347867194147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54388068912224463822925529 40791051684168347867194147)
                ·
                  refine ⟨61186577526252521800791221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40791051684168347867194147 61186577526252521800791221)
                  ·
                    refine ⟨5736241643086173918824177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61186577526252521800791221 5736241643086173918824177)
                    ·
                      refine ⟨4302181232314630439118133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5736241643086173918824177 4302181232314630439118133)
                      ·
                        rfl

theorem cell23_8378468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 1, 5, 2].length) (baseStart_8378468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378468 prefixEnd_8378468 := by exact prefixLift 8378468
  have htrace : WordTrace (prefixWord ++ tailWord_8378468) baseStart_8378468 baseEnd_8378468 := by
    simpa [prefixWord, tailWord_8378468, baseEnd_8378468] using wordTrace_append hprefix tailTrace_8378468
  have hstable : (prefixWord ++ tailWord_8378468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378468).length < 2 ^ (prefixWord ++ tailWord_8378468).sum := by decide
  have hdescent : baseEnd_8378468 < baseStart_8378468 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378492 : List Nat := [2, 2, 2, 1, 1, 4, 3, 3, 1, 1, 3]
def baseStart_8378492 : Nat := 118140960795 + 8378492 * 2 ^ 59
def prefixEnd_8378492 : Nat := 4983230072969 + 3 ^ 40 * 8378492 * 2
def baseEnd_8378492 : Nat := 4302193555850338345218023

theorem tailTrace_8378492 : CollatzResearch.WordTrace tailWord_8378492 prefixEnd_8378492 4302193555850338345218023 := by
  unfold tailWord_8378492
  simp only [CollatzResearch.WordTrace]
  refine ⟨152794354181080945678176865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203725805574774594237569153 152794354181080945678176865)
  ·
    refine ⟨114595765635810709258632649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152794354181080945678176865 114595765635810709258632649)
    ·
      refine ⟨85946824226858031943974487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114595765635810709258632649 85946824226858031943974487)
      ·
        refine ⟨128920236340287047915961731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85946824226858031943974487 128920236340287047915961731)
        ·
          refine ⟨193380354510430571873942597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128920236340287047915961731 193380354510430571873942597)
          ·
            refine ⟨36258816470705732226364237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193380354510430571873942597 36258816470705732226364237)
            ·
              refine ⟨13597056176514649584886589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36258816470705732226364237 13597056176514649584886589)
              ·
                refine ⟨5098896066192993594332471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13597056176514649584886589 5098896066192993594332471)
                ·
                  refine ⟨7648344099289490391498707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5098896066192993594332471 7648344099289490391498707)
                  ·
                    refine ⟨11472516148934235587248061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7648344099289490391498707 11472516148934235587248061)
                    ·
                      refine ⟨4302193555850338345218023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11472516148934235587248061 4302193555850338345218023)
                      ·
                        rfl

theorem cell23_8378492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 3, 1, 1, 3].length) (baseStart_8378492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378492 prefixEnd_8378492 := by exact prefixLift 8378492
  have htrace : WordTrace (prefixWord ++ tailWord_8378492) baseStart_8378492 baseEnd_8378492 := by
    simpa [prefixWord, tailWord_8378492, baseEnd_8378492] using wordTrace_append hprefix tailTrace_8378492
  have hstable : (prefixWord ++ tailWord_8378492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378492).length < 2 ^ (prefixWord ++ tailWord_8378492).sum := by decide
  have hdescent : baseEnd_8378492 < baseStart_8378492 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378525 : List Nat := [1, 4, 2, 1, 1, 4, 1, 3, 2, 4]
def baseStart_8378525 : Nat := 118140960795 + 8378525 * 2 ^ 59
def prefixEnd_8378525 : Nat := 4983230072969 + 3 ^ 40 * 8378525 * 2
def baseEnd_8378525 : Nat := 1434070166903978905368457

theorem tailTrace_8378525 : CollatzResearch.WordTrace tailWord_8378525 prefixEnd_8378525 1434070166903978905368457 := by
  unfold tailWord_8378525
  simp only [CollatzResearch.WordTrace]
  refine ⟨305589911971042337992305029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203726607980694891994870019 305589911971042337992305029)
  ·
    refine ⟨57298108494570438373557193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305589911971042337992305029 57298108494570438373557193)
    ·
      refine ⟨42973581370927828780167895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57298108494570438373557193 42973581370927828780167895)
      ·
        refine ⟨64460372056391743170251843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42973581370927828780167895 64460372056391743170251843)
        ·
          refine ⟨96690558084587614755377765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64460372056391743170251843 96690558084587614755377765)
          ·
            refine ⟨18129479640860177766633331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96690558084587614755377765 18129479640860177766633331)
            ·
              refine ⟨27194219461290266649949997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18129479640860177766633331 27194219461290266649949997)
              ·
                refine ⟨10197832297983849993731249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27194219461290266649949997 10197832297983849993731249)
                ·
                  refine ⟨7648374223487887495298437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10197832297983849993731249 7648374223487887495298437)
                  ·
                    refine ⟨1434070166903978905368457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7648374223487887495298437 1434070166903978905368457)
                    ·
                      rfl

theorem cell23_8378525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_8378525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378525 prefixEnd_8378525 := by exact prefixLift 8378525
  have htrace : WordTrace (prefixWord ++ tailWord_8378525) baseStart_8378525 baseEnd_8378525 := by
    simpa [prefixWord, tailWord_8378525, baseEnd_8378525] using wordTrace_append hprefix tailTrace_8378525
  have hstable : (prefixWord ++ tailWord_8378525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378525).length < 2 ^ (prefixWord ++ tailWord_8378525).sum := by decide
  have hdescent : baseEnd_8378525 < baseStart_8378525 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378532 : List Nat := [2, 3, 1, 2, 4, 2, 1, 2, 1, 1, 4]
def baseStart_8378532 : Nat := 118140960795 + 8378532 * 2 ^ 59
def prefixEnd_8378532 : Nat := 4983230072969 + 3 ^ 40 * 8378532 * 2
def baseEnd_8378532 : Nat := 4302214095076518188717839

theorem tailTrace_8378532 : CollatzResearch.WordTrace tailWord_8378532 prefixEnd_8378532 4302214095076518188717839 := by
  unfold tailWord_8378532
  simp only [CollatzResearch.WordTrace]
  refine ⟨152795083641008489093904925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203726778188011318791873233 152795083641008489093904925)
  ·
    refine ⟨57298156365378183410214347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152795083641008489093904925 57298156365378183410214347)
    ·
      refine ⟨85947234548067275115321521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57298156365378183410214347 85947234548067275115321521)
      ·
        refine ⟨64460425911050456336491141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85947234548067275115321521 64460425911050456336491141)
        ·
          refine ⟨12086329858321960563092089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64460425911050456336491141 12086329858321960563092089)
          ·
            refine ⟨9064747393741470422319067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12086329858321960563092089 9064747393741470422319067)
            ·
              refine ⟨13597121090612205633478601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9064747393741470422319067 13597121090612205633478601)
              ·
                refine ⟨10197840817959154225108951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13597121090612205633478601 10197840817959154225108951)
                ·
                  refine ⟨15296761226938731337663427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10197840817959154225108951 15296761226938731337663427)
                  ·
                    refine ⟨22945141840408097006495141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15296761226938731337663427 22945141840408097006495141)
                    ·
                      refine ⟨4302214095076518188717839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22945141840408097006495141 4302214095076518188717839)
                      ·
                        rfl

theorem cell23_8378532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_8378532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378532 prefixEnd_8378532 := by exact prefixLift 8378532
  have htrace : WordTrace (prefixWord ++ tailWord_8378532) baseStart_8378532 baseEnd_8378532 := by
    simpa [prefixWord, tailWord_8378532, baseEnd_8378532] using wordTrace_append hprefix tailTrace_8378532
  have hstable : (prefixWord ++ tailWord_8378532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378532).length < 2 ^ (prefixWord ++ tailWord_8378532).sum := by decide
  have hdescent : baseEnd_8378532 < baseStart_8378532 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378542 : List Nat := [4, 1, 4, 2, 1, 1, 1, 2, 1, 6]
def baseStart_8378542 : Nat := 118140960795 + 8378542 * 2 ^ 59
def prefixEnd_8378542 : Nat := 4983230072969 + 3 ^ 40 * 8378542 * 2
def baseEnd_8378542 : Nat := 1434073076627687716530931

theorem tailTrace_8378542 : CollatzResearch.WordTrace tailWord_8378542 prefixEnd_8378542 1434073076627687716530931 := by
  unfold tailWord_8378542
  simp only [CollatzResearch.WordTrace]
  refine ⟨38198816501497593736959235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203727021341320499930449253 38198816501497593736959235)
  ·
    refine ⟨57298224752246390605438853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38198816501497593736959235 57298224752246390605438853)
    ·
      refine ⟨10743417141046198238519785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57298224752246390605438853 10743417141046198238519785)
      ·
        refine ⟨8057562855784648678889839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10743417141046198238519785 8057562855784648678889839)
        ·
          refine ⟨12086344283676973018334759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8057562855784648678889839 12086344283676973018334759)
          ·
            refine ⟨18129516425515459527502139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12086344283676973018334759 18129516425515459527502139)
            ·
              refine ⟨27194274638273189291253209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18129516425515459527502139 27194274638273189291253209)
              ·
                refine ⟨20395705978704891968439907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27194274638273189291253209 20395705978704891968439907)
                ·
                  refine ⟨30593558968057337952659861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20395705978704891968439907 30593558968057337952659861)
                  ·
                    refine ⟨1434073076627687716530931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30593558968057337952659861 1434073076627687716530931)
                    ·
                      rfl

theorem cell23_8378542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_8378542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378542 prefixEnd_8378542 := by exact prefixLift 8378542
  have htrace : WordTrace (prefixWord ++ tailWord_8378542) baseStart_8378542 baseEnd_8378542 := by
    simpa [prefixWord, tailWord_8378542, baseEnd_8378542] using wordTrace_append hprefix tailTrace_8378542
  have hstable : (prefixWord ++ tailWord_8378542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378542).length < 2 ^ (prefixWord ++ tailWord_8378542).sum := by decide
  have hdescent : baseEnd_8378542 < baseStart_8378542 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378545 : List Nat := [1, 2, 2, 5, 2, 1, 1, 2, 1, 2, 4]
def baseStart_8378545 : Nat := 118140960795 + 8378545 * 2 ^ 59
def prefixEnd_8378545 : Nat := 4983230072969 + 3 ^ 40 * 8378545 * 2
def baseEnd_8378545 : Nat := 4302220770325026637855279

theorem tailTrace_8378545 : CollatzResearch.WordTrace tailWord_8378545 prefixEnd_8378545 4302220770325026637855279 := by
  unfold tailWord_8378545
  simp only [CollatzResearch.WordTrace]
  refine ⟨305590641430969881408033089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203727094287313254272022059 305590641430969881408033089)
  ·
    refine ⟨229192981073227411056024817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305590641430969881408033089 229192981073227411056024817)
    ·
      refine ⟨171894735804920558292018613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229192981073227411056024817 171894735804920558292018613)
      ·
        refine ⟨16115131481711302339876745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171894735804920558292018613 16115131481711302339876745)
        ·
          refine ⟨12086348611283476754907559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16115131481711302339876745 12086348611283476754907559)
          ·
            refine ⟨18129522916925215132361339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12086348611283476754907559 18129522916925215132361339)
            ·
              refine ⟨27194284375387822698542009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18129522916925215132361339 27194284375387822698542009)
              ·
                refine ⟨20395713281540867023906507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27194284375387822698542009 20395713281540867023906507)
                ·
                  refine ⟨30593569922311300535859761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20395713281540867023906507 30593569922311300535859761)
                  ·
                    refine ⟨22945177441733475401894821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30593569922311300535859761 22945177441733475401894821)
                    ·
                      refine ⟨4302220770325026637855279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22945177441733475401894821 4302220770325026637855279)
                      ·
                        rfl

theorem cell23_8378545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_8378545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378545 prefixEnd_8378545 := by exact prefixLift 8378545
  have htrace : WordTrace (prefixWord ++ tailWord_8378545) baseStart_8378545 baseEnd_8378545 := by
    simpa [prefixWord, tailWord_8378545, baseEnd_8378545] using wordTrace_append hprefix tailTrace_8378545
  have hstable : (prefixWord ++ tailWord_8378545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378545).length < 2 ^ (prefixWord ++ tailWord_8378545).sum := by decide
  have hdescent : baseEnd_8378545 < baseStart_8378545 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378549 : List Nat := [1, 3, 3, 4, 1, 1, 3, 1, 1, 1, 4]
def baseStart_8378549 : Nat := 118140960795 + 8378549 * 2 ^ 59
def prefixEnd_8378549 : Nat := 4983230072969 + 3 ^ 40 * 8378549 * 2
def baseEnd_8378549 : Nat := 4302222824247644622205261

theorem tailTrace_8378549 : CollatzResearch.WordTrace tailWord_8378549 prefixEnd_8378549 4302222824247644622205261 := by
  unfold tailWord_8378549
  simp only [CollatzResearch.WordTrace]
  refine ⟨305590787322955390091178701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203727191548636926727452467 305590787322955390091178701)
  ·
    refine ⟨114596545246108271284192013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305590787322955390091178701 114596545246108271284192013)
    ·
      refine ⟨42973704467290601731572005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114596545246108271284192013 42973704467290601731572005)
      ·
        refine ⟨8057569587616987824669751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42973704467290601731572005 8057569587616987824669751)
        ·
          refine ⟨12086354381425481737004627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8057569587616987824669751 12086354381425481737004627)
          ·
            refine ⟨18129531572138222605506941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12086354381425481737004627 18129531572138222605506941)
            ·
              refine ⟨6798574339551833477065103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18129531572138222605506941 6798574339551833477065103)
              ·
                refine ⟨10197861509327750215597655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6798574339551833477065103 10197861509327750215597655)
                ·
                  refine ⟨15296792263991625323396483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10197861509327750215597655 15296792263991625323396483)
                  ·
                    refine ⟨22945188395987437985094725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15296792263991625323396483 22945188395987437985094725)
                    ·
                      refine ⟨4302222824247644622205261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22945188395987437985094725 4302222824247644622205261)
                      ·
                        rfl

theorem cell23_8378549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_8378549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378549 prefixEnd_8378549 := by exact prefixLift 8378549
  have htrace : WordTrace (prefixWord ++ tailWord_8378549) baseStart_8378549 baseEnd_8378549 := by
    simpa [prefixWord, tailWord_8378549, baseEnd_8378549] using wordTrace_append hprefix tailTrace_8378549
  have hstable : (prefixWord ++ tailWord_8378549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378549).length < 2 ^ (prefixWord ++ tailWord_8378549).sum := by decide
  have hdescent : baseEnd_8378549 < baseStart_8378549 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378565 : List Nat := [1, 3, 1, 1, 1, 1, 5, 4, 2, 1, 3]
def baseStart_8378565 : Nat := 118140960795 + 8378565 * 2 ^ 59
def prefixEnd_8378565 : Nat := 4983230072969 + 3 ^ 40 * 8378565 * 2
def baseEnd_8378565 : Nat := 4302231039938116559605187

theorem tailTrace_8378565 : CollatzResearch.WordTrace tailWord_8378565 prefixEnd_8378565 4302231039938116559605187 := by
  unfold tailWord_8378565
  simp only [CollatzResearch.WordTrace]
  refine ⟨305591370890897424823761149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203727580593931616549174099 305591370890897424823761149)
  ·
    refine ⟨114596764084086534308910431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305591370890897424823761149 114596764084086534308910431)
    ·
      refine ⟨171895146126129801463365647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114596764084086534308910431 171895146126129801463365647)
      ·
        refine ⟨257842719189194702195048471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171895146126129801463365647 257842719189194702195048471)
        ·
          refine ⟨386764078783792053292572707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257842719189194702195048471 386764078783792053292572707)
          ·
            refine ⟨580146118175688079938859061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386764078783792053292572707 580146118175688079938859061)
            ·
              refine ⟨54388698578970757494268037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 580146118175688079938859061 54388698578970757494268037)
              ·
                refine ⟨10197880983557017030175257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54388698578970757494268037 10197880983557017030175257)
                ·
                  refine ⟨7648410737667762772631443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10197880983557017030175257 7648410737667762772631443)
                  ·
                    refine ⟨11472616106501644158947165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7648410737667762772631443 11472616106501644158947165)
                    ·
                      refine ⟨4302231039938116559605187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11472616106501644158947165 4302231039938116559605187)
                      ·
                        rfl

theorem cell23_8378565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 2, 1, 3].length) (baseStart_8378565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378565 prefixEnd_8378565 := by exact prefixLift 8378565
  have htrace : WordTrace (prefixWord ++ tailWord_8378565) baseStart_8378565 baseEnd_8378565 := by
    simpa [prefixWord, tailWord_8378565, baseEnd_8378565] using wordTrace_append hprefix tailTrace_8378565
  have hstable : (prefixWord ++ tailWord_8378565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378565).length < 2 ^ (prefixWord ++ tailWord_8378565).sum := by decide
  have hdescent : baseEnd_8378565 < baseStart_8378565 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378571 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 4]
def baseStart_8378571 : Nat := 118140960795 + 8378571 * 2 ^ 59
def prefixEnd_8378571 : Nat := 4983230072969 + 3 ^ 40 * 8378571 * 2
def baseEnd_8378571 : Nat := 4302234120822043536130159

theorem tailTrace_8378571 : CollatzResearch.WordTrace tailWord_8378571 prefixEnd_8378571 4302234120822043536130159 := by
  unfold tailWord_8378571
  simp only [CollatzResearch.WordTrace]
  refine ⟨305591589728875687848479567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203727726485917125232319711 305591589728875687848479567)
  ·
    refine ⟨458387384593313531772719351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305591589728875687848479567 458387384593313531772719351)
    ·
      refine ⟨687581076889970297659079027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458387384593313531772719351 687581076889970297659079027)
      ·
        refine ⟨1031371615334955446488618541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687581076889970297659079027 1031371615334955446488618541)
        ·
          refine ⟨386764355750608292433231953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1031371615334955446488618541 386764355750608292433231953)
          ·
            refine ⟨290073266812956219324923965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386764355750608292433231953 290073266812956219324923965)
            ·
              refine ⟨108777475054858582246846487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 290073266812956219324923965 108777475054858582246846487)
              ·
                refine ⟨163166212582287873370269731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108777475054858582246846487 163166212582287873370269731)
                ·
                  refine ⟨244749318873431810055404597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163166212582287873370269731 244749318873431810055404597)
                  ·
                    refine ⟨22945248644384232192694181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 244749318873431810055404597 22945248644384232192694181)
                    ·
                      refine ⟨4302234120822043536130159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22945248644384232192694181 4302234120822043536130159)
                      ·
                        rfl

theorem cell23_8378571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 4].length) (baseStart_8378571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378571 prefixEnd_8378571 := by exact prefixLift 8378571
  have htrace : WordTrace (prefixWord ++ tailWord_8378571) baseStart_8378571 baseEnd_8378571 := by
    simpa [prefixWord, tailWord_8378571, baseEnd_8378571] using wordTrace_append hprefix tailTrace_8378571
  have hstable : (prefixWord ++ tailWord_8378571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378571).length < 2 ^ (prefixWord ++ tailWord_8378571).sum := by decide
  have hdescent : baseEnd_8378571 < baseStart_8378571 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378572 : List Nat := [2, 2, 1, 6, 2, 1, 1, 8]
def baseStart_8378572 : Nat := 118140960795 + 8378572 * 2 ^ 59
def prefixEnd_8378572 : Nat := 4983230072969 + 3 ^ 40 * 8378572 * 2
def baseEnd_8378572 : Nat := 159342023492692519711765

theorem tailTrace_8378572 : CollatzResearch.WordTrace tailWord_8378572 prefixEnd_8378572 159342023492692519711765 := by
  unfold tailWord_8378572
  simp only [CollatzResearch.WordTrace]
  refine ⟨152795813100936032509632985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203727750801248043346177313 152795813100936032509632985)
  ·
    refine ⟨114596859825702024382224739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152795813100936032509632985 114596859825702024382224739)
    ·
      refine ⟨171895289738553036573337109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114596859825702024382224739 171895289738553036573337109)
      ·
        refine ⟨8057591706494673589375177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 171895289738553036573337109 8057591706494673589375177)
        ·
          refine ⟨6043193779871005192031383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8057591706494673589375177 6043193779871005192031383)
          ·
            refine ⟨9064790669806507788047075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6043193779871005192031383 9064790669806507788047075)
            ·
              refine ⟨13597186004709761682070613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9064790669806507788047075 13597186004709761682070613)
              ·
                refine ⟨159342023492692519711765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13597186004709761682070613 159342023492692519711765)
                ·
                  rfl

theorem cell23_8378572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 8].length) (baseStart_8378572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378572 prefixEnd_8378572 := by exact prefixLift 8378572
  have htrace : WordTrace (prefixWord ++ tailWord_8378572) baseStart_8378572 baseEnd_8378572 := by
    simpa [prefixWord, tailWord_8378572, baseEnd_8378572] using wordTrace_append hprefix tailTrace_8378572
  have hstable : (prefixWord ++ tailWord_8378572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378572).length < 2 ^ (prefixWord ++ tailWord_8378572).sum := by decide
  have hdescent : baseEnd_8378572 < baseStart_8378572 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378582 : List Nat := [5, 2, 1, 2, 1, 1, 1, 3, 1, 3, 3]
def baseStart_8378582 : Nat := 118140960795 + 8378582 * 2 ^ 59
def prefixEnd_8378582 : Nat := 4983230072969 + 3 ^ 40 * 8378582 * 2
def baseEnd_8378582 : Nat := 4302239769109242993092609

theorem tailTrace_8378582 : CollatzResearch.WordTrace tailWord_8378582 prefixEnd_8378582 4302239769109242993092609 := by
  unfold tailWord_8378582
  simp only [CollatzResearch.WordTrace]
  refine ⟨19099499433239739795445625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203727993954557224484753333 19099499433239739795445625)
  ·
    refine ⟨14324624574929804846584219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19099499433239739795445625 14324624574929804846584219)
    ·
      refine ⟨21486936862394707269876329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14324624574929804846584219 21486936862394707269876329)
      ·
        refine ⟨16115202646796030452407247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21486936862394707269876329 16115202646796030452407247)
        ·
          refine ⟨24172803970194045678610871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16115202646796030452407247 24172803970194045678610871)
          ·
            refine ⟨36259205955291068517916307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24172803970194045678610871 36259205955291068517916307)
            ·
              refine ⟨54388808932936602776874461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36259205955291068517916307 54388808932936602776874461)
              ·
                refine ⟨20395803349851226041327923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54388808932936602776874461 20395803349851226041327923)
                ·
                  refine ⟨30593705024776839061991885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20395803349851226041327923 30593705024776839061991885)
                  ·
                    refine ⟨11472639384291314648246957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30593705024776839061991885 11472639384291314648246957)
                    ·
                      refine ⟨4302239769109242993092609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11472639384291314648246957 4302239769109242993092609)
                      ·
                        rfl

theorem cell23_8378582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_8378582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378582 prefixEnd_8378582 := by exact prefixLift 8378582
  have htrace : WordTrace (prefixWord ++ tailWord_8378582) baseStart_8378582 baseEnd_8378582 := by
    simpa [prefixWord, tailWord_8378582, baseEnd_8378582] using wordTrace_append hprefix tailTrace_8378582
  have hstable : (prefixWord ++ tailWord_8378582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378582).length < 2 ^ (prefixWord ++ tailWord_8378582).sum := by decide
  have hdescent : baseEnd_8378582 < baseStart_8378582 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378611 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 9]
def baseStart_8378611 : Nat := 118140960795 + 8378611 * 2 ^ 59
def prefixEnd_8378611 : Nat := 4983230072969 + 3 ^ 40 * 8378611 * 2
def baseEnd_8378611 : Nat := 478028295560913708847775

theorem tailTrace_8378611 : CollatzResearch.WordTrace tailWord_8378611 prefixEnd_8378611 478028295560913708847775 := by
  unfold tailWord_8378611
  simp only [CollatzResearch.WordTrace]
  refine ⟨305593048648730774679935687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203728699099153849786623791 305593048648730774679935687)
  ·
    refine ⟨458389572973096162019903531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305593048648730774679935687 458389572973096162019903531)
    ·
      refine ⟨687584359459644243029855297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458389572973096162019903531 687584359459644243029855297)
      ·
        refine ⟨515688269594733182272391473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 687584359459644243029855297 515688269594733182272391473)
        ·
          refine ⟨386766202196049886704293605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515688269594733182272391473 386766202196049886704293605)
          ·
            refine ⟨72518662911759353757055051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 386766202196049886704293605 72518662911759353757055051)
            ·
              refine ⟨108777994367639030635582577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72518662911759353757055051 108777994367639030635582577)
              ·
                refine ⟨81583495775729272976686933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108777994367639030635582577 81583495775729272976686933)
                ·
                  refine ⟨478028295560913708847775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 81583495775729272976686933 478028295560913708847775)
                  ·
                    rfl

theorem cell23_8378611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 9].length) (baseStart_8378611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378611 prefixEnd_8378611 := by exact prefixLift 8378611
  have htrace : WordTrace (prefixWord ++ tailWord_8378611) baseStart_8378611 baseEnd_8378611 := by
    simpa [prefixWord, tailWord_8378611, baseEnd_8378611] using wordTrace_append hprefix tailTrace_8378611
  have hstable : (prefixWord ++ tailWord_8378611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378611).length < 2 ^ (prefixWord ++ tailWord_8378611).sum := by decide
  have hdescent : baseEnd_8378611 < baseStart_8378611 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378618 : List Nat := [3, 1, 1, 1, 1, 5, 1, 2, 2, 2, 4]
def baseStart_8378618 : Nat := 118140960795 + 8378618 * 2 ^ 59
def prefixEnd_8378618 : Nat := 4983230072969 + 3 ^ 40 * 8378618 * 2
def baseEnd_8378618 : Nat := 4302258254412804852242443

theorem tailTrace_8378618 : CollatzResearch.WordTrace tailWord_8378618 prefixEnd_8378618 4302258254412804852242443 := by
  unfold tailWord_8378618
  simp only [CollatzResearch.WordTrace]
  refine ⟨76398325989926353718860127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203728869306470276583627005 76398325989926353718860127)
  ·
    refine ⟨114597488984889530578290191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76398325989926353718860127 114597488984889530578290191)
    ·
      refine ⟨171896233477334295867435287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114597488984889530578290191 171896233477334295867435287)
      ·
        refine ⟨257844350216001443801152931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171896233477334295867435287 257844350216001443801152931)
        ·
          refine ⟨386766525324002165701729397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257844350216001443801152931 386766525324002165701729397)
          ·
            refine ⟨36259361749125203034537131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 386766525324002165701729397 36259361749125203034537131)
            ·
              refine ⟨54389042623687804551805697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36259361749125203034537131 54389042623687804551805697)
              ·
                refine ⟨40791781967765853413854273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54389042623687804551805697 40791781967765853413854273)
                ·
                  refine ⟨30593836475824390060390705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40791781967765853413854273 30593836475824390060390705)
                  ·
                    refine ⟨22945377356868292545293029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30593836475824390060390705 22945377356868292545293029)
                    ·
                      refine ⟨4302258254412804852242443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22945377356868292545293029 4302258254412804852242443)
                      ·
                        rfl

theorem cell23_8378618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_8378618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378618 prefixEnd_8378618 := by exact prefixLift 8378618
  have htrace : WordTrace (prefixWord ++ tailWord_8378618) baseStart_8378618 baseEnd_8378618 := by
    simpa [prefixWord, tailWord_8378618, baseEnd_8378618] using wordTrace_append hprefix tailTrace_8378618
  have hstable : (prefixWord ++ tailWord_8378618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378618).length < 2 ^ (prefixWord ++ tailWord_8378618).sum := by decide
  have hdescent : baseEnd_8378618 < baseStart_8378618 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378695 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 1, 6, 2]
def baseStart_8378695 : Nat := 118140960795 + 8378695 * 2 ^ 59
def prefixEnd_8378695 : Nat := 4983230072969 + 3 ^ 40 * 8378695 * 2
def baseEnd_8378695 : Nat := 4302297792423201050979589

theorem tailTrace_8378695 : CollatzResearch.WordTrace tailWord_8378695 prefixEnd_8378695 4302297792423201050979589 := by
  unfold tailWord_8378695
  simp only [CollatzResearch.WordTrace]
  refine ⟨305596112380426457025993539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203730741586950971350662359 305596112380426457025993539)
  ·
    refine ⟨458394168570639685538990309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305596112380426457025993539 458394168570639685538990309)
    ·
      refine ⟨85948906606994941038560683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 458394168570639685538990309 85948906606994941038560683)
      ·
        refine ⟨128923359910492411557841025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85948906606994941038560683 128923359910492411557841025)
        ·
          refine ⟨96692519932869308668380769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128923359910492411557841025 96692519932869308668380769)
          ·
            refine ⟨72519389949651981501285577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96692519932869308668380769 72519389949651981501285577)
            ·
              refine ⟨54389542462238986125964183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72519389949651981501285577 54389542462238986125964183)
              ·
                refine ⟨81584313693358479188946275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54389542462238986125964183 81584313693358479188946275)
                ·
                  refine ⟨122376470540037718783419413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81584313693358479188946275 122376470540037718783419413)
                  ·
                    refine ⟨5736397056564268067972785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 122376470540037718783419413 5736397056564268067972785)
                    ·
                      refine ⟨4302297792423201050979589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5736397056564268067972785 4302297792423201050979589)
                      ·
                        rfl

theorem cell23_8378695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 6, 2].length) (baseStart_8378695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378695 prefixEnd_8378695 := by exact prefixLift 8378695
  have htrace : WordTrace (prefixWord ++ tailWord_8378695) baseStart_8378695 baseEnd_8378695 := by
    simpa [prefixWord, tailWord_8378695, baseEnd_8378695] using wordTrace_append hprefix tailTrace_8378695
  have hstable : (prefixWord ++ tailWord_8378695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378695).length < 2 ^ (prefixWord ++ tailWord_8378695).sum := by decide
  have hdescent : baseEnd_8378695 < baseStart_8378695 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378768 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 4]
def baseStart_8378768 : Nat := 118140960795 + 8378768 * 2 ^ 59
def prefixEnd_8378768 : Nat := 4983230072969 + 3 ^ 40 * 8378768 * 2
def baseEnd_8378768 : Nat := 4302335276510979265366753

theorem tailTrace_8378768 : CollatzResearch.WordTrace tailWord_8378768 prefixEnd_8378768 4302335276510979265366753 := by
  unfold tailWord_8378768
  simp only [CollatzResearch.WordTrace]
  refine ⟨152799387454580995246700479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203732516606107993662267305 152799387454580995246700479)
  ·
    refine ⟨229199081181871492870050719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152799387454580995246700479 229199081181871492870050719)
    ·
      refine ⟨343798621772807239305076079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229199081181871492870050719 343798621772807239305076079)
      ·
        refine ⟨515697932659210858957614119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343798621772807239305076079 515697932659210858957614119)
        ·
          refine ⟨773546898988816288436421179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515697932659210858957614119 773546898988816288436421179)
          ·
            refine ⟨1160320348483224432654631769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773546898988816288436421179 1160320348483224432654631769)
            ·
              refine ⟨870240261362418324490973827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1160320348483224432654631769 870240261362418324490973827)
              ·
                refine ⟨1305360392043627486736460741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 870240261362418324490973827 1305360392043627486736460741)
                ·
                  refine ⟨244755073508180153763086389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1305360392043627486736460741 244755073508180153763086389)
                  ·
                    refine ⟨22945788141391889415289349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 244755073508180153763086389 22945788141391889415289349)
                    ·
                      refine ⟨4302335276510979265366753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22945788141391889415289349 4302335276510979265366753)
                      ·
                        rfl

theorem cell23_8378768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 4].length) (baseStart_8378768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378768 prefixEnd_8378768 := by exact prefixLift 8378768
  have htrace : WordTrace (prefixWord ++ tailWord_8378768) baseStart_8378768 baseEnd_8378768 := by
    simpa [prefixWord, tailWord_8378768, baseEnd_8378768] using wordTrace_append hprefix tailTrace_8378768
  have hstable : (prefixWord ++ tailWord_8378768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378768).length < 2 ^ (prefixWord ++ tailWord_8378768).sum := by decide
  have hdescent : baseEnd_8378768 < baseStart_8378768 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378808 : List Nat := [2, 1, 2, 1, 2, 2, 1, 12]
def baseStart_8378808 : Nat := 118140960795 + 8378808 * 2 ^ 59
def prefixEnd_8378808 : Nat := 4983230072969 + 3 ^ 40 * 8378808 * 2
def baseEnd_8378808 : Nat := 159346511693968855883947

theorem tailTrace_8378808 : CollatzResearch.WordTrace tailWord_8378808 prefixEnd_8378808 159346511693968855883947 := by
  unfold tailWord_8378808
  simp only [CollatzResearch.WordTrace]
  refine ⟨152800116914508538662428539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203733489219344718216571385 152800116914508538662428539)
  ·
    refine ⟨229200175371762807993642809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152800116914508538662428539 229200175371762807993642809)
    ·
      refine ⟨171900131528822105995232107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229200175371762807993642809 171900131528822105995232107)
      ·
        refine ⟨257850197293233158992848161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171900131528822105995232107 257850197293233158992848161)
        ·
          refine ⟨193387647969924869244636121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257850197293233158992848161 193387647969924869244636121)
          ·
            refine ⟨145040735977443651933477091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193387647969924869244636121 145040735977443651933477091)
            ·
              refine ⟨217561103966165477900215637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145040735977443651933477091 217561103966165477900215637)
              ·
                refine ⟨159346511693968855883947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 217561103966165477900215637 159346511693968855883947)
                ·
                  rfl

theorem cell23_8378808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 12].length) (baseStart_8378808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378808 prefixEnd_8378808 := by exact prefixLift 8378808
  have htrace : WordTrace (prefixWord ++ tailWord_8378808) baseStart_8378808 baseEnd_8378808 := by
    simpa [prefixWord, tailWord_8378808, baseEnd_8378808] using wordTrace_append hprefix tailTrace_8378808
  have hstable : (prefixWord ++ tailWord_8378808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378808).length < 2 ^ (prefixWord ++ tailWord_8378808).sum := by decide
  have hdescent : baseEnd_8378808 < baseStart_8378808 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378812 : List Nat := [2, 2, 2, 4, 1, 1, 3, 1, 1, 6]
def baseStart_8378812 : Nat := 118140960795 + 8378812 * 2 ^ 59
def prefixEnd_8378812 : Nat := 4983230072969 + 3 ^ 40 * 8378812 * 2
def baseEnd_8378812 : Nat := 1434119289886592364405517

theorem tailTrace_8378812 : CollatzResearch.WordTrace tailWord_8378812 prefixEnd_8378812 1434119289886592364405517 := by
  unfold tailWord_8378812
  simp only [CollatzResearch.WordTrace]
  refine ⟨152800189860501293004001345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203733586480668390672001793 152800189860501293004001345)
  ·
    refine ⟨114600142395375969753001009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152800189860501293004001345 114600142395375969753001009)
    ·
      refine ⟨85950106796531977314750757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114600142395375969753001009 85950106796531977314750757)
      ·
        refine ⟨16115645024349745746515767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85950106796531977314750757 16115645024349745746515767)
        ·
          refine ⟨24173467536524618619773651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16115645024349745746515767 24173467536524618619773651)
          ·
            refine ⟨36260201304786927929660477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24173467536524618619773651 36260201304786927929660477)
            ·
              refine ⟨13597575489295097973622679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36260201304786927929660477 13597575489295097973622679)
              ·
                refine ⟨20396363233942646960434019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13597575489295097973622679 20396363233942646960434019)
                ·
                  refine ⟨30594544850913970440651029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20396363233942646960434019 30594544850913970440651029)
                  ·
                    refine ⟨1434119289886592364405517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30594544850913970440651029 1434119289886592364405517)
                    ·
                      rfl

theorem cell23_8378812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_8378812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378812 prefixEnd_8378812 := by exact prefixLift 8378812
  have htrace : WordTrace (prefixWord ++ tailWord_8378812) baseStart_8378812 baseEnd_8378812 := by
    simpa [prefixWord, tailWord_8378812, baseEnd_8378812] using wordTrace_append hprefix tailTrace_8378812
  have hstable : (prefixWord ++ tailWord_8378812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378812).length < 2 ^ (prefixWord ++ tailWord_8378812).sum := by decide
  have hdescent : baseEnd_8378812 < baseStart_8378812 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378825 : List Nat := [1, 2, 1, 1, 2, 1, 8, 7]
def baseStart_8378825 : Nat := 118140960795 + 8378825 * 2 ^ 59
def prefixEnd_8378825 : Nat := 4983230072969 + 3 ^ 40 * 8378825 * 2
def baseEnd_8378825 : Nat := 159346834996603168235333

theorem tailTrace_8378825 : CollatzResearch.WordTrace tailWord_8378825 prefixEnd_8378825 159346834996603168235333 := by
  unfold tailWord_8378825
  simp only [CollatzResearch.WordTrace]
  refine ⟨305600853869955489228225929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203733902579970326152150619 305600853869955489228225929)
  ·
    refine ⟨229200640402466616921169447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305600853869955489228225929 229200640402466616921169447)
    ·
      refine ⟨343800960603699925381754171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229200640402466616921169447 343800960603699925381754171)
      ·
        refine ⟨515701440905549888072631257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343800960603699925381754171 515701440905549888072631257)
        ·
          refine ⟨386776080679162416054473443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515701440905549888072631257 386776080679162416054473443)
          ·
            refine ⟨580164121018743624081710165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386776080679162416054473443 580164121018743624081710165)
            ·
              refine ⟨6798798293188401844707541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 580164121018743624081710165 6798798293188401844707541)
              ·
                refine ⟨159346834996603168235333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6798798293188401844707541 159346834996603168235333)
                ·
                  rfl

theorem cell23_8378825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 7].length) (baseStart_8378825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378825 prefixEnd_8378825 := by exact prefixLift 8378825
  have htrace : WordTrace (prefixWord ++ tailWord_8378825) baseStart_8378825 baseEnd_8378825 := by
    simpa [prefixWord, tailWord_8378825, baseEnd_8378825] using wordTrace_append hprefix tailTrace_8378825
  have hstable : (prefixWord ++ tailWord_8378825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378825).length < 2 ^ (prefixWord ++ tailWord_8378825).sum := by decide
  have hdescent : baseEnd_8378825 < baseStart_8378825 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378853 : List Nat := [1, 3, 1, 5, 2, 2, 1, 1, 3, 2, 2]
def baseStart_8378853 : Nat := 118140960795 + 8378853 * 2 ^ 59
def prefixEnd_8378853 : Nat := 4983230072969 + 3 ^ 40 * 8378853 * 2
def baseEnd_8378853 : Nat := 4302378922366611432803863

theorem tailTrace_8378853 : CollatzResearch.WordTrace tailWord_8378853 prefixEnd_8378853 4302378922366611432803863 := by
  unfold tailWord_8378853
  simp only [CollatzResearch.WordTrace]
  refine ⟨305601875113854050010245213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203734583409236033340163475 305601875113854050010245213)
  ·
    refine ⟨114600703167695268753841955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305601875113854050010245213 114600703167695268753841955)
    ·
      refine ⟨171901054751542903130762933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114600703167695268753841955 171901054751542903130762933)
      ·
        refine ⟨16115723882957147168509025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171901054751542903130762933 16115723882957147168509025)
        ·
          refine ⟨12086792912217860376381769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16115723882957147168509025 12086792912217860376381769)
          ·
            refine ⟨9065094684163395282286327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12086792912217860376381769 9065094684163395282286327)
            ·
              refine ⟨13597642026245092923429491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9065094684163395282286327 13597642026245092923429491)
              ·
                refine ⟨20396463039367639385144237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13597642026245092923429491 20396463039367639385144237)
                ·
                  refine ⟨7648673639762864769429089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20396463039367639385144237 7648673639762864769429089)
                  ·
                    refine ⟨5736505229822148577071817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7648673639762864769429089 5736505229822148577071817)
                    ·
                      refine ⟨4302378922366611432803863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5736505229822148577071817 4302378922366611432803863)
                      ·
                        rfl

theorem cell23_8378853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_8378853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378853 prefixEnd_8378853 := by exact prefixLift 8378853
  have htrace : WordTrace (prefixWord ++ tailWord_8378853) baseStart_8378853 baseEnd_8378853 := by
    simpa [prefixWord, tailWord_8378853, baseEnd_8378853] using wordTrace_append hprefix tailTrace_8378853
  have hstable : (prefixWord ++ tailWord_8378853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378853).length < 2 ^ (prefixWord ++ tailWord_8378853).sum := by decide
  have hdescent : baseEnd_8378853 < baseStart_8378853 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378855 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 2, 7]
def baseStart_8378855 : Nat := 118140960795 + 8378855 * 2 ^ 59
def prefixEnd_8378855 : Nat := 4983230072969 + 3 ^ 40 * 8378855 * 2
def baseEnd_8378855 : Nat := 1434126649775973474992951

theorem tailTrace_8378855 : CollatzResearch.WordTrace tailWord_8378855 prefixEnd_8378855 1434126649775973474992951 := by
  unfold tailWord_8378855
  simp only [CollatzResearch.WordTrace]
  refine ⟨305601948059846804351818019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203734632039897869567878679 305601948059846804351818019)
  ·
    refine ⟨458402922089770206527727029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305601948059846804351818019 458402922089770206527727029)
    ·
      refine ⟨42975273945915956861974409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 458402922089770206527727029 42975273945915956861974409)
      ·
        refine ⟨32231455459436967646480807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42975273945915956861974409 32231455459436967646480807)
        ·
          refine ⟨48347183189155451469721211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32231455459436967646480807 48347183189155451469721211)
          ·
            refine ⟨72520774783733177204581817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48347183189155451469721211 72520774783733177204581817)
            ·
              refine ⟨54390581087799882903436363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72520774783733177204581817 54390581087799882903436363)
              ·
                refine ⟨81585871631699824355154545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54390581087799882903436363 81585871631699824355154545)
                ·
                  refine ⟨61189403723774868266365909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81585871631699824355154545 61189403723774868266365909)
                  ·
                    refine ⟨1434126649775973474992951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61189403723774868266365909 1434126649775973474992951)
                    ·
                      rfl

theorem cell23_8378855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_8378855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378855 prefixEnd_8378855 := by exact prefixLift 8378855
  have htrace : WordTrace (prefixWord ++ tailWord_8378855) baseStart_8378855 baseEnd_8378855 := by
    simpa [prefixWord, tailWord_8378855, baseEnd_8378855] using wordTrace_append hprefix tailTrace_8378855
  have hstable : (prefixWord ++ tailWord_8378855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378855).length < 2 ^ (prefixWord ++ tailWord_8378855).sum := by decide
  have hdescent : baseEnd_8378855 < baseStart_8378855 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378895 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 1, 6, 3]
def baseStart_8378895 : Nat := 118140960795 + 8378895 * 2 ^ 59
def prefixEnd_8378895 : Nat := 4983230072969 + 3 ^ 40 * 8378895 * 2
def baseEnd_8378895 : Nat := 4302400488554100268478669

theorem tailTrace_8378895 : CollatzResearch.WordTrace tailWord_8378895 prefixEnd_8378895 4302400488554100268478669 := by
  unfold tailWord_8378895
  simp only [CollatzResearch.WordTrace]
  refine ⟨305603406979701891183274139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203735604653134594122182759 305603406979701891183274139)
  ·
    refine ⟨458405110469552836774911209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305603406979701891183274139 458405110469552836774911209)
    ·
      refine ⟨343803832852164627581183407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458405110469552836774911209 343803832852164627581183407)
      ·
        refine ⟨515705749278246941371775111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343803832852164627581183407 515705749278246941371775111)
        ·
          refine ⟨773558623917370412057662667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515705749278246941371775111 773558623917370412057662667)
          ·
            refine ⟨1160337935876055618086494001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773558623917370412057662667 1160337935876055618086494001)
            ·
              refine ⟨870253451907041713564870501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1160337935876055618086494001 870253451907041713564870501)
              ·
                refine ⟨163172522232570321293413219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 870253451907041713564870501 163172522232570321293413219)
                ·
                  refine ⟨244758783348855481940119829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163172522232570321293413219 244758783348855481940119829)
                  ·
                    refine ⟨11473067969477600715943117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 244758783348855481940119829 11473067969477600715943117)
                    ·
                      refine ⟨4302400488554100268478669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11473067969477600715943117 4302400488554100268478669)
                      ·
                        rfl

theorem cell23_8378895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 6, 3].length) (baseStart_8378895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378895 prefixEnd_8378895 := by exact prefixLift 8378895
  have htrace : WordTrace (prefixWord ++ tailWord_8378895) baseStart_8378895 baseEnd_8378895 := by
    simpa [prefixWord, tailWord_8378895, baseEnd_8378895] using wordTrace_append hprefix tailTrace_8378895
  have hstable : (prefixWord ++ tailWord_8378895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378895).length < 2 ^ (prefixWord ++ tailWord_8378895).sum := by decide
  have hdescent : baseEnd_8378895 < baseStart_8378895 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378903 : List Nat := [1, 1, 3, 6, 1, 1, 2, 2, 2, 1, 3]
def baseStart_8378903 : Nat := 118140960795 + 8378903 * 2 ^ 59
def prefixEnd_8378903 : Nat := 4983230072969 + 3 ^ 40 * 8378903 * 2
def baseEnd_8378903 : Nat := 4302404596399336237178633

theorem tailTrace_8378903 : CollatzResearch.WordTrace tailWord_8378903 prefixEnd_8378903 4302404596399336237178633 := by
  unfold tailWord_8378903
  simp only [CollatzResearch.WordTrace]
  refine ⟨305603698763672908549565363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203735799175781939033043575 305603698763672908549565363)
  ·
    refine ⟨458405548145509362824348045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305603698763672908549565363 458405548145509362824348045)
    ·
      refine ⟨171902080554566011059130517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 458405548145509362824348045 171902080554566011059130517)
      ·
        refine ⟨8057910025995281768396743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 171902080554566011059130517 8057910025995281768396743)
        ·
          refine ⟨12086865038992922652595115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8057910025995281768396743 12086865038992922652595115)
          ·
            refine ⟨18130297558489383978892673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12086865038992922652595115 18130297558489383978892673)
            ·
              refine ⟨13597723168867037984169505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18130297558489383978892673 13597723168867037984169505)
              ·
                refine ⟨10198292376650278488127129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13597723168867037984169505 10198292376650278488127129)
                ·
                  refine ⟨7648719282487708866095347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10198292376650278488127129 7648719282487708866095347)
                  ·
                    refine ⟨11473078923731563299143021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7648719282487708866095347 11473078923731563299143021)
                    ·
                      refine ⟨4302404596399336237178633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11473078923731563299143021 4302404596399336237178633)
                      ·
                        rfl

theorem cell23_8378903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_8378903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378903 prefixEnd_8378903 := by exact prefixLift 8378903
  have htrace : WordTrace (prefixWord ++ tailWord_8378903) baseStart_8378903 baseEnd_8378903 := by
    simpa [prefixWord, tailWord_8378903, baseEnd_8378903] using wordTrace_append hprefix tailTrace_8378903
  have hstable : (prefixWord ++ tailWord_8378903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378903).length < 2 ^ (prefixWord ++ tailWord_8378903).sum := by decide
  have hdescent : baseEnd_8378903 < baseStart_8378903 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378905 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 4, 2, 4]
def baseStart_8378905 : Nat := 118140960795 + 8378905 * 2 ^ 59
def prefixEnd_8378905 : Nat := 4983230072969 + 3 ^ 40 * 8378905 * 2
def baseEnd_8378905 : Nat := 4302405623360645229353623

theorem tailTrace_8378905 : CollatzResearch.WordTrace tailWord_8378905 prefixEnd_8378905 4302405623360645229353623 := by
  unfold tailWord_8378905
  simp only [CollatzResearch.WordTrace]
  refine ⟨305603771709665662891138169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203735847806443775260758779 305603771709665662891138169)
  ·
    refine ⟨229202828782249247168353627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305603771709665662891138169 229202828782249247168353627)
    ·
      refine ⟨343804243173373870752530441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229202828782249247168353627 343804243173373870752530441)
      ·
        refine ⟨257853182380030403064397831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343804243173373870752530441 257853182380030403064397831)
        ·
          refine ⟨386779773570045604596596747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257853182380030403064397831 386779773570045604596596747)
          ·
            refine ⟨580169660355068406894895121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386779773570045604596596747 580169660355068406894895121)
            ·
              refine ⟨435127245266301305171171341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 580169660355068406894895121 435127245266301305171171341)
              ·
                refine ⟨163172716974862989439189253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 435127245266301305171171341 163172716974862989439189253)
                ·
                  refine ⟨30594884432786810519847985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 163172716974862989439189253 30594884432786810519847985)
                  ·
                    refine ⟨22946163324590107889885989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30594884432786810519847985 22946163324590107889885989)
                    ·
                      refine ⟨4302405623360645229353623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22946163324590107889885989 4302405623360645229353623)
                      ·
                        rfl

theorem cell23_8378905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_8378905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378905 prefixEnd_8378905 := by exact prefixLift 8378905
  have htrace : WordTrace (prefixWord ++ tailWord_8378905) baseStart_8378905 baseEnd_8378905 := by
    simpa [prefixWord, tailWord_8378905, baseEnd_8378905] using wordTrace_append hprefix tailTrace_8378905
  have hstable : (prefixWord ++ tailWord_8378905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378905).length < 2 ^ (prefixWord ++ tailWord_8378905).sum := by decide
  have hdescent : baseEnd_8378905 < baseStart_8378905 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378922 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_8378922 : Nat := 118140960795 + 8378922 * 2 ^ 59
def prefixEnd_8378922 : Nat := 4983230072969 + 3 ^ 40 * 8378922 * 2
def baseEnd_8378922 : Nat := 4302414352531771662841045

theorem tailTrace_8378922 : CollatzResearch.WordTrace tailWord_8378922 prefixEnd_8378922 4302414352531771662841045 := by
  unfold tailWord_8378922
  simp only [CollatzResearch.WordTrace]
  refine ⟨76401097937651018698626755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203736261167069383196338013 76401097937651018698626755)
  ·
    refine ⟨114601646906476528047940133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76401097937651018698626755 114601646906476528047940133)
    ·
      refine ⟨21487808794964349008988775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114601646906476528047940133 21487808794964349008988775)
      ·
        refine ⟨32231713192446523513483163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21487808794964349008988775 32231713192446523513483163)
        ·
          refine ⟨48347569788669785270224745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32231713192446523513483163 48347569788669785270224745)
          ·
            refine ⟨36260677341502338952668559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48347569788669785270224745 36260677341502338952668559)
            ·
              refine ⟨54391016012253508429002839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36260677341502338952668559 54391016012253508429002839)
              ·
                refine ⟨81586524018380262643504259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54391016012253508429002839 81586524018380262643504259)
                ·
                  refine ⟨122379786027570393965256389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81586524018380262643504259 122379786027570393965256389)
                  ·
                    refine ⟨22946209880169448868485573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 122379786027570393965256389 22946209880169448868485573)
                    ·
                      refine ⟨4302414352531771662841045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22946209880169448868485573 4302414352531771662841045)
                      ·
                        rfl

theorem cell23_8378922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_8378922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378922 prefixEnd_8378922 := by exact prefixLift 8378922
  have htrace : WordTrace (prefixWord ++ tailWord_8378922) baseStart_8378922 baseEnd_8378922 := by
    simpa [prefixWord, tailWord_8378922, baseEnd_8378922] using wordTrace_append hprefix tailTrace_8378922
  have hstable : (prefixWord ++ tailWord_8378922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378922).length < 2 ^ (prefixWord ++ tailWord_8378922).sum := by decide
  have hdescent : baseEnd_8378922 < baseStart_8378922 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378949 : List Nat := [1, 3, 1, 1, 1, 6, 2, 3, 5]
def baseStart_8378949 : Nat := 118140960795 + 8378949 * 2 ^ 59
def prefixEnd_8378949 : Nat := 4983230072969 + 3 ^ 40 * 8378949 * 2
def baseEnd_8378949 : Nat := 478047579612160339689269

theorem tailTrace_8378949 : CollatzResearch.WordTrace tailWord_8378949 prefixEnd_8378949 478047579612160339689269 := by
  unfold tailWord_8378949
  simp only [CollatzResearch.WordTrace]
  refine ⟨305605376521506258405739901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203736917681004172270493267 305605376521506258405739901)
  ·
    refine ⟨114602016195564846902152463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305605376521506258405739901 114602016195564846902152463)
    ·
      refine ⟨171903024293347270353228695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114602016195564846902152463 171903024293347270353228695)
      ·
        refine ⟨257854536440020905529843043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171903024293347270353228695 257854536440020905529843043)
        ·
          refine ⟨386781804660031358294764565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257854536440020905529843043 386781804660031358294764565)
          ·
            refine ⟨18130397093438969920067089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 386781804660031358294764565 18130397093438969920067089)
            ·
              refine ⟨13597797820079227440050317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18130397093438969920067089 13597797820079227440050317)
              ·
                refine ⟨5099174182529710290018869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13597797820079227440050317 5099174182529710290018869)
                ·
                  refine ⟨478047579612160339689269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5099174182529710290018869 478047579612160339689269)
                  ·
                    rfl

theorem cell23_8378949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 3, 5].length) (baseStart_8378949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378949 prefixEnd_8378949 := by exact prefixLift 8378949
  have htrace : WordTrace (prefixWord ++ tailWord_8378949) baseStart_8378949 baseEnd_8378949 := by
    simpa [prefixWord, tailWord_8378949, baseEnd_8378949] using wordTrace_append hprefix tailTrace_8378949
  have hstable : (prefixWord ++ tailWord_8378949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378949).length < 2 ^ (prefixWord ++ tailWord_8378949).sum := by decide
  have hdescent : baseEnd_8378949 < baseStart_8378949 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378955 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 5]
def baseStart_8378955 : Nat := 118140960795 + 8378955 * 2 ^ 59
def prefixEnd_8378955 : Nat := 4983230072969 + 3 ^ 40 * 8378955 * 2
def baseEnd_8378955 : Nat := 4302431297393370033728393

theorem tailTrace_8378955 : CollatzResearch.WordTrace tailWord_8378955 prefixEnd_8378955 4302431297393370033728393 := by
  unfold tailWord_8378955
  simp only [CollatzResearch.WordTrace]
  refine ⟨305605595359484521430458319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203737063572989680953638879 305605595359484521430458319)
  ·
    refine ⟨458408393039226782145687479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305605595359484521430458319 458408393039226782145687479)
    ·
      refine ⟨687612589558840173218531219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458408393039226782145687479 687612589558840173218531219)
      ·
        refine ⟨1031418884338260259827796829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687612589558840173218531219 1031418884338260259827796829)
        ·
          refine ⟨386782081626847597435423811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1031418884338260259827796829 386782081626847597435423811)
          ·
            refine ⟨580173122440271396153135717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386782081626847597435423811 580173122440271396153135717)
            ·
              refine ⟨108782460457550886778712947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 580173122440271396153135717 108782460457550886778712947)
              ·
                refine ⟨163173690686326330168069421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108782460457550886778712947 163173690686326330168069421)
                ·
                  refine ⟨61190134007372373813026033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163173690686326330168069421 61190134007372373813026033)
                  ·
                    refine ⟨45892600505529280359769525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61190134007372373813026033 45892600505529280359769525)
                    ·
                      refine ⟨4302431297393370033728393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45892600505529280359769525 4302431297393370033728393)
                      ·
                        rfl

theorem cell23_8378955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 5].length) (baseStart_8378955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378955 prefixEnd_8378955 := by exact prefixLift 8378955
  have htrace : WordTrace (prefixWord ++ tailWord_8378955) baseStart_8378955 baseEnd_8378955 := by
    simpa [prefixWord, tailWord_8378955, baseEnd_8378955] using wordTrace_append hprefix tailTrace_8378955
  have hstable : (prefixWord ++ tailWord_8378955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378955).length < 2 ^ (prefixWord ++ tailWord_8378955).sum := by decide
  have hdescent : baseEnd_8378955 < baseStart_8378955 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378962 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 4, 5]
def baseStart_8378962 : Nat := 118140960795 + 8378962 * 2 ^ 59
def prefixEnd_8378962 : Nat := 4983230072969 + 3 ^ 40 * 8378962 * 2
def baseEnd_8378962 : Nat := 1434144963919317168780287

theorem tailTrace_8378962 : CollatzResearch.WordTrace tailWord_8378962 prefixEnd_8378962 1434144963919317168780287 := by
  unfold tailWord_8378962
  simp only [CollatzResearch.WordTrace]
  refine ⟨76401462667614790406490785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203737233780306107750642093 76401462667614790406490785)
  ·
    refine ⟨57301097000711092804868089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76401462667614790406490785 57301097000711092804868089)
    ·
      refine ⟨42975822750533319603651067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57301097000711092804868089 42975822750533319603651067)
      ·
        refine ⟨64463734125799979405476601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42975822750533319603651067 64463734125799979405476601)
        ·
          refine ⟨48347800594349984554107451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64463734125799979405476601 48347800594349984554107451)
          ·
            refine ⟨72521700891524976831161177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48347800594349984554107451 72521700891524976831161177)
            ·
              refine ⟨54391275668643732623370883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72521700891524976831161177 54391275668643732623370883)
              ·
                refine ⟨81586913502965598935056325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54391275668643732623370883 81586913502965598935056325)
                ·
                  refine ⟨15297546281806049800323061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81586913502965598935056325 15297546281806049800323061)
                  ·
                    refine ⟨1434144963919317168780287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15297546281806049800323061 1434144963919317168780287)
                    ·
                      rfl

theorem cell23_8378962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_8378962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378962 prefixEnd_8378962 := by exact prefixLift 8378962
  have htrace : WordTrace (prefixWord ++ tailWord_8378962) baseStart_8378962 baseEnd_8378962 := by
    simpa [prefixWord, tailWord_8378962, baseEnd_8378962] using wordTrace_append hprefix tailTrace_8378962
  have hstable : (prefixWord ++ tailWord_8378962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378962).length < 2 ^ (prefixWord ++ tailWord_8378962).sum := by decide
  have hdescent : baseEnd_8378962 < baseStart_8378962 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8378995 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 6]
def baseStart_8378995 : Nat := 118140960795 + 8378995 * 2 ^ 59
def prefixEnd_8378995 : Nat := 4983230072969 + 3 ^ 40 * 8378995 * 2
def baseEnd_8378995 : Nat := 4302451836619549877228209

theorem tailTrace_8378995 : CollatzResearch.WordTrace tailWord_8378995 prefixEnd_8378995 4302451836619549877228209 := by
  unfold tailWord_8378995
  simp only [CollatzResearch.WordTrace]
  refine ⟨305607054279339608261914439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203738036186226405507942959 305607054279339608261914439)
  ·
    refine ⟨458410581419009412392871659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305607054279339608261914439 458410581419009412392871659)
    ·
      refine ⟨687615872128514118589307489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458410581419009412392871659 687615872128514118589307489)
      ·
        refine ⟨515711904096385588941980617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 687615872128514118589307489 515711904096385588941980617)
        ·
          refine ⟨386783928072289191706485463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515711904096385588941980617 386783928072289191706485463)
          ·
            refine ⟨580175892108433787559728195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386783928072289191706485463 580175892108433787559728195)
            ·
              refine ⟨870263838162650681339592293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580175892108433787559728195 870263838162650681339592293)
              ·
                refine ⟨163174469655497002751173555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 870263838162650681339592293 163174469655497002751173555)
                ·
                  refine ⟨244761704483245504126760333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163174469655497002751173555 244761704483245504126760333)
                  ·
                    refine ⟨91785639181217064047535125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 244761704483245504126760333 91785639181217064047535125)
                    ·
                      refine ⟨4302451836619549877228209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91785639181217064047535125 4302451836619549877228209)
                      ·
                        rfl

theorem cell23_8378995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 6].length) (baseStart_8378995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8378995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8378995 prefixEnd_8378995 := by exact prefixLift 8378995
  have htrace : WordTrace (prefixWord ++ tailWord_8378995) baseStart_8378995 baseEnd_8378995 := by
    simpa [prefixWord, tailWord_8378995, baseEnd_8378995] using wordTrace_append hprefix tailTrace_8378995
  have hstable : (prefixWord ++ tailWord_8378995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8378995).length < 2 ^ (prefixWord ++ tailWord_8378995).sum := by decide
  have hdescent : baseEnd_8378995 < baseStart_8378995 := by decide
  rcases family_descends (prefixWord ++ tailWord_8378995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379022 : List Nat := [4, 1, 1, 3, 1, 1, 1, 3, 8]
def baseStart_8379022 : Nat := 118140960795 + 8379022 * 2 ^ 59
def prefixEnd_8379022 : Nat := 4983230072969 + 3 ^ 40 * 8379022 * 2
def baseEnd_8379022 : Nat := 478051744510802363510065

theorem tailTrace_8379022 : CollatzResearch.WordTrace tailWord_8379022 prefixEnd_8379022 478051744510802363510065 := by
  unfold tailWord_8379022
  simp only [CollatzResearch.WordTrace]
  refine ⟨38201004881280223984143415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203738692700161194582098213 38201004881280223984143415)
  ·
    refine ⟨57301507321920335976215123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38201004881280223984143415 57301507321920335976215123)
    ·
      refine ⟨85952260982880503964322685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57301507321920335976215123 85952260982880503964322685)
      ·
        refine ⟨32232097868580188986621007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85952260982880503964322685 32232097868580188986621007)
        ·
          refine ⟨48348146802870283479931511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32232097868580188986621007 48348146802870283479931511)
          ·
            refine ⟨72522220204305425219897267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48348146802870283479931511 72522220204305425219897267)
            ·
              refine ⟨108783330306458137829845901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72522220204305425219897267 108783330306458137829845901)
              ·
                refine ⟨40793748864921801686192213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108783330306458137829845901 40793748864921801686192213)
                ·
                  refine ⟨478051744510802363510065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40793748864921801686192213 478051744510802363510065)
                  ·
                    rfl

theorem cell23_8379022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 8].length) (baseStart_8379022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379022 prefixEnd_8379022 := by exact prefixLift 8379022
  have htrace : WordTrace (prefixWord ++ tailWord_8379022) baseStart_8379022 baseEnd_8379022 := by
    simpa [prefixWord, tailWord_8379022, baseEnd_8379022] using wordTrace_append hprefix tailTrace_8379022
  have hstable : (prefixWord ++ tailWord_8379022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379022).length < 2 ^ (prefixWord ++ tailWord_8379022).sum := by decide
  have hdescent : baseEnd_8379022 < baseStart_8379022 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379026 : List Nat := [3, 2, 3, 1, 2, 1, 3, 1, 3, 4]
def baseStart_8379026 : Nat := 118140960795 + 8379026 * 2 ^ 59
def prefixEnd_8379026 : Nat := 4983230072969 + 3 ^ 40 * 8379026 * 2
def baseEnd_8379026 : Nat := 1434155918173279751980189

theorem tailTrace_8379026 : CollatzResearch.WordTrace tailWord_8379026 prefixEnd_8379026 1434155918173279751980189 := by
  unfold tailWord_8379026
  simp only [CollatzResearch.WordTrace]
  refine ⟨76402046235556825139073233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203738789961484867037528621 76402046235556825139073233)
  ·
    refine ⟨57301534676667618854304925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76402046235556825139073233 57301534676667618854304925)
    ·
      refine ⟨21488075503750357070364347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57301534676667618854304925 21488075503750357070364347)
      ·
        refine ⟨32232113255625535605546521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21488075503750357070364347 32232113255625535605546521)
        ·
          refine ⟨24174084941719151704159891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32232113255625535605546521 24174084941719151704159891)
          ·
            refine ⟨36261127412578727556239837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24174084941719151704159891 36261127412578727556239837)
            ·
              refine ⟨13597922779717022833589939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36261127412578727556239837 13597922779717022833589939)
              ·
                refine ⟨20396884169575534250384909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13597922779717022833589939 20396884169575534250384909)
                ·
                  refine ⟨7648831563590825343894341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20396884169575534250384909 7648831563590825343894341)
                  ·
                    refine ⟨1434155918173279751980189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7648831563590825343894341 1434155918173279751980189)
                    ·
                      rfl

theorem cell23_8379026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_8379026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379026 prefixEnd_8379026 := by exact prefixLift 8379026
  have htrace : WordTrace (prefixWord ++ tailWord_8379026) baseStart_8379026 baseEnd_8379026 := by
    simpa [prefixWord, tailWord_8379026, baseEnd_8379026] using wordTrace_append hprefix tailTrace_8379026
  have hstable : (prefixWord ++ tailWord_8379026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379026).length < 2 ^ (prefixWord ++ tailWord_8379026).sum := by decide
  have hdescent : baseEnd_8379026 < baseStart_8379026 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379073 : List Nat := [1, 2, 6, 2, 1, 1, 2, 2, 6]
def baseStart_8379073 : Nat := 118140960795 + 8379073 * 2 ^ 59
def prefixEnd_8379073 : Nat := 4983230072969 + 3 ^ 40 * 8379073 * 2
def baseEnd_8379073 : Nat := 478054654234511174672539

theorem tailTrace_8379073 : CollatzResearch.WordTrace tailWord_8379073 prefixEnd_8379073 478054654234511174672539 := by
  unfold tailWord_8379073
  simp only [CollatzResearch.WordTrace]
  refine ⟨305609899173057027583253873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203739932782038018388835915 305609899173057027583253873)
  ·
    refine ⟨229207424379792770687440405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305609899173057027583253873 229207424379792770687440405)
    ·
      refine ⟨10744098017802786125973769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 229207424379792770687440405 10744098017802786125973769)
      ·
        refine ⟨8058073513352089594480327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10744098017802786125973769 8058073513352089594480327)
        ·
          refine ⟨12087110270028134391720491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8058073513352089594480327 12087110270028134391720491)
          ·
            refine ⟨18130665405042201587580737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12087110270028134391720491 18130665405042201587580737)
            ·
              refine ⟨13597999053781651190685553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18130665405042201587580737 13597999053781651190685553)
              ·
                refine ⟨10198499290336238393014165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13597999053781651190685553 10198499290336238393014165)
                ·
                  refine ⟨478054654234511174672539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10198499290336238393014165 478054654234511174672539)
                  ·
                    rfl

theorem cell23_8379073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 6].length) (baseStart_8379073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379073 prefixEnd_8379073 := by exact prefixLift 8379073
  have htrace : WordTrace (prefixWord ++ tailWord_8379073) baseStart_8379073 baseEnd_8379073 := by
    simpa [prefixWord, tailWord_8379073, baseEnd_8379073] using wordTrace_append hprefix tailTrace_8379073
  have hstable : (prefixWord ++ tailWord_8379073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379073).length < 2 ^ (prefixWord ++ tailWord_8379073).sum := by decide
  have hdescent : baseEnd_8379073 < baseStart_8379073 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379119 : List Nat := [1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 4]
def baseStart_8379119 : Nat := 118140960795 + 8379119 * 2 ^ 59
def prefixEnd_8379119 : Nat := 4983230072969 + 3 ^ 40 * 8379119 * 2
def baseEnd_8379119 : Nat := 4302515508220707392077639

theorem tailTrace_8379119 : CollatzResearch.WordTrace tailWord_8379119 prefixEnd_8379119 4302515508220707392077639 := by
  unfold tailWord_8379119
  simp only [CollatzResearch.WordTrace]
  refine ⟨305611576930890377439428411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203741051287260251626285607 305611576930890377439428411)
  ·
    refine ⟨458417365396335566159142617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305611576930890377439428411 458417365396335566159142617)
    ·
      refine ⟨343813024047251674619356963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458417365396335566159142617 343813024047251674619356963)
      ·
        refine ⟨515719536070877511929035445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343813024047251674619356963 515719536070877511929035445)
        ·
          refine ⟨48348706506644766743347073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 515719536070877511929035445 48348706506644766743347073)
          ·
            refine ⟨36261529879983575057510305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48348706506644766743347073 36261529879983575057510305)
            ·
              refine ⟨27196147409987681293132729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36261529879983575057510305 27196147409987681293132729)
              ·
                refine ⟨20397110557490760969849547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27196147409987681293132729 20397110557490760969849547)
                ·
                  refine ⟨30595665836236141454774321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20397110557490760969849547 30595665836236141454774321)
                  ·
                    refine ⟨22946749377177106091080741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30595665836236141454774321 22946749377177106091080741)
                    ·
                      refine ⟨4302515508220707392077639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22946749377177106091080741 4302515508220707392077639)
                      ·
                        rfl

theorem cell23_8379119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 4].length) (baseStart_8379119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379119 prefixEnd_8379119 := by exact prefixLift 8379119
  have htrace : WordTrace (prefixWord ++ tailWord_8379119) baseStart_8379119 baseEnd_8379119 := by
    simpa [prefixWord, tailWord_8379119, baseEnd_8379119] using wordTrace_append hprefix tailTrace_8379119
  have hstable : (prefixWord ++ tailWord_8379119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379119).length < 2 ^ (prefixWord ++ tailWord_8379119).sum := by decide
  have hdescent : baseEnd_8379119 < baseStart_8379119 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379140 : List Nat := [2, 3, 2, 2, 1, 1, 1, 6, 1, 2, 2]
def baseStart_8379140 : Nat := 118140960795 + 8379140 * 2 ^ 59
def prefixEnd_8379140 : Nat := 4983230072969 + 3 ^ 40 * 8379140 * 2
def baseEnd_8379140 : Nat := 4302526291314451809915043

theorem tailTrace_8379140 : CollatzResearch.WordTrace tailWord_8379140 prefixEnd_8379140 4302526291314451809915043 := by
  unfold tailWord_8379140
  simp only [CollatzResearch.WordTrace]
  refine ⟨152806171431907149012971437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203741561909209532017295249 152806171431907149012971437)
  ·
    refine ⟨57302314286965180879864289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152806171431907149012971437 57302314286965180879864289)
    ·
      refine ⟨42976735715223885659898217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57302314286965180879864289 42976735715223885659898217)
      ·
        refine ⟨32232551786417914244923663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42976735715223885659898217 32232551786417914244923663)
        ·
          refine ⟨48348827679626871367385495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32232551786417914244923663 48348827679626871367385495)
          ·
            refine ⟨72523241519440307051078243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48348827679626871367385495 72523241519440307051078243)
            ·
              refine ⟨108784862279160460576617365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72523241519440307051078243 108784862279160460576617365)
              ·
                refine ⟨5099290419335646589528939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108784862279160460576617365 5099290419335646589528939)
                ·
                  refine ⟨7648935629003469884293409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5099290419335646589528939 7648935629003469884293409)
                  ·
                    refine ⟨5736701721752602413220057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7648935629003469884293409 5736701721752602413220057)
                    ·
                      refine ⟨4302526291314451809915043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5736701721752602413220057 4302526291314451809915043)
                      ·
                        rfl

theorem cell23_8379140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_8379140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379140 prefixEnd_8379140 := by exact prefixLift 8379140
  have htrace : WordTrace (prefixWord ++ tailWord_8379140) baseStart_8379140 baseEnd_8379140 := by
    simpa [prefixWord, tailWord_8379140, baseEnd_8379140] using wordTrace_append hprefix tailTrace_8379140
  have hstable : (prefixWord ++ tailWord_8379140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379140).length < 2 ^ (prefixWord ++ tailWord_8379140).sum := by decide
  have hdescent : baseEnd_8379140 < baseStart_8379140 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379217 : List Nat := [1, 2, 2, 1, 7, 1, 1, 2, 1, 3, 2]
def baseStart_8379217 : Nat := 118140960795 + 8379217 * 2 ^ 59
def prefixEnd_8379217 : Nat := 4983230072969 + 3 ^ 40 * 8379217 * 2
def baseEnd_8379217 : Nat := 4302565829324848008652189

theorem tailTrace_8379217 : CollatzResearch.WordTrace tailWord_8379217 prefixEnd_8379217 4302565829324848008652189 := by
  unfold tailWord_8379217
  simp only [CollatzResearch.WordTrace]
  refine ⟨305615151284535340176495905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203743434189690226784330603 305615151284535340176495905)
  ·
    refine ⟨229211363463401505132371929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305615151284535340176495905 229211363463401505132371929)
    ·
      refine ⟨171908522597551128849278947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229211363463401505132371929 171908522597551128849278947)
      ·
        refine ⟨257862783896326693273918421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171908522597551128849278947 257862783896326693273918421)
        ·
          refine ⟨6043658997570156873607463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 257862783896326693273918421 6043658997570156873607463)
          ·
            refine ⟨9065488496355235310411195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6043658997570156873607463 9065488496355235310411195)
            ·
              refine ⟨13598232744532852965616793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9065488496355235310411195 13598232744532852965616793)
              ·
                refine ⟨10198674558399639724212595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13598232744532852965616793 10198674558399639724212595)
                ·
                  refine ⟨15298011837599459586318893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10198674558399639724212595 15298011837599459586318893)
                  ·
                    refine ⟨5736754439099797344869585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15298011837599459586318893 5736754439099797344869585)
                    ·
                      refine ⟨4302565829324848008652189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5736754439099797344869585 4302565829324848008652189)
                      ·
                        rfl

theorem cell23_8379217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 1, 3, 2].length) (baseStart_8379217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379217 prefixEnd_8379217 := by exact prefixLift 8379217
  have htrace : WordTrace (prefixWord ++ tailWord_8379217) baseStart_8379217 baseEnd_8379217 := by
    simpa [prefixWord, tailWord_8379217, baseEnd_8379217] using wordTrace_append hprefix tailTrace_8379217
  have hstable : (prefixWord ++ tailWord_8379217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379217).length < 2 ^ (prefixWord ++ tailWord_8379217).sum := by decide
  have hdescent : baseEnd_8379217 < baseStart_8379217 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379253 : List Nat := [1, 3, 4, 1, 1, 3, 1, 4, 5]
def baseStart_8379253 : Nat := 118140960795 + 8379253 * 2 ^ 59
def prefixEnd_8379253 : Nat := 4983230072969 + 3 ^ 40 * 8379253 * 2
def baseEnd_8379253 : Nat := 478064923847601096422447

theorem tailTrace_8379253 : CollatzResearch.WordTrace tailWord_8379253 prefixEnd_8379253 478064923847601096422447 := by
  unfold tailWord_8379253
  simp only [CollatzResearch.WordTrace]
  refine ⟨305616464312404918324806413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203744309541603278883204275 305616464312404918324806413)
  ·
    refine ⟨114606174117151844371802405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305616464312404918324806413 114606174117151844371802405)
    ·
      refine ⟨21488657646965970819712951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114606174117151844371802405 21488657646965970819712951)
      ·
        refine ⟨32232986470448956229569427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21488657646965970819712951 32232986470448956229569427)
        ·
          refine ⟨48349479705673434344354141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32232986470448956229569427 48349479705673434344354141)
          ·
            refine ⟨18131054889627537879132803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48349479705673434344354141 18131054889627537879132803)
            ·
              refine ⟨27196582334441306818699205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18131054889627537879132803 27196582334441306818699205)
              ·
                refine ⟨5099359187707745028506101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27196582334441306818699205 5099359187707745028506101)
                ·
                  refine ⟨478064923847601096422447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5099359187707745028506101 478064923847601096422447)
                  ·
                    rfl

theorem cell23_8379253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 4, 5].length) (baseStart_8379253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379253 prefixEnd_8379253 := by exact prefixLift 8379253
  have htrace : WordTrace (prefixWord ++ tailWord_8379253) baseStart_8379253 baseEnd_8379253 := by
    simpa [prefixWord, tailWord_8379253, baseEnd_8379253] using wordTrace_append hprefix tailTrace_8379253
  have hstable : (prefixWord ++ tailWord_8379253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379253).length < 2 ^ (prefixWord ++ tailWord_8379253).sum := by decide
  have hdescent : baseEnd_8379253 < baseStart_8379253 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379259 : List Nat := [1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 5]
def baseStart_8379259 : Nat := 118140960795 + 8379259 * 2 ^ 59
def prefixEnd_8379259 : Nat := 4983230072969 + 3 ^ 40 * 8379259 * 2
def baseEnd_8379259 : Nat := 4302587395512336844326995

theorem tailTrace_8379259 : CollatzResearch.WordTrace tailWord_8379259 prefixEnd_8379259 4302587395512336844326995 := by
  unfold tailWord_8379259
  simp only [CollatzResearch.WordTrace]
  refine ⟨305616683150383181349524831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203744455433588787566349887 305616683150383181349524831)
  ·
    refine ⟨458425024725574772024287247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305616683150383181349524831 458425024725574772024287247)
    ·
      refine ⟨687637537088362158036430871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458425024725574772024287247 687637537088362158036430871)
      ·
        refine ⟨1031456305632543237054646307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687637537088362158036430871 1031456305632543237054646307)
        ·
          refine ⟨1547184458448814855581969461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1031456305632543237054646307 1547184458448814855581969461)
          ·
            refine ⟨145048542979576392710809637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1547184458448814855581969461 145048542979576392710809637)
            ·
              refine ⟨27196601808670573633276807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145048542979576392710809637 27196601808670573633276807)
              ·
                refine ⟨40794902713005860449915211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27196601808670573633276807 40794902713005860449915211)
                ·
                  refine ⟨61192354069508790674872817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40794902713005860449915211 61192354069508790674872817)
                  ·
                    refine ⟨45894265552131593006154613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61192354069508790674872817 45894265552131593006154613)
                    ·
                      refine ⟨4302587395512336844326995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45894265552131593006154613 4302587395512336844326995)
                      ·
                        rfl

theorem cell23_8379259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 5].length) (baseStart_8379259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379259 prefixEnd_8379259 := by exact prefixLift 8379259
  have htrace : WordTrace (prefixWord ++ tailWord_8379259) baseStart_8379259 baseEnd_8379259 := by
    simpa [prefixWord, tailWord_8379259, baseEnd_8379259] using wordTrace_append hprefix tailTrace_8379259
  have hstable : (prefixWord ++ tailWord_8379259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379259).length < 2 ^ (prefixWord ++ tailWord_8379259).sum := by decide
  have hdescent : baseEnd_8379259 < baseStart_8379259 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379299 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 6]
def baseStart_8379299 : Nat := 118140960795 + 8379299 * 2 ^ 59
def prefixEnd_8379299 : Nat := 4983230072969 + 3 ^ 40 * 8379299 * 2
def baseEnd_8379299 : Nat := 4302607934738516687826811

theorem tailTrace_8379299 : CollatzResearch.WordTrace tailWord_8379299 prefixEnd_8379299 4302607934738516687826811 := by
  unfold tailWord_8379299
  simp only [CollatzResearch.WordTrace]
  refine ⟨305618142070238268180980951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203745428046825512120653967 305618142070238268180980951)
  ·
    refine ⟨458427213105357402271471427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305618142070238268180980951 458427213105357402271471427)
    ·
      refine ⟨687640819658036103407207141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458427213105357402271471427 687640819658036103407207141)
      ·
        refine ⟨128932653685881769388851339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 687640819658036103407207141 128932653685881769388851339)
        ·
          refine ⟨193398980528822654083277009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128932653685881769388851339 193398980528822654083277009)
          ·
            refine ⟨145049235396616990562457757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193398980528822654083277009 145049235396616990562457757)
            ·
              refine ⟨54393463273731371460921659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145049235396616990562457757 54393463273731371460921659)
              ·
                refine ⟨81590194910597057191382489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54393463273731371460921659 81590194910597057191382489)
                ·
                  refine ⟨61192646182947792893536867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81590194910597057191382489 61192646182947792893536867)
                  ·
                    refine ⟨91788969274421689340305301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61192646182947792893536867 91788969274421689340305301)
                    ·
                      refine ⟨4302607934738516687826811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91788969274421689340305301 4302607934738516687826811)
                      ·
                        rfl

theorem cell23_8379299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_8379299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379299 prefixEnd_8379299 := by exact prefixLift 8379299
  have htrace : WordTrace (prefixWord ++ tailWord_8379299) baseStart_8379299 baseEnd_8379299 := by
    simpa [prefixWord, tailWord_8379299, baseEnd_8379299] using wordTrace_append hprefix tailTrace_8379299
  have hstable : (prefixWord ++ tailWord_8379299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379299).length < 2 ^ (prefixWord ++ tailWord_8379299).sum := by decide
  have hdescent : baseEnd_8379299 < baseStart_8379299 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379370 : List Nat := [3, 1, 3, 1, 2, 2, 3, 1, 3, 1, 3]
def baseStart_8379370 : Nat := 118140960795 + 8379370 * 2 ^ 59
def prefixEnd_8379370 : Nat := 4983230072969 + 3 ^ 40 * 8379370 * 2
def baseEnd_8379370 : Nat := 4302644391864985910038985

theorem tailTrace_8379370 : CollatzResearch.WordTrace tailWord_8379370 prefixEnd_8379370 4302644391864985910038985 := by
  unfold tailWord_8379370
  simp only [CollatzResearch.WordTrace]
  refine ⟨76405182913245261826703891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203747154435320698204543709 76405182913245261826703891)
  ·
    refine ⟨114607774369867892740055837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76405182913245261826703891 114607774369867892740055837)
    ·
      refine ⟨42977915388700459777520939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114607774369867892740055837 42977915388700459777520939)
      ·
        refine ⟨64466873083050689666281409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42977915388700459777520939 64466873083050689666281409)
        ·
          refine ⟨48350154812288017249711057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64466873083050689666281409 48350154812288017249711057)
          ·
            refine ⟨36262616109216012937283293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48350154812288017249711057 36262616109216012937283293)
            ·
              refine ⟨13598481040956004851481235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36262616109216012937283293 13598481040956004851481235)
              ·
                refine ⟨20397721561434007277221853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13598481040956004851481235 20397721561434007277221853)
                ·
                  refine ⟨7649145585537752728958195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20397721561434007277221853 7649145585537752728958195)
                  ·
                    refine ⟨11473718378306629093437293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7649145585537752728958195 11473718378306629093437293)
                    ·
                      refine ⟨4302644391864985910038985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11473718378306629093437293 4302644391864985910038985)
                      ·
                        rfl

theorem cell23_8379370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_8379370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379370 prefixEnd_8379370 := by exact prefixLift 8379370
  have htrace : WordTrace (prefixWord ++ tailWord_8379370) baseStart_8379370 baseEnd_8379370 := by
    simpa [prefixWord, tailWord_8379370, baseEnd_8379370] using wordTrace_append hprefix tailTrace_8379370
  have hstable : (prefixWord ++ tailWord_8379370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379370).length < 2 ^ (prefixWord ++ tailWord_8379370).sum := by decide
  have hdescent : baseEnd_8379370 < baseStart_8379370 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379376 : List Nat := [2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 4]
def baseStart_8379376 : Nat := 118140960795 + 8379376 * 2 ^ 59
def prefixEnd_8379376 : Nat := 4983230072969 + 3 ^ 40 * 8379376 * 2
def baseEnd_8379376 : Nat := 4302647472748912886563957

theorem tailTrace_8379376 : CollatzResearch.WordTrace tailWord_8379376 prefixEnd_8379376 4302647472748912886563957 := by
  unfold tailWord_8379376
  simp only [CollatzResearch.WordTrace]
  refine ⟨152810475245479655165766991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203747300327306206887689321 152810475245479655165766991)
  ·
    refine ⟨229215712868219482748650487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152810475245479655165766991 229215712868219482748650487)
    ·
      refine ⟨343823569302329224122975731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229215712868219482748650487 343823569302329224122975731)
      ·
        refine ⟨515735353953493836184463597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343823569302329224122975731 515735353953493836184463597)
        ·
          refine ⟨193400757732560188569173849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 515735353953493836184463597 193400757732560188569173849)
          ·
            refine ⟨145050568299420141426880387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193400757732560188569173849 145050568299420141426880387)
            ·
              refine ⟨217575852449130212140320581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145050568299420141426880387 217575852449130212140320581)
              ·
                refine ⟨40795472334211914776310109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217575852449130212140320581 40795472334211914776310109)
                ·
                  refine ⟨15298302125329468041116291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40795472334211914776310109 15298302125329468041116291)
                  ·
                    refine ⟨22947453187994202061674437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15298302125329468041116291 22947453187994202061674437)
                    ·
                      refine ⟨4302647472748912886563957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22947453187994202061674437 4302647472748912886563957)
                      ·
                        rfl

theorem cell23_8379376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 4].length) (baseStart_8379376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379376 prefixEnd_8379376 := by exact prefixLift 8379376
  have htrace : WordTrace (prefixWord ++ tailWord_8379376) baseStart_8379376 baseEnd_8379376 := by
    simpa [prefixWord, tailWord_8379376, baseEnd_8379376] using wordTrace_append hprefix tailTrace_8379376
  have hstable : (prefixWord ++ tailWord_8379376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379376).length < 2 ^ (prefixWord ++ tailWord_8379376).sum := by decide
  have hdescent : baseEnd_8379376 < baseStart_8379376 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379390 : List Nat := [4, 2, 2, 2, 2, 1, 1, 1, 3, 5]
def baseStart_8379390 : Nat := 118140960795 + 8379390 * 2 ^ 59
def prefixEnd_8379390 : Nat := 4983230072969 + 3 ^ 40 * 8379390 * 2
def baseEnd_8379390 : Nat := 1434218220492691943929631

theorem tailTrace_8379390 : CollatzResearch.WordTrace tailWord_8379390 prefixEnd_8379390 1434218220492691943929631 := by
  unfold tailWord_8379390
  simp only [CollatzResearch.WordTrace]
  refine ⟨38202682639113573840317953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203747640741939060481695749 38202682639113573840317953)
  ·
    refine ⟨28652011979335180380238465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38202682639113573840317953 28652011979335180380238465)
    ·
      refine ⟨21489008984501385285178849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28652011979335180380238465 21489008984501385285178849)
      ·
        refine ⟨16116756738376038963884137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21489008984501385285178849 16116756738376038963884137)
        ·
          refine ⟨12087567553782029222913103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16116756738376038963884137 12087567553782029222913103)
          ·
            refine ⟨18131351330673043834369655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12087567553782029222913103 18131351330673043834369655)
            ·
              refine ⟨27197026996009565751554483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18131351330673043834369655 27197026996009565751554483)
              ·
                refine ⟨40795540494014348627331725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27197026996009565751554483 40795540494014348627331725)
                ·
                  refine ⟨15298327685255380735249397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40795540494014348627331725 15298327685255380735249397)
                  ·
                    refine ⟨1434218220492691943929631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15298327685255380735249397 1434218220492691943929631)
                    ·
                      rfl

theorem cell23_8379390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_8379390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379390 prefixEnd_8379390 := by exact prefixLift 8379390
  have htrace : WordTrace (prefixWord ++ tailWord_8379390) baseStart_8379390 baseEnd_8379390 := by
    simpa [prefixWord, tailWord_8379390, baseEnd_8379390] using wordTrace_append hprefix tailTrace_8379390
  have hstable : (prefixWord ++ tailWord_8379390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379390).length < 2 ^ (prefixWord ++ tailWord_8379390).sum := by decide
  have hdescent : baseEnd_8379390 < baseStart_8379390 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379393 : List Nat := [1, 2, 4, 1, 2, 3, 1, 1, 3, 1, 4]
def baseStart_8379393 : Nat := 118140960795 + 8379393 * 2 ^ 59
def prefixEnd_8379393 : Nat := 4983230072969 + 3 ^ 40 * 8379393 * 2
def baseEnd_8379393 : Nat := 4302656201920039320051379

theorem tailTrace_8379393 : CollatzResearch.WordTrace tailWord_8379393 prefixEnd_8379393 4302656201920039320051379 := by
  unfold tailWord_8379393
  simp only [CollatzResearch.WordTrace]
  refine ⟨305621570531897722234902833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203747713687931814823268555 305621570531897722234902833)
  ·
    refine ⟨229216177898923291676177125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305621570531897722234902833 229216177898923291676177125)
    ·
      refine ⟨42978033356048117189283211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 229216177898923291676177125 42978033356048117189283211)
      ·
        refine ⟨64467050034072175783924817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42978033356048117189283211 64467050034072175783924817)
        ·
          refine ⟨48350287525554131837943613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64467050034072175783924817 48350287525554131837943613)
          ·
            refine ⟨18131357822082799439228855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48350287525554131837943613 18131357822082799439228855)
            ·
              refine ⟨27197036733124199158843283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18131357822082799439228855 27197036733124199158843283)
              ·
                refine ⟨40795555099686298738264925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27197036733124199158843283 40795555099686298738264925)
                ·
                  refine ⟨15298333162382362026849347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40795555099686298738264925 15298333162382362026849347)
                  ·
                    refine ⟨22947499743573543040274021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15298333162382362026849347 22947499743573543040274021)
                    ·
                      refine ⟨4302656201920039320051379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22947499743573543040274021 4302656201920039320051379)
                      ·
                        rfl

theorem cell23_8379393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_8379393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379393 prefixEnd_8379393 := by exact prefixLift 8379393
  have htrace : WordTrace (prefixWord ++ tailWord_8379393) baseStart_8379393 baseEnd_8379393 := by
    simpa [prefixWord, tailWord_8379393, baseEnd_8379393] using wordTrace_append hprefix tailTrace_8379393
  have hstable : (prefixWord ++ tailWord_8379393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379393).length < 2 ^ (prefixWord ++ tailWord_8379393).sum := by decide
  have hdescent : baseEnd_8379393 < baseStart_8379393 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379413 : List Nat := [1, 3, 2, 1, 4, 1, 3, 1, 1, 1, 5]
def baseStart_8379413 : Nat := 118140960795 + 8379413 * 2 ^ 59
def prefixEnd_8379413 : Nat := 4983230072969 + 3 ^ 40 * 8379413 * 2
def baseEnd_8379413 : Nat := 4302666471533129241801287

theorem tailTrace_8379413 : CollatzResearch.WordTrace tailWord_8379413 prefixEnd_8379413 4302666471533129241801287 := by
  unfold tailWord_8379413
  simp only [CollatzResearch.WordTrace]
  refine ⟨305622299991825265650630893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203748199994550177100420595 305622299991825265650630893)
  ·
    refine ⟨114608362496934474618986585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305622299991825265650630893 114608362496934474618986585)
    ·
      refine ⟨85956271872700855964239939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114608362496934474618986585 85956271872700855964239939)
      ·
        refine ⟨128934407809051283946359909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85956271872700855964239939 128934407809051283946359909)
        ·
          refine ⟨24175201464197115739942483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128934407809051283946359909 24175201464197115739942483)
          ·
            refine ⟨36262802196295673609913725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24175201464197115739942483 36262802196295673609913725)
            ·
              refine ⟨13598550823610877603717647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36262802196295673609913725 13598550823610877603717647)
              ·
                refine ⟨20397826235416316405576471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13598550823610877603717647 20397826235416316405576471)
                ·
                  refine ⟨30596739353124474608364707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20397826235416316405576471 30596739353124474608364707)
                  ·
                    refine ⟨45895109029686711912547061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30596739353124474608364707 45895109029686711912547061)
                    ·
                      refine ⟨4302666471533129241801287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45895109029686711912547061 4302666471533129241801287)
                      ·
                        rfl

theorem cell23_8379413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_8379413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379413 prefixEnd_8379413 := by exact prefixLift 8379413
  have htrace : WordTrace (prefixWord ++ tailWord_8379413) baseStart_8379413 baseEnd_8379413 := by
    simpa [prefixWord, tailWord_8379413, baseEnd_8379413] using wordTrace_append hprefix tailTrace_8379413
  have hstable : (prefixWord ++ tailWord_8379413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379413).length < 2 ^ (prefixWord ++ tailWord_8379413).sum := by decide
  have hdescent : baseEnd_8379413 < baseStart_8379413 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379421 : List Nat := [1, 4, 2, 2, 3, 2, 2, 2, 1, 1, 3]
def baseStart_8379421 : Nat := 118140960795 + 8379421 * 2 ^ 59
def prefixEnd_8379421 : Nat := 4983230072969 + 3 ^ 40 * 8379421 * 2
def baseEnd_8379421 : Nat := 4302670579378365210501251

theorem tailTrace_8379421 : CollatzResearch.WordTrace tailWord_8379421 prefixEnd_8379421 4302670579378365210501251 := by
  unfold tailWord_8379421
  simp only [CollatzResearch.WordTrace]
  refine ⟨305622591775796283016922117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203748394517197522011281411 305622591775796283016922117)
  ·
    refine ⟨57304235957961803065672897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305622591775796283016922117 57304235957961803065672897)
    ·
      refine ⟨42978176968471352299254673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57304235957961803065672897 42978176968471352299254673)
      ·
        refine ⟨32233632726353514224441005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42978176968471352299254673 32233632726353514224441005)
        ·
          refine ⟨12087612272382567834165377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32233632726353514224441005 12087612272382567834165377)
          ·
            refine ⟨9065709204286925875624033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12087612272382567834165377 9065709204286925875624033)
            ·
              refine ⟨6799281903215194406718025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9065709204286925875624033 6799281903215194406718025)
              ·
                refine ⟨5099461427411395805038519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6799281903215194406718025 5099461427411395805038519)
                ·
                  refine ⟨7649192141117093707557779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5099461427411395805038519 7649192141117093707557779)
                  ·
                    refine ⟨11473788211675640561336669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7649192141117093707557779 11473788211675640561336669)
                    ·
                      refine ⟨4302670579378365210501251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11473788211675640561336669 4302670579378365210501251)
                      ·
                        rfl

theorem cell23_8379421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_8379421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379421 prefixEnd_8379421 := by exact prefixLift 8379421
  have htrace : WordTrace (prefixWord ++ tailWord_8379421) baseStart_8379421 baseEnd_8379421 := by
    simpa [prefixWord, tailWord_8379421, baseEnd_8379421] using wordTrace_append hprefix tailTrace_8379421
  have hstable : (prefixWord ++ tailWord_8379421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379421).length < 2 ^ (prefixWord ++ tailWord_8379421).sum := by decide
  have hdescent : baseEnd_8379421 < baseStart_8379421 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379443 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 6, 1, 3]
def baseStart_8379443 : Nat := 118140960795 + 8379443 * 2 ^ 59
def prefixEnd_8379443 : Nat := 4983230072969 + 3 ^ 40 * 8379443 * 2
def baseEnd_8379443 : Nat := 4302681875952764124426149

theorem tailTrace_8379443 : CollatzResearch.WordTrace tailWord_8379443 prefixEnd_8379443 4302681875952764124426149 := by
  unfold tailWord_8379443
  simp only [CollatzResearch.WordTrace]
  refine ⟨305623394181716580774222983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203748929454477720516148655 305623394181716580774222983)
  ·
    refine ⟨458435091272574871161334475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305623394181716580774222983 458435091272574871161334475)
    ·
      refine ⟨687652636908862306742001713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458435091272574871161334475 687652636908862306742001713)
      ·
        refine ⟨515739477681646730056501285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 687652636908862306742001713 515739477681646730056501285)
        ·
          refine ⟨96701152065308761885593991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 515739477681646730056501285 96701152065308761885593991)
          ·
            refine ⟨145051728097963142828390987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96701152065308761885593991 145051728097963142828390987)
            ·
              refine ⟨217577592146944714242586481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145051728097963142828390987 217577592146944714242586481)
              ·
                refine ⟨163183194110208535681939861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217577592146944714242586481 163183194110208535681939861)
                ·
                  refine ⟨7649212223916025110090931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 163183194110208535681939861 7649212223916025110090931)
                  ·
                    refine ⟨11473818335874037665136397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7649212223916025110090931 11473818335874037665136397)
                    ·
                      refine ⟨4302681875952764124426149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11473818335874037665136397 4302681875952764124426149)
                      ·
                        rfl

theorem cell23_8379443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 6, 1, 3].length) (baseStart_8379443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379443 prefixEnd_8379443 := by exact prefixLift 8379443
  have htrace : WordTrace (prefixWord ++ tailWord_8379443) baseStart_8379443 baseEnd_8379443 := by
    simpa [prefixWord, tailWord_8379443, baseEnd_8379443] using wordTrace_append hprefix tailTrace_8379443
  have hstable : (prefixWord ++ tailWord_8379443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379443).length < 2 ^ (prefixWord ++ tailWord_8379443).sum := by decide
  have hdescent : baseEnd_8379443 < baseStart_8379443 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379444 : List Nat := [2, 5, 1, 2, 1, 2, 1, 2, 3, 2, 2]
def baseStart_8379444 : Nat := 118140960795 + 8379444 * 2 ^ 59
def prefixEnd_8379444 : Nat := 4983230072969 + 3 ^ 40 * 8379444 * 2
def baseEnd_8379444 : Nat := 4302682389433418620513645

theorem tailTrace_8379444 : CollatzResearch.WordTrace tailWord_8379444 prefixEnd_8379444 4302682389433418620513645 := by
  unfold tailWord_8379444
  simp only [CollatzResearch.WordTrace]
  refine ⟨152811715327356478972504693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203748953769808638630006257 152811715327356478972504693)
  ·
    refine ⟨14326098311939669903672315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152811715327356478972504693 14326098311939669903672315)
    ·
      refine ⟨21489147467909504855508473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14326098311939669903672315 21489147467909504855508473)
      ·
        refine ⟨16116860600932128641631355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21489147467909504855508473 16116860600932128641631355)
        ·
          refine ⟨24175290901398192962447033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16116860600932128641631355 24175290901398192962447033)
          ·
            refine ⟨18131468176048644721835275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24175290901398192962447033 18131468176048644721835275)
            ·
              refine ⟨27197202264072967082752913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18131468176048644721835275 27197202264072967082752913)
              ·
                refine ⟨20397901698054725312064685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27197202264072967082752913 20397901698054725312064685)
                ·
                  refine ⟨7649213136770521992024257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20397901698054725312064685 7649213136770521992024257)
                  ·
                    refine ⟨5736909852577891494018193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7649213136770521992024257 5736909852577891494018193)
                    ·
                      refine ⟨4302682389433418620513645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5736909852577891494018193 4302682389433418620513645)
                      ·
                        rfl

theorem cell23_8379444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_8379444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379444 prefixEnd_8379444 := by exact prefixLift 8379444
  have htrace : WordTrace (prefixWord ++ tailWord_8379444) baseStart_8379444 baseEnd_8379444 := by
    simpa [prefixWord, tailWord_8379444, baseEnd_8379444] using wordTrace_append hprefix tailTrace_8379444
  have hstable : (prefixWord ++ tailWord_8379444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379444).length < 2 ^ (prefixWord ++ tailWord_8379444).sum := by decide
  have hdescent : baseEnd_8379444 < baseStart_8379444 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379456 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 5]
def baseStart_8379456 : Nat := 118140960795 + 8379456 * 2 ^ 59
def prefixEnd_8379456 : Nat := 4983230072969 + 3 ^ 40 * 8379456 * 2
def baseEnd_8379456 : Nat := 4302688551201272573563589

theorem tailTrace_8379456 : CollatzResearch.WordTrace tailWord_8379456 prefixEnd_8379456 4302688551201272573563589 := by
  unfold tailWord_8379456
  simp only [CollatzResearch.WordTrace]
  refine ⟨152811934165334741997223111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203749245553779655996297481 152811934165334741997223111)
  ·
    refine ⟨229217901248002112995834667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152811934165334741997223111 229217901248002112995834667)
    ·
      refine ⟨343826851872003169493752001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229217901248002112995834667 343826851872003169493752001)
      ·
        refine ⟨257870138904002377120314001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343826851872003169493752001 257870138904002377120314001)
        ·
          refine ⟨193402604178001782840235501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257870138904002377120314001 193402604178001782840235501)
          ·
            refine ⟨72525976566750668565088313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193402604178001782840235501 72525976566750668565088313)
            ·
              refine ⟨54394482425063001423816235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72525976566750668565088313 54394482425063001423816235)
              ·
                refine ⟨81591723637594502135724353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54394482425063001423816235 81591723637594502135724353)
                ·
                  refine ⟨61193792728195876601793265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81591723637594502135724353 61193792728195876601793265)
                  ·
                    refine ⟨45895344546146907451344949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61193792728195876601793265 45895344546146907451344949)
                    ·
                      refine ⟨4302688551201272573563589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45895344546146907451344949 4302688551201272573563589)
                      ·
                        rfl

theorem cell23_8379456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_8379456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379456 prefixEnd_8379456 := by exact prefixLift 8379456
  have htrace : WordTrace (prefixWord ++ tailWord_8379456) baseStart_8379456 baseEnd_8379456 := by
    simpa [prefixWord, tailWord_8379456, baseEnd_8379456] using wordTrace_append hprefix tailTrace_8379456
  have hstable : (prefixWord ++ tailWord_8379456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379456).length < 2 ^ (prefixWord ++ tailWord_8379456).sum := by decide
  have hdescent : baseEnd_8379456 < baseStart_8379456 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379536 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 3, 7]
def baseStart_8379536 : Nat := 118140960795 + 8379536 * 2 ^ 59
def prefixEnd_8379536 : Nat := 4983230072969 + 3 ^ 40 * 8379536 * 2
def baseEnd_8379536 : Nat := 1434243209884544086854407

theorem tailTrace_8379536 : CollatzResearch.WordTrace tailWord_8379536 prefixEnd_8379536 1434243209884544086854407 := by
  unfold tailWord_8379536
  simp only [CollatzResearch.WordTrace]
  refine ⟨152813393085189828828679231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203751190780253105104905641 152813393085189828828679231)
  ·
    refine ⟨229220089627784743243018847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152813393085189828828679231 229220089627784743243018847)
    ·
      refine ⟨343830134441677114864528271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229220089627784743243018847 343830134441677114864528271)
      ·
        refine ⟨515745201662515672296792407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343830134441677114864528271 515745201662515672296792407)
        ·
          refine ⟨773617802493773508445188611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515745201662515672296792407 773617802493773508445188611)
          ·
            refine ⟨1160426703740660262667782917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773617802493773508445188611 1160426703740660262667782917)
            ·
              refine ⟨217580006951373799250209297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1160426703740660262667782917 217580006951373799250209297)
              ·
                refine ⟨163185005213530349437656973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217580006951373799250209297 163185005213530349437656973)
                ·
                  refine ⟨61194376955073881039121365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163185005213530349437656973 61194376955073881039121365)
                  ·
                    refine ⟨1434243209884544086854407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61194376955073881039121365 1434243209884544086854407)
                    ·
                      rfl

theorem cell23_8379536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 3, 7].length) (baseStart_8379536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379536 prefixEnd_8379536 := by exact prefixLift 8379536
  have htrace : WordTrace (prefixWord ++ tailWord_8379536) baseStart_8379536 baseEnd_8379536 := by
    simpa [prefixWord, tailWord_8379536, baseEnd_8379536] using wordTrace_append hprefix tailTrace_8379536
  have hstable : (prefixWord ++ tailWord_8379536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379536).length < 2 ^ (prefixWord ++ tailWord_8379536).sum := by decide
  have hdescent : baseEnd_8379536 < baseStart_8379536 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379553 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 4, 5]
def baseStart_8379553 : Nat := 118140960795 + 8379553 * 2 ^ 59
def prefixEnd_8379553 : Nat := 4983230072969 + 3 ^ 40 * 8379553 * 2
def baseEnd_8379553 : Nat := 1434246119608252898016881

theorem tailTrace_8379553 : CollatzResearch.WordTrace tailWord_8379553 prefixEnd_8379553 1434246119608252898016881 := by
  unfold tailWord_8379553
  simp only [CollatzResearch.WordTrace]
  refine ⟨305627406211318069560727313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203751604140878713040484875 305627406211318069560727313)
  ·
    refine ⟨229220554658488552170545485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305627406211318069560727313 229220554658488552170545485)
    ·
      refine ⟨85957707996933207063954557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229220554658488552170545485 85957707996933207063954557)
      ·
        refine ⟨32234140498849952648982959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85957707996933207063954557 32234140498849952648982959)
        ·
          refine ⟨48351210748274928973474439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32234140498849952648982959 48351210748274928973474439)
          ·
            refine ⟨72526816122412393460211659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48351210748274928973474439 72526816122412393460211659)
            ·
              refine ⟨108790224183618590190317489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72526816122412393460211659 108790224183618590190317489)
              ·
                refine ⟨81592668137713942642738117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108790224183618590190317489 81592668137713942642738117)
                ·
                  refine ⟨15298625275821364245513397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81592668137713942642738117 15298625275821364245513397)
                  ·
                    refine ⟨1434246119608252898016881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15298625275821364245513397 1434246119608252898016881)
                    ·
                      rfl

theorem cell23_8379553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_8379553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379553 prefixEnd_8379553 := by exact prefixLift 8379553
  have htrace : WordTrace (prefixWord ++ tailWord_8379553) baseStart_8379553 baseEnd_8379553 := by
    simpa [prefixWord, tailWord_8379553, baseEnd_8379553] using wordTrace_append hprefix tailTrace_8379553
  have hstable : (prefixWord ++ tailWord_8379553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379553).length < 2 ^ (prefixWord ++ tailWord_8379553).sum := by decide
  have hdescent : baseEnd_8379553 < baseStart_8379553 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379570 : List Nat := [3, 2, 1, 1, 1, 5, 2, 1, 2, 5]
def baseStart_8379570 : Nat := 118140960795 + 8379570 * 2 ^ 59
def prefixEnd_8379570 : Nat := 4983230072969 + 3 ^ 40 * 8379570 * 2
def baseEnd_8379570 : Nat := 1434249029331961709179355

theorem tailTrace_8379570 : CollatzResearch.WordTrace tailWord_8379570 prefixEnd_8379570 1434249029331961709179355 := by
  unfold tailWord_8379570
  simp only [CollatzResearch.WordTrace]
  refine ⟨76407006563064120366024041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203752017501504320976064109 76407006563064120366024041)
  ·
    refine ⟨57305254922298090274518031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76407006563064120366024041 57305254922298090274518031)
    ·
      refine ⟨85957882383447135411777047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57305254922298090274518031 85957882383447135411777047)
      ·
        refine ⟨128936823575170703117665571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85957882383447135411777047 128936823575170703117665571)
        ·
          refine ⟨193405235362756054676498357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128936823575170703117665571 193405235362756054676498357)
          ·
            refine ⟨18131740815258380125921721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 193405235362756054676498357 18131740815258380125921721)
            ·
              refine ⟨13598805611443785094441291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18131740815258380125921721 13598805611443785094441291)
              ·
                refine ⟨20398208417165677641661937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13598805611443785094441291 20398208417165677641661937)
                ·
                  refine ⟨15298656312874258231246453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20398208417165677641661937 15298656312874258231246453)
                  ·
                    refine ⟨1434249029331961709179355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15298656312874258231246453 1434249029331961709179355)
                    ·
                      rfl

theorem cell23_8379570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_8379570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379570 prefixEnd_8379570 := by exact prefixLift 8379570
  have htrace : WordTrace (prefixWord ++ tailWord_8379570) baseStart_8379570 baseEnd_8379570 := by
    simpa [prefixWord, tailWord_8379570, baseEnd_8379570] using wordTrace_append hprefix tailTrace_8379570
  have hstable : (prefixWord ++ tailWord_8379570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379570).length < 2 ^ (prefixWord ++ tailWord_8379570).sum := by decide
  have hdescent : baseEnd_8379570 < baseStart_8379570 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379627 : List Nat := [1, 1, 1, 1, 2, 8, 1, 1, 2, 2, 3]
def baseStart_8379627 : Nat := 118140960795 + 8379627 * 2 ^ 59
def prefixEnd_8379627 : Nat := 4983230072969 + 3 ^ 40 * 8379627 * 2
def baseEnd_8379627 : Nat := 4302776356393191404525303

theorem tailTrace_8379627 : CollatzResearch.WordTrace tailWord_8379627 prefixEnd_8379627 4302776356393191404525303 := by
  unfold tailWord_8379627
  simp only [CollatzResearch.WordTrace]
  refine ⟨305630105213049980198921135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203753403475366653465947423 305630105213049980198921135)
  ·
    refine ⟨458445157819574970298381703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305630105213049980198921135 458445157819574970298381703)
    ·
      refine ⟨687667736729362455447572555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458445157819574970298381703 687667736729362455447572555)
      ·
        refine ⟨1031501605094043683171358833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687667736729362455447572555 1031501605094043683171358833)
        ·
          refine ⟨773626203820532762378519125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1031501605094043683171358833 773626203820532762378519125)
          ·
            refine ⟨9065932076021868309123271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 773626203820532762378519125 9065932076021868309123271)
            ·
              refine ⟨13598898114032802463684907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9065932076021868309123271 13598898114032802463684907)
              ·
                refine ⟨20398347171049203695527361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13598898114032802463684907 20398347171049203695527361)
                ·
                  refine ⟨15298760378286902771645521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20398347171049203695527361 15298760378286902771645521)
                  ·
                    refine ⟨11474070283715177078734141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15298760378286902771645521 11474070283715177078734141)
                    ·
                      refine ⟨4302776356393191404525303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11474070283715177078734141 4302776356393191404525303)
                      ·
                        rfl

theorem cell23_8379627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 2, 3].length) (baseStart_8379627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379627 prefixEnd_8379627 := by exact prefixLift 8379627
  have htrace : WordTrace (prefixWord ++ tailWord_8379627) baseStart_8379627 baseEnd_8379627 := by
    simpa [prefixWord, tailWord_8379627, baseEnd_8379627] using wordTrace_append hprefix tailTrace_8379627
  have hstable : (prefixWord ++ tailWord_8379627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379627).length < 2 ^ (prefixWord ++ tailWord_8379627).sum := by decide
  have hdescent : baseEnd_8379627 < baseStart_8379627 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379657 : List Nat := [1, 2, 1, 1, 3, 3, 4, 1, 3, 1, 3]
def baseStart_8379657 : Nat := 118140960795 + 8379657 * 2 ^ 59
def prefixEnd_8379657 : Nat := 4983230072969 + 3 ^ 40 * 8379657 * 2
def baseEnd_8379657 : Nat := 4302791760812826287150165

theorem tailTrace_8379657 : CollatzResearch.WordTrace tailWord_8379657 prefixEnd_8379657 4302791760812826287150165 := by
  unfold tailWord_8379657
  simp only [CollatzResearch.WordTrace]
  refine ⟨305631199402941295322513225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203754132935294196881675483 305631199402941295322513225)
  ·
    refine ⟨229223399552205971491884919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305631199402941295322513225 229223399552205971491884919)
    ·
      refine ⟨343835099328308957237827379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229223399552205971491884919 343835099328308957237827379)
      ·
        refine ⟨515752648992463435856741069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343835099328308957237827379 515752648992463435856741069)
        ·
          refine ⟨193407243372173788446277901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 515752648992463435856741069 193407243372173788446277901)
          ·
            refine ⟨72527716264565170667354213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193407243372173788446277901 72527716264565170667354213)
            ·
              refine ⟨13598946799605969500128915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72527716264565170667354213 13598946799605969500128915)
              ·
                refine ⟨20398420199408954250193373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13598946799605969500128915 20398420199408954250193373)
                ·
                  refine ⟨7649407574778357843822515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20398420199408954250193373 7649407574778357843822515)
                  ·
                    refine ⟨11474111362167536765733773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7649407574778357843822515 11474111362167536765733773)
                    ·
                      refine ⟨4302791760812826287150165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11474111362167536765733773 4302791760812826287150165)
                      ·
                        rfl

theorem cell23_8379657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 3, 1, 3].length) (baseStart_8379657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379657 prefixEnd_8379657 := by exact prefixLift 8379657
  have htrace : WordTrace (prefixWord ++ tailWord_8379657) baseStart_8379657 baseEnd_8379657 := by
    simpa [prefixWord, tailWord_8379657, baseEnd_8379657] using wordTrace_append hprefix tailTrace_8379657
  have hstable : (prefixWord ++ tailWord_8379657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379657).length < 2 ^ (prefixWord ++ tailWord_8379657).sum := by decide
  have hdescent : baseEnd_8379657 < baseStart_8379657 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379677 : List Nat := [1, 4, 2, 3, 1, 1, 1, 4, 1, 5]
def baseStart_8379677 : Nat := 118140960795 + 8379677 * 2 ^ 59
def prefixEnd_8379677 : Nat := 4983230072969 + 3 ^ 40 * 8379677 * 2
def baseEnd_8379677 : Nat := 1434267343475305402966691

theorem tailTrace_8379677 : CollatzResearch.WordTrace tailWord_8379677 prefixEnd_8379677 1434267343475305402966691 := by
  unfold tailWord_8379677
  simp only [CollatzResearch.WordTrace]
  refine ⟨305631928862868838738241285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203754619241912559158827523 305631928862868838738241285)
  ·
    refine ⟨57305986661787907263420241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305631928862868838738241285 57305986661787907263420241)
    ·
      refine ⟨42979489996340930447565181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57305986661787907263420241 42979489996340930447565181)
      ·
        refine ⟨16117308748627848917836943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42979489996340930447565181 16117308748627848917836943)
        ·
          refine ⟨24175963122941773376755415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16117308748627848917836943 24175963122941773376755415)
          ·
            refine ⟨36263944684412660065133123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24175963122941773376755415 36263944684412660065133123)
            ·
              refine ⟨54395917026618990097699685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36263944684412660065133123 54395917026618990097699685)
              ·
                refine ⟨10199234442491060643318691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54395917026618990097699685 10199234442491060643318691)
                ·
                  refine ⟨15298851663736590964978037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10199234442491060643318691 15298851663736590964978037)
                  ·
                    refine ⟨1434267343475305402966691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15298851663736590964978037 1434267343475305402966691)
                    ·
                      rfl

theorem cell23_8379677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_8379677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379677 prefixEnd_8379677 := by exact prefixLift 8379677
  have htrace : WordTrace (prefixWord ++ tailWord_8379677) baseStart_8379677 baseEnd_8379677 := by
    simpa [prefixWord, tailWord_8379677, baseEnd_8379677] using wordTrace_append hprefix tailTrace_8379677
  have hstable : (prefixWord ++ tailWord_8379677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379677).length < 2 ^ (prefixWord ++ tailWord_8379677).sum := by decide
  have hdescent : baseEnd_8379677 < baseStart_8379677 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379697 : List Nat := [1, 2, 2, 3, 3, 1, 2, 3, 1, 1, 4]
def baseStart_8379697 : Nat := 118140960795 + 8379697 * 2 ^ 59
def prefixEnd_8379697 : Nat := 4983230072969 + 3 ^ 40 * 8379697 * 2
def baseEnd_8379697 : Nat := 4302812300039006130649981

theorem tailTrace_8379697 : CollatzResearch.WordTrace tailWord_8379697 prefixEnd_8379697 4302812300039006130649981 := by
  unfold tailWord_8379697
  simp only [CollatzResearch.WordTrace]
  refine ⟨305632658322796382153969345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203755105548530921435979563 305632658322796382153969345)
  ·
    refine ⟨229224493742097286615477009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305632658322796382153969345 229224493742097286615477009)
    ·
      refine ⟨171918370306572964961607757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229224493742097286615477009 171918370306572964961607757)
      ·
        refine ⟨64469388864964861860602909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171918370306572964961607757 64469388864964861860602909)
        ·
          refine ⟨24176020824361823197726091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64469388864964861860602909 24176020824361823197726091)
          ·
            refine ⟨36264031236542734796589137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24176020824361823197726091 36264031236542734796589137)
            ·
              refine ⟨27198023427407051097441853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36264031236542734796589137 27198023427407051097441853)
              ·
                refine ⟨10199258785277644161540695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27198023427407051097441853 10199258785277644161540695)
                ·
                  refine ⟨15298888177916466242311043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10199258785277644161540695 15298888177916466242311043)
                  ·
                    refine ⟨22948332266874699363466565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15298888177916466242311043 22948332266874699363466565)
                    ·
                      refine ⟨4302812300039006130649981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22948332266874699363466565 4302812300039006130649981)
                      ·
                        rfl

theorem cell23_8379697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_8379697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379697 prefixEnd_8379697 := by exact prefixLift 8379697
  have htrace : WordTrace (prefixWord ++ tailWord_8379697) baseStart_8379697 baseEnd_8379697 := by
    simpa [prefixWord, tailWord_8379697, baseEnd_8379697] using wordTrace_append hprefix tailTrace_8379697
  have hstable : (prefixWord ++ tailWord_8379697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379697).length < 2 ^ (prefixWord ++ tailWord_8379697).sum := by decide
  have hdescent : baseEnd_8379697 < baseStart_8379697 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379710 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 3, 1, 6]
def baseStart_8379710 : Nat := 118140960795 + 8379710 * 2 ^ 59
def prefixEnd_8379710 : Nat := 4983230072969 + 3 ^ 40 * 8379710 * 2
def baseEnd_8379710 : Nat := 4302818975287514579787421

theorem tailTrace_8379710 : CollatzResearch.WordTrace tailWord_8379710 prefixEnd_8379710 4302818975287514579787421 := by
  unfold tailWord_8379710
  simp only [CollatzResearch.WordTrace]
  refine ⟨38204141558968660671774073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203755421647832856916128389 38204141558968660671774073)
  ·
    refine ⟨28653106169226495503830555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38204141558968660671774073 28653106169226495503830555)
    ·
      refine ⟨42979659253839743255745833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28653106169226495503830555 42979659253839743255745833)
      ·
        refine ⟨32234744440379807441809375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42979659253839743255745833 32234744440379807441809375)
        ·
          refine ⟨48352116660569711162714063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32234744440379807441809375 48352116660569711162714063)
          ·
            refine ⟨72528174990854566744071095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48352116660569711162714063 72528174990854566744071095)
            ·
              refine ⟨108792262486281850116106643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72528174990854566744071095 108792262486281850116106643)
              ·
                refine ⟨163188393729422775174159965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108792262486281850116106643 163188393729422775174159965)
                ·
                  refine ⟨61195647648533540690309987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163188393729422775174159965 61195647648533540690309987)
                  ·
                    refine ⟨91793471472800311035464981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61195647648533540690309987 91793471472800311035464981)
                    ·
                      refine ⟨4302818975287514579787421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91793471472800311035464981 4302818975287514579787421)
                      ·
                        rfl

theorem cell23_8379710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_8379710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379710 prefixEnd_8379710 := by exact prefixLift 8379710
  have htrace : WordTrace (prefixWord ++ tailWord_8379710) baseStart_8379710 baseEnd_8379710 := by
    simpa [prefixWord, tailWord_8379710, baseEnd_8379710] using wordTrace_append hprefix tailTrace_8379710
  have hstable : (prefixWord ++ tailWord_8379710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379710).length < 2 ^ (prefixWord ++ tailWord_8379710).sum := by decide
  have hdescent : baseEnd_8379710 < baseStart_8379710 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379724 : List Nat := [2, 2, 1, 3, 2, 2, 4, 1, 2, 4]
def baseStart_8379724 : Nat := 118140960795 + 8379724 * 2 ^ 59
def prefixEnd_8379724 : Nat := 4983230072969 + 3 ^ 40 * 8379724 * 2
def baseEnd_8379724 : Nat := 1434275388005559175004119

theorem tailTrace_8379724 : CollatzResearch.WordTrace tailWord_8379724 prefixEnd_8379724 1434275388005559175004119 := by
  unfold tailWord_8379724
  simp only [CollatzResearch.WordTrace]
  refine ⟨152816821546849282882601113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203755762062465710510134817 152816821546849282882601113)
  ·
    refine ⟨114612616160136962161950835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152816821546849282882601113 114612616160136962161950835)
    ·
      refine ⟨171918924240205443242926253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114612616160136962161950835 171918924240205443242926253)
      ·
        refine ⟨64469596590077041216097345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171918924240205443242926253 64469596590077041216097345)
        ·
          refine ⟨48352197442557780912073009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64469596590077041216097345 48352197442557780912073009)
          ·
            refine ⟨36264148081918335684054757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48352197442557780912073009 36264148081918335684054757)
            ·
              refine ⟨6799527765359687940760267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36264148081918335684054757 6799527765359687940760267)
              ·
                refine ⟨10199291648039531911140401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6799527765359687940760267 10199291648039531911140401)
                ·
                  refine ⟨7649468736029648933355301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10199291648039531911140401 7649468736029648933355301)
                  ·
                    refine ⟨1434275388005559175004119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7649468736029648933355301 1434275388005559175004119)
                    ·
                      rfl

theorem cell23_8379724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 2, 4].length) (baseStart_8379724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379724 prefixEnd_8379724 := by exact prefixLift 8379724
  have htrace : WordTrace (prefixWord ++ tailWord_8379724) baseStart_8379724 baseEnd_8379724 := by
    simpa [prefixWord, tailWord_8379724, baseEnd_8379724] using wordTrace_append hprefix tailTrace_8379724
  have hstable : (prefixWord ++ tailWord_8379724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379724).length < 2 ^ (prefixWord ++ tailWord_8379724).sum := by decide
  have hdescent : baseEnd_8379724 < baseStart_8379724 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379741 : List Nat := [1, 4, 5, 1, 1, 1, 1, 2, 1, 6]
def baseStart_8379741 : Nat := 118140960795 + 8379741 * 2 ^ 59
def prefixEnd_8379741 : Nat := 4983230072969 + 3 ^ 40 * 8379741 * 2
def baseEnd_8379741 : Nat := 1434278297729267986166593

theorem tailTrace_8379741 : CollatzResearch.WordTrace tailWord_8379741 prefixEnd_8379741 1434278297729267986166593 := by
  unfold tailWord_8379741
  simp only [CollatzResearch.WordTrace]
  refine ⟨305634263134636977668571077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203756175423091318445714051 305634263134636977668571077)
  ·
    refine ⟨57306424337744433312857077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305634263134636977668571077 57306424337744433312857077)
    ·
      refine ⟨5372477281663540623080351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57306424337744433312857077 5372477281663540623080351)
      ·
        refine ⟨8058715922495310934620527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5372477281663540623080351 8058715922495310934620527)
        ·
          refine ⟨12088073883742966401930791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8058715922495310934620527 12088073883742966401930791)
          ·
            refine ⟨18132110825614449602896187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12088073883742966401930791 18132110825614449602896187)
            ·
              refine ⟨27198166238421674404344281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18132110825614449602896187 27198166238421674404344281)
              ·
                refine ⟨20398624678816255803258211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27198166238421674404344281 20398624678816255803258211)
                ·
                  refine ⟨30597937018224383704887317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20398624678816255803258211 30597937018224383704887317)
                  ·
                    refine ⟨1434278297729267986166593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30597937018224383704887317 1434278297729267986166593)
                    ·
                      rfl

theorem cell23_8379741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_8379741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379741 prefixEnd_8379741 := by exact prefixLift 8379741
  have htrace : WordTrace (prefixWord ++ tailWord_8379741) baseStart_8379741 baseEnd_8379741 := by
    simpa [prefixWord, tailWord_8379741, baseEnd_8379741] using wordTrace_append hprefix tailTrace_8379741
  have hstable : (prefixWord ++ tailWord_8379741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379741).length < 2 ^ (prefixWord ++ tailWord_8379741).sum := by decide
  have hdescent : baseEnd_8379741 < baseStart_8379741 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379747 : List Nat := [1, 1, 1, 5, 2, 3, 1, 2, 1, 3, 3]
def baseStart_8379747 : Nat := 118140960795 + 8379747 * 2 ^ 59
def prefixEnd_8379747 : Nat := 4983230072969 + 3 ^ 40 * 8379747 * 2
def baseEnd_8379747 : Nat := 4302837974071730935024751

theorem tailTrace_8379747 : CollatzResearch.WordTrace tailWord_8379747 prefixEnd_8379747 4302837974071730935024751 := by
  unfold tailWord_8379747
  simp only [CollatzResearch.WordTrace]
  refine ⟨305634481972615240693289495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203756321315076827128859663 305634481972615240693289495)
  ·
    refine ⟨458451722958922861039934243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305634481972615240693289495 458451722958922861039934243)
    ·
      refine ⟨687677584438384291559901365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458451722958922861039934243 687677584438384291559901365)
      ·
        refine ⟨64469773541098527333740753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 687677584438384291559901365 64469773541098527333740753)
        ·
          refine ⟨48352330155823895500305565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64469773541098527333740753 48352330155823895500305565)
          ·
            refine ⟨18132123808433960812614587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48352330155823895500305565 18132123808433960812614587)
            ·
              refine ⟨27198185712650941218921881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18132123808433960812614587 27198185712650941218921881)
              ·
                refine ⟨20398639284488205914191411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27198185712650941218921881 20398639284488205914191411)
                ·
                  refine ⟨30597958926732308871287117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20398639284488205914191411 30597958926732308871287117)
                  ·
                    refine ⟨11474234597524615826732669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30597958926732308871287117 11474234597524615826732669)
                    ·
                      refine ⟨4302837974071730935024751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11474234597524615826732669 4302837974071730935024751)
                      ·
                        rfl

theorem cell23_8379747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_8379747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379747 prefixEnd_8379747 := by exact prefixLift 8379747
  have htrace : WordTrace (prefixWord ++ tailWord_8379747) baseStart_8379747 baseEnd_8379747 := by
    simpa [prefixWord, tailWord_8379747, baseEnd_8379747] using wordTrace_append hprefix tailTrace_8379747
  have hstable : (prefixWord ++ tailWord_8379747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379747).length < 2 ^ (prefixWord ++ tailWord_8379747).sum := by decide
  have hdescent : baseEnd_8379747 < baseStart_8379747 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379751 : List Nat := [1, 1, 5, 1, 4, 1, 3, 1, 1, 2, 3]
def baseStart_8379751 : Nat := 118140960795 + 8379751 * 2 ^ 59
def prefixEnd_8379751 : Nat := 4983230072969 + 3 ^ 40 * 8379751 * 2
def baseEnd_8379751 : Nat := 4302840027994348919374733

theorem tailTrace_8379751 : CollatzResearch.WordTrace tailWord_8379751 prefixEnd_8379751 4302840027994348919374733 := by
  unfold tailWord_8379751
  simp only [CollatzResearch.WordTrace]
  refine ⟨305634627864600749376435107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203756418576400499584290071 305634627864600749376435107)
  ·
    refine ⟨458451941796901124064652661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305634627864600749376435107 458451941796901124064652661)
    ·
      refine ⟨42979869543459480381061187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 458451941796901124064652661 42979869543459480381061187)
      ·
        refine ⟨64469804315189220571591781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42979869543459480381061187 64469804315189220571591781)
        ·
          refine ⟨12088088309097978857173459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64469804315189220571591781 12088088309097978857173459)
          ·
            refine ⟨18132132463646968285760189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12088088309097978857173459 18132132463646968285760189)
            ·
              refine ⟨6799549673867613107160071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18132132463646968285760189 6799549673867613107160071)
              ·
                refine ⟨10199324510801419660740107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6799549673867613107160071 10199324510801419660740107)
                ·
                  refine ⟨15298986766202129491110161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10199324510801419660740107 15298986766202129491110161)
                  ·
                    refine ⟨11474240074651597118332621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15298986766202129491110161 11474240074651597118332621)
                    ·
                      refine ⟨4302840027994348919374733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11474240074651597118332621 4302840027994348919374733)
                      ·
                        rfl

theorem cell23_8379751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_8379751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379751 prefixEnd_8379751 := by exact prefixLift 8379751
  have htrace : WordTrace (prefixWord ++ tailWord_8379751) baseStart_8379751 baseEnd_8379751 := by
    simpa [prefixWord, tailWord_8379751, baseEnd_8379751] using wordTrace_append hprefix tailTrace_8379751
  have hstable : (prefixWord ++ tailWord_8379751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379751).length < 2 ^ (prefixWord ++ tailWord_8379751).sum := by decide
  have hdescent : baseEnd_8379751 < baseStart_8379751 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379780 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 1, 8]
def baseStart_8379780 : Nat := 118140960795 + 8379780 * 2 ^ 59
def prefixEnd_8379780 : Nat := 4983230072969 + 3 ^ 40 * 8379780 * 2
def baseEnd_8379780 : Nat := 1434284972977776435304033

theorem tailTrace_8379780 : CollatzResearch.WordTrace tailWord_8379780 prefixEnd_8379780 1434284972977776435304033 := by
  unfold tailWord_8379780
  simp only [CollatzResearch.WordTrace]
  refine ⟨152817842790747843664620397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203757123720997124886160529 152817842790747843664620397)
  ·
    refine ⟨57306691046530441374232649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152817842790747843664620397 57306691046530441374232649)
    ·
      refine ⟨42980018284897831030674487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57306691046530441374232649 42980018284897831030674487)
      ·
        refine ⟨64470027427346746546011731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42980018284897831030674487 64470027427346746546011731)
        ·
          refine ⟨96705041141020119819017597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64470027427346746546011731 96705041141020119819017597)
          ·
            refine ⟨36264390427882544932131599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96705041141020119819017597 36264390427882544932131599)
            ·
              refine ⟨54396585641823817398197399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36264390427882544932131599 54396585641823817398197399)
              ·
                refine ⟨81594878462735726097296099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54396585641823817398197399 81594878462735726097296099)
                ·
                  refine ⟨122392317694103589145944149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81594878462735726097296099 122392317694103589145944149)
                  ·
                    refine ⟨1434284972977776435304033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 122392317694103589145944149 1434284972977776435304033)
                    ·
                      rfl

theorem cell23_8379780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_8379780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379780 prefixEnd_8379780 := by exact prefixLift 8379780
  have htrace : WordTrace (prefixWord ++ tailWord_8379780) baseStart_8379780 baseEnd_8379780 := by
    simpa [prefixWord, tailWord_8379780, baseEnd_8379780] using wordTrace_append hprefix tailTrace_8379780
  have hstable : (prefixWord ++ tailWord_8379780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379780).length < 2 ^ (prefixWord ++ tailWord_8379780).sum := by decide
  have hdescent : baseEnd_8379780 < baseStart_8379780 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379837 : List Nat := [1, 4, 1, 2, 2, 1, 1, 3, 2, 3, 3]
def baseStart_8379837 : Nat := 118140960795 + 8379837 * 2 ^ 59
def prefixEnd_8379837 : Nat := 4983230072969 + 3 ^ 40 * 8379837 * 2
def baseEnd_8379837 : Nat := 4302884187330635582899337

theorem tailTrace_8379837 : CollatzResearch.WordTrace tailWord_8379837 prefixEnd_8379837 4302884187330635582899337 := by
  unfold tailWord_8379837
  simp only [CollatzResearch.WordTrace]
  refine ⟨305637764542289186064065765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203758509694859457376043843 305637764542289186064065765)
  ·
    refine ⟨57307080851679222387012331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305637764542289186064065765 57307080851679222387012331)
    ·
      refine ⟨85960621277518833580518497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57307080851679222387012331 85960621277518833580518497)
      ·
        refine ⟨64470465958139125185388873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85960621277518833580518497 64470465958139125185388873)
        ·
          refine ⟨48352849468604343889041655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64470465958139125185388873 48352849468604343889041655)
          ·
            refine ⟨72529274202906515833562483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48352849468604343889041655 72529274202906515833562483)
            ·
              refine ⟨108793911304359773750343725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72529274202906515833562483 108793911304359773750343725)
              ·
                refine ⟨40797716739134915156378897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108793911304359773750343725 40797716739134915156378897)
                ·
                  refine ⟨30598287554351186367284173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40797716739134915156378897 30598287554351186367284173)
                  ·
                    refine ⟨11474357832881694887731565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30598287554351186367284173 11474357832881694887731565)
                    ·
                      refine ⟨4302884187330635582899337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11474357832881694887731565 4302884187330635582899337)
                      ·
                        rfl

theorem cell23_8379837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_8379837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379837 prefixEnd_8379837 := by exact prefixLift 8379837
  have htrace : WordTrace (prefixWord ++ tailWord_8379837) baseStart_8379837 baseEnd_8379837 := by
    simpa [prefixWord, tailWord_8379837, baseEnd_8379837] using wordTrace_append hprefix tailTrace_8379837
  have hstable : (prefixWord ++ tailWord_8379837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379837).length < 2 ^ (prefixWord ++ tailWord_8379837).sum := by decide
  have hdescent : baseEnd_8379837 < baseStart_8379837 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379840 : List Nat := [2, 1, 1, 2, 3, 1, 3, 2, 1, 7]
def baseStart_8379840 : Nat := 118140960795 + 8379840 * 2 ^ 59
def prefixEnd_8379840 : Nat := 4983230072969 + 3 ^ 40 * 8379840 * 2
def baseEnd_8379840 : Nat := 1434295242590866357053941

theorem tailTrace_8379840 : CollatzResearch.WordTrace tailWord_8379840 prefixEnd_8379840 1434295242590866357053941 := by
  unfold tailWord_8379840
  simp only [CollatzResearch.WordTrace]
  refine ⟨152818936980639158788212487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203758582640852211717616649 152818936980639158788212487)
  ·
    refine ⟨229228405470958738182318731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152818936980639158788212487 229228405470958738182318731)
    ·
      refine ⟨343842608206438107273478097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229228405470958738182318731 343842608206438107273478097)
      ·
        refine ⟨257881956154828580455108573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343842608206438107273478097 257881956154828580455108573)
        ·
          refine ⟨96705733558060717670665715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257881956154828580455108573 96705733558060717670665715)
          ·
            refine ⟨145058600337091076505998573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96705733558060717670665715 145058600337091076505998573)
            ·
              refine ⟨54396975126409153689749465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145058600337091076505998573 54396975126409153689749465)
              ·
                refine ⟨40797731344806865267312099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54396975126409153689749465 40797731344806865267312099)
                ·
                  refine ⟨61196597017210297900968149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40797731344806865267312099 61196597017210297900968149)
                  ·
                    refine ⟨1434295242590866357053941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61196597017210297900968149 1434295242590866357053941)
                    ·
                      rfl

theorem cell23_8379840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 1, 7].length) (baseStart_8379840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379840 prefixEnd_8379840 := by exact prefixLift 8379840
  have htrace : WordTrace (prefixWord ++ tailWord_8379840) baseStart_8379840 baseEnd_8379840 := by
    simpa [prefixWord, tailWord_8379840, baseEnd_8379840] using wordTrace_append hprefix tailTrace_8379840
  have hstable : (prefixWord ++ tailWord_8379840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379840).length < 2 ^ (prefixWord ++ tailWord_8379840).sum := by decide
  have hdescent : baseEnd_8379840 < baseStart_8379840 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379897 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 6, 2, 3]
def baseStart_8379897 : Nat := 118140960795 + 8379897 * 2 ^ 59
def prefixEnd_8379897 : Nat := 4983230072969 + 3 ^ 40 * 8379897 * 2
def baseEnd_8379897 : Nat := 4302914996169905348149061

theorem tailTrace_8379897 : CollatzResearch.WordTrace tailWord_8379897 prefixEnd_8379897 4302914996169905348149061 := by
  unfold tailWord_8379897
  simp only [CollatzResearch.WordTrace]
  refine ⟨305639952922071816311249945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203759968614714544207499963 305639952922071816311249945)
  ·
    refine ⟨229229964691553862233437459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305639952922071816311249945 229229964691553862233437459)
    ·
      refine ⟨343844947037330793350156189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229229964691553862233437459 343844947037330793350156189)
      ·
        refine ⟨128941855138999047506308571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343844947037330793350156189 128941855138999047506308571)
        ·
          refine ⟨193412782708498571259462857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128941855138999047506308571 193412782708498571259462857)
          ·
            refine ⟨145059587031373928444597143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193412782708498571259462857 145059587031373928444597143)
            ·
              refine ⟨217589380547060892666895715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145059587031373928444597143 217589380547060892666895715)
              ·
                refine ⟨326384070820591339000343573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217589380547060892666895715 326384070820591339000343573)
                ·
                  refine ⟨15299253319715219015641105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 326384070820591339000343573 15299253319715219015641105)
                  ·
                    refine ⟨11474439989786414261730829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15299253319715219015641105 11474439989786414261730829)
                    ·
                      refine ⟨4302914996169905348149061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11474439989786414261730829 4302914996169905348149061)
                      ·
                        rfl

theorem cell23_8379897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_8379897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379897 prefixEnd_8379897 := by exact prefixLift 8379897
  have htrace : WordTrace (prefixWord ++ tailWord_8379897) baseStart_8379897 baseEnd_8379897 := by
    simpa [prefixWord, tailWord_8379897, baseEnd_8379897] using wordTrace_append hprefix tailTrace_8379897
  have hstable : (prefixWord ++ tailWord_8379897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379897).length < 2 ^ (prefixWord ++ tailWord_8379897).sum := by decide
  have hdescent : baseEnd_8379897 < baseStart_8379897 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379914 : List Nat := [3, 1, 2, 2, 2, 2, 1, 3, 2, 2, 3]
def baseStart_8379914 : Nat := 118140960795 + 8379914 * 2 ^ 59
def prefixEnd_8379914 : Nat := 4983230072969 + 3 ^ 40 * 8379914 * 2
def baseEnd_8379914 : Nat := 4302923725341031781636483

theorem tailTrace_8379914 : CollatzResearch.WordTrace tailWord_8379914 prefixEnd_8379914 4302923725341031781636483 := by
  unfold tailWord_8379914
  simp only [CollatzResearch.WordTrace]
  refine ⟨76410143240752557053654699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203760381975340152143079197 76410143240752557053654699)
  ·
    refine ⟨114615214861128835580482049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76410143240752557053654699 114615214861128835580482049)
    ·
      refine ⟨85961411145846626685361537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114615214861128835580482049 85961411145846626685361537)
      ·
        refine ⟨64471058359384970014021153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85961411145846626685361537 64471058359384970014021153)
        ·
          refine ⟨48353293769538727510515865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64471058359384970014021153 48353293769538727510515865)
          ·
            refine ⟨36264970327154045632886899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48353293769538727510515865 36264970327154045632886899)
            ·
              refine ⟨54397455490731068449330349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36264970327154045632886899 54397455490731068449330349)
              ·
                refine ⟨20399045809024150668498881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54397455490731068449330349 20399045809024150668498881)
                ·
                  refine ⟨15299284356768113001374161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20399045809024150668498881 15299284356768113001374161)
                  ·
                    refine ⟨11474463267576084751030621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15299284356768113001374161 11474463267576084751030621)
                    ·
                      refine ⟨4302923725341031781636483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11474463267576084751030621 4302923725341031781636483)
                      ·
                        rfl

theorem cell23_8379914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_8379914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379914 prefixEnd_8379914 := by exact prefixLift 8379914
  have htrace : WordTrace (prefixWord ++ tailWord_8379914) baseStart_8379914 baseEnd_8379914 := by
    simpa [prefixWord, tailWord_8379914, baseEnd_8379914] using wordTrace_append hprefix tailTrace_8379914
  have hstable : (prefixWord ++ tailWord_8379914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379914).length < 2 ^ (prefixWord ++ tailWord_8379914).sum := by decide
  have hdescent : baseEnd_8379914 < baseStart_8379914 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379938 : List Nat := [3, 3, 1, 1, 1, 1, 6, 2, 1, 4]
def baseStart_8379938 : Nat := 118140960795 + 8379938 * 2 ^ 59
def prefixEnd_8379938 : Nat := 4983230072969 + 3 ^ 40 * 8379938 * 2
def baseEnd_8379938 : Nat := 1434312016292246562578791

theorem tailTrace_8379938 : CollatzResearch.WordTrace tailWord_8379938 prefixEnd_8379938 1434312016292246562578791 := by
  unfold tailWord_8379938
  simp only [CollatzResearch.WordTrace]
  refine ⟨76410362078730820078373117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203760965543282186875661645 76410362078730820078373117)
  ·
    refine ⟨28653885779524057529389919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76410362078730820078373117 28653885779524057529389919)
    ·
      refine ⟨42980828669286086294084879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28653885779524057529389919 42980828669286086294084879)
      ·
        refine ⟨64471243003929129441127319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42980828669286086294084879 64471243003929129441127319)
        ·
          refine ⟨96706864505893694161690979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64471243003929129441127319 96706864505893694161690979)
          ·
            refine ⟨145060296758840541242536469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96706864505893694161690979 145060296758840541242536469)
            ·
              refine ⟨6799701410570650370743897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 145060296758840541242536469 6799701410570650370743897)
              ·
                refine ⟨5099776057927987778057923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6799701410570650370743897 5099776057927987778057923)
                ·
                  refine ⟨7649664086891981667086885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5099776057927987778057923 7649664086891981667086885)
                  ·
                    refine ⟨1434312016292246562578791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7649664086891981667086885 1434312016292246562578791)
                    ·
                      rfl

theorem cell23_8379938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_8379938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379938 prefixEnd_8379938 := by exact prefixLift 8379938
  have htrace : WordTrace (prefixWord ++ tailWord_8379938) baseStart_8379938 baseEnd_8379938 := by
    simpa [prefixWord, tailWord_8379938, baseEnd_8379938] using wordTrace_append hprefix tailTrace_8379938
  have hstable : (prefixWord ++ tailWord_8379938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379938).length < 2 ^ (prefixWord ++ tailWord_8379938).sum := by decide
  have hdescent : baseEnd_8379938 < baseStart_8379938 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379954 : List Nat := [3, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2]
def baseStart_8379954 : Nat := 118140960795 + 8379954 * 2 ^ 59
def prefixEnd_8379954 : Nat := 4983230072969 + 3 ^ 40 * 8379954 * 2
def baseEnd_8379954 : Nat := 4302944264567211625136299

theorem tailTrace_8379954 : CollatzResearch.WordTrace tailWord_8379954 prefixEnd_8379954 4302944264567211625136299 := by
  unfold tailWord_8379954
  simp only [CollatzResearch.WordTrace]
  refine ⟨76410507970716328761518729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203761354588576876697383277 76410507970716328761518729)
  ·
    refine ⟨57307880978037246571139047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76410507970716328761518729 57307880978037246571139047)
    ·
      refine ⟨85961821467055869856708571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57307880978037246571139047 85961821467055869856708571)
      ·
        refine ⟨128942732200583804785062857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85961821467055869856708571 128942732200583804785062857)
        ·
          refine ⟨96707049150437853588797143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128942732200583804785062857 96707049150437853588797143)
          ·
            refine ⟨145060573725656780383195715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96707049150437853588797143 145060573725656780383195715)
            ·
              refine ⟨217590860588485170574793573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145060573725656780383195715 217590860588485170574793573)
              ·
                refine ⟨40798286360340969482773795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217590860588485170574793573 40798286360340969482773795)
                ·
                  refine ⟨61197429540511454224160693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40798286360340969482773795 61197429540511454224160693)
                  ·
                    refine ⟨5737259019422948833515065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61197429540511454224160693 5737259019422948833515065)
                    ·
                      refine ⟨4302944264567211625136299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5737259019422948833515065 4302944264567211625136299)
                      ·
                        rfl

theorem cell23_8379954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2].length) (baseStart_8379954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379954 prefixEnd_8379954 := by exact prefixLift 8379954
  have htrace : WordTrace (prefixWord ++ tailWord_8379954) baseStart_8379954 baseEnd_8379954 := by
    simpa [prefixWord, tailWord_8379954, baseEnd_8379954] using wordTrace_append hprefix tailTrace_8379954
  have hstable : (prefixWord ++ tailWord_8379954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379954).length < 2 ^ (prefixWord ++ tailWord_8379954).sum := by decide
  have hdescent : baseEnd_8379954 < baseStart_8379954 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379961 : List Nat := [1, 2, 1, 5, 1, 3, 1, 2, 3, 1, 3]
def baseStart_8379961 : Nat := 118140960795 + 8379961 * 2 ^ 59
def prefixEnd_8379961 : Nat := 4983230072969 + 3 ^ 40 * 8379961 * 2
def baseEnd_8379961 : Nat := 4302947858931793097748767

theorem tailTrace_8379961 : CollatzResearch.WordTrace tailWord_8379961 prefixEnd_8379961 4302947858931793097748767 := by
  unfold tailWord_8379961
  simp only [CollatzResearch.WordTrace]
  refine ⟨305642287193839955241579737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203761524795893303494386491 305642287193839955241579737)
  ·
    refine ⟨229231715395379966431184803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305642287193839955241579737 229231715395379966431184803)
    ·
      refine ⟨343847573093069949646777205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229231715395379966431184803 343847573093069949646777205)
      ·
        refine ⟨32235709977475307779385363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 343847573093069949646777205 32235709977475307779385363)
        ·
          refine ⟨48353564966212961669078045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32235709977475307779385363 48353564966212961669078045)
          ·
            refine ⟨18132586862329860625904267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48353564966212961669078045 18132586862329860625904267)
            ·
              refine ⟨27198880293494790938856401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18132586862329860625904267 27198880293494790938856401)
              ·
                refine ⟨20399160220121093204142301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27198880293494790938856401 20399160220121093204142301)
                ·
                  refine ⟨7649685082545409951553363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20399160220121093204142301 7649685082545409951553363)
                  ·
                    refine ⟨11474527623818114927330045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7649685082545409951553363 11474527623818114927330045)
                    ·
                      refine ⟨4302947858931793097748767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11474527623818114927330045 4302947858931793097748767)
                      ·
                        rfl

theorem cell23_8379961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_8379961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379961 prefixEnd_8379961 := by exact prefixLift 8379961
  have htrace : WordTrace (prefixWord ++ tailWord_8379961) baseStart_8379961 baseEnd_8379961 := by
    simpa [prefixWord, tailWord_8379961, baseEnd_8379961] using wordTrace_append hprefix tailTrace_8379961
  have hstable : (prefixWord ++ tailWord_8379961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379961).length < 2 ^ (prefixWord ++ tailWord_8379961).sum := by decide
  have hdescent : baseEnd_8379961 < baseStart_8379961 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379978 : List Nat := [3, 1, 2, 1, 1, 3, 4, 3, 1, 1, 3]
def baseStart_8379978 : Nat := 118140960795 + 8379978 * 2 ^ 59
def prefixEnd_8379978 : Nat := 4983230072969 + 3 ^ 40 * 8379978 * 2
def baseEnd_8379978 : Nat := 4302956588102919531236189

theorem tailTrace_8379978 : CollatzResearch.WordTrace tailWord_8379978 prefixEnd_8379978 4302956588102919531236189 := by
  unfold tailWord_8379978
  simp only [CollatzResearch.WordTrace]
  refine ⟨76410726808694591786237147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203761938156518911429965725 76410726808694591786237147)
  ·
    refine ⟨114616090213041887679355721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76410726808694591786237147 114616090213041887679355721)
    ·
      refine ⟨85962067659781415759516791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114616090213041887679355721 85962067659781415759516791)
      ·
        refine ⟨128943101489672123639275187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85962067659781415759516791 128943101489672123639275187)
        ·
          refine ⟨193414652234508185458912781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128943101489672123639275187 193414652234508185458912781)
          ·
            refine ⟨72530494587940569547092293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193414652234508185458912781 72530494587940569547092293)
            ·
              refine ⟨13599467735238856790079805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72530494587940569547092293 13599467735238856790079805)
              ·
                refine ⟨5099800400714571296279927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13599467735238856790079805 5099800400714571296279927)
                ·
                  refine ⟨7649700601071856944419891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5099800400714571296279927 7649700601071856944419891)
                  ·
                    refine ⟨11474550901607785416629837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7649700601071856944419891 11474550901607785416629837)
                    ·
                      refine ⟨4302956588102919531236189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11474550901607785416629837 4302956588102919531236189)
                      ·
                        rfl

theorem cell23_8379978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 3, 1, 1, 3].length) (baseStart_8379978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379978 prefixEnd_8379978 := by exact prefixLift 8379978
  have htrace : WordTrace (prefixWord ++ tailWord_8379978) baseStart_8379978 baseEnd_8379978 := by
    simpa [prefixWord, tailWord_8379978, baseEnd_8379978] using wordTrace_append hprefix tailTrace_8379978
  have hstable : (prefixWord ++ tailWord_8379978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379978).length < 2 ^ (prefixWord ++ tailWord_8379978).sum := by decide
  have hdescent : baseEnd_8379978 < baseStart_8379978 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8379984 : List Nat := [2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 4]
def baseStart_8379984 : Nat := 118140960795 + 8379984 * 2 ^ 59
def prefixEnd_8379984 : Nat := 4983230072969 + 3 ^ 40 * 8379984 * 2
def baseEnd_8379984 : Nat := 4302959668986846507761161

theorem tailTrace_8379984 : CollatzResearch.WordTrace tailWord_8379984 prefixEnd_8379984 4302959668986846507761161 := by
  unfold tailWord_8379984
  simp only [CollatzResearch.WordTrace]
  refine ⟨152821563036378315084833503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203762084048504420113111337 152821563036378315084833503)
  ·
    refine ⟨229232344554567472627250255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152821563036378315084833503 229232344554567472627250255)
    ·
      refine ⟨343848516831851208940875383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229232344554567472627250255 343848516831851208940875383)
      ·
        refine ⟨515772775247776813411313075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343848516831851208940875383 515772775247776813411313075)
        ·
          refine ⟨773659162871665220116969613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515772775247776813411313075 773659162871665220116969613)
          ·
            refine ⟨290122186076874457543863605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 773659162871665220116969613 290122186076874457543863605)
            ·
              refine ⟨27198954944706980394737213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 290122186076874457543863605 27198954944706980394737213)
              ·
                refine ⟨10199608104265117648026455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27198954944706980394737213 10199608104265117648026455)
                ·
                  refine ⟨15299412156397676472039683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10199608104265117648026455 15299412156397676472039683)
                  ·
                    refine ⟨22949118234596514708059525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15299412156397676472039683 22949118234596514708059525)
                    ·
                      refine ⟨4302959668986846507761161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22949118234596514708059525 4302959668986846507761161)
                      ·
                        rfl

theorem cell23_8379984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 4].length) (baseStart_8379984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8379984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8379984 prefixEnd_8379984 := by exact prefixLift 8379984
  have htrace : WordTrace (prefixWord ++ tailWord_8379984) baseStart_8379984 baseEnd_8379984 := by
    simpa [prefixWord, tailWord_8379984, baseEnd_8379984] using wordTrace_append hprefix tailTrace_8379984
  have hstable : (prefixWord ++ tailWord_8379984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8379984).length < 2 ^ (prefixWord ++ tailWord_8379984).sum := by decide
  have hdescent : baseEnd_8379984 < baseStart_8379984 := by decide
  rcases family_descends (prefixWord ++ tailWord_8379984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380004 : List Nat := [2, 3, 1, 1, 2, 4, 1, 2, 1, 1, 5]
def baseStart_8380004 : Nat := 118140960795 + 8380004 * 2 ^ 59
def prefixEnd_8380004 : Nat := 4983230072969 + 3 ^ 40 * 8380004 * 2
def baseEnd_8380004 : Nat := 4302969938599936429511069

theorem tailTrace_8380004 : CollatzResearch.WordTrace tailWord_8380004 prefixEnd_8380004 4302969938599936429511069 := by
  unfold tailWord_8380004
  simp only [CollatzResearch.WordTrace]
  refine ⟨152821927766342086792697533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203762570355122782390263377 152821927766342086792697533)
  ·
    refine ⟨57308222912378282547261575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152821927766342086792697533 57308222912378282547261575)
    ·
      refine ⟨85962334368567423820892363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57308222912378282547261575 85962334368567423820892363)
      ·
        refine ⟨128943501552851135731338545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85962334368567423820892363 128943501552851135731338545)
        ·
          refine ⟨96707626164638351798503909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128943501552851135731338545 96707626164638351798503909)
          ·
            refine ⟨18132679905869690962219483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96707626164638351798503909 18132679905869690962219483)
            ·
              refine ⟨27199019858804536443329225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18132679905869690962219483 27199019858804536443329225)
              ·
                refine ⟨20399264894103402332496919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27199019858804536443329225 20399264894103402332496919)
                ·
                  refine ⟨30598897341155103498745379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20399264894103402332496919 30598897341155103498745379)
                  ·
                    refine ⟨45898346011732655248118069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30598897341155103498745379 45898346011732655248118069)
                    ·
                      refine ⟨4302969938599936429511069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45898346011732655248118069 4302969938599936429511069)
                      ·
                        rfl

theorem cell23_8380004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_8380004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380004 prefixEnd_8380004 := by exact prefixLift 8380004
  have htrace : WordTrace (prefixWord ++ tailWord_8380004) baseStart_8380004 baseEnd_8380004 := by
    simpa [prefixWord, tailWord_8380004, baseEnd_8380004] using wordTrace_append hprefix tailTrace_8380004
  have hstable : (prefixWord ++ tailWord_8380004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380004).length < 2 ^ (prefixWord ++ tailWord_8380004).sum := by decide
  have hdescent : baseEnd_8380004 < baseStart_8380004 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380018 : List Nat := [3, 2, 1, 2, 3, 1, 2, 2, 3, 2, 2]
def baseStart_8380018 : Nat := 118140960795 + 8380018 * 2 ^ 59
def prefixEnd_8380018 : Nat := 4983230072969 + 3 ^ 40 * 8380018 * 2
def baseEnd_8380018 : Nat := 4302977127329099374736005

theorem tailTrace_8380018 : CollatzResearch.WordTrace tailWord_8380018 prefixEnd_8380018 4302977127329099374736005 := by
  unfold tailWord_8380018
  simp only [CollatzResearch.WordTrace]
  refine ⟨76411091538658363494101177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203762910769755635984269805 76411091538658363494101177)
  ·
    refine ⟨57308318653993772620575883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76411091538658363494101177 57308318653993772620575883)
    ·
      refine ⟨85962477980990658930863825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57308318653993772620575883 85962477980990658930863825)
      ·
        refine ⟨64471858485742994198147869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85962477980990658930863825 64471858485742994198147869)
        ·
          refine ⟨24176946932153622824305451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64471858485742994198147869 24176946932153622824305451)
          ·
            refine ⟨36265420398230434236458177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24176946932153622824305451 36265420398230434236458177)
            ·
              refine ⟨27199065298672825677343633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36265420398230434236458177 27199065298672825677343633)
              ·
                refine ⟨20399298974004619258007725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27199065298672825677343633 20399298974004619258007725)
                ·
                  refine ⟨7649737115251732221752897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20399298974004619258007725 7649737115251732221752897)
                  ·
                    refine ⟨5737302836438799166314673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7649737115251732221752897 5737302836438799166314673)
                    ·
                      refine ⟨4302977127329099374736005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5737302836438799166314673 4302977127329099374736005)
                      ·
                        rfl

theorem cell23_8380018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_8380018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380018 prefixEnd_8380018 := by exact prefixLift 8380018
  have htrace : WordTrace (prefixWord ++ tailWord_8380018) baseStart_8380018 baseEnd_8380018 := by
    simpa [prefixWord, tailWord_8380018, baseEnd_8380018] using wordTrace_append hprefix tailTrace_8380018
  have hstable : (prefixWord ++ tailWord_8380018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380018).length < 2 ^ (prefixWord ++ tailWord_8380018).sum := by decide
  have hdescent : baseEnd_8380018 < baseStart_8380018 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380052 : List Nat := [2, 4, 2, 2, 2, 2, 1, 1, 3, 2, 2]
def baseStart_8380052 : Nat := 118140960795 + 8380052 * 2 ^ 59
def prefixEnd_8380052 : Nat := 4983230072969 + 3 ^ 40 * 8380052 * 2
def baseEnd_8380052 : Nat := 4302994585671352241710849

theorem tailTrace_8380052 : CollatzResearch.WordTrace tailWord_8380052 prefixEnd_8380052 4302994585671352241710849 := by
  unfold tailWord_8380052
  simp only [CollatzResearch.WordTrace]
  refine ⟨152822803118255138891571205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203763737491006851855428273 152822803118255138891571205)
  ·
    refine ⟨28654275584672838542169601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152822803118255138891571205 28654275584672838542169601)
    ·
      refine ⟨21490706688504628906627201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28654275584672838542169601 21490706688504628906627201)
      ·
        refine ⟨16118030016378471679970401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21490706688504628906627201 16118030016378471679970401)
        ·
          refine ⟨12088522512283853759977801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16118030016378471679970401 12088522512283853759977801)
          ·
            refine ⟨9066391884212890319983351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12088522512283853759977801 9066391884212890319983351)
            ·
              refine ⟨13599587826319335479975027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9066391884212890319983351 13599587826319335479975027)
              ·
                refine ⟨20399381739479003219962541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13599587826319335479975027 20399381739479003219962541)
                ·
                  refine ⟨7649768152304626207485953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20399381739479003219962541 7649768152304626207485953)
                  ·
                    refine ⟨5737326114228469655614465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7649768152304626207485953 5737326114228469655614465)
                    ·
                      refine ⟨4302994585671352241710849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5737326114228469655614465 4302994585671352241710849)
                      ·
                        rfl

theorem cell23_8380052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_8380052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380052 prefixEnd_8380052 := by exact prefixLift 8380052
  have htrace : WordTrace (prefixWord ++ tailWord_8380052) baseStart_8380052 baseEnd_8380052 := by
    simpa [prefixWord, tailWord_8380052, baseEnd_8380052] using wordTrace_append hprefix tailTrace_8380052
  have hstable : (prefixWord ++ tailWord_8380052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380052).length < 2 ^ (prefixWord ++ tailWord_8380052).sum := by decide
  have hdescent : baseEnd_8380052 < baseStart_8380052 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380061 : List Nat := [1, 4, 2, 1, 1, 1, 1, 4, 3, 3, 2]
def baseStart_8380061 : Nat := 118140960795 + 8380061 * 2 ^ 59
def prefixEnd_8380061 : Nat := 4983230072969 + 3 ^ 40 * 8380061 * 2
def baseEnd_8380061 : Nat := 4302999206997242706498307

theorem tailTrace_8380061 : CollatzResearch.WordTrace tailWord_8380061 prefixEnd_8380061 4302999206997242706498307 := by
  unfold tailWord_8380061
  simp only [CollatzResearch.WordTrace]
  refine ⟨305645934493477672320220037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203763956328985114880146691 305645934493477672320220037)
  ·
    refine ⟨57308612717527063560041257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305645934493477672320220037 57308612717527063560041257)
    ·
      refine ⟨42981459538145297670030943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57308612717527063560041257 42981459538145297670030943)
      ·
        refine ⟨64472189307217946505046415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42981459538145297670030943 64472189307217946505046415)
        ·
          refine ⟨96708283960826919757569623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64472189307217946505046415 96708283960826919757569623)
          ·
            refine ⟨145062425941240379636354435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96708283960826919757569623 145062425941240379636354435)
            ·
              refine ⟨217593638911860569454531653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145062425941240379636354435 217593638911860569454531653)
              ·
                refine ⟨40798807295973856772724685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217593638911860569454531653 40798807295973856772724685)
                ·
                  refine ⟨15299552735990196289771757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40798807295973856772724685 15299552735990196289771757)
                  ·
                    refine ⟨5737332275996323608664409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15299552735990196289771757 5737332275996323608664409)
                    ·
                      refine ⟨4302999206997242706498307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5737332275996323608664409 4302999206997242706498307)
                      ·
                        rfl

theorem cell23_8380061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_8380061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380061 prefixEnd_8380061 := by exact prefixLift 8380061
  have htrace : WordTrace (prefixWord ++ tailWord_8380061) baseStart_8380061 baseEnd_8380061 := by
    simpa [prefixWord, tailWord_8380061, baseEnd_8380061] using wordTrace_append hprefix tailTrace_8380061
  have hstable : (prefixWord ++ tailWord_8380061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380061).length < 2 ^ (prefixWord ++ tailWord_8380061).sum := by decide
  have hdescent : baseEnd_8380061 < baseStart_8380061 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380067 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 1, 8]
def baseStart_8380067 : Nat := 118140960795 + 8380067 * 2 ^ 59
def prefixEnd_8380067 : Nat := 4983230072969 + 3 ^ 40 * 8380067 * 2
def baseEnd_8380067 : Nat := 1434334095960389894341093

theorem tailTrace_8380067 : CollatzResearch.WordTrace tailWord_8380067 prefixEnd_8380067 1434334095960389894341093 := by
  unfold tailWord_8380067
  simp only [CollatzResearch.WordTrace]
  refine ⟨305646153331455935344938455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203764102220970623563292303 305646153331455935344938455)
  ·
    refine ⟨458469229997183903017407683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305646153331455935344938455 458469229997183903017407683)
    ·
      refine ⟨687703844995775854526111525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458469229997183903017407683 687703844995775854526111525)
      ·
        refine ⟨128944470936707972723645911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 687703844995775854526111525 128944470936707972723645911)
        ·
          refine ⟨193416706405061959085468867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128944470936707972723645911 193416706405061959085468867)
          ·
            refine ⟨290125059607592938628203301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193416706405061959085468867 290125059607592938628203301)
            ·
              refine ⟨54398448676423675992788119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 290125059607592938628203301 54398448676423675992788119)
              ·
                refine ⟨81597673014635513989182179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54398448676423675992788119 81597673014635513989182179)
                ·
                  refine ⟨122396509521953270983773269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81597673014635513989182179 122396509521953270983773269)
                  ·
                    refine ⟨1434334095960389894341093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 122396509521953270983773269 1434334095960389894341093)
                    ·
                      rfl

theorem cell23_8380067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 8].length) (baseStart_8380067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380067 prefixEnd_8380067 := by exact prefixLift 8380067
  have htrace : WordTrace (prefixWord ++ tailWord_8380067) baseStart_8380067 baseEnd_8380067 := by
    simpa [prefixWord, tailWord_8380067, baseEnd_8380067] using wordTrace_append hprefix tailTrace_8380067
  have hstable : (prefixWord ++ tailWord_8380067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380067).length < 2 ^ (prefixWord ++ tailWord_8380067).sum := by decide
  have hdescent : baseEnd_8380067 < baseStart_8380067 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380068 : List Nat := [2, 3, 1, 2, 2, 3, 1, 3, 2, 1, 3]
def baseStart_8380068 : Nat := 118140960795 + 8380068 * 2 ^ 59
def prefixEnd_8380068 : Nat := 4983230072969 + 3 ^ 40 * 8380068 * 2
def baseEnd_8380068 : Nat := 4303002801361824179110775

theorem tailTrace_8380068 : CollatzResearch.WordTrace tailWord_8380068 prefixEnd_8380068 4303002801361824179110775 := by
  unfold tailWord_8380068
  simp only [CollatzResearch.WordTrace]
  refine ⟨152823094902226156257862429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203764126536301541677149905 152823094902226156257862429)
  ·
    refine ⟨57308660588334808596698411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152823094902226156257862429 57308660588334808596698411)
    ·
      refine ⟨85962990882502212895047617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57308660588334808596698411 85962990882502212895047617)
      ·
        refine ⟨64472243161876659671285713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85962990882502212895047617 64472243161876659671285713)
        ·
          refine ⟨48354182371407494753464285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64472243161876659671285713 48354182371407494753464285)
          ·
            refine ⟨18132818389277810532549107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48354182371407494753464285 18132818389277810532549107)
            ·
              refine ⟨27199227583916715798823661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18132818389277810532549107 27199227583916715798823661)
              ·
                refine ⟨10199710343968768424558873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27199227583916715798823661 10199710343968768424558873)
                ·
                  refine ⟨7649782757976576318419155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10199710343968768424558873 7649782757976576318419155)
                  ·
                    refine ⟨11474674136964864477628733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7649782757976576318419155 11474674136964864477628733)
                    ·
                      refine ⟨4303002801361824179110775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11474674136964864477628733 4303002801361824179110775)
                      ·
                        rfl

theorem cell23_8380068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_8380068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380068 prefixEnd_8380068 := by exact prefixLift 8380068
  have htrace : WordTrace (prefixWord ++ tailWord_8380068) baseStart_8380068 baseEnd_8380068 := by
    simpa [prefixWord, tailWord_8380068, baseEnd_8380068] using wordTrace_append hprefix tailTrace_8380068
  have hstable : (prefixWord ++ tailWord_8380068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380068).length < 2 ^ (prefixWord ++ tailWord_8380068).sum := by decide
  have hdescent : baseEnd_8380068 < baseStart_8380068 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380091 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 6, 2, 2]
def baseStart_8380091 : Nat := 118140960795 + 8380091 * 2 ^ 59
def prefixEnd_8380091 : Nat := 4983230072969 + 3 ^ 40 * 8380091 * 2
def baseEnd_8380091 : Nat := 4303014611416877589123169

theorem tailTrace_8380091 : CollatzResearch.WordTrace tailWord_8380091 prefixEnd_8380091 4303014611416877589123169 := by
  unfold tailWord_8380091
  simp only [CollatzResearch.WordTrace]
  refine ⟨305647028683368987443812127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203764685788912658295874751 305647028683368987443812127)
  ·
    refine ⟨458470543025053481165718191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305647028683368987443812127 458470543025053481165718191)
    ·
      refine ⟨687705814537580221748577287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458470543025053481165718191 687705814537580221748577287)
      ·
        refine ⟨1031558721806370332622865931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687705814537580221748577287 1031558721806370332622865931)
        ·
          refine ⟨1547338082709555498934298897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1031558721806370332622865931 1547338082709555498934298897)
          ·
            refine ⟨1160503562032166624200724173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1547338082709555498934298897 1160503562032166624200724173)
            ·
              refine ⟨435188835762062484075271565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1160503562032166624200724173 435188835762062484075271565)
              ·
                refine ⟨163195813410773431528226837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 435188835762062484075271565 163195813410773431528226837)
                ·
                  refine ⟨7649803753630004602885633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 163195813410773431528226837 7649803753630004602885633)
                  ·
                    refine ⟨5737352815222503452164225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7649803753630004602885633 5737352815222503452164225)
                    ·
                      refine ⟨4303014611416877589123169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5737352815222503452164225 4303014611416877589123169)
                      ·
                        rfl

theorem cell23_8380091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6, 2, 2].length) (baseStart_8380091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380091 prefixEnd_8380091 := by exact prefixLift 8380091
  have htrace : WordTrace (prefixWord ++ tailWord_8380091) baseStart_8380091 baseEnd_8380091 := by
    simpa [prefixWord, tailWord_8380091, baseEnd_8380091] using wordTrace_append hprefix tailTrace_8380091
  have hstable : (prefixWord ++ tailWord_8380091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380091).length < 2 ^ (prefixWord ++ tailWord_8380091).sum := by decide
  have hdescent : baseEnd_8380091 < baseStart_8380091 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380102 : List Nat := [6, 1, 2, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_8380102 : Nat := 118140960795 + 8380102 * 2 ^ 59
def prefixEnd_8380102 : Nat := 4983230072969 + 3 ^ 40 * 8380102 * 2
def baseEnd_8380102 : Nat := 4303020259704077046085619

theorem tailTrace_8380102 : CollatzResearch.WordTrace tailWord_8380102 prefixEnd_8380102 4303020259704077046085619 := by
  unfold tailWord_8380102
  simp only [CollatzResearch.WordTrace]
  refine ⟨9551482183947785510076955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 203764953257552757548308373 9551482183947785510076955)
  ·
    refine ⟨14327223275921678265115433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9551482183947785510076955 14327223275921678265115433)
    ·
      refine ⟨10745417456941258698836575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14327223275921678265115433 10745417456941258698836575)
      ·
        refine ⟨16118126185411888048254863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10745417456941258698836575 16118126185411888048254863)
        ·
          refine ⟨24177189278117832072382295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16118126185411888048254863 24177189278117832072382295)
          ·
            refine ⟨36265783917176748108573443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24177189278117832072382295 36265783917176748108573443)
            ·
              refine ⟨54398675875765122162860165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36265783917176748108573443 54398675875765122162860165)
              ·
                refine ⟨10199751726705960405536281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54398675875765122162860165 10199751726705960405536281)
                ·
                  refine ⟨7649813795029470304152211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10199751726705960405536281 7649813795029470304152211)
                  ·
                    refine ⟨11474720692544205456228317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7649813795029470304152211 11474720692544205456228317)
                    ·
                      refine ⟨4303020259704077046085619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11474720692544205456228317 4303020259704077046085619)
                      ·
                        rfl

theorem cell23_8380102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_8380102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380102 prefixEnd_8380102 := by exact prefixLift 8380102
  have htrace : WordTrace (prefixWord ++ tailWord_8380102) baseStart_8380102 baseEnd_8380102 := by
    simpa [prefixWord, tailWord_8380102, baseEnd_8380102] using wordTrace_append hprefix tailTrace_8380102
  have hstable : (prefixWord ++ tailWord_8380102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380102).length < 2 ^ (prefixWord ++ tailWord_8380102).sum := by decide
  have hdescent : baseEnd_8380102 < baseStart_8380102 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380104 : List Nat := [2, 1, 3, 1, 2, 2, 2, 2, 2, 2, 4]
def baseStart_8380104 : Nat := 118140960795 + 8380104 * 2 ^ 59
def prefixEnd_8380104 : Nat := 4983230072969 + 3 ^ 40 * 8380104 * 2
def baseEnd_8380104 : Nat := 4303021286665386038260609

theorem tailTrace_8380104 : CollatzResearch.WordTrace tailWord_8380104 prefixEnd_8380104 4303021286665386038260609 := by
  unfold tailWord_8380104
  simp only [CollatzResearch.WordTrace]
  refine ⟨152823751416160945332017683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203765001888214593776023577 152823751416160945332017683)
  ·
    refine ⟨229235627124241417998026525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152823751416160945332017683 229235627124241417998026525)
    ·
      refine ⟨85963360171590531749259947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229235627124241417998026525 85963360171590531749259947)
      ·
        refine ⟨128945040257385797623889921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85963360171590531749259947 128945040257385797623889921)
        ·
          refine ⟨96708780193039348217917441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128945040257385797623889921 96708780193039348217917441)
          ·
            refine ⟨72531585144779511163438081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96708780193039348217917441 72531585144779511163438081)
            ·
              refine ⟨54398688858584633372578561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72531585144779511163438081 54398688858584633372578561)
              ·
                refine ⟨40799016643938475029433921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54398688858584633372578561 40799016643938475029433921)
                ·
                  refine ⟨30599262482953856272075441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40799016643938475029433921 30599262482953856272075441)
                  ·
                    refine ⟨22949446862215392204056581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30599262482953856272075441 22949446862215392204056581)
                    ·
                      refine ⟨4303021286665386038260609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22949446862215392204056581 4303021286665386038260609)
                      ·
                        rfl

theorem cell23_8380104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_8380104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380104 prefixEnd_8380104 := by exact prefixLift 8380104
  have htrace : WordTrace (prefixWord ++ tailWord_8380104) baseStart_8380104 baseEnd_8380104 := by
    simpa [prefixWord, tailWord_8380104, baseEnd_8380104] using wordTrace_append hprefix tailTrace_8380104
  have hstable : (prefixWord ++ tailWord_8380104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380104).length < 2 ^ (prefixWord ++ tailWord_8380104).sum := by decide
  have hdescent : baseEnd_8380104 < baseStart_8380104 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380107 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 7]
def baseStart_8380107 : Nat := 118140960795 + 8380107 * 2 ^ 59
def prefixEnd_8380107 : Nat := 4983230072969 + 3 ^ 40 * 8380107 * 2
def baseEnd_8380107 : Nat := 4303022827107349526523095

theorem tailTrace_8380107 : CollatzResearch.WordTrace tailWord_8380107 prefixEnd_8380107 4303022827107349526523095 := by
  unfold tailWord_8380107
  simp only [CollatzResearch.WordTrace]
  refine ⟨305647612251311022176394575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203765074834207348117596383 305647612251311022176394575)
  ·
    refine ⟨458471418376966533264591863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305647612251311022176394575 458471418376966533264591863)
    ·
      refine ⟨687707127565449799896887795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458471418376966533264591863 687707127565449799896887795)
      ·
        refine ⟨1031560691348174699845331693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687707127565449799896887795 1031560691348174699845331693)
        ·
          refine ⟨386835259255565512441999385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1031560691348174699845331693 386835259255565512441999385)
          ·
            refine ⟨290126444441674134331499539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386835259255565512441999385 290126444441674134331499539)
            ·
              refine ⟨435189666662511201497249309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290126444441674134331499539 435189666662511201497249309)
              ·
                refine ⟨163196124998441700561468491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 435189666662511201497249309 163196124998441700561468491)
                ·
                  refine ⟨244794187497662550842202737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163196124998441700561468491 244794187497662550842202737)
                  ·
                    refine ⟨183595640623246913131652053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 244794187497662550842202737 183595640623246913131652053)
                    ·
                      refine ⟨4303022827107349526523095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 183595640623246913131652053 4303022827107349526523095)
                      ·
                        rfl

theorem cell23_8380107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 7].length) (baseStart_8380107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380107 prefixEnd_8380107 := by exact prefixLift 8380107
  have htrace : WordTrace (prefixWord ++ tailWord_8380107) baseStart_8380107 baseEnd_8380107 := by
    simpa [prefixWord, tailWord_8380107, baseEnd_8380107] using wordTrace_append hprefix tailTrace_8380107
  have hstable : (prefixWord ++ tailWord_8380107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380107).length < 2 ^ (prefixWord ++ tailWord_8380107).sum := by decide
  have hdescent : baseEnd_8380107 < baseStart_8380107 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380131 : List Nat := [1, 1, 1, 7, 2, 1, 1, 2, 7]
def baseStart_8380131 : Nat := 118140960795 + 8380131 * 2 ^ 59
def prefixEnd_8380131 : Nat := 4983230072969 + 3 ^ 40 * 8380131 * 2
def baseEnd_8380131 : Nat := 478115016738117492513665

theorem tailTrace_8380131 : CollatzResearch.WordTrace tailWord_8380131 prefixEnd_8380131 478115016738117492513665 := by
  unfold tailWord_8380131
  simp only [CollatzResearch.WordTrace]
  refine ⟨305648487603224074275268247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203765658402149382850178831 305648487603224074275268247)
  ·
    refine ⟨458472731404836111412902371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305648487603224074275268247 458472731404836111412902371)
    ·
      refine ⟨687709097107254167119353557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458472731404836111412902371 687709097107254167119353557)
      ·
        refine ⟨16118181963451269541859849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 687709097107254167119353557 16118181963451269541859849)
        ·
          refine ⟨12088636472588452156394887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16118181963451269541859849 12088636472588452156394887)
          ·
            refine ⟨18132954708882678234592331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12088636472588452156394887 18132954708882678234592331)
            ·
              refine ⟨27199432063324017351888497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18132954708882678234592331 27199432063324017351888497)
              ·
                refine ⟨20399574047493013013916373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27199432063324017351888497 20399574047493013013916373)
                ·
                  refine ⟨478115016738117492513665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20399574047493013013916373 478115016738117492513665)
                  ·
                    rfl

theorem cell23_8380131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 7].length) (baseStart_8380131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380131 prefixEnd_8380131 := by exact prefixLift 8380131
  have htrace : WordTrace (prefixWord ++ tailWord_8380131) baseStart_8380131 baseEnd_8380131 := by
    simpa [prefixWord, tailWord_8380131, baseEnd_8380131] using wordTrace_append hprefix tailTrace_8380131
  have hstable : (prefixWord ++ tailWord_8380131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380131).length < 2 ^ (prefixWord ++ tailWord_8380131).sum := by decide
  have hdescent : baseEnd_8380131 < baseStart_8380131 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380144 : List Nat := [2, 1, 1, 1, 3, 1, 2, 5, 2, 5]
def baseStart_8380144 : Nat := 118140960795 + 8380144 * 2 ^ 59
def prefixEnd_8380144 : Nat := 4983230072969 + 3 ^ 40 * 8380144 * 2
def baseEnd_8380144 : Nat := 1434347275297188627253475

theorem tailTrace_8380144 : CollatzResearch.WordTrace tailWord_8380144 prefixEnd_8380144 1434347275297188627253475 := by
  unfold tailWord_8380144
  simp only [CollatzResearch.WordTrace]
  refine ⟨152824480876088488747745743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203765974501451318330327657 152824480876088488747745743)
  ·
    refine ⟨229236721314132733121618615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152824480876088488747745743 229236721314132733121618615)
    ·
      refine ⟨343855081971199099682427923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229236721314132733121618615 343855081971199099682427923)
      ·
        refine ⟨515782622956798649523641885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343855081971199099682427923 515782622956798649523641885)
        ·
          refine ⟨193418483608799493571365707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 515782622956798649523641885 193418483608799493571365707)
          ·
            refine ⟨290127725413199240357048561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193418483608799493571365707 290127725413199240357048561)
            ·
              refine ⟨217595794059899430267786421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290127725413199240357048561 217595794059899430267786421)
              ·
                refine ⟨20399605693115571587604977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 217595794059899430267786421 20399605693115571587604977)
                ·
                  refine ⟨15299704269836678690703733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20399605693115571587604977 15299704269836678690703733)
                  ·
                    refine ⟨1434347275297188627253475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15299704269836678690703733 1434347275297188627253475)
                    ·
                      rfl

theorem cell23_8380144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 2, 5].length) (baseStart_8380144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380144 prefixEnd_8380144 := by exact prefixLift 8380144
  have htrace : WordTrace (prefixWord ++ tailWord_8380144) baseStart_8380144 baseEnd_8380144 := by
    simpa [prefixWord, tailWord_8380144, baseEnd_8380144] using wordTrace_append hprefix tailTrace_8380144
  have hstable : (prefixWord ++ tailWord_8380144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380144).length < 2 ^ (prefixWord ++ tailWord_8380144).sum := by decide
  have hdescent : baseEnd_8380144 < baseStart_8380144 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380191 : List Nat := [1, 1, 2, 4, 2, 1, 1, 4, 3, 4]
def baseStart_8380191 : Nat := 118140960795 + 8380191 * 2 ^ 59
def prefixEnd_8380191 : Nat := 4983230072969 + 3 ^ 40 * 8380191 * 2
def baseEnd_8380191 : Nat := 1434355319827442399290903

theorem tailTrace_8380191 : CollatzResearch.WordTrace tailWord_8380191 prefixEnd_8380191 1434355319827442399290903 := by
  unfold tailWord_8380191
  simp only [CollatzResearch.WordTrace]
  refine ⟨305650675983006704522452427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203767117322004469681634951 305650675983006704522452427)
  ·
    refine ⟨458476013974510056783678641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305650675983006704522452427 458476013974510056783678641)
    ·
      refine ⟨343857010480882542587758981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458476013974510056783678641 343857010480882542587758981)
      ·
        refine ⟨64473189465165476735204809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 343857010480882542587758981 64473189465165476735204809)
        ·
          refine ⟨48354892098874107551403607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64473189465165476735204809 48354892098874107551403607)
          ·
            refine ⟨72532338148311161327105411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48354892098874107551403607 72532338148311161327105411)
            ·
              refine ⟨108798507222466741990658117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72532338148311161327105411 108798507222466741990658117)
              ·
                refine ⟨20399720104212514123248397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108798507222466741990658117 20399720104212514123248397)
                ·
                  refine ⟨7649895039079692796218149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20399720104212514123248397 7649895039079692796218149)
                  ·
                    refine ⟨1434355319827442399290903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7649895039079692796218149 1434355319827442399290903)
                    ·
                      rfl

theorem cell23_8380191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 3, 4].length) (baseStart_8380191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380191 prefixEnd_8380191 := by exact prefixLift 8380191
  have htrace : WordTrace (prefixWord ++ tailWord_8380191) baseStart_8380191 baseEnd_8380191 := by
    simpa [prefixWord, tailWord_8380191, baseEnd_8380191] using wordTrace_append hprefix tailTrace_8380191
  have hstable : (prefixWord ++ tailWord_8380191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380191).length < 2 ^ (prefixWord ++ tailWord_8380191).sum := by decide
  have hdescent : baseEnd_8380191 < baseStart_8380191 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380204 : List Nat := [2, 2, 1, 1, 1, 5, 1, 2, 8]
def baseStart_8380204 : Nat := 118140960795 + 8380204 * 2 ^ 59
def prefixEnd_8380204 : Nat := 4983230072969 + 3 ^ 40 * 8380204 * 2
def baseEnd_8380204 : Nat := 478119181636759516334461

theorem tailTrace_8380204 : CollatzResearch.WordTrace tailWord_8380204 prefixEnd_8380204 478119181636759516334461 := by
  unfold tailWord_8380204
  simp only [CollatzResearch.WordTrace]
  refine ⟨152825575065979803871337833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203767433421306405161783777 152825575065979803871337833)
  ·
    refine ⟨114619181299484852903503375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152825575065979803871337833 114619181299484852903503375)
    ·
      refine ⟨171928771949227279355255063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114619181299484852903503375 171928771949227279355255063)
      ·
        refine ⟨257893157923840919032882595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171928771949227279355255063 257893157923840919032882595)
        ·
          refine ⟨386839736885761378549323893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257893157923840919032882595 386839736885761378549323893)
          ·
            refine ⟨36266225333040129238999115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 386839736885761378549323893 36266225333040129238999115)
            ·
              refine ⟨54399337999560193858498673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36266225333040129238999115 54399337999560193858498673)
              ·
                refine ⟨40799503499670145393874005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54399337999560193858498673 40799503499670145393874005)
                ·
                  refine ⟨478119181636759516334461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40799503499670145393874005 478119181636759516334461)
                  ·
                    rfl

theorem cell23_8380204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 8].length) (baseStart_8380204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380204 prefixEnd_8380204 := by exact prefixLift 8380204
  have htrace : WordTrace (prefixWord ++ tailWord_8380204) baseStart_8380204 baseEnd_8380204 := by
    simpa [prefixWord, tailWord_8380204, baseEnd_8380204] using wordTrace_append hprefix tailTrace_8380204
  have hstable : (prefixWord ++ tailWord_8380204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380204).length < 2 ^ (prefixWord ++ tailWord_8380204).sum := by decide
  have hdescent : baseEnd_8380204 < baseStart_8380204 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380218 : List Nat := [3, 1, 1, 1, 5, 2, 1, 2, 2, 2, 3]
def baseStart_8380218 : Nat := 118140960795 + 8380218 * 2 ^ 59
def prefixEnd_8380218 : Nat := 4983230072969 + 3 ^ 40 * 8380218 * 2
def baseEnd_8380218 : Nat := 4303079823459998592235085

theorem tailTrace_8380218 : CollatzResearch.WordTrace tailWord_8380218 prefixEnd_8380218 4303079823459998592235085 := by
  unfold tailWord_8380218
  simp only [CollatzResearch.WordTrace]
  refine ⟨76412915188477222033421327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203767773835939258755790205 76412915188477222033421327)
  ·
    refine ⟨114619372782715833050131991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76412915188477222033421327 114619372782715833050131991)
    ·
      refine ⟨171929059174073749575197987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114619372782715833050131991 171929059174073749575197987)
      ·
        refine ⟨257893588761110624362796981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171929059174073749575197987 257893588761110624362796981)
        ·
          refine ⟨24177523946354121034012217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 257893588761110624362796981 24177523946354121034012217)
          ·
            refine ⟨18133142959765590775509163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24177523946354121034012217 18133142959765590775509163)
            ·
              refine ⟨27199714439648386163263745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18133142959765590775509163 27199714439648386163263745)
              ·
                refine ⟨20399785829736289622447809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27199714439648386163263745 20399785829736289622447809)
                ·
                  refine ⟨15299839372302217216835857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20399785829736289622447809 15299839372302217216835857)
                  ·
                    refine ⟨11474879529226662912626893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15299839372302217216835857 11474879529226662912626893)
                    ·
                      refine ⟨4303079823459998592235085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11474879529226662912626893 4303079823459998592235085)
                      ·
                        rfl

theorem cell23_8380218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 2, 2, 3].length) (baseStart_8380218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380218 prefixEnd_8380218 := by exact prefixLift 8380218
  have htrace : WordTrace (prefixWord ++ tailWord_8380218) baseStart_8380218 baseEnd_8380218 := by
    simpa [prefixWord, tailWord_8380218, baseEnd_8380218] using wordTrace_append hprefix tailTrace_8380218
  have hstable : (prefixWord ++ tailWord_8380218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380218).length < 2 ^ (prefixWord ++ tailWord_8380218).sum := by decide
  have hdescent : baseEnd_8380218 < baseStart_8380218 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380221 : List Nat := [1, 4, 1, 4, 1, 1, 2, 1, 8]
def baseStart_8380221 : Nat := 118140960795 + 8380221 * 2 ^ 59
def prefixEnd_8380221 : Nat := 4983230072969 + 3 ^ 40 * 8380221 * 2
def baseEnd_8380221 : Nat := 478120151544662453388619

theorem tailTrace_8380221 : CollatzResearch.WordTrace tailWord_8380221 prefixEnd_8380221 478120151544662453388619 := by
  unfold tailWord_8380221
  simp only [CollatzResearch.WordTrace]
  refine ⟨305651770172898019646044517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203767846781932013097363011 305651770172898019646044517)
  ·
    refine ⟨57309706907418378683633347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305651770172898019646044517 57309706907418378683633347)
    ·
      refine ⟨85964560361127568025450021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57309706907418378683633347 85964560361127568025450021)
      ·
        refine ⟨16118355067711419004771879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85964560361127568025450021 16118355067711419004771879)
        ·
          refine ⟨24177532601567128507157819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16118355067711419004771879 24177532601567128507157819)
          ·
            refine ⟨36266298902350692760736729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24177532601567128507157819 36266298902350692760736729)
            ·
              refine ⟨27199724176763019570552547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36266298902350692760736729 27199724176763019570552547)
              ·
                refine ⟨40799586265144529355828821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27199724176763019570552547 40799586265144529355828821)
                ·
                  refine ⟨478120151544662453388619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40799586265144529355828821 478120151544662453388619)
                  ·
                    rfl

theorem cell23_8380221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 8].length) (baseStart_8380221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380221 prefixEnd_8380221 := by exact prefixLift 8380221
  have htrace : WordTrace (prefixWord ++ tailWord_8380221) baseStart_8380221 baseEnd_8380221 := by
    simpa [prefixWord, tailWord_8380221, baseEnd_8380221] using wordTrace_append hprefix tailTrace_8380221
  have hstable : (prefixWord ++ tailWord_8380221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380221).length < 2 ^ (prefixWord ++ tailWord_8380221).sum := by decide
  have hdescent : baseEnd_8380221 < baseStart_8380221 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380282 : List Nat := [3, 1, 1, 1, 1, 1, 8, 2, 1, 1, 3]
def baseStart_8380282 : Nat := 118140960795 + 8380282 * 2 ^ 59
def prefixEnd_8380282 : Nat := 4983230072969 + 3 ^ 40 * 8380282 * 2
def baseEnd_8380282 : Nat := 4303112686221886341834791

theorem tailTrace_8380282 : CollatzResearch.WordTrace tailWord_8380282 prefixEnd_8380282 4303112686221886341834791 := by
  unfold tailWord_8380282
  simp only [CollatzResearch.WordTrace]
  refine ⟨76413498756419256766003775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203769330017118018042676733 76413498756419256766003775)
  ·
    refine ⟨114620248134628885149005663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76413498756419256766003775 114620248134628885149005663)
    ·
      refine ⟨171930372201943327723508495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114620248134628885149005663 171930372201943327723508495)
      ·
        refine ⟨257895558302914991585262743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171930372201943327723508495 257895558302914991585262743)
        ·
          refine ⟨386843337454372487377894115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257895558302914991585262743 386843337454372487377894115)
          ·
            refine ⟨580265006181558731066841173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386843337454372487377894115 580265006181558731066841173)
            ·
              refine ⟨6799980541190141379689545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 580265006181558731066841173 6799980541190141379689545)
              ·
                refine ⟨5099985405892606034767159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6799980541190141379689545 5099985405892606034767159)
                ·
                  refine ⟨7649978108838909052150739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5099985405892606034767159 7649978108838909052150739)
                  ·
                    refine ⟨11474967163258363578226109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7649978108838909052150739 11474967163258363578226109)
                    ·
                      refine ⟨4303112686221886341834791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11474967163258363578226109 4303112686221886341834791)
                      ·
                        rfl

theorem cell23_8380282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 2, 1, 1, 3].length) (baseStart_8380282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380282 prefixEnd_8380282 := by exact prefixLift 8380282
  have htrace : WordTrace (prefixWord ++ tailWord_8380282) baseStart_8380282 baseEnd_8380282 := by
    simpa [prefixWord, tailWord_8380282, baseEnd_8380282] using wordTrace_append hprefix tailTrace_8380282
  have hstable : (prefixWord ++ tailWord_8380282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380282).length < 2 ^ (prefixWord ++ tailWord_8380282).sum := by decide
  have hdescent : baseEnd_8380282 < baseStart_8380282 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380406 : List Nat := [5, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3]
def baseStart_8380406 : Nat := 118140960795 + 8380406 * 2 ^ 59
def prefixEnd_8380406 : Nat := 4983230072969 + 3 ^ 40 * 8380406 * 2
def baseEnd_8380406 : Nat := 4303176357823043856684221

theorem tailTrace_8380406 : CollatzResearch.WordTrace tailWord_8380406 prefixEnd_8380406 4303176357823043856684221 := by
  unfold tailWord_8380406
  simp only [CollatzResearch.WordTrace]
  refine ⟨19103657354826737265095567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203772345118151864161019381 19103657354826737265095567)
  ·
    refine ⟨28655486032240105897643351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19103657354826737265095567 28655486032240105897643351)
    ·
      refine ⟨42983229048360158846465027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28655486032240105897643351 42983229048360158846465027)
      ·
        refine ⟨64474843572540238269697541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42983229048360158846465027 64474843572540238269697541)
        ·
          refine ⟨12089033169851294675568289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64474843572540238269697541 12089033169851294675568289)
          ·
            refine ⟨9066774877388471006676217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12089033169851294675568289 9066774877388471006676217)
            ·
              refine ⟨6800081158041353255007163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9066774877388471006676217 6800081158041353255007163)
              ·
                refine ⟨10200121737062029882510745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6800081158041353255007163 10200121737062029882510745)
                ·
                  refine ⟨7650091302796522411883059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10200121737062029882510745 7650091302796522411883059)
                  ·
                    refine ⟨11475136954194783617824589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7650091302796522411883059 11475136954194783617824589)
                    ·
                      refine ⟨4303176357823043856684221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11475136954194783617824589 4303176357823043856684221)
                      ·
                        rfl

theorem cell23_8380406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_8380406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380406 prefixEnd_8380406 := by exact prefixLift 8380406
  have htrace : WordTrace (prefixWord ++ tailWord_8380406) baseStart_8380406 baseEnd_8380406 := by
    simpa [prefixWord, tailWord_8380406, baseEnd_8380406] using wordTrace_append hprefix tailTrace_8380406
  have hstable : (prefixWord ++ tailWord_8380406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380406).length < 2 ^ (prefixWord ++ tailWord_8380406).sum := by decide
  have hdescent : baseEnd_8380406 < baseStart_8380406 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380412 : List Nat := [2, 2, 2, 1, 2, 2, 3, 3, 2, 2, 2]
def baseStart_8380412 : Nat := 118140960795 + 8380412 * 2 ^ 59
def prefixEnd_8380412 : Nat := 4983230072969 + 3 ^ 40 * 8380412 * 2
def baseEnd_8380412 : Nat := 4303179438706970833209193

theorem tailTrace_8380412 : CollatzResearch.WordTrace tailWord_8380412 prefixEnd_8380412 4303179438706970833209193 := by
  unfold tailWord_8380412
  simp only [CollatzResearch.WordTrace]
  refine ⟨152829368257603029633123745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203772491010137372844164993 152829368257603029633123745)
  ·
    refine ⟨114622026193202272224842809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152829368257603029633123745 114622026193202272224842809)
    ·
      refine ⟨85966519644901704168632107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114622026193202272224842809 85966519644901704168632107)
      ·
        refine ⟨128949779467352556252948161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85966519644901704168632107 128949779467352556252948161)
        ·
          refine ⟨96712334600514417189711121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128949779467352556252948161 96712334600514417189711121)
          ·
            refine ⟨72534250950385812892283341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96712334600514417189711121 72534250950385812892283341)
            ·
              refine ⟨27200344106394679834606253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72534250950385812892283341 27200344106394679834606253)
              ·
                refine ⟨10200129039898004937977345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27200344106394679834606253 10200129039898004937977345)
                ·
                  refine ⟨7650096779923503703483009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10200129039898004937977345 7650096779923503703483009)
                  ·
                    refine ⟨5737572584942627777612257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7650096779923503703483009 5737572584942627777612257)
                    ·
                      refine ⟨4303179438706970833209193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5737572584942627777612257 4303179438706970833209193)
                      ·
                        rfl

theorem cell23_8380412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 2, 2, 2].length) (baseStart_8380412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380412 prefixEnd_8380412 := by exact prefixLift 8380412
  have htrace : WordTrace (prefixWord ++ tailWord_8380412) baseStart_8380412 baseEnd_8380412 := by
    simpa [prefixWord, tailWord_8380412, baseEnd_8380412] using wordTrace_append hprefix tailTrace_8380412
  have hstable : (prefixWord ++ tailWord_8380412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380412).length < 2 ^ (prefixWord ++ tailWord_8380412).sum := by decide
  have hdescent : baseEnd_8380412 < baseStart_8380412 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380452 : List Nat := [2, 3, 1, 4, 2, 1, 1, 4, 5]
def baseStart_8380452 : Nat := 118140960795 + 8380452 * 2 ^ 59
def prefixEnd_8380452 : Nat := 4983230072969 + 3 ^ 40 * 8380452 * 2
def baseEnd_8380452 : Nat := 478133330881461186301001

theorem tailTrace_8380452 : CollatzResearch.WordTrace tailWord_8380452 prefixEnd_8380452 478133330881461186301001 := by
  unfold tailWord_8380452
  simp only [CollatzResearch.WordTrace]
  refine ⟨152830097717530573048851805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203773463623374097398469073 152830097717530573048851805)
  ·
    refine ⟨57311286644073964893319427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152830097717530573048851805 57311286644073964893319427)
    ·
      refine ⟨85966929966110947339979141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57311286644073964893319427 85966929966110947339979141)
      ·
        refine ⟨16118799368645802626246089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85966929966110947339979141 16118799368645802626246089)
        ·
          refine ⟨12089099526484351969684567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16118799368645802626246089 12089099526484351969684567)
          ·
            refine ⟨18133649289726527954526851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12089099526484351969684567 18133649289726527954526851)
            ·
              refine ⟨27200473934589791931790277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18133649289726527954526851 27200473934589791931790277)
              ·
                refine ⟨5100088862735585987210677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27200473934589791931790277 5100088862735585987210677)
                ·
                  refine ⟨478133330881461186301001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5100088862735585987210677 478133330881461186301001)
                  ·
                    rfl

theorem cell23_8380452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 4, 5].length) (baseStart_8380452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380452 prefixEnd_8380452 := by exact prefixLift 8380452
  have htrace : WordTrace (prefixWord ++ tailWord_8380452) baseStart_8380452 baseEnd_8380452 := by
    simpa [prefixWord, tailWord_8380452, baseEnd_8380452] using wordTrace_append hprefix tailTrace_8380452
  have hstable : (prefixWord ++ tailWord_8380452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380452).length < 2 ^ (prefixWord ++ tailWord_8380452).sum := by decide
  have hdescent : baseEnd_8380452 < baseStart_8380452 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380491 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 10]
def baseStart_8380491 : Nat := 118140960795 + 8380491 * 2 ^ 59
def prefixEnd_8380491 : Nat := 4983230072969 + 3 ^ 40 * 8380491 * 2
def baseEnd_8380491 : Nat := 478135555964297336013481

theorem tailTrace_8380491 : CollatzResearch.WordTrace tailWord_8380491 prefixEnd_8380491 478135555964297336013481 := by
  unfold tailWord_8380491
  simp only [CollatzResearch.WordTrace]
  refine ⟨305661617881919855758373327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203774411921279903838915551 305661617881919855758373327)
  ·
    refine ⟨458492426822879783637559991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305661617881919855758373327 458492426822879783637559991)
    ·
      refine ⟨687738640234319675456339987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458492426822879783637559991 687738640234319675456339987)
      ·
        refine ⟨1031607960351479513184509981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687738640234319675456339987 1031607960351479513184509981)
        ·
          refine ⟨386852985131804817444191243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1031607960351479513184509981 386852985131804817444191243)
          ·
            refine ⟨580279477697707226166286865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386852985131804817444191243 580279477697707226166286865)
            ·
              refine ⟨435209608273280419624715149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 580279477697707226166286865 435209608273280419624715149)
              ·
                refine ⟨163203603102480157359268181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 435209608273280419624715149 163203603102480157359268181)
                ·
                  refine ⟨478135555964297336013481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 163203603102480157359268181 478135555964297336013481)
                  ·
                    rfl

theorem cell23_8380491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 10].length) (baseStart_8380491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380491 prefixEnd_8380491 := by exact prefixLift 8380491
  have htrace : WordTrace (prefixWord ++ tailWord_8380491) baseStart_8380491 baseEnd_8380491 := by
    simpa [prefixWord, tailWord_8380491, baseEnd_8380491] using wordTrace_append hprefix tailTrace_8380491
  have hstable : (prefixWord ++ tailWord_8380491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380491).length < 2 ^ (prefixWord ++ tailWord_8380491).sum := by decide
  have hdescent : baseEnd_8380491 < baseStart_8380491 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380512 : List Nat := [2, 1, 1, 3, 2, 3, 2, 4, 1, 4]
def baseStart_8380512 : Nat := 118140960795 + 8380512 * 2 ^ 59
def prefixEnd_8380512 : Nat := 4983230072969 + 3 ^ 40 * 8380512 * 2
def baseEnd_8380512 : Nat := 1434410262257473480652911

theorem tailTrace_8380512 : CollatzResearch.WordTrace tailWord_8380512 prefixEnd_8380512 1434410262257473480652911 := by
  unfold tailWord_8380512
  simp only [CollatzResearch.WordTrace]
  refine ⟨152831191907421888172443895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203774922543229184229925193 152831191907421888172443895)
  ·
    refine ⟨229246787861132832258665843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152831191907421888172443895 229246787861132832258665843)
    ·
      refine ⟨343870181791699248387998765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229246787861132832258665843 343870181791699248387998765)
      ·
        refine ⟨128951318171887218145499537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343870181791699248387998765 128951318171887218145499537)
        ·
          refine ⟨96713488628915413609124653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128951318171887218145499537 96713488628915413609124653)
          ·
            refine ⟨36267558235843280103421745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96713488628915413609124653 36267558235843280103421745)
            ·
              refine ⟨27200668676882460077566309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36267558235843280103421745 27200668676882460077566309)
              ·
                refine ⟨5100125376915461264543683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27200668676882460077566309 5100125376915461264543683)
                ·
                  refine ⟨7650188065373191896815525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5100125376915461264543683 7650188065373191896815525)
                  ·
                    refine ⟨1434410262257473480652911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7650188065373191896815525 1434410262257473480652911)
                    ·
                      rfl

theorem cell23_8380512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 4, 1, 4].length) (baseStart_8380512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380512 prefixEnd_8380512 := by exact prefixLift 8380512
  have htrace : WordTrace (prefixWord ++ tailWord_8380512) baseStart_8380512 baseEnd_8380512 := by
    simpa [prefixWord, tailWord_8380512, baseEnd_8380512] using wordTrace_append hprefix tailTrace_8380512
  have hstable : (prefixWord ++ tailWord_8380512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380512).length < 2 ^ (prefixWord ++ tailWord_8380512).sum := by decide
  have hdescent : baseEnd_8380512 < baseStart_8380512 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380589 : List Nat := [1, 5, 2, 1, 2, 3, 1, 2, 1, 5]
def baseStart_8380589 : Nat := 118140960795 + 8380589 * 2 ^ 59
def prefixEnd_8380589 : Nat := 4983230072969 + 3 ^ 40 * 8380589 * 2
def baseEnd_8380589 : Nat := 1434423441594272213565293

theorem tailTrace_8380589 : CollatzResearch.WordTrace tailWord_8380589 prefixEnd_8380589 1434423441594272213565293 := by
  unfold tailWord_8380589
  simp only [CollatzResearch.WordTrace]
  refine ⟨305665192235564818495440821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203776794823709878996960547 305665192235564818495440821)
  ·
    refine ⟨28656111772084201733947577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 305665192235564818495440821 28656111772084201733947577)
    ·
      refine ⟨21492083829063151300460683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28656111772084201733947577 21492083829063151300460683)
      ·
        refine ⟨32238125743594726950691025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21492083829063151300460683 32238125743594726950691025)
        ·
          refine ⟨24178594307696045213018269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32238125743594726950691025 24178594307696045213018269)
          ·
            refine ⟨9066972865386016954881851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24178594307696045213018269 9066972865386016954881851)
            ·
              refine ⟨13600459298079025432322777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9066972865386016954881851 13600459298079025432322777)
              ·
                refine ⟨10200344473559269074242083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13600459298079025432322777 10200344473559269074242083)
                ·
                  refine ⟨15300516710338903611363125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10200344473559269074242083 15300516710338903611363125)
                  ·
                    refine ⟨1434423441594272213565293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15300516710338903611363125 1434423441594272213565293)
                    ·
                      rfl

theorem cell23_8380589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_8380589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380589 prefixEnd_8380589 := by exact prefixLift 8380589
  have htrace : WordTrace (prefixWord ++ tailWord_8380589) baseStart_8380589 baseEnd_8380589 := by
    simpa [prefixWord, tailWord_8380589, baseEnd_8380589] using wordTrace_append hprefix tailTrace_8380589
  have hstable : (prefixWord ++ tailWord_8380589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380589).length < 2 ^ (prefixWord ++ tailWord_8380589).sum := by decide
  have hdescent : baseEnd_8380589 < baseStart_8380589 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380612 : List Nat := [2, 3, 3, 1, 2, 1, 3, 1, 1, 1, 5]
def baseStart_8380612 : Nat := 118140960795 + 8380612 * 2 ^ 59
def prefixEnd_8380612 : Nat := 4983230072969 + 3 ^ 40 * 8380612 * 2
def baseEnd_8380612 : Nat := 4303282134837870050708273

theorem tailTrace_8380612 : CollatzResearch.WordTrace tailWord_8380612 prefixEnd_8380612 4303282134837870050708273 := by
  unfold tailWord_8380612
  simp only [CollatzResearch.WordTrace]
  refine ⟨152833015557240746711764045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203777354076320995615685393 152833015557240746711764045)
  ·
    refine ⟨57312380833965280016911517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152833015557240746711764045 57312380833965280016911517)
    ·
      refine ⟨21492142812736980006341819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57312380833965280016911517 21492142812736980006341819)
      ·
        refine ⟨32238214219105470009512729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21492142812736980006341819 32238214219105470009512729)
        ·
          refine ⟨24178660664329102507134547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32238214219105470009512729 24178660664329102507134547)
          ·
            refine ⟨36267990996493653760701821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24178660664329102507134547 36267990996493653760701821)
            ·
              refine ⟨13600496623685120160263183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36267990996493653760701821 13600496623685120160263183)
              ·
                refine ⟨20400744935527680240394775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13600496623685120160263183 20400744935527680240394775)
                ·
                  refine ⟨30601117403291520360592163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20400744935527680240394775 30601117403291520360592163)
                  ·
                    refine ⟨45901676104937280540888245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30601117403291520360592163 45901676104937280540888245)
                    ·
                      refine ⟨4303282134837870050708273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45901676104937280540888245 4303282134837870050708273)
                      ·
                        rfl

theorem cell23_8380612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_8380612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380612 prefixEnd_8380612 := by exact prefixLift 8380612
  have htrace : WordTrace (prefixWord ++ tailWord_8380612) baseStart_8380612 baseEnd_8380612 := by
    simpa [prefixWord, tailWord_8380612, baseEnd_8380612] using wordTrace_append hprefix tailTrace_8380612
  have hstable : (prefixWord ++ tailWord_8380612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380612).length < 2 ^ (prefixWord ++ tailWord_8380612).sum := by decide
  have hdescent : baseEnd_8380612 < baseStart_8380612 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380620 : List Nat := [2, 2, 1, 6, 1, 2, 2, 2, 1, 1, 3]
def baseStart_8380620 : Nat := 118140960795 + 8380620 * 2 ^ 59
def prefixEnd_8380620 : Nat := 4983230072969 + 3 ^ 40 * 8380620 * 2
def baseEnd_8380620 : Nat := 4303286242683106019408237

theorem tailTrace_8380620 : CollatzResearch.WordTrace tailWord_8380620 prefixEnd_8380620 4303286242683106019408237 := by
  unfold tailWord_8380620
  simp only [CollatzResearch.WordTrace]
  refine ⟨152833161449226255394909657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203777548598968340526546209 152833161449226255394909657)
  ·
    refine ⟨114624871086919691546182243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152833161449226255394909657 114624871086919691546182243)
    ·
      refine ⟨171937306630379537319273365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114624871086919691546182243 171937306630379537319273365)
      ·
        refine ⟨8059561248299040811840939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 171937306630379537319273365 8059561248299040811840939)
        ·
          refine ⟨12089341872448561217761409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8059561248299040811840939 12089341872448561217761409)
          ·
            refine ⟨9067006404336420913321057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12089341872448561217761409 9067006404336420913321057)
            ·
              refine ⟨6800254803252315684990793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9067006404336420913321057 6800254803252315684990793)
              ·
                refine ⟨5100191102439236763743095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6800254803252315684990793 5100191102439236763743095)
                ·
                  refine ⟨7650286653658855145614643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5100191102439236763743095 7650286653658855145614643)
                  ·
                    refine ⟨11475429980488282718421965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7650286653658855145614643 11475429980488282718421965)
                    ·
                      refine ⟨4303286242683106019408237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11475429980488282718421965 4303286242683106019408237)
                      ·
                        rfl

theorem cell23_8380620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_8380620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380620 prefixEnd_8380620 := by exact prefixLift 8380620
  have htrace : WordTrace (prefixWord ++ tailWord_8380620) baseStart_8380620 baseEnd_8380620 := by
    simpa [prefixWord, tailWord_8380620, baseEnd_8380620] using wordTrace_append hprefix tailTrace_8380620
  have hstable : (prefixWord ++ tailWord_8380620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380620).length < 2 ^ (prefixWord ++ tailWord_8380620).sum := by decide
  have hdescent : baseEnd_8380620 < baseStart_8380620 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380635 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 2, 7, 2]
def baseStart_8380635 : Nat := 118140960795 + 8380635 * 2 ^ 59
def prefixEnd_8380635 : Nat := 4983230072969 + 3 ^ 40 * 8380635 * 2
def baseEnd_8380635 : Nat := 4303293944892923460720667

theorem tailTrace_8380635 : CollatzResearch.WordTrace tailWord_8380635 prefixEnd_8380635 4303293944892923460720667 := by
  unfold tailWord_8380635
  simp only [CollatzResearch.WordTrace]
  refine ⟨305666869993398168351615359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203777913328932112234410239 305666869993398168351615359)
  ·
    refine ⟨458500304990097252527423039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305666869993398168351615359 458500304990097252527423039)
    ·
      refine ⟨687750457485145878791134559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458500304990097252527423039 687750457485145878791134559)
      ·
        refine ⟨1031625686227718818186701839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687750457485145878791134559 1031625686227718818186701839)
        ·
          refine ⟨1547438529341578227280052759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1031625686227718818186701839 1547438529341578227280052759)
          ·
            refine ⟨2321157794012367340920079139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1547438529341578227280052759 2321157794012367340920079139)
            ·
              refine ⟨3481736691018551011380118709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2321157794012367340920079139 3481736691018551011380118709)
              ·
                refine ⟨326412814782989157316886129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3481736691018551011380118709 326412814782989157316886129)
                ·
                  refine ⟨244809611087241867987664597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 326412814782989157316886129 244809611087241867987664597)
                  ·
                    refine ⟨5737725259857231280960889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 244809611087241867987664597 5737725259857231280960889)
                    ·
                      refine ⟨4303293944892923460720667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5737725259857231280960889 4303293944892923460720667)
                      ·
                        rfl

theorem cell23_8380635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 7, 2].length) (baseStart_8380635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380635 prefixEnd_8380635 := by exact prefixLift 8380635
  have htrace : WordTrace (prefixWord ++ tailWord_8380635) baseStart_8380635 baseEnd_8380635 := by
    simpa [prefixWord, tailWord_8380635, baseEnd_8380635] using wordTrace_append hprefix tailTrace_8380635
  have hstable : (prefixWord ++ tailWord_8380635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380635).length < 2 ^ (prefixWord ++ tailWord_8380635).sum := by decide
  have hdescent : baseEnd_8380635 < baseStart_8380635 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380652 : List Nat := [2, 2, 1, 1, 2, 3, 1, 3, 3, 3, 2]
def baseStart_8380652 : Nat := 118140960795 + 8380652 * 2 ^ 59
def prefixEnd_8380652 : Nat := 4983230072969 + 3 ^ 40 * 8380652 * 2
def baseEnd_8380652 : Nat := 4303302674064049894208089

theorem tailTrace_8380652 : CollatzResearch.WordTrace tailWord_8380652 prefixEnd_8380652 4303302674064049894208089 := by
  unfold tailWord_8380652
  simp only [CollatzResearch.WordTrace]
  refine ⟨152833745017168290127492105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203778326689557720169989473 152833745017168290127492105)
  ·
    refine ⟨114625308762876217595619079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152833745017168290127492105 114625308762876217595619079)
    ·
      refine ⟨171937963144314326393428619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114625308762876217595619079 171937963144314326393428619)
      ·
        refine ⟨257906944716471489590142929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171937963144314326393428619 257906944716471489590142929)
        ·
          refine ⟨193430208537353617192607197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257906944716471489590142929 193430208537353617192607197)
          ·
            refine ⟨72536328201507606447227699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193430208537353617192607197 72536328201507606447227699)
            ·
              refine ⟨108804492302261409670841549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72536328201507606447227699 108804492302261409670841549)
              ·
                refine ⟨40801684613348028626565581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108804492302261409670841549 40801684613348028626565581)
                ·
                  refine ⟨15300631730005510734962093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40801684613348028626565581 15300631730005510734962093)
                  ·
                    refine ⟨5737736898752066525610785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15300631730005510734962093 5737736898752066525610785)
                    ·
                      refine ⟨4303302674064049894208089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5737736898752066525610785 4303302674064049894208089)
                      ·
                        rfl

theorem cell23_8380652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 3, 2].length) (baseStart_8380652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380652 prefixEnd_8380652 := by exact prefixLift 8380652
  have htrace : WordTrace (prefixWord ++ tailWord_8380652) baseStart_8380652 baseEnd_8380652 := by
    simpa [prefixWord, tailWord_8380652, baseEnd_8380652] using wordTrace_append hprefix tailTrace_8380652
  have hstable : (prefixWord ++ tailWord_8380652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380652).length < 2 ^ (prefixWord ++ tailWord_8380652).sum := by decide
  have hdescent : baseEnd_8380652 < baseStart_8380652 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380682 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2]
def baseStart_8380682 : Nat := 118140960795 + 8380682 * 2 ^ 59
def prefixEnd_8380682 : Nat := 4983230072969 + 3 ^ 40 * 8380682 * 2
def baseEnd_8380682 : Nat := 4303318078483684776832951

theorem tailTrace_8380682 : CollatzResearch.WordTrace tailWord_8380682 prefixEnd_8380682 4303318078483684776832951 := by
  unfold tailWord_8380682
  simp only [CollatzResearch.WordTrace]
  refine ⟨76417146056056973844644075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203779056149485263585717533 76417146056056973844644075)
  ·
    refine ⟨114625719084085460766966113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76417146056056973844644075 114625719084085460766966113)
    ·
      refine ⟨85969289313064095575224585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114625719084085460766966113 85969289313064095575224585)
      ·
        refine ⟨64476966984798071681418439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85969289313064095575224585 64476966984798071681418439)
        ·
          refine ⟨96715450477197107522127659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64476966984798071681418439 96715450477197107522127659)
          ·
            refine ⟨145073175715795661283191489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96715450477197107522127659 145073175715795661283191489)
            ·
              refine ⟨108804881786846745962393617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145073175715795661283191489 108804881786846745962393617)
              ·
                refine ⟨81603661340135059471795213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108804881786846745962393617 81603661340135059471795213)
                ·
                  refine ⟨30601373002550647301923205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81603661340135059471795213 30601373002550647301923205)
                  ·
                    refine ⟨5737757437978246369110601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30601373002550647301923205 5737757437978246369110601)
                    ·
                      refine ⟨4303318078483684776832951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5737757437978246369110601 4303318078483684776832951)
                      ·
                        rfl

theorem cell23_8380682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_8380682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380682 prefixEnd_8380682 := by exact prefixLift 8380682
  have htrace : WordTrace (prefixWord ++ tailWord_8380682) baseStart_8380682 baseEnd_8380682 := by
    simpa [prefixWord, tailWord_8380682, baseEnd_8380682] using wordTrace_append hprefix tailTrace_8380682
  have hstable : (prefixWord ++ tailWord_8380682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380682).length < 2 ^ (prefixWord ++ tailWord_8380682).sum := by decide
  have hdescent : baseEnd_8380682 < baseStart_8380682 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380699 : List Nat := [1, 1, 1, 1, 1, 1, 6, 5, 2, 2, 2]
def baseStart_8380699 : Nat := 118140960795 + 8380699 * 2 ^ 59
def prefixEnd_8380699 : Nat := 4983230072969 + 3 ^ 40 * 8380699 * 2
def baseEnd_8380699 : Nat := 4303326807654811210320373

theorem tailTrace_8380699 : CollatzResearch.WordTrace tailWord_8380699 prefixEnd_8380699 4303326807654811210320373 := by
  unfold tailWord_8380699
  simp only [CollatzResearch.WordTrace]
  refine ⟨305669204265166307281945151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203779469510110871521296767 305669204265166307281945151)
  ·
    refine ⟨458503806397749460922917727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305669204265166307281945151 458503806397749460922917727)
    ·
      refine ⟨687755709596624191384376591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458503806397749460922917727 687755709596624191384376591)
      ·
        refine ⟨1031633564394936287076564887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687755709596624191384376591 1031633564394936287076564887)
        ·
          refine ⟨1547450346592404430614847331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1031633564394936287076564887 1547450346592404430614847331)
          ·
            refine ⟨2321175519888606645922270997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1547450346592404430614847331 2321175519888606645922270997)
            ·
              refine ⟨108805102494778436527606453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2321175519888606645922270997 108805102494778436527606453)
              ·
                refine ⟨10200478358885478424463105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108805102494778436527606453 10200478358885478424463105)
                ·
                  refine ⟨7650358769164108818347329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10200478358885478424463105 7650358769164108818347329)
                  ·
                    refine ⟨5737769076873081613760497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7650358769164108818347329 5737769076873081613760497)
                    ·
                      refine ⟨4303326807654811210320373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5737769076873081613760497 4303326807654811210320373)
                      ·
                        rfl

theorem cell23_8380699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 2, 2, 2].length) (baseStart_8380699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380699 prefixEnd_8380699 := by exact prefixLift 8380699
  have htrace : WordTrace (prefixWord ++ tailWord_8380699) baseStart_8380699 baseEnd_8380699 := by
    simpa [prefixWord, tailWord_8380699, baseEnd_8380699] using wordTrace_append hprefix tailTrace_8380699
  have hstable : (prefixWord ++ tailWord_8380699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380699).length < 2 ^ (prefixWord ++ tailWord_8380699).sum := by decide
  have hdescent : baseEnd_8380699 < baseStart_8380699 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380705 : List Nat := [1, 2, 3, 2, 1, 1, 4, 2, 7]
def baseStart_8380705 : Nat := 118140960795 + 8380705 * 2 ^ 59
def prefixEnd_8380705 : Nat := 4983230072969 + 3 ^ 40 * 8380705 * 2
def baseEnd_8380705 : Nat := 478147765393193131871705

theorem tailTrace_8380705 : CollatzResearch.WordTrace tailWord_8380705 prefixEnd_8380705 478147765393193131871705 := by
  unfold tailWord_8380705
  simp only [CollatzResearch.WordTrace]
  refine ⟨305669423103144570306663569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203779615402096380204442379 305669423103144570306663569)
  ·
    refine ⟨229252067327358427729997677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305669423103144570306663569 229252067327358427729997677)
    ·
      refine ⟨85969525247759410398749129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229252067327358427729997677 85969525247759410398749129)
      ·
        refine ⟨64477143935819557799061847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85969525247759410398749129 64477143935819557799061847)
        ·
          refine ⟨96715715903729336698592771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64477143935819557799061847 96715715903729336698592771)
          ·
            refine ⟨145073573855594005047889157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96715715903729336698592771 145073573855594005047889157)
            ·
              refine ⟨27201295097923875946479217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145073573855594005047889157 27201295097923875946479217)
              ·
                refine ⟨20400971323442906959859413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27201295097923875946479217 20400971323442906959859413)
                ·
                  refine ⟨478147765393193131871705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20400971323442906959859413 478147765393193131871705)
                  ·
                    rfl

theorem cell23_8380705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 7].length) (baseStart_8380705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380705 prefixEnd_8380705 := by exact prefixLift 8380705
  have htrace : WordTrace (prefixWord ++ tailWord_8380705) baseStart_8380705 baseEnd_8380705 := by
    simpa [prefixWord, tailWord_8380705, baseEnd_8380705] using wordTrace_append hprefix tailTrace_8380705
  have hstable : (prefixWord ++ tailWord_8380705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380705).length < 2 ^ (prefixWord ++ tailWord_8380705).sum := by decide
  have hdescent : baseEnd_8380705 < baseStart_8380705 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380755 : List Nat := [1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 4]
def baseStart_8380755 : Nat := 118140960795 + 8380755 * 2 ^ 59
def prefixEnd_8380755 : Nat := 4983230072969 + 3 ^ 40 * 8380755 * 2
def baseEnd_8380755 : Nat := 4303355562571462991220115

theorem tailTrace_8380755 : CollatzResearch.WordTrace tailWord_8380755 prefixEnd_8380755 4303355562571462991220115 := by
  unfold tailWord_8380755
  simp only [CollatzResearch.WordTrace]
  refine ⟨305671246752963428845983719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203780831168642285897322479 305671246752963428845983719)
  ·
    refine ⟨458506870129445143268975579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305671246752963428845983719 458506870129445143268975579)
    ·
      refine ⟨687760305194167714903463369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458506870129445143268975579 687760305194167714903463369)
      ·
        refine ⟨515820228895625786177597527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 687760305194167714903463369 515820228895625786177597527)
        ·
          refine ⟨773730343343438679266396291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515820228895625786177597527 773730343343438679266396291)
          ·
            refine ⟨1160595515015158018899594437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773730343343438679266396291 1160595515015158018899594437)
            ·
              refine ⟨217611659065342128543673957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1160595515015158018899594437 217611659065342128543673957)
              ·
                refine ⟨40802186074751649101938867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217611659065342128543673957 40802186074751649101938867)
                ·
                  refine ⟨61203279112127473652908301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40802186074751649101938867 61203279112127473652908301)
                  ·
                    refine ⟨22951229667047802619840613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61203279112127473652908301 22951229667047802619840613)
                    ·
                      refine ⟨4303355562571462991220115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22951229667047802619840613 4303355562571462991220115)
                      ·
                        rfl

theorem cell23_8380755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 4].length) (baseStart_8380755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380755 prefixEnd_8380755 := by exact prefixLift 8380755
  have htrace : WordTrace (prefixWord ++ tailWord_8380755) baseStart_8380755 baseEnd_8380755 := by
    simpa [prefixWord, tailWord_8380755, baseEnd_8380755] using wordTrace_append hprefix tailTrace_8380755
  have hstable : (prefixWord ++ tailWord_8380755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380755).length < 2 ^ (prefixWord ++ tailWord_8380755).sum := by decide
  have hdescent : baseEnd_8380755 < baseStart_8380755 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380785 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 2, 1, 6]
def baseStart_8380785 : Nat := 118140960795 + 8380785 * 2 ^ 59
def prefixEnd_8380785 : Nat := 4983230072969 + 3 ^ 40 * 8380785 * 2
def baseEnd_8380785 : Nat := 4303370966991097873844977

theorem tailTrace_8380785 : CollatzResearch.WordTrace tailWord_8380785 prefixEnd_8380785 4303370966991097873844977 := by
  unfold tailWord_8380785
  simp only [CollatzResearch.WordTrace]
  refine ⟨305672340942854743969575809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203781560628569829313050539 305672340942854743969575809)
  ·
    refine ⟨229254255707141057977181857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305672340942854743969575809 229254255707141057977181857)
    ·
      refine ⟨171940691780355793482886393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229254255707141057977181857 171940691780355793482886393)
      ·
        refine ⟨128955518835266845112164795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171940691780355793482886393 128955518835266845112164795)
        ·
          refine ⟨193433278252900267668247193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128955518835266845112164795 193433278252900267668247193)
          ·
            refine ⟨145074958689675200751185395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193433278252900267668247193 145074958689675200751185395)
            ·
              refine ⟨217612438034512801126778093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145074958689675200751185395 217612438034512801126778093)
              ·
                refine ⟨81604664262942300422541785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217612438034512801126778093 81604664262942300422541785)
                ·
                  refine ⟨61203498197206725316906339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81604664262942300422541785 61203498197206725316906339)
                  ·
                    refine ⟨91805247295810087975359509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61203498197206725316906339 91805247295810087975359509)
                    ·
                      refine ⟨4303370966991097873844977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91805247295810087975359509 4303370966991097873844977)
                      ·
                        rfl

theorem cell23_8380785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_8380785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380785 prefixEnd_8380785 := by exact prefixLift 8380785
  have htrace : WordTrace (prefixWord ++ tailWord_8380785) baseStart_8380785 baseEnd_8380785 := by
    simpa [prefixWord, tailWord_8380785, baseEnd_8380785] using wordTrace_append hprefix tailTrace_8380785
  have hstable : (prefixWord ++ tailWord_8380785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380785).length < 2 ^ (prefixWord ++ tailWord_8380785).sum := by decide
  have hdescent : baseEnd_8380785 < baseStart_8380785 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380789 : List Nat := [1, 3, 4, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_8380789 : Nat := 118140960795 + 8380789 * 2 ^ 59
def prefixEnd_8380789 : Nat := 4983230072969 + 3 ^ 40 * 8380789 * 2
def baseEnd_8380789 : Nat := 4303373020913715858194959

theorem tailTrace_8380789 : CollatzResearch.WordTrace tailWord_8380789 prefixEnd_8380789 4303373020913715858194959 := by
  unfold tailWord_8380789
  simp only [CollatzResearch.WordTrace]
  refine ⟨305672486834840252652721421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203781657889893501768480947 305672486834840252652721421)
  ·
    refine ⟨114627182563065094744770533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305672486834840252652721421 114627182563065094744770533)
    ·
      refine ⟨21492596730574705264644475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114627182563065094744770533 21492596730574705264644475)
      ·
        refine ⟨32238895095862057896966713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21492596730574705264644475 32238895095862057896966713)
        ·
          refine ⟨24179171321896543422725035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32238895095862057896966713 24179171321896543422725035)
          ·
            refine ⟨36268756982844815134087553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24179171321896543422725035 36268756982844815134087553)
            ·
              refine ⟨27201567737133611350565665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36268756982844815134087553 27201567737133611350565665)
              ·
                refine ⟨20401175802850208512924249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27201567737133611350565665 20401175802850208512924249)
                ·
                  refine ⟨15300881852137656384693187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20401175802850208512924249 15300881852137656384693187)
                  ·
                    refine ⟨22951322778206484577039781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15300881852137656384693187 22951322778206484577039781)
                    ·
                      refine ⟨4303373020913715858194959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22951322778206484577039781 4303373020913715858194959)
                      ·
                        rfl

theorem cell23_8380789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_8380789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380789 prefixEnd_8380789 := by exact prefixLift 8380789
  have htrace : WordTrace (prefixWord ++ tailWord_8380789) baseStart_8380789 baseEnd_8380789 := by
    simpa [prefixWord, tailWord_8380789, baseEnd_8380789] using wordTrace_append hprefix tailTrace_8380789
  have hstable : (prefixWord ++ tailWord_8380789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380789).length < 2 ^ (prefixWord ++ tailWord_8380789).sum := by decide
  have hdescent : baseEnd_8380789 < baseStart_8380789 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380790 : List Nat := [5, 1, 1, 4, 1, 2, 2, 2, 5]
def baseStart_8380790 : Nat := 118140960795 + 8380790 * 2 ^ 59
def prefixEnd_8380790 : Nat := 4983230072969 + 3 ^ 40 * 8380790 * 2
def baseEnd_8380790 : Nat := 478152614932707817142495

theorem tailTrace_8380790 : CollatzResearch.WordTrace tailWord_8380790 prefixEnd_8380790 478152614932707817142495 := by
  unfold tailWord_8380790
  simp only [CollatzResearch.WordTrace]
  refine ⟨19104532706739789363969239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203781682205224419882338549 19104532706739789363969239)
  ·
    refine ⟨28656799060109684045953859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19104532706739789363969239 28656799060109684045953859)
    ·
      refine ⟨42985198590164526068930789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28656799060109684045953859 42985198590164526068930789)
      ·
        refine ⟨8059724735655848637924523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42985198590164526068930789 8059724735655848637924523)
        ·
          refine ⟨12089587103483772956886785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8059724735655848637924523 12089587103483772956886785)
          ·
            refine ⟨9067190327612829717665089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12089587103483772956886785 9067190327612829717665089)
            ·
              refine ⟨6800392745709622288248817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9067190327612829717665089 6800392745709622288248817)
              ·
                refine ⟨5100294559282216716186613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6800392745709622288248817 5100294559282216716186613)
                ·
                  refine ⟨478152614932707817142495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5100294559282216716186613 478152614932707817142495)
                  ·
                    rfl

theorem cell23_8380790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_8380790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380790 prefixEnd_8380790 := by exact prefixLift 8380790
  have htrace : WordTrace (prefixWord ++ tailWord_8380790) baseStart_8380790 baseEnd_8380790 := by
    simpa [prefixWord, tailWord_8380790, baseEnd_8380790] using wordTrace_append hprefix tailTrace_8380790
  have hstable : (prefixWord ++ tailWord_8380790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380790).length < 2 ^ (prefixWord ++ tailWord_8380790).sum := by decide
  have hdescent : baseEnd_8380790 < baseStart_8380790 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380799 : List Nat := [1, 1, 2, 2, 1, 1, 2, 8, 1, 4]
def baseStart_8380799 : Nat := 118140960795 + 8380799 * 2 ^ 59
def prefixEnd_8380799 : Nat := 4983230072969 + 3 ^ 40 * 8380799 * 2
def baseEnd_8380799 : Nat := 1434459385240086939689971

theorem tailTrace_8380799 : CollatzResearch.WordTrace tailWord_8380799 prefixEnd_8380799 1434459385240086939689971 := by
  unfold tailWord_8380799
  simp only [CollatzResearch.WordTrace]
  refine ⟨305672851564804024360585451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203781901043202682907056967 305672851564804024360585451)
  ·
    refine ⟨458509277347206036540878177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305672851564804024360585451 458509277347206036540878177)
    ·
      refine ⟨343881958010404527405658633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458509277347206036540878177 343881958010404527405658633)
      ·
        refine ⟨257911468507803395554243975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343881958010404527405658633 257911468507803395554243975)
        ·
          refine ⟨386867202761705093331365963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257911468507803395554243975 386867202761705093331365963)
          ·
            refine ⟨580300804142557639997048945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386867202761705093331365963 580300804142557639997048945)
            ·
              refine ⟨435225603106918229997786709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 580300804142557639997048945 435225603106918229997786709)
              ·
                refine ⟨5100300036409198007786563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 435225603106918229997786709 5100300036409198007786563)
                ·
                  refine ⟨7650450054613797011679845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5100300036409198007786563 7650450054613797011679845)
                  ·
                    refine ⟨1434459385240086939689971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7650450054613797011679845 1434459385240086939689971)
                    ·
                      rfl

theorem cell23_8380799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 8, 1, 4].length) (baseStart_8380799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380799 prefixEnd_8380799 := by exact prefixLift 8380799
  have htrace : WordTrace (prefixWord ++ tailWord_8380799) baseStart_8380799 baseEnd_8380799 := by
    simpa [prefixWord, tailWord_8380799, baseEnd_8380799] using wordTrace_append hprefix tailTrace_8380799
  have hstable : (prefixWord ++ tailWord_8380799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380799).length < 2 ^ (prefixWord ++ tailWord_8380799).sum := by decide
  have hdescent : baseEnd_8380799 < baseStart_8380799 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380812 : List Nat := [2, 2, 1, 2, 1, 4, 2, 3, 6]
def baseStart_8380812 : Nat := 118140960795 + 8380812 * 2 ^ 59
def prefixEnd_8380812 : Nat := 4983230072969 + 3 ^ 40 * 8380812 * 2
def baseEnd_8380812 : Nat := 478153870107641029800817

theorem tailTrace_8380812 : CollatzResearch.WordTrace tailWord_8380812 prefixEnd_8380812 478153870107641029800817 := by
  unfold tailWord_8380812
  simp only [CollatzResearch.WordTrace]
  refine ⟨152836662856878463790404345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203782217142504618387205793 152836662856878463790404345)
  ·
    refine ⟨114627497142658847842803259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152836662856878463790404345 114627497142658847842803259)
    ·
      refine ⟨171941245713988271764204889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114627497142658847842803259 171941245713988271764204889)
      ·
        refine ⟨128955934285491203823153667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171941245713988271764204889 128955934285491203823153667)
        ·
          refine ⟨193433901428236805734730501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128955934285491203823153667 193433901428236805734730501)
          ·
            refine ⟨36268856517794401075261969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193433901428236805734730501 36268856517794401075261969)
            ·
              refine ⟨27201642388345800806446477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36268856517794401075261969 27201642388345800806446477)
              ·
                refine ⟨10200615895629675302417429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27201642388345800806446477 10200615895629675302417429)
                ·
                  refine ⟨478153870107641029800817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10200615895629675302417429 478153870107641029800817)
                  ·
                    rfl

theorem cell23_8380812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 6].length) (baseStart_8380812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380812 prefixEnd_8380812 := by exact prefixLift 8380812
  have htrace : WordTrace (prefixWord ++ tailWord_8380812) baseStart_8380812 baseEnd_8380812 := by
    simpa [prefixWord, tailWord_8380812, baseEnd_8380812] using wordTrace_append hprefix tailTrace_8380812
  have hstable : (prefixWord ++ tailWord_8380812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380812).length < 2 ^ (prefixWord ++ tailWord_8380812).sum := by decide
  have hdescent : baseEnd_8380812 < baseStart_8380812 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380826 : List Nat := [3, 1, 1, 4, 1, 4, 1, 1, 2, 2, 3]
def baseStart_8380826 : Nat := 118140960795 + 8380826 * 2 ^ 59
def prefixEnd_8380826 : Nat := 4983230072969 + 3 ^ 40 * 8380826 * 2
def baseEnd_8380826 : Nat := 4303392019697932213432289

theorem tailTrace_8380826 : CollatzResearch.WordTrace tailWord_8380826 prefixEnd_8380826 4303392019697932213432289 := by
  unfold tailWord_8380826
  simp only [CollatzResearch.WordTrace]
  refine ⟨76418459083926551992954583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203782557557137471981212221 76418459083926551992954583)
  ·
    refine ⟨114627688625889827989431875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76418459083926551992954583 114627688625889827989431875)
    ·
      refine ⟨171941532938834741984147813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114627688625889827989431875 171941532938834741984147813)
      ·
        refine ⟨32239037426031514122027715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171941532938834741984147813 32239037426031514122027715)
        ·
          refine ⟨48358556139047271183041573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32239037426031514122027715 48358556139047271183041573)
          ·
            refine ⟨9067229276071363346820295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48358556139047271183041573 9067229276071363346820295)
            ·
              refine ⟨13600843914107045020230443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9067229276071363346820295 13600843914107045020230443)
              ·
                refine ⟨20401265871160567530345665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13600843914107045020230443 20401265871160567530345665)
                ·
                  refine ⟨15300949403370425647759249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20401265871160567530345665 15300949403370425647759249)
                  ·
                    refine ⟨11475712052527819235819437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15300949403370425647759249 11475712052527819235819437)
                    ·
                      refine ⟨4303392019697932213432289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11475712052527819235819437 4303392019697932213432289)
                      ·
                        rfl

theorem cell23_8380826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_8380826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380826 prefixEnd_8380826 := by exact prefixLift 8380826
  have htrace : WordTrace (prefixWord ++ tailWord_8380826) baseStart_8380826 baseEnd_8380826 := by
    simpa [prefixWord, tailWord_8380826, baseEnd_8380826] using wordTrace_append hprefix tailTrace_8380826
  have hstable : (prefixWord ++ tailWord_8380826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380826).length < 2 ^ (prefixWord ++ tailWord_8380826).sum := by decide
  have hdescent : baseEnd_8380826 < baseStart_8380826 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380876 : List Nat := [2, 2, 1, 4, 3, 1, 2, 2, 1, 5]
def baseStart_8380876 : Nat := 118140960795 + 8380876 * 2 ^ 59
def prefixEnd_8380876 : Nat := 4983230072969 + 3 ^ 40 * 8380876 * 2
def baseEnd_8380876 : Nat := 1434472564576885672602353

theorem tailTrace_8380876 : CollatzResearch.WordTrace tailWord_8380876 prefixEnd_8380876 1434472564576885672602353 := by
  unfold tailWord_8380876
  simp only [CollatzResearch.WordTrace]
  refine ⟨152837829992762533255569241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203783773323683377674092321 152837829992762533255569241)
  ·
    refine ⟨114628372494571899941676931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152837829992762533255569241 114628372494571899941676931)
    ·
      refine ⟨171942558741857849912515397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114628372494571899941676931 171942558741857849912515397)
      ·
        refine ⟨32239229764098346858596637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171942558741857849912515397 32239229764098346858596637)
        ·
          refine ⟨12089711161536880071973739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32239229764098346858596637 12089711161536880071973739)
          ·
            refine ⟨18134566742305320107960609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12089711161536880071973739 18134566742305320107960609)
            ·
              refine ⟨13600925056728990080970457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18134566742305320107960609 13600925056728990080970457)
              ·
                refine ⟨10200693792546742560727843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13600925056728990080970457 10200693792546742560727843)
                ·
                  refine ⟨15301040688820113841091765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10200693792546742560727843 15301040688820113841091765)
                  ·
                    refine ⟨1434472564576885672602353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15301040688820113841091765 1434472564576885672602353)
                    ·
                      rfl

theorem cell23_8380876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 1, 5].length) (baseStart_8380876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380876 prefixEnd_8380876 := by exact prefixLift 8380876
  have htrace : WordTrace (prefixWord ++ tailWord_8380876) baseStart_8380876 baseEnd_8380876 := by
    simpa [prefixWord, tailWord_8380876, baseEnd_8380876] using wordTrace_append hprefix tailTrace_8380876
  have hstable : (prefixWord ++ tailWord_8380876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380876).length < 2 ^ (prefixWord ++ tailWord_8380876).sum := by decide
  have hdescent : baseEnd_8380876 < baseStart_8380876 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380909 : List Nat := [1, 5, 1, 3, 1, 1, 1, 2, 1, 1, 6]
def baseStart_8380909 : Nat := 118140960795 + 8380909 * 2 ^ 59
def prefixEnd_8380909 : Nat := 4983230072969 + 3 ^ 40 * 8380909 * 2
def baseEnd_8380909 : Nat := 4303434638592255388694407

theorem tailTrace_8380909 : CollatzResearch.WordTrace tailWord_8380909 prefixEnd_8380909 4303434638592255388694407 := by
  unfold tailWord_8380909
  simp only [CollatzResearch.WordTrace]
  refine ⟨305676863594405513147089781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203784575729603675431393187 305676863594405513147089781)
  ·
    refine ⟨28657205961975516857539667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 305676863594405513147089781 28657205961975516857539667)
    ·
      refine ⟨42985808942963275286309501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28657205961975516857539667 42985808942963275286309501)
      ·
        refine ⟨16119678353611228232366063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42985808942963275286309501 16119678353611228232366063)
        ·
          refine ⟨24179517530416842348549095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16119678353611228232366063 24179517530416842348549095)
          ·
            refine ⟨36269276295625263522823643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24179517530416842348549095 36269276295625263522823643)
            ·
              refine ⟨54403914443437895284235465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36269276295625263522823643 54403914443437895284235465)
              ·
                refine ⟨40802935832578421463176599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54403914443437895284235465 40802935832578421463176599)
                ·
                  refine ⟨61204403748867632194764899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40802935832578421463176599 61204403748867632194764899)
                  ·
                    refine ⟨91806605623301448292147349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61204403748867632194764899 91806605623301448292147349)
                    ·
                      refine ⟨4303434638592255388694407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91806605623301448292147349 4303434638592255388694407)
                      ·
                        rfl

theorem cell23_8380909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_8380909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380909 prefixEnd_8380909 := by exact prefixLift 8380909
  have htrace : WordTrace (prefixWord ++ tailWord_8380909) baseStart_8380909 baseEnd_8380909 := by
    simpa [prefixWord, tailWord_8380909, baseEnd_8380909] using wordTrace_append hprefix tailTrace_8380909
  have hstable : (prefixWord ++ tailWord_8380909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380909).length < 2 ^ (prefixWord ++ tailWord_8380909).sum := by decide
  have hdescent : baseEnd_8380909 < baseStart_8380909 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380930 : List Nat := [3, 4, 1, 2, 2, 2, 1, 2, 1, 1, 4]
def baseStart_8380930 : Nat := 118140960795 + 8380930 * 2 ^ 59
def prefixEnd_8380930 : Nat := 4983230072969 + 3 ^ 40 * 8380930 * 2
def baseEnd_8380930 : Nat := 4303445421685999806531811

theorem tailTrace_8380930 : CollatzResearch.WordTrace tailWord_8380930 prefixEnd_8380930 4303445421685999806531811 := by
  unfold tailWord_8380930
  simp only [CollatzResearch.WordTrace]
  refine ⟨76419407381832358433401061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203785086351552955822402829 76419407381832358433401061)
  ·
    refine ⟨14328638884093567206262699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76419407381832358433401061 14328638884093567206262699)
    ·
      refine ⟨21492958326140350809394049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14328638884093567206262699 21492958326140350809394049)
      ·
        refine ⟨16119718744605263107045537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21492958326140350809394049 16119718744605263107045537)
        ·
          refine ⟨12089789058453947330284153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16119718744605263107045537 12089789058453947330284153)
          ·
            refine ⟨9067341793840460497713115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12089789058453947330284153 9067341793840460497713115)
            ·
              refine ⟨13601012690760690746569673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9067341793840460497713115 13601012690760690746569673)
              ·
                refine ⟨10200759518070518059927255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13601012690760690746569673 10200759518070518059927255)
                ·
                  refine ⟨15301139277105777089890883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10200759518070518059927255 15301139277105777089890883)
                  ·
                    refine ⟨22951708915658665634836325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15301139277105777089890883 22951708915658665634836325)
                    ·
                      refine ⟨4303445421685999806531811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22951708915658665634836325 4303445421685999806531811)
                      ·
                        rfl

theorem cell23_8380930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_8380930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380930 prefixEnd_8380930 := by exact prefixLift 8380930
  have htrace : WordTrace (prefixWord ++ tailWord_8380930) baseStart_8380930 baseEnd_8380930 := by
    simpa [prefixWord, tailWord_8380930, baseEnd_8380930] using wordTrace_append hprefix tailTrace_8380930
  have hstable : (prefixWord ++ tailWord_8380930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380930).length < 2 ^ (prefixWord ++ tailWord_8380930).sum := by decide
  have hdescent : baseEnd_8380930 < baseStart_8380930 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380963 : List Nat := [1, 1, 1, 4, 4, 2, 2, 2, 2, 1, 3]
def baseStart_8380963 : Nat := 118140960795 + 8380963 * 2 ^ 59
def prefixEnd_8380963 : Nat := 4983230072969 + 3 ^ 40 * 8380963 * 2
def baseEnd_8380963 : Nat := 4303462366547598177419159

theorem tailTrace_8380963 : CollatzResearch.WordTrace tailWord_8380963 prefixEnd_8380963 4303462366547598177419159 := by
  unfold tailWord_8380963
  simp only [CollatzResearch.WordTrace]
  refine ⟨305678833136209880369555543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203785888757473253579703695 305678833136209880369555543)
  ·
    refine ⟨458518249704314820554333315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305678833136209880369555543 458518249704314820554333315)
    ·
      refine ⟨687777374556472230831499973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458518249704314820554333315 687777374556472230831499973)
      ·
        refine ⟨128958257729338543280906245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 687777374556472230831499973 128958257729338543280906245)
        ·
          refine ⟨24179673324250976865169921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128958257729338543280906245 24179673324250976865169921)
          ·
            refine ⟨18134754993188232648877441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24179673324250976865169921 18134754993188232648877441)
            ·
              refine ⟨13601066244891174486658081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18134754993188232648877441 13601066244891174486658081)
              ·
                refine ⟨10200799683668380864993561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13601066244891174486658081 10200799683668380864993561)
                ·
                  refine ⟨7650599762751285648745171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10200799683668380864993561 7650599762751285648745171)
                  ·
                    refine ⟨11475899644126928473117757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7650599762751285648745171 11475899644126928473117757)
                    ·
                      refine ⟨4303462366547598177419159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11475899644126928473117757 4303462366547598177419159)
                      ·
                        rfl

theorem cell23_8380963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_8380963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380963 prefixEnd_8380963 := by exact prefixLift 8380963
  have htrace : WordTrace (prefixWord ++ tailWord_8380963) baseStart_8380963 baseEnd_8380963 := by
    simpa [prefixWord, tailWord_8380963, baseEnd_8380963] using wordTrace_append hprefix tailTrace_8380963
  have hstable : (prefixWord ++ tailWord_8380963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380963).length < 2 ^ (prefixWord ++ tailWord_8380963).sum := by decide
  have hdescent : baseEnd_8380963 < baseStart_8380963 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380972 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 5]
def baseStart_8380972 : Nat := 118140960795 + 8380972 * 2 ^ 59
def prefixEnd_8380972 : Nat := 4983230072969 + 3 ^ 40 * 8380972 * 2
def baseEnd_8380972 : Nat := 4303466987873488642206617

theorem tailTrace_8380972 : CollatzResearch.WordTrace tailWord_8380972 prefixEnd_8380972 4303466987873488642206617 := by
  unfold tailWord_8380972
  simp only [CollatzResearch.WordTrace]
  refine ⟨152839580696588637453316585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203786107595451516604422113 152839580696588637453316585)
  ·
    refine ⟨114629685522441478089987439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152839580696588637453316585 114629685522441478089987439)
    ·
      refine ⟨171944528283662217134981159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114629685522441478089987439 171944528283662217134981159)
      ·
        refine ⟨257916792425493325702471739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171944528283662217134981159 257916792425493325702471739)
        ·
          refine ⟨386875188638239988553707609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257916792425493325702471739 386875188638239988553707609)
          ·
            refine ⟨290156391478679991415280707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386875188638239988553707609 290156391478679991415280707)
            ·
              refine ⟨435234587218019987122921061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290156391478679991415280707 435234587218019987122921061)
              ·
                refine ⟨81606485103378747585547699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 435234587218019987122921061 81606485103378747585547699)
                ·
                  refine ⟨122409727655068121378321549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81606485103378747585547699 122409727655068121378321549)
                  ·
                    refine ⟨45903647870650545516870581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 122409727655068121378321549 45903647870650545516870581)
                    ·
                      refine ⟨4303466987873488642206617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45903647870650545516870581 4303466987873488642206617)
                      ·
                        rfl

theorem cell23_8380972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_8380972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380972 prefixEnd_8380972 := by exact prefixLift 8380972
  have htrace : WordTrace (prefixWord ++ tailWord_8380972) baseStart_8380972 baseEnd_8380972 := by
    simpa [prefixWord, tailWord_8380972, baseEnd_8380972] using wordTrace_append hprefix tailTrace_8380972
  have hstable : (prefixWord ++ tailWord_8380972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380972).length < 2 ^ (prefixWord ++ tailWord_8380972).sum := by decide
  have hdescent : baseEnd_8380972 < baseStart_8380972 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380980 : List Nat := [2, 5, 1, 3, 1, 1, 2, 1, 1, 3, 3]
def baseStart_8380980 : Nat := 118140960795 + 8380980 * 2 ^ 59
def prefixEnd_8380980 : Nat := 4983230072969 + 3 ^ 40 * 8380980 * 2
def baseEnd_8380980 : Nat := 4303471095718724610906581

theorem tailTrace_8380980 : CollatzResearch.WordTrace tailWord_8380980 prefixEnd_8380980 4303471095718724610906581 := by
  unfold tailWord_8380980
  simp only [CollatzResearch.WordTrace]
  refine ⟨152839726588574146136462197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203786302118098861515282929 152839726588574146136462197)
  ·
    refine ⟨14328724367678826200293331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152839726588574146136462197 14328724367678826200293331)
    ·
      refine ⟨21493086551518239300439997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14328724367678826200293331 21493086551518239300439997)
      ·
        refine ⟨8059907456819339737664999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21493086551518239300439997 8059907456819339737664999)
        ·
          refine ⟨12089861185229009606497499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8059907456819339737664999 12089861185229009606497499)
          ·
            refine ⟨18134791777843514409746249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12089861185229009606497499 18134791777843514409746249)
            ·
              refine ⟨13601093833382635807309687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18134791777843514409746249 13601093833382635807309687)
              ·
                refine ⟨20401640750073953710964531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13601093833382635807309687 20401640750073953710964531)
                ·
                  refine ⟨30602461125110930566446797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20401640750073953710964531 30602461125110930566446797)
                  ·
                    refine ⟨11475922921916598962417549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30602461125110930566446797 11475922921916598962417549)
                    ·
                      refine ⟨4303471095718724610906581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11475922921916598962417549 4303471095718724610906581)
                      ·
                        rfl

theorem cell23_8380980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_8380980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380980 prefixEnd_8380980 := by exact prefixLift 8380980
  have htrace : WordTrace (prefixWord ++ tailWord_8380980) baseStart_8380980 baseEnd_8380980 := by
    simpa [prefixWord, tailWord_8380980, baseEnd_8380980] using wordTrace_append hprefix tailTrace_8380980
  have hstable : (prefixWord ++ tailWord_8380980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380980).length < 2 ^ (prefixWord ++ tailWord_8380980).sum := by decide
  have hdescent : baseEnd_8380980 < baseStart_8380980 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380986 : List Nat := [3, 1, 1, 1, 3, 3, 1, 3, 1, 4, 2]
def baseStart_8380986 : Nat := 118140960795 + 8380986 * 2 ^ 59
def prefixEnd_8380986 : Nat := 4983230072969 + 3 ^ 40 * 8380986 * 2
def baseEnd_8380986 : Nat := 4303474176602651587431553

theorem tailTrace_8380986 : CollatzResearch.WordTrace tailWord_8380986 prefixEnd_8380986 4303474176602651587431553 := by
  unfold tailWord_8380986
  simp only [CollatzResearch.WordTrace]
  refine ⟨76419918003781638824410703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203786448010084370198428541 76419918003781638824410703)
  ·
    refine ⟨114629877005672458236616055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76419918003781638824410703 114629877005672458236616055)
    ·
      refine ⟨171944815508508687354924083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114629877005672458236616055 171944815508508687354924083)
      ·
        refine ⟨257917223262763031032386125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171944815508508687354924083 257917223262763031032386125)
        ·
          refine ⟨96718958723536136637144797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257917223262763031032386125 96718958723536136637144797)
          ·
            refine ⟨36269609521326051238929299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96718958723536136637144797 36269609521326051238929299)
            ·
              refine ⟨54404414281989076858393949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36269609521326051238929299 54404414281989076858393949)
              ·
                refine ⟨20401655355745903821897731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54404414281989076858393949 20401655355745903821897731)
                ·
                  refine ⟨30602483033618855732846597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20401655355745903821897731 30602483033618855732846597)
                  ·
                    refine ⟨5737965568803535449908737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30602483033618855732846597 5737965568803535449908737)
                    ·
                      refine ⟨4303474176602651587431553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5737965568803535449908737 4303474176602651587431553)
                      ·
                        rfl

theorem cell23_8380986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 1, 4, 2].length) (baseStart_8380986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380986 prefixEnd_8380986 := by exact prefixLift 8380986
  have htrace : WordTrace (prefixWord ++ tailWord_8380986) baseStart_8380986 baseEnd_8380986 := by
    simpa [prefixWord, tailWord_8380986, baseEnd_8380986] using wordTrace_append hprefix tailTrace_8380986
  have hstable : (prefixWord ++ tailWord_8380986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380986).length < 2 ^ (prefixWord ++ tailWord_8380986).sum := by decide
  have hdescent : baseEnd_8380986 < baseStart_8380986 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8380992 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 9]
def baseStart_8380992 : Nat := 118140960795 + 8380992 * 2 ^ 59
def prefixEnd_8380992 : Nat := 4983230072969 + 3 ^ 40 * 8380992 * 2
def baseEnd_8380992 : Nat := 478164139720730951550725

theorem tailTrace_8380992 : CollatzResearch.WordTrace tailWord_8380992 prefixEnd_8380992 478164139720730951550725 := by
  unfold tailWord_8380992
  simp only [CollatzResearch.WordTrace]
  refine ⟨152839945426552409161180615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203786593902069878881574153 152839945426552409161180615)
  ·
    refine ⟨229259918139828613741770923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152839945426552409161180615 229259918139828613741770923)
    ·
      refine ⟨343889877209742920612656385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229259918139828613741770923 343889877209742920612656385)
      ·
        refine ⟨257917407907307190459492289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343889877209742920612656385 257917407907307190459492289)
        ·
          refine ⟨193438055930480392844619217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257917407907307190459492289 193438055930480392844619217)
          ·
            refine ⟨145078541947860294633464413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193438055930480392844619217 145078541947860294633464413)
            ·
              refine ⟨54404453230447610487549155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145078541947860294633464413 54404453230447610487549155)
              ·
                refine ⟨81606679845671415731323733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54404453230447610487549155 81606679845671415731323733)
                ·
                  refine ⟨478164139720730951550725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 81606679845671415731323733 478164139720730951550725)
                  ·
                    rfl

theorem cell23_8380992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 9].length) (baseStart_8380992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8380992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8380992 prefixEnd_8380992 := by exact prefixLift 8380992
  have htrace : WordTrace (prefixWord ++ tailWord_8380992) baseStart_8380992 baseEnd_8380992 := by
    simpa [prefixWord, tailWord_8380992, baseEnd_8380992] using wordTrace_append hprefix tailTrace_8380992
  have hstable : (prefixWord ++ tailWord_8380992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8380992).length < 2 ^ (prefixWord ++ tailWord_8380992).sum := by decide
  have hdescent : baseEnd_8380992 < baseStart_8380992 := by decide
  rcases family_descends (prefixWord ++ tailWord_8380992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381020 : List Nat := [2, 2, 4, 1, 3, 1, 1, 1, 4, 2, 2]
def baseStart_8381020 : Nat := 118140960795 + 8381020 * 2 ^ 59
def prefixEnd_8381020 : Nat := 4983230072969 + 3 ^ 40 * 8381020 * 2
def baseEnd_8381020 : Nat := 4303491634944904454406397

theorem tailTrace_8381020 : CollatzResearch.WordTrace tailWord_8381020 prefixEnd_8381020 4303491634944904454406397 := by
  unfold tailWord_8381020
  simp only [CollatzResearch.WordTrace]
  refine ⟨152840456048501689552190257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203787274731335586069587009 152840456048501689552190257)
  ·
    refine ⟨114630342036376267164142693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152840456048501689552190257 114630342036376267164142693)
    ·
      refine ⟨21493189131820550093276755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114630342036376267164142693 21493189131820550093276755)
      ·
        refine ⟨32239783697730825139915133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21493189131820550093276755 32239783697730825139915133)
        ·
          refine ⟨12089918886649059427468175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32239783697730825139915133 12089918886649059427468175)
          ·
            refine ⟨18134878329973589141202263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12089918886649059427468175 18134878329973589141202263)
            ·
              refine ⟨27202317494960383711803395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18134878329973589141202263 27202317494960383711803395)
              ·
                refine ⟨40803476242440575567705093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27202317494960383711803395 40803476242440575567705093)
                ·
                  refine ⟨7650651795457607918944705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40803476242440575567705093 7650651795457607918944705)
                  ·
                    refine ⟨5737988846593205939208529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7650651795457607918944705 5737988846593205939208529)
                    ·
                      refine ⟨4303491634944904454406397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5737988846593205939208529 4303491634944904454406397)
                      ·
                        rfl

theorem cell23_8381020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_8381020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381020 prefixEnd_8381020 := by exact prefixLift 8381020
  have htrace : WordTrace (prefixWord ++ tailWord_8381020) baseStart_8381020 baseEnd_8381020 := by
    simpa [prefixWord, tailWord_8381020, baseEnd_8381020] using wordTrace_append hprefix tailTrace_8381020
  have hstable : (prefixWord ++ tailWord_8381020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381020).length < 2 ^ (prefixWord ++ tailWord_8381020).sum := by decide
  have hdescent : baseEnd_8381020 < baseStart_8381020 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381037 : List Nat := [1, 5, 1, 1, 3, 2, 3, 1, 2, 2, 2]
def baseStart_8381037 : Nat := 118140960795 + 8381037 * 2 ^ 59
def prefixEnd_8381037 : Nat := 4983230072969 + 3 ^ 40 * 8381037 * 2
def baseEnd_8381037 : Nat := 4303500364116030887893819

theorem tailTrace_8381037 : CollatzResearch.WordTrace tailWord_8381037 prefixEnd_8381037 4303500364116030887893819 := by
  unfold tailWord_8381037
  simp only [CollatzResearch.WordTrace]
  refine ⟨305681532137941791007749365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203787688091961194005166243 305681532137941791007749365)
  ·
    refine ⟨28657643637932042906976503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 305681532137941791007749365 28657643637932042906976503)
    ·
      refine ⟨42986465456898064360464755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28657643637932042906976503 42986465456898064360464755)
      ·
        refine ⟨64479698185347096540697133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42986465456898064360464755 64479698185347096540697133)
        ·
          refine ⟨24179886819505161202761425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64479698185347096540697133 24179886819505161202761425)
          ·
            refine ⟨18134915114628870902071069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24179886819505161202761425 18134915114628870902071069)
            ·
              refine ⟨6800593167985826588276651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18134915114628870902071069 6800593167985826588276651)
              ·
                refine ⟨10200889751978739882414977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6800593167985826588276651 10200889751978739882414977)
                ·
                  refine ⟨7650667313984054911811233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10200889751978739882414977 7650667313984054911811233)
                  ·
                    refine ⟨5738000485488041183858425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7650667313984054911811233 5738000485488041183858425)
                    ·
                      refine ⟨4303500364116030887893819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5738000485488041183858425 4303500364116030887893819)
                      ·
                        rfl

theorem cell23_8381037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_8381037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381037 prefixEnd_8381037 := by exact prefixLift 8381037
  have htrace : WordTrace (prefixWord ++ tailWord_8381037) baseStart_8381037 baseEnd_8381037 := by
    simpa [prefixWord, tailWord_8381037, baseEnd_8381037] using wordTrace_append hprefix tailTrace_8381037
  have hstable : (prefixWord ++ tailWord_8381037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381037).length < 2 ^ (prefixWord ++ tailWord_8381037).sum := by decide
  have hdescent : baseEnd_8381037 < baseStart_8381037 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381059 : List Nat := [1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 4]
def baseStart_8381059 : Nat := 118140960795 + 8381059 * 2 ^ 59
def prefixEnd_8381059 : Nat := 4983230072969 + 3 ^ 40 * 8381059 * 2
def baseEnd_8381059 : Nat := 4303511660690429801818717

theorem tailTrace_8381059 : CollatzResearch.WordTrace tailWord_8381059 prefixEnd_8381059 4303511660690429801818717 := by
  unfold tailWord_8381059
  simp only [CollatzResearch.WordTrace]
  refine ⟨305682334543862088765050231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203788223029241392510033487 305682334543862088765050231)
  ·
    refine ⟨458523501815793133147575347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305682334543862088765050231 458523501815793133147575347)
    ·
      refine ⟨687785252723689699721363021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458523501815793133147575347 687785252723689699721363021)
      ·
        refine ⟨257919469771383637395511133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 687785252723689699721363021 257919469771383637395511133)
        ·
          refine ⟨96719801164268864023316675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257919469771383637395511133 96719801164268864023316675)
          ·
            refine ⟨145079701746403296034975013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96719801164268864023316675 145079701746403296034975013)
            ·
              refine ⟨27202444077450618006557815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145079701746403296034975013 27202444077450618006557815)
              ·
                refine ⟨40803666116175927009836723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27202444077450618006557815 40803666116175927009836723)
                ·
                  refine ⟨61205499174263890514755085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40803666116175927009836723 61205499174263890514755085)
                  ·
                    refine ⟨22952062190348958943033157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61205499174263890514755085 22952062190348958943033157)
                    ·
                      refine ⟨4303511660690429801818717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22952062190348958943033157 4303511660690429801818717)
                      ·
                        rfl

theorem cell23_8381059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_8381059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381059 prefixEnd_8381059 := by exact prefixLift 8381059
  have htrace : WordTrace (prefixWord ++ tailWord_8381059) baseStart_8381059 baseEnd_8381059 := by
    simpa [prefixWord, tailWord_8381059, baseEnd_8381059] using wordTrace_append hprefix tailTrace_8381059
  have hstable : (prefixWord ++ tailWord_8381059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381059).length < 2 ^ (prefixWord ++ tailWord_8381059).sum := by decide
  have hdescent : baseEnd_8381059 < baseStart_8381059 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381160 : List Nat := [2, 1, 4, 1, 4, 1, 1, 2, 3, 1, 3]
def baseStart_8381160 : Nat := 118140960795 + 8381160 * 2 ^ 59
def prefixEnd_8381160 : Nat := 4983230072969 + 3 ^ 40 * 8381160 * 2
def baseEnd_8381160 : Nat := 4303563522236533906655753

theorem tailTrace_8381160 : CollatzResearch.WordTrace tailWord_8381160 prefixEnd_8381160 4303563522236533906655753 := by
  unfold tailWord_8381160
  simp only [CollatzResearch.WordTrace]
  refine ⟨152843009158248091507238467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203790678877664122009651289 152843009158248091507238467)
  ·
    refine ⟨229264513737372137260857701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152843009158248091507238467 229264513737372137260857701)
    ·
      refine ⟨42987096325757275736410819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 229264513737372137260857701 42987096325757275736410819)
      ·
        refine ⟨64480644488635913604616229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42987096325757275736410819 64480644488635913604616229)
        ·
          refine ⟨12090120841619233800865543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64480644488635913604616229 12090120841619233800865543)
          ·
            refine ⟨18135181262428850701298315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12090120841619233800865543 18135181262428850701298315)
            ·
              refine ⟨27202771893643276051947473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18135181262428850701298315 27202771893643276051947473)
              ·
                refine ⟨20402078920232457038960605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27202771893643276051947473 20402078920232457038960605)
                ·
                  refine ⟨7650779595087171389610227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20402078920232457038960605 7650779595087171389610227)
                  ·
                    refine ⟨11476169392630757084415341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7650779595087171389610227 11476169392630757084415341)
                    ·
                      refine ⟨4303563522236533906655753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11476169392630757084415341 4303563522236533906655753)
                      ·
                        rfl

theorem cell23_8381160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_8381160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381160 prefixEnd_8381160 := by exact prefixLift 8381160
  have htrace : WordTrace (prefixWord ++ tailWord_8381160) baseStart_8381160 baseEnd_8381160 := by
    simpa [prefixWord, tailWord_8381160, baseEnd_8381160] using wordTrace_append hprefix tailTrace_8381160
  have hstable : (prefixWord ++ tailWord_8381160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381160).length < 2 ^ (prefixWord ++ tailWord_8381160).sum := by decide
  have hdescent : baseEnd_8381160 < baseStart_8381160 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381170 : List Nat := [3, 2, 1, 3, 1, 2, 3, 1, 2, 3, 2]
def baseStart_8381170 : Nat := 118140960795 + 8381170 * 2 ^ 59
def prefixEnd_8381170 : Nat := 4983230072969 + 3 ^ 40 * 8381170 * 2
def baseEnd_8381170 : Nat := 4303568657043078867530707

theorem tailTrace_8381170 : CollatzResearch.WordTrace tailWord_8381170 prefixEnd_8381170 4303568657043078867530707 := by
  unfold tailWord_8381170
  simp only [CollatzResearch.WordTrace]
  refine ⟨76421595761614988680585241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203790922030973303148227309 76421595761614988680585241)
  ·
    refine ⟨57316196821211241510438931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76421595761614988680585241 57316196821211241510438931)
    ·
      refine ⟨85974295231816862265658397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57316196821211241510438931 85974295231816862265658397)
      ·
        refine ⟨32240360711931323349621899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85974295231816862265658397 32240360711931323349621899)
        ·
          refine ⟨48360541067896985024432849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32240360711931323349621899 48360541067896985024432849)
          ·
            refine ⟨36270405800922738768324637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48360541067896985024432849 36270405800922738768324637)
            ·
              refine ⟨13601402175346027038121739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36270405800922738768324637 13601402175346027038121739)
              ·
                refine ⟨20402103263019040557182609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13601402175346027038121739 20402103263019040557182609)
                ·
                  refine ⟨15301577447264280417886957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20402103263019040557182609 15301577447264280417886957)
                  ·
                    refine ⟨5738091542724105156707609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15301577447264280417886957 5738091542724105156707609)
                    ·
                      refine ⟨4303568657043078867530707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5738091542724105156707609 4303568657043078867530707)
                      ·
                        rfl

theorem cell23_8381170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_8381170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381170 prefixEnd_8381170 := by exact prefixLift 8381170
  have htrace : WordTrace (prefixWord ++ tailWord_8381170) baseStart_8381170 baseEnd_8381170 := by
    simpa [prefixWord, tailWord_8381170, baseEnd_8381170] using wordTrace_append hprefix tailTrace_8381170
  have hstable : (prefixWord ++ tailWord_8381170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381170).length < 2 ^ (prefixWord ++ tailWord_8381170).sum := by decide
  have hdescent : baseEnd_8381170 < baseStart_8381170 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381176 : List Nat := [2, 1, 2, 1, 1, 2, 4, 2, 4, 4]
def baseStart_8381176 : Nat := 118140960795 + 8381176 * 2 ^ 59
def prefixEnd_8381176 : Nat := 4983230072969 + 3 ^ 40 * 8381176 * 2
def baseEnd_8381176 : Nat := 1434523912642335281351893

theorem tailTrace_8381176 : CollatzResearch.WordTrace tailWord_8381176 prefixEnd_8381176 1434523912642335281351893 := by
  unfold tailWord_8381176
  simp only [CollatzResearch.WordTrace]
  refine ⟨152843300942219108873529691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203791067922958811831372921 152843300942219108873529691)
  ·
    refine ⟨229264951413328663310294537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152843300942219108873529691 229264951413328663310294537)
    ·
      refine ⟨171948713559996497482720903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229264951413328663310294537 171948713559996497482720903)
      ·
        refine ⟨257923070339994746224081355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171948713559996497482720903 257923070339994746224081355)
        ·
          refine ⟨386884605509992119336122033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257923070339994746224081355 386884605509992119336122033)
          ·
            refine ⟨290163454132494089502091525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386884605509992119336122033 290163454132494089502091525)
            ·
              refine ⟨54405647649842641781642161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 290163454132494089502091525 54405647649842641781642161)
              ·
                refine ⟨40804235737381981336231621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54405647649842641781642161 40804235737381981336231621)
                ·
                  refine ⟨7650794200759121500543429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40804235737381981336231621 7650794200759121500543429)
                  ·
                    refine ⟨1434523912642335281351893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7650794200759121500543429 1434523912642335281351893)
                    ·
                      rfl

theorem cell23_8381176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 4, 4].length) (baseStart_8381176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381176 prefixEnd_8381176 := by exact prefixLift 8381176
  have htrace : WordTrace (prefixWord ++ tailWord_8381176) baseStart_8381176 baseEnd_8381176 := by
    simpa [prefixWord, tailWord_8381176, baseEnd_8381176] using wordTrace_append hprefix tailTrace_8381176
  have hstable : (prefixWord ++ tailWord_8381176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381176).length < 2 ^ (prefixWord ++ tailWord_8381176).sum := by decide
  have hdescent : baseEnd_8381176 < baseStart_8381176 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381179 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 4]
def baseStart_8381179 : Nat := 118140960795 + 8381179 * 2 ^ 59
def prefixEnd_8381179 : Nat := 4983230072969 + 3 ^ 40 * 8381179 * 2
def baseEnd_8381179 : Nat := 4303573278368969332318165

theorem tailTrace_8381179 : CollatzResearch.WordTrace tailWord_8381179 prefixEnd_8381179 4303573278368969332318165 := by
  unfold tailWord_8381179
  simp only [CollatzResearch.WordTrace]
  refine ⟨305686711303427349259418591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203791140868951566172945727 305686711303427349259418591)
  ·
    refine ⟨458530066955141023889127887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305686711303427349259418591 458530066955141023889127887)
    ·
      refine ⟨687795100432711535833691831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458530066955141023889127887 687795100432711535833691831)
      ·
        refine ⟨1031692650649067303750537747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687795100432711535833691831 1031692650649067303750537747)
        ·
          refine ⟨1547538975973600955625806621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1031692650649067303750537747 1547538975973600955625806621)
          ·
            refine ⟨580327115990100358359677483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1547538975973600955625806621 580327115990100358359677483)
            ·
              refine ⟨870490673985150537539516225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580327115990100358359677483 870490673985150537539516225)
              ·
                refine ⟨652868005488862903154637169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 870490673985150537539516225 652868005488862903154637169)
                ·
                  refine ⟨489651004116647177365977877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 652868005488862903154637169 489651004116647177365977877)
                  ·
                    refine ⟨22952390817967836439030213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 489651004116647177365977877 22952390817967836439030213)
                    ·
                      refine ⟨4303573278368969332318165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22952390817967836439030213 4303573278368969332318165)
                      ·
                        rfl

theorem cell23_8381179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 4].length) (baseStart_8381179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381179 prefixEnd_8381179 := by exact prefixLift 8381179
  have htrace : WordTrace (prefixWord ++ tailWord_8381179) baseStart_8381179 baseEnd_8381179 := by
    simpa [prefixWord, tailWord_8381179, baseEnd_8381179] using wordTrace_append hprefix tailTrace_8381179
  have hstable : (prefixWord ++ tailWord_8381179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381179).length < 2 ^ (prefixWord ++ tailWord_8381179).sum := by decide
  have hdescent : baseEnd_8381179 < baseStart_8381179 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381180 : List Nat := [2, 2, 2, 1, 3, 4, 2, 1, 1, 5]
def baseStart_8381180 : Nat := 118140960795 + 8381180 * 2 ^ 59
def prefixEnd_8381180 : Nat := 4983230072969 + 3 ^ 40 * 8381180 * 2
def baseEnd_8381180 : Nat := 1434524597283207942801887

theorem tailTrace_8381180 : CollatzResearch.WordTrace tailWord_8381180 prefixEnd_8381180 1434524597283207942801887 := by
  unfold tailWord_8381180
  simp only [CollatzResearch.WordTrace]
  refine ⟨152843373888211863215102497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203791165184282484286803329 152843373888211863215102497)
  ·
    refine ⟨114632530416158897411326873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152843373888211863215102497 114632530416158897411326873)
    ·
      refine ⟨85974397812119173058495155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114632530416158897411326873 85974397812119173058495155)
      ·
        refine ⟨128961596718178759587742733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85974397812119173058495155 128961596718178759587742733)
        ·
          refine ⟨48360598769317034845403525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128961596718178759587742733 48360598769317034845403525)
          ·
            refine ⟨9067612269246944033513161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48360598769317034845403525 9067612269246944033513161)
            ·
              refine ⟨6800709201935208025134871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9067612269246944033513161 6800709201935208025134871)
              ·
                refine ⟨10201063802902812037702307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6800709201935208025134871 10201063802902812037702307)
                ·
                  refine ⟨15301595704354218056553461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10201063802902812037702307 15301595704354218056553461)
                  ·
                    refine ⟨1434524597283207942801887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15301595704354218056553461 1434524597283207942801887)
                    ·
                      rfl

theorem cell23_8381180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_8381180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381180 prefixEnd_8381180 := by exact prefixLift 8381180
  have htrace : WordTrace (prefixWord ++ tailWord_8381180) baseStart_8381180 baseEnd_8381180 := by
    simpa [prefixWord, tailWord_8381180, baseEnd_8381180] using wordTrace_append hprefix tailTrace_8381180
  have hstable : (prefixWord ++ tailWord_8381180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381180).length < 2 ^ (prefixWord ++ tailWord_8381180).sum := by decide
  have hdescent : baseEnd_8381180 < baseStart_8381180 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381183 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 7, 2, 2]
def baseStart_8381183 : Nat := 118140960795 + 8381183 * 2 ^ 59
def prefixEnd_8381183 : Nat := 4983230072969 + 3 ^ 40 * 8381183 * 2
def baseEnd_8381183 : Nat := 4303575332291587316668147

theorem tailTrace_8381183 : CollatzResearch.WordTrace tailWord_8381183 prefixEnd_8381183 4303575332291587316668147 := by
  unfold tailWord_8381183
  simp only [CollatzResearch.WordTrace]
  refine ⟨305686857195412857942564203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203791238130275238628376135 305686857195412857942564203)
  ·
    refine ⟨458530285793119286913846305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305686857195412857942564203 458530285793119286913846305)
    ·
      refine ⟨343897714344839465185384729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458530285793119286913846305 343897714344839465185384729)
      ·
        refine ⟨257923285758629598889038547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343897714344839465185384729 257923285758629598889038547)
        ·
          refine ⟨386884928637944398333557821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257923285758629598889038547 386884928637944398333557821)
          ·
            refine ⟨145081848239229149375084183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 386884928637944398333557821 145081848239229149375084183)
            ·
              refine ⟨217622772358843724062626275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145081848239229149375084183 217622772358843724062626275)
              ·
                refine ⟨326434158538265586093939413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217622772358843724062626275 326434158538265586093939413)
                ·
                  refine ⟨7650800590740599674076705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 326434158538265586093939413 7650800590740599674076705)
                  ·
                    refine ⟨5738100443055449755557529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7650800590740599674076705 5738100443055449755557529)
                    ·
                      refine ⟨4303575332291587316668147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5738100443055449755557529 4303575332291587316668147)
                      ·
                        rfl

theorem cell23_8381183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 7, 2, 2].length) (baseStart_8381183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381183 prefixEnd_8381183 := by exact prefixLift 8381183
  have htrace : WordTrace (prefixWord ++ tailWord_8381183) baseStart_8381183 baseEnd_8381183 := by
    simpa [prefixWord, tailWord_8381183, baseEnd_8381183] using wordTrace_append hprefix tailTrace_8381183
  have hstable : (prefixWord ++ tailWord_8381183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381183).length < 2 ^ (prefixWord ++ tailWord_8381183).sum := by decide
  have hdescent : baseEnd_8381183 < baseStart_8381183 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381193 : List Nat := [1, 2, 1, 1, 3, 2, 5, 2, 2, 4]
def baseStart_8381193 : Nat := 118140960795 + 8381193 * 2 ^ 59
def prefixEnd_8381193 : Nat := 4983230072969 + 3 ^ 40 * 8381193 * 2
def baseEnd_8381193 : Nat := 1434526822366044092514367

theorem tailTrace_8381193 : CollatzResearch.WordTrace tailWord_8381193 prefixEnd_8381193 1434526822366044092514367 := by
  unfold tailWord_8381193
  simp only [CollatzResearch.WordTrace]
  refine ⟨305687221925376629650428233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203791481283584419766952155 305687221925376629650428233)
  ·
    refine ⟨229265416444032472237821175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305687221925376629650428233 229265416444032472237821175)
    ·
      refine ⟨343898124666048708356731763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229265416444032472237821175 343898124666048708356731763)
      ·
        refine ⟨515847186999073062535097645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343898124666048708356731763 515847186999073062535097645)
        ·
          refine ⟨193442695124652398450661617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 515847186999073062535097645 193442695124652398450661617)
          ·
            refine ⟨145082021343489298837996213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193442695124652398450661617 145082021343489298837996213)
            ·
              refine ⟨13601439500952121766062145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 145082021343489298837996213 13601439500952121766062145)
              ·
                refine ⟨10201079625714091324546609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13601439500952121766062145 10201079625714091324546609)
                ·
                  refine ⟨7650809719285568493409957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10201079625714091324546609 7650809719285568493409957)
                  ·
                    refine ⟨1434526822366044092514367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7650809719285568493409957 1434526822366044092514367)
                    ·
                      rfl

theorem cell23_8381193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 2, 4].length) (baseStart_8381193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381193 prefixEnd_8381193 := by exact prefixLift 8381193
  have htrace : WordTrace (prefixWord ++ tailWord_8381193) baseStart_8381193 baseEnd_8381193 := by
    simpa [prefixWord, tailWord_8381193, baseEnd_8381193] using wordTrace_append hprefix tailTrace_8381193
  have hstable : (prefixWord ++ tailWord_8381193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381193).length < 2 ^ (prefixWord ++ tailWord_8381193).sum := by decide
  have hdescent : baseEnd_8381193 < baseStart_8381193 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381209 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 1, 4, 6]
def baseStart_8381209 : Nat := 118140960795 + 8381209 * 2 ^ 59
def prefixEnd_8381209 : Nat := 4983230072969 + 3 ^ 40 * 8381209 * 2
def baseEnd_8381209 : Nat := 4303588682788604214943027

theorem tailTrace_8381209 : CollatzResearch.WordTrace tailWord_8381209 prefixEnd_8381209 4303588682788604214943027 := by
  unfold tailWord_8381209
  simp only [CollatzResearch.WordTrace]
  refine ⟨305687805493318664383010681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203791870328879109588673787 305687805493318664383010681)
  ·
    refine ⟨229265854119988998287258011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305687805493318664383010681 229265854119988998287258011)
    ·
      refine ⟨343898781179983497430887017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229265854119988998287258011 343898781179983497430887017)
      ·
        refine ⟨257924085884987623073165263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343898781179983497430887017 257924085884987623073165263)
        ·
          refine ⟨386886128827481434609747895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257924085884987623073165263 386886128827481434609747895)
          ·
            refine ⟨580329193241222151914621843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386886128827481434609747895 580329193241222151914621843)
            ·
              refine ⟨870493789861833227871932765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580329193241222151914621843 870493789861833227871932765)
              ·
                refine ⟨326435171198187460451974787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 870493789861833227871932765 326435171198187460451974787)
                ·
                  refine ⟨489652756797281190677962181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 326435171198187460451974787 489652756797281190677962181)
                  ·
                    refine ⟨91809891899490223252117909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 489652756797281190677962181 91809891899490223252117909)
                    ·
                      refine ⟨4303588682788604214943027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91809891899490223252117909 4303588682788604214943027)
                      ·
                        rfl

theorem cell23_8381209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_8381209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381209 prefixEnd_8381209 := by exact prefixLift 8381209
  have htrace : WordTrace (prefixWord ++ tailWord_8381209) baseStart_8381209 baseEnd_8381209 := by
    simpa [prefixWord, tailWord_8381209, baseEnd_8381209] using wordTrace_append hprefix tailTrace_8381209
  have hstable : (prefixWord ++ tailWord_8381209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381209).length < 2 ^ (prefixWord ++ tailWord_8381209).sum := by decide
  have hdescent : baseEnd_8381209 < baseStart_8381209 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381210 : List Nat := [3, 1, 1, 3, 2, 1, 5, 1, 2, 4]
def baseStart_8381210 : Nat := 118140960795 + 8381210 * 2 ^ 59
def prefixEnd_8381210 : Nat := 4983230072969 + 3 ^ 40 * 8381210 * 2
def baseEnd_8381210 : Nat := 1434529732089752903676841

theorem tailTrace_8381210 : CollatzResearch.WordTrace tailWord_8381210 prefixEnd_8381210 1434529732089752903676841 := by
  unfold tailWord_8381210
  simp only [CollatzResearch.WordTrace]
  refine ⟨76421960491578760388449271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203791894644210027702531389 76421960491578760388449271)
  ·
    refine ⟨114632940737368140582673907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76421960491578760388449271 114632940737368140582673907)
    ·
      refine ⟨171949411106052210874010861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114632940737368140582673907 171949411106052210874010861)
      ·
        refine ⟨64481029164769579077754073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171949411106052210874010861 64481029164769579077754073)
        ·
          refine ⟨48360771873577184308315555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64481029164769579077754073 48360771873577184308315555)
          ·
            refine ⟨72541157810365776462473333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48360771873577184308315555 72541157810365776462473333)
            ·
              refine ⟨6800733544721791543356875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72541157810365776462473333 6800733544721791543356875)
              ·
                refine ⟨10201100317082687315035313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6800733544721791543356875 10201100317082687315035313)
                ·
                  refine ⟨7650825237812015486276485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10201100317082687315035313 7650825237812015486276485)
                  ·
                    refine ⟨1434529732089752903676841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7650825237812015486276485 1434529732089752903676841)
                    ·
                      rfl

theorem cell23_8381210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 2, 4].length) (baseStart_8381210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381210 prefixEnd_8381210 := by exact prefixLift 8381210
  have htrace : WordTrace (prefixWord ++ tailWord_8381210) baseStart_8381210 baseEnd_8381210 := by
    simpa [prefixWord, tailWord_8381210, baseEnd_8381210] using wordTrace_append hprefix tailTrace_8381210
  have hstable : (prefixWord ++ tailWord_8381210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381210).length < 2 ^ (prefixWord ++ tailWord_8381210).sum := by decide
  have hdescent : baseEnd_8381210 < baseStart_8381210 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381233 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 6, 1, 3]
def baseStart_8381233 : Nat := 118140960795 + 8381233 * 2 ^ 59
def prefixEnd_8381233 : Nat := 4983230072969 + 3 ^ 40 * 8381233 * 2
def baseEnd_8381233 : Nat := 4303601006324312121042917

theorem tailTrace_8381233 : CollatzResearch.WordTrace tailWord_8381233 prefixEnd_8381233 4303601006324312121042917 := by
  unfold tailWord_8381233
  simp only [CollatzResearch.WordTrace]
  refine ⟨305688680845231716481884353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203792453896821144321256235 305688680845231716481884353)
  ·
    refine ⟨229266510633923787361413265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305688680845231716481884353 229266510633923787361413265)
    ·
      refine ⟨171949882975442840521059949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229266510633923787361413265 171949882975442840521059949)
      ·
        refine ⟨64481206115791065195397481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171949882975442840521059949 64481206115791065195397481)
        ·
          refine ⟨48360904586843298896548111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64481206115791065195397481 48360904586843298896548111)
          ·
            refine ⟨72541356880264948344822167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48360904586843298896548111 72541356880264948344822167)
            ·
              refine ⟨108812035320397422517233251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72541356880264948344822167 108812035320397422517233251)
              ·
                refine ⟨163218052980596133775849877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108812035320397422517233251 163218052980596133775849877)
                ·
                  refine ⟨7650846233465443770742963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 163218052980596133775849877 7650846233465443770742963)
                  ·
                    refine ⟨11476269350198165656114445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7650846233465443770742963 11476269350198165656114445)
                    ·
                      refine ⟨4303601006324312121042917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11476269350198165656114445 4303601006324312121042917)
                      ·
                        rfl

theorem cell23_8381233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_8381233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381233 prefixEnd_8381233 := by exact prefixLift 8381233
  have htrace : WordTrace (prefixWord ++ tailWord_8381233) baseStart_8381233 baseEnd_8381233 := by
    simpa [prefixWord, tailWord_8381233, baseEnd_8381233] using wordTrace_append hprefix tailTrace_8381233
  have hstable : (prefixWord ++ tailWord_8381233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381233).length < 2 ^ (prefixWord ++ tailWord_8381233).sum := by decide
  have hdescent : baseEnd_8381233 < baseStart_8381233 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381256 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 2, 3, 4]
def baseStart_8381256 : Nat := 118140960795 + 8381256 * 2 ^ 59
def prefixEnd_8381256 : Nat := 4983230072969 + 3 ^ 40 * 8381256 * 2
def baseEnd_8381256 : Nat := 4303612816379365531055311

theorem tailTrace_8381256 : CollatzResearch.WordTrace tailWord_8381256 prefixEnd_8381256 4303612816379365531055311 := by
  unfold tailWord_8381256
  simp only [CollatzResearch.WordTrace]
  refine ⟨152844759862074195704985811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203793013149432260939981081 152844759862074195704985811)
  ·
    refine ⟨229267139793111293557478717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152844759862074195704985811 229267139793111293557478717)
    ·
      refine ⟨85975177422416735084054519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229267139793111293557478717 85975177422416735084054519)
      ·
        refine ⟨128962766133625102626081779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85975177422416735084054519 128962766133625102626081779)
        ·
          refine ⟨193444149200437653939122669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128962766133625102626081779 193444149200437653939122669)
          ·
            refine ⟨72541555950164120227171001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193444149200437653939122669 72541555950164120227171001)
            ·
              refine ⟨54406166962623090170378251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72541555950164120227171001 54406166962623090170378251)
              ·
                refine ⟨81609250443934635255567377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54406166962623090170378251 81609250443934635255567377)
                ·
                  refine ⟨61206937832950976441675533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81609250443934635255567377 61206937832950976441675533)
                  ·
                    refine ⟨22952601687356616165628325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61206937832950976441675533 22952601687356616165628325)
                    ·
                      refine ⟨4303612816379365531055311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22952601687356616165628325 4303612816379365531055311)
                      ·
                        rfl

theorem cell23_8381256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_8381256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381256 prefixEnd_8381256 := by exact prefixLift 8381256
  have htrace : WordTrace (prefixWord ++ tailWord_8381256) baseStart_8381256 baseEnd_8381256 := by
    simpa [prefixWord, tailWord_8381256, baseEnd_8381256] using wordTrace_append hprefix tailTrace_8381256
  have hstable : (prefixWord ++ tailWord_8381256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381256).length < 2 ^ (prefixWord ++ tailWord_8381256).sum := by decide
  have hdescent : baseEnd_8381256 < baseStart_8381256 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381261 : List Nat := [1, 6, 1, 2, 3, 1, 2, 1, 2, 4]
def baseStart_8381261 : Nat := 118140960795 + 8381261 * 2 ^ 59
def prefixEnd_8381261 : Nat := 4983230072969 + 3 ^ 40 * 8381261 * 2
def baseEnd_8381261 : Nat := 1434538461260879337164263

theorem tailTrace_8381261 : CollatzResearch.WordTrace tailWord_8381261 prefixEnd_8381261 1434538461260879337164263 := by
  unfold tailWord_8381261
  simp only [CollatzResearch.WordTrace]
  refine ⟨305689702089130277263903637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203793134726086851509269091 305689702089130277263903637)
  ·
    refine ⟨14329204785427981746745483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 305689702089130277263903637 14329204785427981746745483)
    ·
      refine ⟨21493807178141972620118225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14329204785427981746745483 21493807178141972620118225)
      ·
        refine ⟨16120355383606479465088669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21493807178141972620118225 16120355383606479465088669)
        ·
          refine ⟨6045133268852429799408251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16120355383606479465088669 6045133268852429799408251)
          ·
            refine ⟨9067699903278644699112377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6045133268852429799408251 9067699903278644699112377)
            ·
              refine ⟨6800774927458983524334283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9067699903278644699112377 6800774927458983524334283)
              ·
                refine ⟨10201162391188475286501425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6800774927458983524334283 10201162391188475286501425)
                ·
                  refine ⟨7650871793391356464876069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10201162391188475286501425 7650871793391356464876069)
                  ·
                    refine ⟨1434538461260879337164263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7650871793391356464876069 1434538461260879337164263)
                    ·
                      rfl

theorem cell23_8381261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_8381261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381261 prefixEnd_8381261 := by exact prefixLift 8381261
  have htrace : WordTrace (prefixWord ++ tailWord_8381261) baseStart_8381261 baseEnd_8381261 := by
    simpa [prefixWord, tailWord_8381261, baseEnd_8381261] using wordTrace_append hprefix tailTrace_8381261
  have hstable : (prefixWord ++ tailWord_8381261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381261).length < 2 ^ (prefixWord ++ tailWord_8381261).sum := by decide
  have hdescent : baseEnd_8381261 < baseStart_8381261 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381266 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 1, 8]
def baseStart_8381266 : Nat := 118140960795 + 8381266 * 2 ^ 59
def prefixEnd_8381266 : Nat := 4983230072969 + 3 ^ 40 * 8381266 * 2
def baseEnd_8381266 : Nat := 1434539317061970163976755

theorem tailTrace_8381266 : CollatzResearch.WordTrace tailWord_8381266 prefixEnd_8381266 1434539317061970163976755 := by
  unfold tailWord_8381266
  simp only [CollatzResearch.WordTrace]
  refine ⟨76422471113528040779458913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203793256302741442078557101 76422471113528040779458913)
  ·
    refine ⟨57316853335146030584594185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76422471113528040779458913 57316853335146030584594185)
    ·
      refine ⟨42987640001359522938445639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57316853335146030584594185 42987640001359522938445639)
      ·
        refine ⟨64481460002039284407668459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42987640001359522938445639 64481460002039284407668459)
        ·
          refine ⟨96722190003058926611502689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64481460002039284407668459 96722190003058926611502689)
          ·
            refine ⟨72541642502294194958627017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96722190003058926611502689 72541642502294194958627017)
            ·
              refine ⟨54406231876720646218970263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72541642502294194958627017 54406231876720646218970263)
              ·
                refine ⟨81609347815080969328455395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54406231876720646218970263 81609347815080969328455395)
                ·
                  refine ⟨122414021722621453992683093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81609347815080969328455395 122414021722621453992683093)
                  ·
                    refine ⟨1434539317061970163976755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 122414021722621453992683093 1434539317061970163976755)
                    ·
                      rfl

theorem cell23_8381266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_8381266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381266 prefixEnd_8381266 := by exact prefixLift 8381266
  have htrace : WordTrace (prefixWord ++ tailWord_8381266) baseStart_8381266 baseEnd_8381266 := by
    simpa [prefixWord, tailWord_8381266, baseEnd_8381266] using wordTrace_append hprefix tailTrace_8381266
  have hstable : (prefixWord ++ tailWord_8381266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381266).length < 2 ^ (prefixWord ++ tailWord_8381266).sum := by decide
  have hdescent : baseEnd_8381266 < baseStart_8381266 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381316 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 2, 1, 8]
def baseStart_8381316 : Nat := 118140960795 + 8381316 * 2 ^ 59
def prefixEnd_8381316 : Nat := 4983230072969 + 3 ^ 40 * 8381316 * 2
def baseEnd_8381316 : Nat := 4303643625218635296305035

theorem tailTrace_8381316 : CollatzResearch.WordTrace tailWord_8381316 prefixEnd_8381316 4303643625218635296305035 := by
  unfold tailWord_8381316
  simp only [CollatzResearch.WordTrace]
  refine ⟨152845854051965510828577901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203794472069287347771437201 152845854051965510828577901)
  ·
    refine ⟨57317195269487066560716713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152845854051965510828577901 57317195269487066560716713)
    ·
      refine ⟨42987896452115299920537535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57317195269487066560716713 42987896452115299920537535)
      ·
        refine ⟨64481844678172949880806303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42987896452115299920537535 64481844678172949880806303)
        ·
          refine ⟨96722767017259424821209455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64481844678172949880806303 96722767017259424821209455)
          ·
            refine ⟨145084150525889137231814183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96722767017259424821209455 145084150525889137231814183)
            ·
              refine ⟨217626225788833705847721275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145084150525889137231814183 217626225788833705847721275)
              ·
                refine ⟨326439338683250558771581913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217626225788833705847721275 326439338683250558771581913)
                ·
                  refine ⟨244829504012437919078686435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 326439338683250558771581913 244829504012437919078686435)
                  ·
                    refine ⟨367244256018656878618029653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 244829504012437919078686435 367244256018656878618029653)
                    ·
                      refine ⟨4303643625218635296305035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 367244256018656878618029653 4303643625218635296305035)
                      ·
                        rfl

theorem cell23_8381316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_8381316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381316 prefixEnd_8381316 := by exact prefixLift 8381316
  have htrace : WordTrace (prefixWord ++ tailWord_8381316) baseStart_8381316 baseEnd_8381316 := by
    simpa [prefixWord, tailWord_8381316, baseEnd_8381316] using wordTrace_append hprefix tailTrace_8381316
  have hstable : (prefixWord ++ tailWord_8381316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381316).length < 2 ^ (prefixWord ++ tailWord_8381316).sum := by decide
  have hdescent : baseEnd_8381316 < baseStart_8381316 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381330 : List Nat := [3, 2, 3, 2, 2, 1, 1, 2, 7]
def baseStart_8381330 : Nat := 118140960795 + 8381330 * 2 ^ 59
def prefixEnd_8381330 : Nat := 4983230072969 + 3 ^ 40 * 8381330 * 2
def baseEnd_8381330 : Nat := 478183423771977582392219

theorem tailTrace_8381330 : CollatzResearch.WordTrace tailWord_8381330 prefixEnd_8381330 478183423771977582392219 := by
  unfold tailWord_8381330
  simp only [CollatzResearch.WordTrace]
  refine ⟨76423054681470075512041361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203794812483920201365443629 76423054681470075512041361)
  ·
    refine ⟨57317291011102556634031021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76423054681470075512041361 57317291011102556634031021)
    ·
      refine ⟨21493984129163458737761633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57317291011102556634031021 21493984129163458737761633)
      ·
        refine ⟨16120488096872594053321225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21493984129163458737761633 16120488096872594053321225)
        ·
          refine ⟨12090366072654445539990919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16120488096872594053321225 12090366072654445539990919)
          ·
            refine ⟨18135549108981668309986379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12090366072654445539990919 18135549108981668309986379)
            ·
              refine ⟨27203323663472502464979569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18135549108981668309986379 27203323663472502464979569)
              ·
                refine ⟨20402492747604376848734677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27203323663472502464979569 20402492747604376848734677)
                ·
                  refine ⟨478183423771977582392219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20402492747604376848734677 478183423771977582392219)
                  ·
                    rfl

theorem cell23_8381330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 7].length) (baseStart_8381330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381330 prefixEnd_8381330 := by exact prefixLift 8381330
  have htrace : WordTrace (prefixWord ++ tailWord_8381330) baseStart_8381330 baseEnd_8381330 := by
    simpa [prefixWord, tailWord_8381330, baseEnd_8381330] using wordTrace_append hprefix tailTrace_8381330
  have hstable : (prefixWord ++ tailWord_8381330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381330).length < 2 ^ (prefixWord ++ tailWord_8381330).sum := by decide
  have hdescent : baseEnd_8381330 < baseStart_8381330 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381343 : List Nat := [1, 1, 2, 5, 2, 2, 1, 1, 1, 7]
def baseStart_8381343 : Nat := 118140960795 + 8381343 * 2 ^ 59
def prefixEnd_8381343 : Nat := 4983230072969 + 3 ^ 40 * 8381343 * 2
def baseEnd_8381343 : Nat := 1434552496398768896889137

theorem tailTrace_8381343 : CollatzResearch.WordTrace tailWord_8381343 prefixEnd_8381343 1434552496398768896889137 := by
  unfold tailWord_8381343
  simp only [CollatzResearch.WordTrace]
  refine ⟨305692692874833205268388683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203795128583222136845592455 305692692874833205268388683)
  ·
    refine ⟨458539039312249807902583025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305692692874833205268388683 458539039312249807902583025)
    ·
      refine ⟨343904279484187355926937269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458539039312249807902583025 343904279484187355926937269)
      ·
        refine ⟨32241026201642564618150369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 343904279484187355926937269 32241026201642564618150369)
        ·
          refine ⟨24180769651231923463612777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32241026201642564618150369 24180769651231923463612777)
          ·
            refine ⟨18135577238423942597709583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24180769651231923463612777 18135577238423942597709583)
            ·
              refine ⟨27203365857635913896564375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18135577238423942597709583 27203365857635913896564375)
              ·
                refine ⟨40805048786453870844846563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27203365857635913896564375 40805048786453870844846563)
                ·
                  refine ⟨61207573179680806267269845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40805048786453870844846563 61207573179680806267269845)
                  ·
                    refine ⟨1434552496398768896889137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61207573179680806267269845 1434552496398768896889137)
                    ·
                      rfl

theorem cell23_8381343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 7].length) (baseStart_8381343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381343 prefixEnd_8381343 := by exact prefixLift 8381343
  have htrace : WordTrace (prefixWord ++ tailWord_8381343) baseStart_8381343 baseEnd_8381343 := by
    simpa [prefixWord, tailWord_8381343, baseEnd_8381343] using wordTrace_append hprefix tailTrace_8381343
  have hstable : (prefixWord ++ tailWord_8381343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381343).length < 2 ^ (prefixWord ++ tailWord_8381343).sum := by decide
  have hdescent : baseEnd_8381343 < baseStart_8381343 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381383 : List Nat := [1, 1, 4, 1, 1, 2, 3, 2, 1, 4, 3]
def baseStart_8381383 : Nat := 118140960795 + 8381383 * 2 ^ 59
def prefixEnd_8381383 : Nat := 4983230072969 + 3 ^ 40 * 8381383 * 2
def baseEnd_8381383 : Nat := 4303678028422486534167227

theorem tailTrace_8381383 : CollatzResearch.WordTrace tailWord_8381383 prefixEnd_8381383 4303678028422486534167227 := by
  unfold tailWord_8381383
  simp only [CollatzResearch.WordTrace]
  refine ⟨305694151794688292099844803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203796101196458861399896535 305694151794688292099844803)
  ·
    refine ⟨458541227692032438149767205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305694151794688292099844803 458541227692032438149767205)
    ·
      refine ⟨85976480192256082153081351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 458541227692032438149767205 85976480192256082153081351)
      ·
        refine ⟨128964720288384123229622027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85976480192256082153081351 128964720288384123229622027)
        ·
          refine ⟨193447080432576184844433041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128964720288384123229622027 193447080432576184844433041)
          ·
            refine ⟨145085310324432138633324781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193447080432576184844433041 145085310324432138633324781)
            ·
              refine ⟨54406991371662051987496793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145085310324432138633324781 54406991371662051987496793)
              ·
                refine ⟨40805243528746538990622595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54406991371662051987496793 40805243528746538990622595)
                ·
                  refine ⟨61207865293119808485933893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40805243528746538990622595 61207865293119808485933893)
                  ·
                    refine ⟨11476474742459964091112605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61207865293119808485933893 11476474742459964091112605)
                    ·
                      refine ⟨4303678028422486534167227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11476474742459964091112605 4303678028422486534167227)
                      ·
                        rfl

theorem cell23_8381383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_8381383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381383 prefixEnd_8381383 := by exact prefixLift 8381383
  have htrace : WordTrace (prefixWord ++ tailWord_8381383) baseStart_8381383 baseEnd_8381383 := by
    simpa [prefixWord, tailWord_8381383, baseEnd_8381383] using wordTrace_append hprefix tailTrace_8381383
  have hstable : (prefixWord ++ tailWord_8381383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381383).length < 2 ^ (prefixWord ++ tailWord_8381383).sum := by decide
  have hdescent : baseEnd_8381383 < baseStart_8381383 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381390 : List Nat := [4, 1, 1, 1, 2, 3, 2, 2, 3, 4]
def baseStart_8381390 : Nat := 118140960795 + 8381390 * 2 ^ 59
def prefixEnd_8381390 : Nat := 4983230072969 + 3 ^ 40 * 8381390 * 2
def baseEnd_8381390 : Nat := 1434560540929022668926565

theorem tailTrace_8381390 : CollatzResearch.WordTrace tailWord_8381390 prefixEnd_8381390 1434560540929022668926565 := by
  unfold tailWord_8381390
  simp only [CollatzResearch.WordTrace]
  refine ⟨38211800888207866536918703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203796271403775288196899749 38211800888207866536918703)
  ·
    refine ⟨57317701332311799805378055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38211800888207866536918703 57317701332311799805378055)
    ·
      refine ⟨85976551998467699708067083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57317701332311799805378055 85976551998467699708067083)
      ·
        refine ⟨128964827997701549562100625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85976551998467699708067083 128964827997701549562100625)
        ·
          refine ⟨96723620998276162171575469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128964827997701549562100625 96723620998276162171575469)
          ·
            refine ⟨36271357874353560814340801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96723620998276162171575469 36271357874353560814340801)
            ·
              refine ⟨27203518405765170610755601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36271357874353560814340801 27203518405765170610755601)
              ·
                refine ⟨20402638804323877958066701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27203518405765170610755601 20402638804323877958066701)
                ·
                  refine ⟨7650989551621454234275013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20402638804323877958066701 7650989551621454234275013)
                  ·
                    refine ⟨1434560540929022668926565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7650989551621454234275013 1434560540929022668926565)
                    ·
                      rfl

theorem cell23_8381390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_8381390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381390 prefixEnd_8381390 := by exact prefixLift 8381390
  have htrace : WordTrace (prefixWord ++ tailWord_8381390) baseStart_8381390 baseEnd_8381390 := by
    simpa [prefixWord, tailWord_8381390, baseEnd_8381390] using wordTrace_append hprefix tailTrace_8381390
  have hstable : (prefixWord ++ tailWord_8381390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381390).length < 2 ^ (prefixWord ++ tailWord_8381390).sum := by decide
  have hdescent : baseEnd_8381390 < baseStart_8381390 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381433 : List Nat := [1, 2, 1, 3, 1, 3, 2, 2, 3, 5]
def baseStart_8381433 : Nat := 118140960795 + 8381433 * 2 ^ 59
def prefixEnd_8381433 : Nat := 4983230072969 + 3 ^ 40 * 8381433 * 2
def baseEnd_8381433 : Nat := 1434567900818403779513999

theorem tailTrace_8381433 : CollatzResearch.WordTrace tailWord_8381433 prefixEnd_8381433 1434567900818403779513999 := by
  unfold tailWord_8381433
  simp only [CollatzResearch.WordTrace]
  refine ⟨305695975444507150639164953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203797316963004767092776635 305695975444507150639164953)
  ·
    refine ⟨229271981583380362979373715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305695975444507150639164953 229271981583380362979373715)
    ·
      refine ⟨343907972375070544469060573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229271981583380362979373715 343907972375070544469060573)
      ·
        refine ⟨128965489640651454175897715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343907972375070544469060573 128965489640651454175897715)
        ·
          refine ⟨193448234460977181263846573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128965489640651454175897715 193448234460977181263846573)
          ·
            refine ⟨72543087922866442973942465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193448234460977181263846573 72543087922866442973942465)
            ·
              refine ⟨54407315942149832230456849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72543087922866442973942465 54407315942149832230456849)
              ·
                refine ⟨40805486956612374172842637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54407315942149832230456849 40805486956612374172842637)
                ·
                  refine ⟨15302057608729640314815989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40805486956612374172842637 15302057608729640314815989)
                  ·
                    refine ⟨1434567900818403779513999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15302057608729640314815989 1434567900818403779513999)
                    ·
                      rfl

theorem cell23_8381433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 5].length) (baseStart_8381433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381433 prefixEnd_8381433 := by exact prefixLift 8381433
  have htrace : WordTrace (prefixWord ++ tailWord_8381433) baseStart_8381433 baseEnd_8381433 := by
    simpa [prefixWord, tailWord_8381433, baseEnd_8381433] using wordTrace_append hprefix tailTrace_8381433
  have hstable : (prefixWord ++ tailWord_8381433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381433).length < 2 ^ (prefixWord ++ tailWord_8381433).sum := by decide
  have hdescent : baseEnd_8381433 < baseStart_8381433 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381450 : List Nat := [3, 1, 2, 2, 3, 2, 1, 1, 3, 5]
def baseStart_8381450 : Nat := 118140960795 + 8381450 * 2 ^ 59
def prefixEnd_8381450 : Nat := 4983230072969 + 3 ^ 40 * 8381450 * 2
def baseEnd_8381450 : Nat := 1434570810542112590676473

theorem tailTrace_8381450 : CollatzResearch.WordTrace tailWord_8381450 prefixEnd_8381450 1434570810542112590676473 := by
  unfold tailWord_8381450
  simp only [CollatzResearch.WordTrace]
  refine ⟨76424148871361390635633451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203797730323630375028355869 76424148871361390635633451)
  ·
    refine ⟨114636223307042085953450177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76424148871361390635633451 114636223307042085953450177)
    ·
      refine ⟨85977167480281564465087633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114636223307042085953450177 85977167480281564465087633)
      ·
        refine ⟨64482875610211173348815725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85977167480281564465087633 64482875610211173348815725)
        ·
          refine ⟨24181078353829190005805897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64482875610211173348815725 24181078353829190005805897)
          ·
            refine ⟨18135808765371892504354423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24181078353829190005805897 18135808765371892504354423)
            ·
              refine ⟨27203713148057838756531635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18135808765371892504354423 27203713148057838756531635)
              ·
                refine ⟨40805569722086758134797453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27203713148057838756531635 40805569722086758134797453)
                ·
                  refine ⟨15302088645782534300549045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40805569722086758134797453 15302088645782534300549045)
                  ·
                    refine ⟨1434570810542112590676473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15302088645782534300549045 1434570810542112590676473)
                    ·
                      rfl

theorem cell23_8381450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_8381450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381450 prefixEnd_8381450 := by exact prefixLift 8381450
  have htrace : WordTrace (prefixWord ++ tailWord_8381450) baseStart_8381450 baseEnd_8381450 := by
    simpa [prefixWord, tailWord_8381450, baseEnd_8381450] using wordTrace_append hprefix tailTrace_8381450
  have hstable : (prefixWord ++ tailWord_8381450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381450).length < 2 ^ (prefixWord ++ tailWord_8381450).sum := by decide
  have hdescent : baseEnd_8381450 < baseStart_8381450 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381483 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 4]
def baseStart_8381483 : Nat := 118140960795 + 8381483 * 2 ^ 59
def prefixEnd_8381483 : Nat := 4983230072969 + 3 ^ 40 * 8381483 * 2
def baseEnd_8381483 : Nat := 4303729376487936142916767

theorem tailTrace_8381483 : CollatzResearch.WordTrace tailWord_8381483 prefixEnd_8381483 4303729376487936142916767 := by
  unfold tailWord_8381483
  simp only [CollatzResearch.WordTrace]
  refine ⟨305697799094326009178485103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203798532729550672785656735 305697799094326009178485103)
  ·
    refine ⟨458546698641489013767727655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305697799094326009178485103 458546698641489013767727655)
    ·
      refine ⟨687820047962233520651591483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458546698641489013767727655 687820047962233520651591483)
      ·
        refine ⟨1031730071943350280977387225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687820047962233520651591483 1031730071943350280977387225)
        ·
          refine ⟨773797553957512710733040419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1031730071943350280977387225 773797553957512710733040419)
          ·
            refine ⟨1160696330936269066099560629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773797553957512710733040419 1160696330936269066099560629)
            ·
              refine ⟨108815281025275224946833809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1160696330936269066099560629 108815281025275224946833809)
              ·
                refine ⟨81611460768956418710125357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108815281025275224946833809 81611460768956418710125357)
                ·
                  refine ⟨30604297788358657016297009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81611460768956418710125357 30604297788358657016297009)
                  ·
                    refine ⟨22953223341268992762222757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30604297788358657016297009 22953223341268992762222757)
                    ·
                      refine ⟨4303729376487936142916767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22953223341268992762222757 4303729376487936142916767)
                      ·
                        rfl

theorem cell23_8381483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 4].length) (baseStart_8381483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381483 prefixEnd_8381483 := by exact prefixLift 8381483
  have htrace : WordTrace (prefixWord ++ tailWord_8381483) baseStart_8381483 baseEnd_8381483 := by
    simpa [prefixWord, tailWord_8381483, baseEnd_8381483] using wordTrace_append hprefix tailTrace_8381483
  have hstable : (prefixWord ++ tailWord_8381483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381483).length < 2 ^ (prefixWord ++ tailWord_8381483).sum := by decide
  have hdescent : baseEnd_8381483 < baseStart_8381483 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381490 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3]
def baseStart_8381490 : Nat := 118140960795 + 8381490 * 2 ^ 59
def prefixEnd_8381490 : Nat := 4983230072969 + 3 ^ 40 * 8381490 * 2
def baseEnd_8381490 : Nat := 4303732970852517615529235

theorem tailTrace_8381490 : CollatzResearch.WordTrace tailWord_8381490 prefixEnd_8381490 4303732970852517615529235 := by
  unfold tailWord_8381490
  simp only [CollatzResearch.WordTrace]
  refine ⟨76424513601325162343497481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203798702936867099582659949 76424513601325162343497481)
  ·
    refine ⟨57318385200993871757623111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76424513601325162343497481 57318385200993871757623111)
    ·
      refine ⟨85977577801490807636434667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57318385200993871757623111 85977577801490807636434667)
      ·
        refine ⟨128966366702236211454652001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85977577801490807636434667 128966366702236211454652001)
        ·
          refine ⟨96724775026677158590989001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128966366702236211454652001 96724775026677158590989001)
          ·
            refine ⟨72543581270007868943241751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96724775026677158590989001 72543581270007868943241751)
            ·
              refine ⟨108815371905011803414862627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72543581270007868943241751 108815371905011803414862627)
              ·
                refine ⟨163223057857517705122293941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108815371905011803414862627 163223057857517705122293941)
                ·
                  refine ⟨15302161674142284855215057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 163223057857517705122293941 15302161674142284855215057)
                  ·
                    refine ⟨11476621255606713641411293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15302161674142284855215057 11476621255606713641411293)
                    ·
                      refine ⟨4303732970852517615529235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11476621255606713641411293 4303732970852517615529235)
                      ·
                        rfl

theorem cell23_8381490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_8381490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381490 prefixEnd_8381490 := by exact prefixLift 8381490
  have htrace : WordTrace (prefixWord ++ tailWord_8381490) baseStart_8381490 baseEnd_8381490 := by
    simpa [prefixWord, tailWord_8381490, baseEnd_8381490] using wordTrace_append hprefix tailTrace_8381490
  have hstable : (prefixWord ++ tailWord_8381490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381490).length < 2 ^ (prefixWord ++ tailWord_8381490).sum := by decide
  have hdescent : baseEnd_8381490 < baseStart_8381490 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381497 : List Nat := [1, 2, 1, 5, 2, 1, 2, 3, 2, 4]
def baseStart_8381497 : Nat := 118140960795 + 8381497 * 2 ^ 59
def prefixEnd_8381497 : Nat := 4983230072969 + 3 ^ 40 * 8381497 * 2
def baseEnd_8381497 : Nat := 1434578855072366362713901

theorem tailTrace_8381497 : CollatzResearch.WordTrace tailWord_8381497 prefixEnd_8381497 1434578855072366362713901 := by
  unfold tailWord_8381497
  simp only [CollatzResearch.WordTrace]
  refine ⟨305698309716275289569494745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203798873144183526379663163 305698309716275289569494745)
  ·
    refine ⟨229273732287206467177121059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305698309716275289569494745 229273732287206467177121059)
    ·
      refine ⟨343910598430809700765681589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229273732287206467177121059 343910598430809700765681589)
      ·
        refine ⟨32241618602888409446782649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 343910598430809700765681589 32241618602888409446782649)
        ·
          refine ⟨24181213952166307085086987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32241618602888409446782649 24181213952166307085086987)
          ·
            refine ⟨36271820928249460627630481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24181213952166307085086987 36271820928249460627630481)
            ·
              refine ⟨27203865696187095470722861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36271820928249460627630481 27203865696187095470722861)
              ·
                refine ⟨10201449636070160801521073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27203865696187095470722861 10201449636070160801521073)
                ·
                  refine ⟨7651087227052620601140805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10201449636070160801521073 7651087227052620601140805)
                  ·
                    refine ⟨1434578855072366362713901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7651087227052620601140805 1434578855072366362713901)
                    ·
                      rfl

theorem cell23_8381497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 2, 4].length) (baseStart_8381497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381497 prefixEnd_8381497 := by exact prefixLift 8381497
  have htrace : WordTrace (prefixWord ++ tailWord_8381497) baseStart_8381497 baseEnd_8381497 := by
    simpa [prefixWord, tailWord_8381497, baseEnd_8381497] using wordTrace_append hprefix tailTrace_8381497
  have hstable : (prefixWord ++ tailWord_8381497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381497).length < 2 ^ (prefixWord ++ tailWord_8381497).sum := by decide
  have hdescent : baseEnd_8381497 < baseStart_8381497 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381500 : List Nat := [2, 2, 2, 2, 2, 2, 1, 3, 1, 2, 4]
def baseStart_8381500 : Nat := 118140960795 + 8381500 * 2 ^ 59
def prefixEnd_8381500 : Nat := 4983230072969 + 3 ^ 40 * 8381500 * 2
def baseEnd_8381500 : Nat := 4303738105659062576404189

theorem tailTrace_8381500 : CollatzResearch.WordTrace tailWord_8381500 prefixEnd_8381500 4303738105659062576404189 := by
  unfold tailWord_8381500
  simp only [CollatzResearch.WordTrace]
  refine ⟨152849209567632210540926977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203798946090176280721235969 152849209567632210540926977)
  ·
    refine ⟨114636907175724157905695233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152849209567632210540926977 114636907175724157905695233)
    ·
      refine ⟨85977680381793118429271425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114636907175724157905695233 85977680381793118429271425)
      ·
        refine ⟨64483260286344838821953569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85977680381793118429271425 64483260286344838821953569)
        ·
          refine ⟨48362445214758629116465177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64483260286344838821953569 48362445214758629116465177)
          ·
            refine ⟨36271833911068971837348883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48362445214758629116465177 36271833911068971837348883)
            ·
              refine ⟨54407750866603457756023325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36271833911068971837348883 54407750866603457756023325)
              ·
                refine ⟨20402906574976296658508747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54407750866603457756023325 20402906574976296658508747)
                ·
                  refine ⟨30604359862464444987763121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20402906574976296658508747 30604359862464444987763121)
                  ·
                    refine ⟨22953269896848333740822341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30604359862464444987763121 22953269896848333740822341)
                    ·
                      refine ⟨4303738105659062576404189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22953269896848333740822341 4303738105659062576404189)
                      ·
                        rfl

theorem cell23_8381500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_8381500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381500 prefixEnd_8381500 := by exact prefixLift 8381500
  have htrace : WordTrace (prefixWord ++ tailWord_8381500) baseStart_8381500 baseEnd_8381500 := by
    simpa [prefixWord, tailWord_8381500, baseEnd_8381500] using wordTrace_append hprefix tailTrace_8381500
  have hstable : (prefixWord ++ tailWord_8381500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381500).length < 2 ^ (prefixWord ++ tailWord_8381500).sum := by decide
  have hdescent : baseEnd_8381500 < baseStart_8381500 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381517 : List Nat := [1, 6, 1, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_8381517 : Nat := 118140960795 + 8381517 * 2 ^ 59
def prefixEnd_8381517 : Nat := 4983230072969 + 3 ^ 40 * 8381517 * 2
def baseEnd_8381517 : Nat := 4303746834830189009891611

theorem tailTrace_8381517 : CollatzResearch.WordTrace tailWord_8381517 prefixEnd_8381517 4303746834830189009891611 := by
  unfold tailWord_8381517
  simp only [CollatzResearch.WordTrace]
  refine ⟨305699039176202832985222805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203799359450801888656815203 305699039176202832985222805)
  ·
    refine ⟨14329642461384507796182319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 305699039176202832985222805 14329642461384507796182319)
    ·
      refine ⟨21494463692076761694273479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14329642461384507796182319 21494463692076761694273479)
      ·
        refine ⟨32241695538115142541410219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21494463692076761694273479 32241695538115142541410219)
        ·
          refine ⟨48362543307172713812115329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32241695538115142541410219 48362543307172713812115329)
          ·
            refine ⟨36271907480379535359086497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48362543307172713812115329 36271907480379535359086497)
            ·
              refine ⟨27203930610284651519314873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36271907480379535359086497 27203930610284651519314873)
              ·
                refine ⟨20402947957713488639486155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27203930610284651519314873 20402947957713488639486155)
                ·
                  refine ⟨30604421936570232959229233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20402947957713488639486155 30604421936570232959229233)
                  ·
                    refine ⟨22953316452427674719421925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30604421936570232959229233 22953316452427674719421925)
                    ·
                      refine ⟨4303746834830189009891611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22953316452427674719421925 4303746834830189009891611)
                      ·
                        rfl

theorem cell23_8381517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_8381517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381517 prefixEnd_8381517 := by exact prefixLift 8381517
  have htrace : WordTrace (prefixWord ++ tailWord_8381517) baseStart_8381517 baseEnd_8381517 := by
    simpa [prefixWord, tailWord_8381517, baseEnd_8381517] using wordTrace_append hprefix tailTrace_8381517
  have hstable : (prefixWord ++ tailWord_8381517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381517).length < 2 ^ (prefixWord ++ tailWord_8381517).sum := by decide
  have hdescent : baseEnd_8381517 < baseStart_8381517 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381524 : List Nat := [2, 4, 1, 1, 1, 1, 6, 1, 1, 2, 3]
def baseStart_8381524 : Nat := 118140960795 + 8381524 * 2 ^ 59
def prefixEnd_8381524 : Nat := 4983230072969 + 3 ^ 40 * 8381524 * 2
def baseEnd_8381524 : Nat := 4303750429194770482504079

theorem tailTrace_8381524 : CollatzResearch.WordTrace tailWord_8381524 prefixEnd_8381524 4303750429194770482504079 := by
  unfold tailWord_8381524
  simp only [CollatzResearch.WordTrace]
  refine ⟨152849647243588736590363813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203799529658118315453818417 152849647243588736590363813)
  ·
    refine ⟨28659308858172888110693215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152849647243588736590363813 28659308858172888110693215)
    ·
      refine ⟨42988963287259332166039823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28659308858172888110693215 42988963287259332166039823)
      ·
        refine ⟨64483444930888998249059735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42988963287259332166039823 64483444930888998249059735)
        ·
          refine ⟨96725167396333497373589603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64483444930888998249059735 96725167396333497373589603)
          ·
            refine ⟨145087751094500246060384405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96725167396333497373589603 145087751094500246060384405)
            ·
              refine ⟨6800988332554699034080519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 145087751094500246060384405 6800988332554699034080519)
              ·
                refine ⟨10201482498832048551120779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6800988332554699034080519 10201482498832048551120779)
                ·
                  refine ⟨15302223748248072826681169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10201482498832048551120779 15302223748248072826681169)
                  ·
                    refine ⟨11476667811186054620010877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15302223748248072826681169 11476667811186054620010877)
                    ·
                      refine ⟨4303750429194770482504079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11476667811186054620010877 4303750429194770482504079)
                      ·
                        rfl

theorem cell23_8381524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_8381524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381524 prefixEnd_8381524 := by exact prefixLift 8381524
  have htrace : WordTrace (prefixWord ++ tailWord_8381524) baseStart_8381524 baseEnd_8381524 := by
    simpa [prefixWord, tailWord_8381524, baseEnd_8381524] using wordTrace_append hprefix tailTrace_8381524
  have hstable : (prefixWord ++ tailWord_8381524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381524).length < 2 ^ (prefixWord ++ tailWord_8381524).sum := by decide
  have hdescent : baseEnd_8381524 < baseStart_8381524 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381538 : List Nat := [3, 3, 2, 2, 1, 1, 2, 4, 1, 2, 2]
def baseStart_8381538 : Nat := 118140960795 + 8381538 * 2 ^ 59
def prefixEnd_8381538 : Nat := 4983230072969 + 3 ^ 40 * 8381538 * 2
def baseEnd_8381538 : Nat := 4303757617923933427729015

theorem tailTrace_8381538 : CollatzResearch.WordTrace tailWord_8381538 prefixEnd_8381538 4303757617923933427729015 := by
  unfold tailWord_8381538
  simp only [CollatzResearch.WordTrace]
  refine ⟨76424951277281688392934317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203799870072751169047824845 76424951277281688392934317)
  ·
    refine ⟨28659356728980633147350369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76424951277281688392934317 28659356728980633147350369)
    ·
      refine ⟨21494517546735474860512777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28659356728980633147350369 21494517546735474860512777)
      ·
        refine ⟨16120888160051606145384583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21494517546735474860512777 16120888160051606145384583)
        ·
          refine ⟨24181332240077409218076875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16120888160051606145384583 24181332240077409218076875)
          ·
            refine ⟨36271998360116113827115313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24181332240077409218076875 36271998360116113827115313)
            ·
              refine ⟨27203998770087085370336485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36271998360116113827115313 27203998770087085370336485)
              ·
                refine ⟨5100749769391328506938091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27203998770087085370336485 5100749769391328506938091)
                ·
                  refine ⟨7651124654086992760407137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5100749769391328506938091 7651124654086992760407137)
                  ·
                    refine ⟨5738343490565244570305353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7651124654086992760407137 5738343490565244570305353)
                    ·
                      refine ⟨4303757617923933427729015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5738343490565244570305353 4303757617923933427729015)
                      ·
                        rfl

theorem cell23_8381538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_8381538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381538 prefixEnd_8381538 := by exact prefixLift 8381538
  have htrace : WordTrace (prefixWord ++ tailWord_8381538) baseStart_8381538 baseEnd_8381538 := by
    simpa [prefixWord, tailWord_8381538, baseEnd_8381538] using wordTrace_append hprefix tailTrace_8381538
  have hstable : (prefixWord ++ tailWord_8381538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381538).length < 2 ^ (prefixWord ++ tailWord_8381538).sum := by decide
  have hdescent : baseEnd_8381538 < baseStart_8381538 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381553 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 1, 8]
def baseStart_8381553 : Nat := 118140960795 + 8381553 * 2 ^ 59
def prefixEnd_8381553 : Nat := 4983230072969 + 3 ^ 40 * 8381553 * 2
def baseEnd_8381553 : Nat := 1434588440044583623013815

theorem tailTrace_8381553 : CollatzResearch.WordTrace tailWord_8381553 prefixEnd_8381553 1434588440044583623013815 := by
  unfold tailWord_8381553
  simp only [CollatzResearch.WordTrace]
  refine ⟨305700352204072411133533313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203800234802714940755688875 305700352204072411133533313)
  ·
    refine ⟨229275264153054308350149985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305700352204072411133533313 229275264153054308350149985)
    ·
      refine ⟨171956448114790731262612489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229275264153054308350149985 171956448114790731262612489)
      ·
        refine ⟨128967336086093048446959367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171956448114790731262612489 128967336086093048446959367)
        ·
          refine ⟨193451004129139572670439051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128967336086093048446959367 193451004129139572670439051)
          ·
            refine ⟨290176506193709359005658577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193451004129139572670439051 290176506193709359005658577)
            ·
              refine ⟨217632379645282019254243933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290176506193709359005658577 217632379645282019254243933)
              ·
                refine ⟨81612142366980757220341475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217632379645282019254243933 81612142366980757220341475)
                ·
                  refine ⟨122418213550471135830512213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81612142366980757220341475 122418213550471135830512213)
                  ·
                    refine ⟨1434588440044583623013815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 122418213550471135830512213 1434588440044583623013815)
                    ·
                      rfl

theorem cell23_8381553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 8].length) (baseStart_8381553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381553 prefixEnd_8381553 := by exact prefixLift 8381553
  have htrace : WordTrace (prefixWord ++ tailWord_8381553) baseStart_8381553 baseEnd_8381553 := by
    simpa [prefixWord, tailWord_8381553, baseEnd_8381553] using wordTrace_append hprefix tailTrace_8381553
  have hstable : (prefixWord ++ tailWord_8381553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381553).length < 2 ^ (prefixWord ++ tailWord_8381553).sum := by decide
  have hdescent : baseEnd_8381553 < baseStart_8381553 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381563 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 5]
def baseStart_8381563 : Nat := 118140960795 + 8381563 * 2 ^ 59
def prefixEnd_8381563 : Nat := 4983230072969 + 3 ^ 40 * 8381563 * 2
def baseEnd_8381563 : Nat := 4303770454940295829916399

theorem tailTrace_8381563 : CollatzResearch.WordTrace tailWord_8381563 prefixEnd_8381563 4303770454940295829916399 := by
  unfold tailWord_8381563
  simp only [CollatzResearch.WordTrace]
  refine ⟨305700716934036182841397343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203800477956024121894264895 305700716934036182841397343)
  ·
    refine ⟨458551075401054274262096015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305700716934036182841397343 458551075401054274262096015)
    ·
      refine ⟨687826613101581411393144023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458551075401054274262096015 687826613101581411393144023)
      ·
        refine ⟨1031739919652372117089716035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687826613101581411393144023 1031739919652372117089716035)
        ·
          refine ⟨1547609879478558175634574053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1031739919652372117089716035 1547609879478558175634574053)
          ·
            refine ⟨290176852402229657931482635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1547609879478558175634574053 290176852402229657931482635)
            ·
              refine ⟨435265278603344486897223953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290176852402229657931482635 435265278603344486897223953)
              ·
                refine ⟨326448958952508365172917965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 435265278603344486897223953 326448958952508365172917965)
                ·
                  refine ⟨122418359607190636939844237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 326448958952508365172917965 122418359607190636939844237)
                  ·
                    refine ⟨45906884852696488852441589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 122418359607190636939844237 45906884852696488852441589)
                    ·
                      refine ⟨4303770454940295829916399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45906884852696488852441589 4303770454940295829916399)
                      ·
                        rfl

theorem cell23_8381563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 5].length) (baseStart_8381563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381563 prefixEnd_8381563 := by exact prefixLift 8381563
  have htrace : WordTrace (prefixWord ++ tailWord_8381563) baseStart_8381563 baseEnd_8381563 := by
    simpa [prefixWord, tailWord_8381563, baseEnd_8381563] using wordTrace_append hprefix tailTrace_8381563
  have hstable : (prefixWord ++ tailWord_8381563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381563).length < 2 ^ (prefixWord ++ tailWord_8381563).sum := by decide
  have hdescent : baseEnd_8381563 < baseStart_8381563 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381564 : List Nat := [2, 2, 2, 1, 1, 3, 4, 2, 1, 3, 2]
def baseStart_8381564 : Nat := 118140960795 + 8381564 * 2 ^ 59
def prefixEnd_8381564 : Nat := 4983230072969 + 3 ^ 40 * 8381564 * 2
def baseEnd_8381564 : Nat := 4303770968420950326003895

theorem tailTrace_8381564 : CollatzResearch.WordTrace tailWord_8381564 prefixEnd_8381564 4303770968420950326003895 := by
  unfold tailWord_8381564
  simp only [CollatzResearch.WordTrace]
  refine ⟨152850376703516280006091873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203800502271355040008122497 152850376703516280006091873)
  ·
    refine ⟨114637782527637210004568905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152850376703516280006091873 114637782527637210004568905)
    ·
      refine ⟨85978336895727907503426679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114637782527637210004568905 85978336895727907503426679)
      ·
        refine ⟨128967505343591861255140019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85978336895727907503426679 128967505343591861255140019)
        ·
          refine ⟨193451258015387791882710029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128967505343591861255140019 193451258015387791882710029)
          ·
            refine ⟨72544221755770421956016261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193451258015387791882710029 72544221755770421956016261)
            ·
              refine ⟨13602041579206954116753049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72544221755770421956016261 13602041579206954116753049)
              ·
                refine ⟨10201531184405215587564787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13602041579206954116753049 10201531184405215587564787)
                ·
                  refine ⟨15302296776607823381347181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10201531184405215587564787 15302296776607823381347181)
                  ·
                    refine ⟨5738361291227933768005193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15302296776607823381347181 5738361291227933768005193)
                    ·
                      refine ⟨4303770968420950326003895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5738361291227933768005193 4303770968420950326003895)
                      ·
                        rfl

theorem cell23_8381564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 1, 3, 2].length) (baseStart_8381564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381564 prefixEnd_8381564 := by exact prefixLift 8381564
  have htrace : WordTrace (prefixWord ++ tailWord_8381564) baseStart_8381564 baseEnd_8381564 := by
    simpa [prefixWord, tailWord_8381564, baseEnd_8381564] using wordTrace_append hprefix tailTrace_8381564
  have hstable : (prefixWord ++ tailWord_8381564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381564).length < 2 ^ (prefixWord ++ tailWord_8381564).sum := by decide
  have hdescent : baseEnd_8381564 < baseStart_8381564 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381640 : List Nat := [2, 1, 3, 1, 2, 1, 3, 2, 1, 2, 5]
def baseStart_8381640 : Nat := 118140960795 + 8381640 * 2 ^ 59
def prefixEnd_8381640 : Nat := 4983230072969 + 3 ^ 40 * 8381640 * 2
def baseEnd_8381640 : Nat := 4303809992950692028653545

theorem tailTrace_8381640 : CollatzResearch.WordTrace tailWord_8381640 prefixEnd_8381640 4303809992950692028653545 := by
  unfold tailWord_8381640
  simp only [CollatzResearch.WordTrace]
  refine ⟨152851762677378612495975187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203802350236504816661300249 152851762677378612495975187)
  ·
    refine ⟨229277644016067918743962781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152851762677378612495975187 229277644016067918743962781)
    ·
      refine ⟨85979116506025469528986043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229277644016067918743962781 85979116506025469528986043)
      ·
        refine ⟨128968674759038204293479065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85979116506025469528986043 128968674759038204293479065)
        ·
          refine ⟨96726506069278653220109299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128968674759038204293479065 96726506069278653220109299)
          ·
            refine ⟨145089759103917979830163949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96726506069278653220109299 145089759103917979830163949)
            ·
              refine ⟨54408659663969242436311481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145089759103917979830163949 54408659663969242436311481)
              ·
                refine ⟨40806494747976931827233611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54408659663969242436311481 40806494747976931827233611)
                ·
                  refine ⟨61209742121965397740850417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40806494747976931827233611 61209742121965397740850417)
                  ·
                    refine ⟨45907306591474048305637813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61209742121965397740850417 45907306591474048305637813)
                    ·
                      refine ⟨4303809992950692028653545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45907306591474048305637813 4303809992950692028653545)
                      ·
                        rfl

theorem cell23_8381640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_8381640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381640 prefixEnd_8381640 := by exact prefixLift 8381640
  have htrace : WordTrace (prefixWord ++ tailWord_8381640) baseStart_8381640 baseEnd_8381640 := by
    simpa [prefixWord, tailWord_8381640, baseEnd_8381640] using wordTrace_append hprefix tailTrace_8381640
  have hstable : (prefixWord ++ tailWord_8381640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381640).length < 2 ^ (prefixWord ++ tailWord_8381640).sum := by decide
  have hdescent : baseEnd_8381640 < baseStart_8381640 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381690 : List Nat := [3, 1, 1, 1, 1, 4, 2, 2, 8]
def baseStart_8381690 : Nat := 118140960795 + 8381690 * 2 ^ 59
def prefixEnd_8381690 : Nat := 4983230072969 + 3 ^ 40 * 8381690 * 2
def baseEnd_8381690 : Nat := 478203962998157425892035

theorem tailTrace_8381690 : CollatzResearch.WordTrace tailWord_8381690 prefixEnd_8381690 478203962998157425892035 := by
  unfold tailWord_8381690
  simp only [CollatzResearch.WordTrace]
  refine ⟨76426337251144020882817631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203803566003050722354180349 76426337251144020882817631)
  ·
    refine ⟨114639505876716031324226447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76426337251144020882817631 114639505876716031324226447)
    ·
      refine ⟨171959258815074046986339671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114639505876716031324226447 171959258815074046986339671)
      ·
        refine ⟨257938888222611070479509507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171959258815074046986339671 257938888222611070479509507)
        ·
          refine ⟨386908332333916605719264261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257938888222611070479509507 386908332333916605719264261)
          ·
            refine ⟨72545312312609363572362049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 386908332333916605719264261 72545312312609363572362049)
            ·
              refine ⟨54408984234457022679271537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72545312312609363572362049 54408984234457022679271537)
              ·
                refine ⟨40806738175842767009453653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54408984234457022679271537 40806738175842767009453653)
                ·
                  refine ⟨478203962998157425892035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40806738175842767009453653 478203962998157425892035)
                  ·
                    rfl

theorem cell23_8381690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 8].length) (baseStart_8381690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381690 prefixEnd_8381690 := by exact prefixLift 8381690
  have htrace : WordTrace (prefixWord ++ tailWord_8381690) baseStart_8381690 baseEnd_8381690 := by
    simpa [prefixWord, tailWord_8381690, baseEnd_8381690] using wordTrace_append hprefix tailTrace_8381690
  have hstable : (prefixWord ++ tailWord_8381690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381690).length < 2 ^ (prefixWord ++ tailWord_8381690).sum := by decide
  have hdescent : baseEnd_8381690 < baseStart_8381690 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381707 : List Nat := [1, 1, 1, 1, 5, 3, 3, 2, 6]
def baseStart_8381707 : Nat := 118140960795 + 8381707 * 2 ^ 59
def prefixEnd_8381707 : Nat := 4983230072969 + 3 ^ 40 * 8381707 * 2
def baseEnd_8381707 : Nat := 478204932906060362946193

theorem tailTrace_8381707 : CollatzResearch.WordTrace tailWord_8381707 prefixEnd_8381707 478204932906060362946193 := by
  unfold tailWord_8381707
  simp only [CollatzResearch.WordTrace]
  refine ⟨305705969045514495434639375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203803979363676330289759583 305705969045514495434639375)
  ·
    refine ⟨458558953568271743151959063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305705969045514495434639375 458558953568271743151959063)
    ·
      refine ⟨687838430352407614727938595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458558953568271743151959063 687838430352407614727938595)
      ·
        refine ⟨1031757645528611422091907893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687838430352407614727938595 1031757645528611422091907893)
        ·
          refine ⟨96727279268307320821116365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1031757645528611422091907893 96727279268307320821116365)
          ·
            refine ⟨36272729725615245307918637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96727279268307320821116365 36272729725615245307918637)
            ·
              refine ⟨13602273647105716990469489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36272729725615245307918637 13602273647105716990469489)
              ·
                refine ⟨10201705235329287742852117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13602273647105716990469489 10201705235329287742852117)
                ·
                  refine ⟨478204932906060362946193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10201705235329287742852117 478204932906060362946193)
                  ·
                    rfl

theorem cell23_8381707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 6].length) (baseStart_8381707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381707 prefixEnd_8381707 := by exact prefixLift 8381707
  have htrace : WordTrace (prefixWord ++ tailWord_8381707) baseStart_8381707 baseEnd_8381707 := by
    simpa [prefixWord, tailWord_8381707, baseEnd_8381707] using wordTrace_append hprefix tailTrace_8381707
  have hstable : (prefixWord ++ tailWord_8381707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381707).length < 2 ^ (prefixWord ++ tailWord_8381707).sum := by decide
  have hdescent : baseEnd_8381707 < baseStart_8381707 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381744 : List Nat := [2, 1, 1, 1, 2, 2, 4, 3, 2, 3, 2]
def baseStart_8381744 : Nat := 118140960795 + 8381744 * 2 ^ 59
def prefixEnd_8381744 : Nat := 4983230072969 + 3 ^ 40 * 8381744 * 2
def baseEnd_8381744 : Nat := 4303863394938759621753067

theorem tailTrace_8381744 : CollatzResearch.WordTrace tailWord_8381744 prefixEnd_8381744 4303863394938759621753067 := by
  unfold tailWord_8381744
  simp only [CollatzResearch.WordTrace]
  refine ⟨152853659273190225376868143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203804879030920300502490857 152853659273190225376868143)
  ·
    refine ⟨229280488909785338065302215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152853659273190225376868143 229280488909785338065302215)
    ·
      refine ⟨343920733364678007097953323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229280488909785338065302215 343920733364678007097953323)
      ·
        refine ⟨515881100047017010646929985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343920733364678007097953323 515881100047017010646929985)
        ·
          refine ⟨386910825035262757985197489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515881100047017010646929985 386910825035262757985197489)
          ·
            refine ⟨290183118776447068488898117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386910825035262757985197489 290183118776447068488898117)
            ·
              refine ⟨54409334770583825341668397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 290183118776447068488898117 54409334770583825341668397)
              ·
                refine ⟨20403500538968934503125649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54409334770583825341668397 20403500538968934503125649)
                ·
                  refine ⟨15302625404226700877344237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20403500538968934503125649 15302625404226700877344237)
                  ·
                    refine ⟨5738484526585012829004089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15302625404226700877344237 5738484526585012829004089)
                    ·
                      refine ⟨4303863394938759621753067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5738484526585012829004089 4303863394938759621753067)
                      ·
                        rfl

theorem cell23_8381744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 2, 3, 2].length) (baseStart_8381744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381744 prefixEnd_8381744 := by exact prefixLift 8381744
  have htrace : WordTrace (prefixWord ++ tailWord_8381744) baseStart_8381744 baseEnd_8381744 := by
    simpa [prefixWord, tailWord_8381744, baseEnd_8381744] using wordTrace_append hprefix tailTrace_8381744
  have hstable : (prefixWord ++ tailWord_8381744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381744).length < 2 ^ (prefixWord ++ tailWord_8381744).sum := by decide
  have hdescent : baseEnd_8381744 < baseStart_8381744 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381761 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 4, 3, 2]
def baseStart_8381761 : Nat := 118140960795 + 8381761 * 2 ^ 59
def prefixEnd_8381761 : Nat := 4983230072969 + 3 ^ 40 * 8381761 * 2
def baseEnd_8381761 : Nat := 4303872124109886055240489

theorem tailTrace_8381761 : CollatzResearch.WordTrace tailWord_8381761 prefixEnd_8381761 4303872124109886055240489 := by
  unfold tailWord_8381761
  simp only [CollatzResearch.WordTrace]
  refine ⟨305707938587318862657105137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203805292391545908438070091 305707938587318862657105137)
  ·
    refine ⟨229280953940489146992828853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305707938587318862657105137 229280953940489146992828853)
    ·
      refine ⟨21495089431920857530577705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 229280953940489146992828853 21495089431920857530577705)
      ·
        refine ⟨16121317073940643147933279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21495089431920857530577705 16121317073940643147933279)
        ·
          refine ⟨24181975610910964721899919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16121317073940643147933279 24181975610910964721899919)
          ·
            refine ⟨36272963416366447082849879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24181975610910964721899919 36272963416366447082849879)
            ·
              refine ⟨54409445124549670624274819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36272963416366447082849879 54409445124549670624274819)
              ·
                refine ⟨81614167686824505936412229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54409445124549670624274819 81614167686824505936412229)
                ·
                  refine ⟨15302656441279594863077293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81614167686824505936412229 15302656441279594863077293)
                  ·
                    refine ⟨5738496165479848073653985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15302656441279594863077293 5738496165479848073653985)
                    ·
                      refine ⟨4303872124109886055240489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5738496165479848073653985 4303872124109886055240489)
                      ·
                        rfl

theorem cell23_8381761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_8381761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381761 prefixEnd_8381761 := by exact prefixLift 8381761
  have htrace : WordTrace (prefixWord ++ tailWord_8381761) baseStart_8381761 baseEnd_8381761 := by
    simpa [prefixWord, tailWord_8381761, baseEnd_8381761] using wordTrace_append hprefix tailTrace_8381761
  have hstable : (prefixWord ++ tailWord_8381761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381761).length < 2 ^ (prefixWord ++ tailWord_8381761).sum := by decide
  have hdescent : baseEnd_8381761 < baseStart_8381761 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381777 : List Nat := [1, 2, 2, 1, 4, 1, 1, 4, 1, 1, 5]
def baseStart_8381777 : Nat := 118140960795 + 8381777 * 2 ^ 59
def prefixEnd_8381777 : Nat := 4983230072969 + 3 ^ 40 * 8381777 * 2
def baseEnd_8381777 : Nat := 4303880339800357992640415

theorem tailTrace_8381777 : CollatzResearch.WordTrace tailWord_8381777 prefixEnd_8381777 4303880339800357992640415 := by
  unfold tailWord_8381777
  simp only [CollatzResearch.WordTrace]
  refine ⟨305708522155260897389687585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203805681436840598259791723 305708522155260897389687585)
  ·
    refine ⟨229281391616445673042265689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305708522155260897389687585 229281391616445673042265689)
    ·
      refine ⟨171961043712334254781699267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229281391616445673042265689 171961043712334254781699267)
      ·
        refine ⟨257941565568501382172548901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171961043712334254781699267 257941565568501382172548901)
        ·
          refine ⟨48364043544094009157352919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257941565568501382172548901 48364043544094009157352919)
          ·
            refine ⟨72546065316141013736029379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48364043544094009157352919 72546065316141013736029379)
            ·
              refine ⟨108819097974211520604044069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72546065316141013736029379 108819097974211520604044069)
              ·
                refine ⟨20403580870164660113258263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108819097974211520604044069 20403580870164660113258263)
                ·
                  refine ⟨30605371305246990169887395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20403580870164660113258263 30605371305246990169887395)
                  ·
                    refine ⟨45908056957870485254831093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30605371305246990169887395 45908056957870485254831093)
                    ·
                      refine ⟨4303880339800357992640415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45908056957870485254831093 4303880339800357992640415)
                      ·
                        rfl

theorem cell23_8381777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_8381777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381777 prefixEnd_8381777 := by exact prefixLift 8381777
  have htrace : WordTrace (prefixWord ++ tailWord_8381777) baseStart_8381777 baseEnd_8381777 := by
    simpa [prefixWord, tailWord_8381777, baseEnd_8381777] using wordTrace_append hprefix tailTrace_8381777
  have hstable : (prefixWord ++ tailWord_8381777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381777).length < 2 ^ (prefixWord ++ tailWord_8381777).sum := by decide
  have hdescent : baseEnd_8381777 < baseStart_8381777 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
