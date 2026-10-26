import V185TrunkScan23Chunk0259

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1538207 : List Nat := [1, 1, 2, 6, 1, 3, 1, 1, 1, 3, 3]
def baseStart_1538207 : Nat := 118140960795 + 1538207 * 2 ^ 59
def prefixEnd_1538207 : Nat := 4983230072969 + 3 ^ 40 * 1538207 * 2
def baseEnd_1538207 : Nat := 789839537110568491738421

theorem tailTrace_1538207 : CollatzResearch.WordTrace tailWord_1538207 prefixEnd_1538207 789839537110568491738421 := by
  unfold tailWord_1538207
  simp only [CollatzResearch.WordTrace]
  refine ⟨56103018338346218685708875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37402012225564145790472583 56103018338346218685708875)
  ·
    refine ⟨84154527507519328028563313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56103018338346218685708875 84154527507519328028563313)
    ·
      refine ⟨63115895630639496021422485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84154527507519328028563313 63115895630639496021422485)
      ·
        refine ⟨2958557607686226376004179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 63115895630639496021422485 2958557607686226376004179)
        ·
          refine ⟨4437836411529339564006269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2958557607686226376004179 4437836411529339564006269)
          ·
            refine ⟨1664188654323502336502351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4437836411529339564006269 1664188654323502336502351)
            ·
              refine ⟨2496282981485253504753527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1664188654323502336502351 2496282981485253504753527)
              ·
                refine ⟨3744424472227880257130291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2496282981485253504753527 3744424472227880257130291)
                ·
                  refine ⟨5616636708341820385695437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3744424472227880257130291 5616636708341820385695437)
                  ·
                    refine ⟨2106238765628182644635789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5616636708341820385695437 2106238765628182644635789)
                    ·
                      refine ⟨789839537110568491738421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2106238765628182644635789 789839537110568491738421)
                      ·
                        rfl

theorem cell23_1538207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_1538207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538207 prefixEnd_1538207 := by exact prefixLift 1538207
  have htrace : WordTrace (prefixWord ++ tailWord_1538207) baseStart_1538207 baseEnd_1538207 := by
    simpa [prefixWord, tailWord_1538207, baseEnd_1538207] using wordTrace_append hprefix tailTrace_1538207
  have hstable : (prefixWord ++ tailWord_1538207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538207).length < 2 ^ (prefixWord ++ tailWord_1538207).sum := by decide
  have hdescent : baseEnd_1538207 < baseStart_1538207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538233 : List Nat := [1, 2, 1, 4, 1, 2, 3, 1, 2, 1, 5]
def baseStart_1538233 : Nat := 118140960795 + 1538233 * 2 ^ 59
def prefixEnd_1538233 : Nat := 4983230072969 + 3 ^ 40 * 1538233 * 2
def baseEnd_1538233 : Nat := 789852887607585390013301

theorem tailTrace_1538233 : CollatzResearch.WordTrace tailWord_1538233 prefixEnd_1538233 789852887607585390013301 := by
  unfold tailWord_1538233
  simp only [CollatzResearch.WordTrace]
  refine ⟨56103966636252025126155353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37402644424168016750770235 56103966636252025126155353)
  ·
    refine ⟨42077974977189018844616515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56103966636252025126155353 42077974977189018844616515)
    ·
      refine ⟨63116962465783528266924773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42077974977189018844616515 63116962465783528266924773)
      ·
        refine ⟨11834430462334411550048395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63116962465783528266924773 11834430462334411550048395)
        ·
          refine ⟨17751645693501617325072593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11834430462334411550048395 17751645693501617325072593)
          ·
            refine ⟨13313734270126212993804445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17751645693501617325072593 13313734270126212993804445)
            ·
              refine ⟨4992650351297329872676667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13313734270126212993804445 4992650351297329872676667)
              ·
                refine ⟨7488975526945994809015001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4992650351297329872676667 7488975526945994809015001)
                ·
                  refine ⟨5616731645209496106761251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7488975526945994809015001 5616731645209496106761251)
                  ·
                    refine ⟨8425097467814244160141877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5616731645209496106761251 8425097467814244160141877)
                    ·
                      refine ⟨789852887607585390013301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8425097467814244160141877 789852887607585390013301)
                      ·
                        rfl

theorem cell23_1538233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_1538233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538233 prefixEnd_1538233 := by exact prefixLift 1538233
  have htrace : WordTrace (prefixWord ++ tailWord_1538233) baseStart_1538233 baseEnd_1538233 := by
    simpa [prefixWord, tailWord_1538233, baseEnd_1538233] using wordTrace_append hprefix tailTrace_1538233
  have hstable : (prefixWord ++ tailWord_1538233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538233).length < 2 ^ (prefixWord ++ tailWord_1538233).sum := by decide
  have hdescent : baseEnd_1538233 < baseStart_1538233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538263 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 1, 5, 3]
def baseStart_1538263 : Nat := 118140960795 + 1538263 * 2 ^ 59
def prefixEnd_1538263 : Nat := 4983230072969 + 3 ^ 40 * 1538263 * 2
def baseEnd_1538263 : Nat := 789868292027220272638163

theorem tailTrace_1538263 : CollatzResearch.WordTrace tailWord_1538263 prefixEnd_1538263 789868292027220272638163 := by
  unfold tailWord_1538263
  simp only [CollatzResearch.WordTrace]
  refine ⟨56105060826143340249747443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37403373884095560166498295 56105060826143340249747443)
  ·
    refine ⟨84157591239215010374621165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56105060826143340249747443 84157591239215010374621165)
    ·
      refine ⟨31559096714705628890482937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84157591239215010374621165 31559096714705628890482937)
      ·
        refine ⟨23669322536029221667862203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31559096714705628890482937 23669322536029221667862203)
        ·
          refine ⟨35503983804043832501793305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23669322536029221667862203 35503983804043832501793305)
          ·
            refine ⟨26627987853032874376344979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35503983804043832501793305 26627987853032874376344979)
            ·
              refine ⟨39941981779549311564517469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26627987853032874376344979 39941981779549311564517469)
              ·
                refine ⟨14978243167330991836694051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39941981779549311564517469 14978243167330991836694051)
                ·
                  refine ⟨22467364750996487755041077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14978243167330991836694051 22467364750996487755041077)
                  ·
                    refine ⟨2106315445405920727035101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22467364750996487755041077 2106315445405920727035101)
                    ·
                      refine ⟨789868292027220272638163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2106315445405920727035101 789868292027220272638163)
                      ·
                        rfl

theorem cell23_1538263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_1538263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538263 prefixEnd_1538263 := by exact prefixLift 1538263
  have htrace : WordTrace (prefixWord ++ tailWord_1538263) baseStart_1538263 baseEnd_1538263 := by
    simpa [prefixWord, tailWord_1538263, baseEnd_1538263] using wordTrace_append hprefix tailTrace_1538263
  have hstable : (prefixWord ++ tailWord_1538263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538263).length < 2 ^ (prefixWord ++ tailWord_1538263).sum := by decide
  have hdescent : baseEnd_1538263 < baseStart_1538263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538264 : List Nat := [2, 1, 2, 2, 4, 2, 1, 3, 2, 2, 2]
def baseStart_1538264 : Nat := 118140960795 + 1538264 * 2 ^ 59
def prefixEnd_1538264 : Nat := 4983230072969 + 3 ^ 40 * 1538264 * 2
def baseEnd_1538264 : Nat := 789868805507874768725659

theorem tailTrace_1538264 : CollatzResearch.WordTrace tailWord_1538264 prefixEnd_1538264 789868805507874768725659 := by
  unfold tailWord_1538264
  simp only [CollatzResearch.WordTrace]
  refine ⟨28052548649569858710266923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37403398199426478280355897 28052548649569858710266923)
  ·
    refine ⟨42078822974354788065400385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28052548649569858710266923 42078822974354788065400385)
    ·
      refine ⟨31559117230766091049050289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42078822974354788065400385 31559117230766091049050289)
      ·
        refine ⟨23669337923074568286787717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31559117230766091049050289 23669337923074568286787717)
        ·
          refine ⟨4438000860576481553772697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23669337923074568286787717 4438000860576481553772697)
          ·
            refine ⟨3328500645432361165329523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4438000860576481553772697 3328500645432361165329523)
            ·
              refine ⟨4992750968148541747994285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3328500645432361165329523 4992750968148541747994285)
              ·
                refine ⟨1872281613055703155497857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4992750968148541747994285 1872281613055703155497857)
                ·
                  refine ⟨1404211209791777366623393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1872281613055703155497857 1404211209791777366623393)
                  ·
                    refine ⟨1053158407343833024967545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1404211209791777366623393 1053158407343833024967545)
                    ·
                      refine ⟨789868805507874768725659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1053158407343833024967545 789868805507874768725659)
                      ·
                        rfl

theorem cell23_1538264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 2, 2, 2].length) (baseStart_1538264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538264 prefixEnd_1538264 := by exact prefixLift 1538264
  have htrace : WordTrace (prefixWord ++ tailWord_1538264) baseStart_1538264 baseEnd_1538264 := by
    simpa [prefixWord, tailWord_1538264, baseEnd_1538264] using wordTrace_append hprefix tailTrace_1538264
  have hstable : (prefixWord ++ tailWord_1538264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538264).length < 2 ^ (prefixWord ++ tailWord_1538264).sum := by decide
  have hdescent : baseEnd_1538264 < baseStart_1538264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538268 : List Nat := [2, 2, 5, 2, 1, 2, 1, 2, 1, 3, 2]
def baseStart_1538268 : Nat := 118140960795 + 1538268 * 2 ^ 59
def prefixEnd_1538268 : Nat := 4983230072969 + 3 ^ 40 * 1538268 * 2
def baseEnd_1538268 : Nat := 789870859430492753075641

theorem tailTrace_1538268 : CollatzResearch.WordTrace tailWord_1538268 prefixEnd_1538268 789870859430492753075641 := by
  unfold tailWord_1538268
  simp only [CollatzResearch.WordTrace]
  refine ⟨28052621595562613051839729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37403495460750150735786305 28052621595562613051839729)
  ·
    refine ⟨21039466196671959788879797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28052621595562613051839729 21039466196671959788879797)
    ·
      refine ⟨1972449955937996230207481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21039466196671959788879797 1972449955937996230207481)
      ·
        refine ⟨1479337466953497172655611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1972449955937996230207481 1479337466953497172655611)
        ·
          refine ⟨2219006200430245758983417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1479337466953497172655611 2219006200430245758983417)
          ·
            refine ⟨1664254650322684319237563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2219006200430245758983417 1664254650322684319237563)
            ·
              refine ⟨2496381975484026478856345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1664254650322684319237563 2496381975484026478856345)
              ·
                refine ⟨1872286481613019859142259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2496381975484026478856345 1872286481613019859142259)
                ·
                  refine ⟨2808429722419529788713389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1872286481613019859142259 2808429722419529788713389)
                  ·
                    refine ⟨1053161145907323670767521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2808429722419529788713389 1053161145907323670767521)
                    ·
                      refine ⟨789870859430492753075641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1053161145907323670767521 789870859430492753075641)
                      ·
                        rfl

theorem cell23_1538268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_1538268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538268 prefixEnd_1538268 := by exact prefixLift 1538268
  have htrace : WordTrace (prefixWord ++ tailWord_1538268) baseStart_1538268 baseEnd_1538268 := by
    simpa [prefixWord, tailWord_1538268, baseEnd_1538268] using wordTrace_append hprefix tailTrace_1538268
  have hstable : (prefixWord ++ tailWord_1538268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538268).length < 2 ^ (prefixWord ++ tailWord_1538268).sum := by decide
  have hdescent : baseEnd_1538268 < baseStart_1538268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538300 : List Nat := [2, 2, 2, 1, 4, 1, 2, 2, 2, 5]
def baseStart_1538300 : Nat := 118140960795 + 1538300 * 2 ^ 59
def prefixEnd_1538300 : Nat := 4983230072969 + 3 ^ 40 * 1538300 * 2
def baseEnd_1538300 : Nat := 263295763603812209291831

theorem tailTrace_1538300 : CollatzResearch.WordTrace tailWord_1538300 prefixEnd_1538300 263295763603812209291831 := by
  unfold tailWord_1538300
  simp only [CollatzResearch.WordTrace]
  refine ⟨28053205163504647784422177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37404273551339530379229569 28053205163504647784422177)
  ·
    refine ⟨21039903872628485838316633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28053205163504647784422177 21039903872628485838316633)
    ·
      refine ⟨15779927904471364378737475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21039903872628485838316633 15779927904471364378737475)
      ·
        refine ⟨23669891856707046568106213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15779927904471364378737475 23669891856707046568106213)
        ·
          refine ⟨4438104723132571231519915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23669891856707046568106213 4438104723132571231519915)
          ·
            refine ⟨6657157084698856847279873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4438104723132571231519915 6657157084698856847279873)
            ·
              refine ⟨4992867813524142635459905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6657157084698856847279873 4992867813524142635459905)
              ·
                refine ⟨3744650860143106976594929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4992867813524142635459905 3744650860143106976594929)
                ·
                  refine ⟨2808488145107330232446197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3744650860143106976594929 2808488145107330232446197)
                  ·
                    refine ⟨263295763603812209291831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2808488145107330232446197 263295763603812209291831)
                    ·
                      rfl

theorem cell23_1538300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_1538300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538300 prefixEnd_1538300 := by exact prefixLift 1538300
  have htrace : WordTrace (prefixWord ++ tailWord_1538300) baseStart_1538300 baseEnd_1538300 := by
    simpa [prefixWord, tailWord_1538300, baseEnd_1538300] using wordTrace_append hprefix tailTrace_1538300
  have hstable : (prefixWord ++ tailWord_1538300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538300).length < 2 ^ (prefixWord ++ tailWord_1538300).sum := by decide
  have hdescent : baseEnd_1538300 < baseStart_1538300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538334 : List Nat := [4, 3, 2, 1, 1, 1, 3, 1, 2, 5]
def baseStart_1538334 : Nat := 118140960795 + 1538334 * 2 ^ 59
def prefixEnd_1538334 : Nat := 4983230072969 + 3 ^ 40 * 1538334 * 2
def baseEnd_1538334 : Nat := 263301583051229831616779

theorem tailTrace_1538334 : CollatzResearch.WordTrace tailWord_1538334 prefixEnd_1538334 263301583051229831616779 := by
  unfold tailWord_1538334
  simp only [CollatzResearch.WordTrace]
  refine ⟨7013456301110764921947757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37405100272590746250388037 7013456301110764921947757)
  ·
    refine ⟨2630046112916536845730409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7013456301110764921947757 2630046112916536845730409)
    ·
      refine ⟨1972534584687402634297807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2630046112916536845730409 1972534584687402634297807)
      ·
        refine ⟨2958801877031103951446711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1972534584687402634297807 2958801877031103951446711)
        ·
          refine ⟨4438202815546655927170067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2958801877031103951446711 4438202815546655927170067)
          ·
            refine ⟨6657304223319983890755101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4438202815546655927170067 6657304223319983890755101)
            ·
              refine ⟨2496489083744993959033163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6657304223319983890755101 2496489083744993959033163)
              ·
                refine ⟨3744733625617490938549745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2496489083744993959033163 3744733625617490938549745)
                ·
                  refine ⟨2808550219213118203912309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3744733625617490938549745 2808550219213118203912309)
                  ·
                    refine ⟨263301583051229831616779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2808550219213118203912309 263301583051229831616779)
                    ·
                      rfl

theorem cell23_1538334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_1538334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538334 prefixEnd_1538334 := by exact prefixLift 1538334
  have htrace : WordTrace (prefixWord ++ tailWord_1538334) baseStart_1538334 baseEnd_1538334 := by
    simpa [prefixWord, tailWord_1538334, baseEnd_1538334] using wordTrace_append hprefix tailTrace_1538334
  have hstable : (prefixWord ++ tailWord_1538334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538334).length < 2 ^ (prefixWord ++ tailWord_1538334).sum := by decide
  have hdescent : baseEnd_1538334 < baseStart_1538334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538360 : List Nat := [2, 1, 2, 1, 3, 1, 5, 2, 6]
def baseStart_1538360 : Nat := 118140960795 + 1538360 * 2 ^ 59
def prefixEnd_1538360 : Nat := 4983230072969 + 3 ^ 40 * 1538360 * 2
def baseEnd_1538360 : Nat := 87768677738967377013913

theorem tailTrace_1538360 : CollatzResearch.WordTrace tailWord_1538360 prefixEnd_1538360 87768677738967377013913 := by
  unfold tailWord_1538360
  simp only [CollatzResearch.WordTrace]
  refine ⟨28054299353395962908014267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37405732471194617210685689 28054299353395962908014267)
  ·
    refine ⟨42081449030093944362021401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28054299353395962908014267 42081449030093944362021401)
    ·
      refine ⟨31561086772570458271516051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42081449030093944362021401 31561086772570458271516051)
      ·
        refine ⟨47341630158855687407274077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31561086772570458271516051 47341630158855687407274077)
        ·
          refine ⟨17753111309570882777727779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47341630158855687407274077 17753111309570882777727779)
          ·
            refine ⟨26629666964356324166591669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17753111309570882777727779 26629666964356324166591669)
            ·
              refine ⟨2496531277908405390617969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26629666964356324166591669 2496531277908405390617969)
              ·
                refine ⟨1872398458431304042963477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2496531277908405390617969 1872398458431304042963477)
                ·
                  refine ⟨87768677738967377013913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1872398458431304042963477 87768677738967377013913)
                  ·
                    rfl

theorem cell23_1538360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 6].length) (baseStart_1538360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538360 prefixEnd_1538360 := by exact prefixLift 1538360
  have htrace : WordTrace (prefixWord ++ tailWord_1538360) baseStart_1538360 baseEnd_1538360 := by
    simpa [prefixWord, tailWord_1538360, baseEnd_1538360] using wordTrace_append hprefix tailTrace_1538360
  have hstable : (prefixWord ++ tailWord_1538360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538360).length < 2 ^ (prefixWord ++ tailWord_1538360).sum := by decide
  have hdescent : baseEnd_1538360 < baseStart_1538360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538407 : List Nat := [1, 1, 5, 1, 3, 1, 2, 3, 1, 5]
def baseStart_1538407 : Nat := 118140960795 + 1538407 * 2 ^ 59
def prefixEnd_1538407 : Nat := 4983230072969 + 3 ^ 40 * 1538407 * 2
def baseEnd_1538407 : Nat := 263314077747155903079167

theorem tailTrace_1538407 : CollatzResearch.WordTrace tailWord_1538407 prefixEnd_1538407 263314077747155903079167 := by
  unfold tailWord_1538407
  simp only [CollatzResearch.WordTrace]
  refine ⟨56110312937621652842989475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37406875291747768561992983 56110312937621652842989475)
  ·
    refine ⟨84165469406432479264484213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56110312937621652842989475 84165469406432479264484213)
    ·
      refine ⟨7890512756853044931045395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84165469406432479264484213 7890512756853044931045395)
      ·
        refine ⟨11835769135279567396568093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7890512756853044931045395 11835769135279567396568093)
        ·
          refine ⟨4438413425729837773713035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11835769135279567396568093 4438413425729837773713035)
          ·
            refine ⟨6657620138594756660569553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4438413425729837773713035 6657620138594756660569553)
            ·
              refine ⟨4993215103946067495427165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6657620138594756660569553 4993215103946067495427165)
              ·
                refine ⟨1872455663979775310785187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4993215103946067495427165 1872455663979775310785187)
                ·
                  refine ⟨2808683495969662966177781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1872455663979775310785187 2808683495969662966177781)
                  ·
                    refine ⟨263314077747155903079167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2808683495969662966177781 263314077747155903079167)
                    ·
                      rfl

theorem cell23_1538407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_1538407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538407 prefixEnd_1538407 := by exact prefixLift 1538407
  have htrace : WordTrace (prefixWord ++ tailWord_1538407) baseStart_1538407 baseEnd_1538407 := by
    simpa [prefixWord, tailWord_1538407, baseEnd_1538407] using wordTrace_append hprefix tailTrace_1538407
  have hstable : (prefixWord ++ tailWord_1538407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538407).length < 2 ^ (prefixWord ++ tailWord_1538407).sum := by decide
  have hdescent : baseEnd_1538407 < baseStart_1538407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538421 : List Nat := [1, 3, 4, 1, 2, 3, 1, 1, 3, 1, 3]
def baseStart_1538421 : Nat := 118140960795 + 1538421 * 2 ^ 59
def prefixEnd_1538421 : Nat := 4983230072969 + 3 ^ 40 * 1538421 * 2
def baseEnd_1538421 : Nat := 789949421970630654462437

theorem tailTrace_1538421 : CollatzResearch.WordTrace tailWord_1538421 prefixEnd_1538421 789949421970630654462437 := by
  unfold tailWord_1538421
  simp only [CollatzResearch.WordTrace]
  refine ⟨56110823559570933233999117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37407215706380622155999411 56110823559570933233999117)
  ·
    refine ⟨21041558834839099962749669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56110823559570933233999117 21041558834839099962749669)
    ·
      refine ⟨3945292281532331243015563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21041558834839099962749669 3945292281532331243015563)
      ·
        refine ⟨5917938422298496864523345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3945292281532331243015563 5917938422298496864523345)
        ·
          refine ⟨4438453816723872648392509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5917938422298496864523345 4438453816723872648392509)
          ·
            refine ⟨1664420181271452243147191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4438453816723872648392509 1664420181271452243147191)
            ·
              refine ⟨2496630271907178364720787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1664420181271452243147191 2496630271907178364720787)
              ·
                refine ⟨3744945407860767547081181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2496630271907178364720787 3744945407860767547081181)
                ·
                  refine ⟨1404354527947787830155443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3744945407860767547081181 1404354527947787830155443)
                  ·
                    refine ⟨2106531791921681745233165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1404354527947787830155443 2106531791921681745233165)
                    ·
                      refine ⟨789949421970630654462437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2106531791921681745233165 789949421970630654462437)
                      ·
                        rfl

theorem cell23_1538421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_1538421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538421 prefixEnd_1538421 := by exact prefixLift 1538421
  have htrace : WordTrace (prefixWord ++ tailWord_1538421) baseStart_1538421 baseEnd_1538421 := by
    simpa [prefixWord, tailWord_1538421, baseEnd_1538421] using wordTrace_append hprefix tailTrace_1538421
  have hstable : (prefixWord ++ tailWord_1538421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538421).length < 2 ^ (prefixWord ++ tailWord_1538421).sum := by decide
  have hdescent : baseEnd_1538421 < baseStart_1538421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538440 : List Nat := [2, 1, 3, 3, 1, 1, 1, 3, 1, 1, 6]
def baseStart_1538440 : Nat := 118140960795 + 1538440 * 2 ^ 59
def prefixEnd_1538440 : Nat := 4983230072969 + 3 ^ 40 * 1538440 * 2
def baseEnd_1538440 : Nat := 789959178103066080124849

theorem tailTrace_1538440 : CollatzResearch.WordTrace tailWord_1538440 prefixEnd_1538440 789959178103066080124849 := by
  unfold tailWord_1538440
  simp only [CollatzResearch.WordTrace]
  refine ⟨28055758273251049739470387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37407677697668066319293849 28055758273251049739470387)
  ·
    refine ⟨42083637409876574609205581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28055758273251049739470387 42083637409876574609205581)
    ·
      refine ⟨15781364028703715478452093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42083637409876574609205581 15781364028703715478452093)
      ·
        refine ⟨5918011510763893304419535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15781364028703715478452093 5918011510763893304419535)
        ·
          refine ⟨8877017266145839956629303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5918011510763893304419535 8877017266145839956629303)
          ·
            refine ⟨13315525899218759934943955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8877017266145839956629303 13315525899218759934943955)
            ·
              refine ⟨19973288848828139902415933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13315525899218759934943955 19973288848828139902415933)
              ·
                refine ⟨7489983318310552463405975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19973288848828139902415933 7489983318310552463405975)
                ·
                  refine ⟨11234974977465828695108963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7489983318310552463405975 11234974977465828695108963)
                  ·
                    refine ⟨16852462466198743042663445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11234974977465828695108963 16852462466198743042663445)
                    ·
                      refine ⟨789959178103066080124849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16852462466198743042663445 789959178103066080124849)
                      ·
                        rfl

theorem cell23_1538440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_1538440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538440 prefixEnd_1538440 := by exact prefixLift 1538440
  have htrace : WordTrace (prefixWord ++ tailWord_1538440) baseStart_1538440 baseEnd_1538440 := by
    simpa [prefixWord, tailWord_1538440, baseEnd_1538440] using wordTrace_append hprefix tailTrace_1538440
  have hstable : (prefixWord ++ tailWord_1538440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538440).length < 2 ^ (prefixWord ++ tailWord_1538440).sum := by decide
  have hdescent : baseEnd_1538440 < baseStart_1538440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538444 : List Nat := [2, 2, 1, 2, 1, 6, 1, 2, 1, 1, 4]
def baseStart_1538444 : Nat := 118140960795 + 1538444 * 2 ^ 59
def prefixEnd_1538444 : Nat := 4983230072969 + 3 ^ 40 * 1538444 * 2
def baseEnd_1538444 : Nat := 789961232025684064474831

theorem tailTrace_1538444 : CollatzResearch.WordTrace tailWord_1538444 prefixEnd_1538444 789961232025684064474831 := by
  unfold tailWord_1538444
  simp only [CollatzResearch.WordTrace]
  refine ⟨28055831219243804081043193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37407774958991738774724257 28055831219243804081043193)
  ·
    refine ⟨21041873414432853060782395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28055831219243804081043193 21041873414432853060782395)
    ·
      refine ⟨31562810121649279591173593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21041873414432853060782395 31562810121649279591173593)
      ·
        refine ⟨23672107591236959693380195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31562810121649279591173593 23672107591236959693380195)
        ·
          refine ⟨35508161386855439540070293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23672107591236959693380195 35508161386855439540070293)
          ·
            refine ⟨1664445065008848728440795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35508161386855439540070293 1664445065008848728440795)
            ·
              refine ⟨2496667597513273092661193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1664445065008848728440795 2496667597513273092661193)
              ·
                refine ⟨1872500698134954819495895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2496667597513273092661193 1872500698134954819495895)
                ·
                  refine ⟨2808751047202432229243843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1872500698134954819495895 2808751047202432229243843)
                  ·
                    refine ⟨4213126570803648343865765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2808751047202432229243843 4213126570803648343865765)
                    ·
                      refine ⟨789961232025684064474831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4213126570803648343865765 789961232025684064474831)
                      ·
                        rfl

theorem cell23_1538444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_1538444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538444 prefixEnd_1538444 := by exact prefixLift 1538444
  have htrace : WordTrace (prefixWord ++ tailWord_1538444) baseStart_1538444 baseEnd_1538444 := by
    simpa [prefixWord, tailWord_1538444, baseEnd_1538444] using wordTrace_append hprefix tailTrace_1538444
  have hstable : (prefixWord ++ tailWord_1538444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538444).length < 2 ^ (prefixWord ++ tailWord_1538444).sum := by decide
  have hdescent : baseEnd_1538444 < baseStart_1538444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538461 : List Nat := [1, 4, 2, 1, 4, 1, 3, 1, 1, 1, 4]
def baseStart_1538461 : Nat := 118140960795 + 1538461 * 2 ^ 59
def prefixEnd_1538461 : Nat := 4983230072969 + 3 ^ 40 * 1538461 * 2
def baseEnd_1538461 : Nat := 789969961196810497962253

theorem tailTrace_1538461 : CollatzResearch.WordTrace tailWord_1538461 prefixEnd_1538461 789969961196810497962253 := by
  unfold tailWord_1538461
  simp only [CollatzResearch.WordTrace]
  refine ⟨56112282479426020065455237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37408188319617346710303491 56112282479426020065455237)
  ·
    refine ⟨10521052964892378762272857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56112282479426020065455237 10521052964892378762272857)
    ·
      refine ⟨7890789723669284071704643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10521052964892378762272857 7890789723669284071704643)
      ·
        refine ⟨11836184585503926107556965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7890789723669284071704643 11836184585503926107556965)
        ·
          refine ⟨2219284609781986145166931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11836184585503926107556965 2219284609781986145166931)
          ·
            refine ⟨3328926914672979217750397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2219284609781986145166931 3328926914672979217750397)
            ·
              refine ⟨1248347593002367206656399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3328926914672979217750397 1248347593002367206656399)
              ·
                refine ⟨1872521389503550809984599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1248347593002367206656399 1872521389503550809984599)
                ·
                  refine ⟨2808782084255326214976899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1872521389503550809984599 2808782084255326214976899)
                  ·
                    refine ⟨4213173126382989322465349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2808782084255326214976899 4213173126382989322465349)
                    ·
                      refine ⟨789969961196810497962253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4213173126382989322465349 789969961196810497962253)
                      ·
                        rfl

theorem cell23_1538461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_1538461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538461 prefixEnd_1538461 := by exact prefixLift 1538461
  have htrace : WordTrace (prefixWord ++ tailWord_1538461) baseStart_1538461 baseEnd_1538461 := by
    simpa [prefixWord, tailWord_1538461, baseEnd_1538461] using wordTrace_append hprefix tailTrace_1538461
  have hstable : (prefixWord ++ tailWord_1538461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538461).length < 2 ^ (prefixWord ++ tailWord_1538461).sum := by decide
  have hdescent : baseEnd_1538461 < baseStart_1538461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538504 : List Nat := [2, 1, 3, 1, 3, 2, 2, 1, 3, 3, 2]
def baseStart_1538504 : Nat := 118140960795 + 1538504 * 2 ^ 59
def prefixEnd_1538504 : Nat := 4983230072969 + 3 ^ 40 * 1538504 * 2
def baseEnd_1538504 : Nat := 789992040864953829724555

theorem tailTrace_1538504 : CollatzResearch.WordTrace tailWord_1538504 prefixEnd_1538504 789992040864953829724555 := by
  unfold tailWord_1538504
  simp only [CollatzResearch.WordTrace]
  refine ⟨28056925409135119204635283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37409233878846825606180377 28056925409135119204635283)
  ·
    refine ⟨42085388113702678806952925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28056925409135119204635283 42085388113702678806952925)
    ·
      refine ⟨15782020542638504552607347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42085388113702678806952925 15782020542638504552607347)
      ·
        refine ⟨23673030813957756828911021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15782020542638504552607347 23673030813957756828911021)
        ·
          refine ⟨8877386555234158810841633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23673030813957756828911021 8877386555234158810841633)
          ·
            refine ⟨6658039916425619108131225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8877386555234158810841633 6658039916425619108131225)
            ·
              refine ⟨4993529937319214331098419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6658039916425619108131225 4993529937319214331098419)
              ·
                refine ⟨7490294905978821496647629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4993529937319214331098419 7490294905978821496647629)
                ·
                  refine ⟨2808860589742058061242861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7490294905978821496647629 2808860589742058061242861)
                  ·
                    refine ⟨1053322721153271772966073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2808860589742058061242861 1053322721153271772966073)
                    ·
                      refine ⟨789992040864953829724555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1053322721153271772966073 789992040864953829724555)
                      ·
                        rfl

theorem cell23_1538504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 3, 3, 2].length) (baseStart_1538504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538504 prefixEnd_1538504 := by exact prefixLift 1538504
  have htrace : WordTrace (prefixWord ++ tailWord_1538504) baseStart_1538504 baseEnd_1538504 := by
    simpa [prefixWord, tailWord_1538504, baseEnd_1538504] using wordTrace_append hprefix tailTrace_1538504
  have hstable : (prefixWord ++ tailWord_1538504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538504).length < 2 ^ (prefixWord ++ tailWord_1538504).sum := by decide
  have hdescent : baseEnd_1538504 < baseStart_1538504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538510 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 3, 8]
def baseStart_1538510 : Nat := 118140960795 + 1538510 * 2 ^ 59
def prefixEnd_1538510 : Nat := 4983230072969 + 3 ^ 40 * 1538510 * 2
def baseEnd_1538510 : Nat := 263331707249626935416509

theorem tailTrace_1538510 : CollatzResearch.WordTrace tailWord_1538510 prefixEnd_1538510 263331707249626935416509 := by
  unfold tailWord_1538510
  simp only [CollatzResearch.WordTrace]
  refine ⟨7014258707031062679248623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37409379770832334289325989 7014258707031062679248623)
  ·
    refine ⟨10521388060546594018872935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7014258707031062679248623 10521388060546594018872935)
    ·
      refine ⟨15782082090819891028309403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10521388060546594018872935 15782082090819891028309403)
      ·
        refine ⟨23673123136229836542464105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15782082090819891028309403 23673123136229836542464105)
        ·
          refine ⟨17754842352172377406848079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23673123136229836542464105 17754842352172377406848079)
          ·
            refine ⟨26632263528258566110272119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17754842352172377406848079 26632263528258566110272119)
            ·
              refine ⟨39948395292387849165408179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26632263528258566110272119 39948395292387849165408179)
              ·
                refine ⟨59922592938581773748112269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39948395292387849165408179 59922592938581773748112269)
                ·
                  refine ⟨22470972351968165155542101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59922592938581773748112269 22470972351968165155542101)
                  ·
                    refine ⟨263331707249626935416509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 22470972351968165155542101 263331707249626935416509)
                    ·
                      rfl

theorem cell23_1538510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_1538510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538510 prefixEnd_1538510 := by exact prefixLift 1538510
  have htrace : WordTrace (prefixWord ++ tailWord_1538510) baseStart_1538510 baseEnd_1538510 := by
    simpa [prefixWord, tailWord_1538510, baseEnd_1538510] using wordTrace_append hprefix tailTrace_1538510
  have hstable : (prefixWord ++ tailWord_1538510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538510).length < 2 ^ (prefixWord ++ tailWord_1538510).sum := by decide
  have hdescent : baseEnd_1538510 < baseStart_1538510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538520 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 1, 3, 5]
def baseStart_1538520 : Nat := 118140960795 + 1538520 * 2 ^ 59
def prefixEnd_1538520 : Nat := 4983230072969 + 3 ^ 40 * 1538520 * 2
def baseEnd_1538520 : Nat := 790000256555425767124481

theorem tailTrace_1538520 : CollatzResearch.WordTrace tailWord_1538520 prefixEnd_1538520 790000256555425767124481 := by
  unfold tailWord_1538520
  simp only [CollatzResearch.WordTrace]
  refine ⟨28057217193106136570926507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37409622924141515427902009 28057217193106136570926507)
  ·
    refine ⟨42085825789659204856389761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28057217193106136570926507 42085825789659204856389761)
    ·
      refine ⟨31564369342244403642292321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42085825789659204856389761 31564369342244403642292321)
      ·
        refine ⟨23673277006683302731719241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31564369342244403642292321 23673277006683302731719241)
        ·
          refine ⟨17754957755012477048789431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23673277006683302731719241 17754957755012477048789431)
          ·
            refine ⟨26632436632518715573184147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17754957755012477048789431 26632436632518715573184147)
            ·
              refine ⟨39948654948778073359776221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26632436632518715573184147 39948654948778073359776221)
              ·
                refine ⟨14980745605791777509916083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39948654948778073359776221 14980745605791777509916083)
                ·
                  refine ⟨22471118408687666264874125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14980745605791777509916083 22471118408687666264874125)
                  ·
                    refine ⟨8426669403257874849327797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22471118408687666264874125 8426669403257874849327797)
                    ·
                      refine ⟨790000256555425767124481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8426669403257874849327797 790000256555425767124481)
                      ·
                        rfl

theorem cell23_1538520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_1538520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538520 prefixEnd_1538520 := by exact prefixLift 1538520
  have htrace : WordTrace (prefixWord ++ tailWord_1538520) baseStart_1538520 baseEnd_1538520 := by
    simpa [prefixWord, tailWord_1538520, baseEnd_1538520] using wordTrace_append hprefix tailTrace_1538520
  have hstable : (prefixWord ++ tailWord_1538520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538520).length < 2 ^ (prefixWord ++ tailWord_1538520).sum := by decide
  have hdescent : baseEnd_1538520 < baseStart_1538520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538594 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 2, 5, 2]
def baseStart_1538594 : Nat := 118140960795 + 1538594 * 2 ^ 59
def prefixEnd_1538594 : Nat := 4983230072969 + 3 ^ 40 * 1538594 * 2
def baseEnd_1538594 : Nat := 790038254123858477599141

theorem tailTrace_1538594 : CollatzResearch.WordTrace tailWord_1538594 prefixEnd_1538594 790038254123858477599141 := by
  unfold tailWord_1538594
  simp only [CollatzResearch.WordTrace]
  refine ⟨14029283346986045945011709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37411422258629455853364557 14029283346986045945011709)
  ·
    refine ⟨5260981255119767229379391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14029283346986045945011709 5260981255119767229379391)
    ·
      refine ⟨7891471882679650844069087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5260981255119767229379391 7891471882679650844069087)
      ·
        refine ⟨11837207824019476266103631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7891471882679650844069087 11837207824019476266103631)
        ·
          refine ⟨17755811736029214399155447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11837207824019476266103631 17755811736029214399155447)
          ·
            refine ⟨26633717604043821598733171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17755811736029214399155447 26633717604043821598733171)
            ·
              refine ⟨39950576406065732398099757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26633717604043821598733171 39950576406065732398099757)
              ·
                refine ⟨14981466152274649649287409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39950576406065732398099757 14981466152274649649287409)
                ·
                  refine ⟨11236099614205987236965557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14981466152274649649287409 11236099614205987236965557)
                  ·
                    refine ⟨1053384338831811303465521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11236099614205987236965557 1053384338831811303465521)
                    ·
                      refine ⟨790038254123858477599141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1053384338831811303465521 790038254123858477599141)
                      ·
                        rfl

theorem cell23_1538594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_1538594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538594 prefixEnd_1538594 := by exact prefixLift 1538594
  have htrace : WordTrace (prefixWord ++ tailWord_1538594) baseStart_1538594 baseEnd_1538594 := by
    simpa [prefixWord, tailWord_1538594, baseEnd_1538594] using wordTrace_append hprefix tailTrace_1538594
  have hstable : (prefixWord ++ tailWord_1538594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538594).length < 2 ^ (prefixWord ++ tailWord_1538594).sum := by decide
  have hdescent : baseEnd_1538594 < baseStart_1538594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538627 : List Nat := [1, 1, 1, 3, 1, 2, 1, 5, 1, 4, 3]
def baseStart_1538627 : Nat := 118140960795 + 1538627 * 2 ^ 59
def prefixEnd_1538627 : Nat := 4983230072969 + 3 ^ 40 * 1538627 * 2
def baseEnd_1538627 : Nat := 790055198985456848486489

theorem tailTrace_1538627 : CollatzResearch.WordTrace tailWord_1538627 prefixEnd_1538627 790055198985456848486489 := by
  unfold tailWord_1538627
  simp only [CollatzResearch.WordTrace]
  refine ⟨56118336996824630415998135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37412224664549753610665423 56118336996824630415998135)
  ·
    refine ⟨84177505495236945623997203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56118336996824630415998135 84177505495236945623997203)
    ·
      refine ⟨126266258242855418435995805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84177505495236945623997203 126266258242855418435995805)
      ·
        refine ⟨47349846841070781913498427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126266258242855418435995805 47349846841070781913498427)
        ·
          refine ⟨71024770261606172870247641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47349846841070781913498427 71024770261606172870247641)
          ·
            refine ⟨53268577696204629652685731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71024770261606172870247641 53268577696204629652685731)
            ·
              refine ⟨79902866544306944479028597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53268577696204629652685731 79902866544306944479028597)
              ·
                refine ⟨7490893738528776044908931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79902866544306944479028597 7490893738528776044908931)
                ·
                  refine ⟨11236340607793164067363397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7490893738528776044908931 11236340607793164067363397)
                  ·
                    refine ⟨2106813863961218262630637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11236340607793164067363397 2106813863961218262630637)
                    ·
                      refine ⟨790055198985456848486489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2106813863961218262630637 790055198985456848486489)
                      ·
                        rfl

theorem cell23_1538627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 4, 3].length) (baseStart_1538627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538627 prefixEnd_1538627 := by exact prefixLift 1538627
  have htrace : WordTrace (prefixWord ++ tailWord_1538627) baseStart_1538627 baseEnd_1538627 := by
    simpa [prefixWord, tailWord_1538627, baseEnd_1538627] using wordTrace_append hprefix tailTrace_1538627
  have hstable : (prefixWord ++ tailWord_1538627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538627).length < 2 ^ (prefixWord ++ tailWord_1538627).sum := by decide
  have hdescent : baseEnd_1538627 < baseStart_1538627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538698 : List Nat := [3, 1, 2, 3, 4, 1, 1, 2, 6]
def baseStart_1538698 : Nat := 118140960795 + 1538698 * 2 ^ 59
def prefixEnd_1538698 : Nat := 4983230072969 + 3 ^ 40 * 1538698 * 2
def baseEnd_1538698 : Nat := 87787961790214007855407

theorem tailTrace_1538698 : CollatzResearch.WordTrace tailWord_1538698 prefixEnd_1538698 87787961790214007855407 := by
  unfold tailWord_1538698
  simp only [CollatzResearch.WordTrace]
  refine ⟨14030231644891852385458187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37413951053044939694555165 14030231644891852385458187)
  ·
    refine ⟨21045347467337778578187281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14030231644891852385458187 21045347467337778578187281)
    ·
      refine ⟨15784010600503333933640461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21045347467337778578187281 15784010600503333933640461)
      ·
        refine ⟨5919003975188750225115173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15784010600503333933640461 5919003975188750225115173)
        ·
          refine ⟨1109813245347890667209095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5919003975188750225115173 1109813245347890667209095)
          ·
            refine ⟨1664719868021836000813643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1109813245347890667209095 1664719868021836000813643)
            ·
              refine ⟨2497079802032754001220465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1664719868021836000813643 2497079802032754001220465)
              ·
                refine ⟨1872809851524565500915349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2497079802032754001220465 1872809851524565500915349)
                ·
                  refine ⟨87787961790214007855407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1872809851524565500915349 87787961790214007855407)
                  ·
                    rfl

theorem cell23_1538698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 6].length) (baseStart_1538698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538698 prefixEnd_1538698 := by exact prefixLift 1538698
  have htrace : WordTrace (prefixWord ++ tailWord_1538698) baseStart_1538698 baseEnd_1538698 := by
    simpa [prefixWord, tailWord_1538698, baseEnd_1538698] using wordTrace_append hprefix tailTrace_1538698
  have hstable : (prefixWord ++ tailWord_1538698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538698).length < 2 ^ (prefixWord ++ tailWord_1538698).sum := by decide
  have hdescent : baseEnd_1538698 < baseStart_1538698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538708 : List Nat := [2, 4, 2, 2, 1, 1, 1, 3, 3, 1, 3]
def baseStart_1538708 : Nat := 118140960795 + 1538708 * 2 ^ 59
def prefixEnd_1538708 : Nat := 4983230072969 + 3 ^ 40 * 1538708 * 2
def baseEnd_1538708 : Nat := 790096790918471031573617

theorem tailTrace_1538708 : CollatzResearch.WordTrace tailWord_1538708 prefixEnd_1538708 790096790918471031573617 := by
  unfold tailWord_1538708
  simp only [CollatzResearch.WordTrace]
  refine ⟨28060645654765590624848389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37414194206354120833131185 28060645654765590624848389)
  ·
    refine ⟨5261371060268548242159073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28060645654765590624848389 5261371060268548242159073)
    ·
      refine ⟨3946028295201411181619305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5261371060268548242159073 3946028295201411181619305)
      ·
        refine ⟨2959521221401058386214479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3946028295201411181619305 2959521221401058386214479)
        ·
          refine ⟨4439281832101587579321719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2959521221401058386214479 4439281832101587579321719)
          ·
            refine ⟨6658922748152381368982579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4439281832101587579321719 6658922748152381368982579)
            ·
              refine ⟨9988384122228572053473869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6658922748152381368982579 9988384122228572053473869)
              ·
                refine ⟨3745644045835714520052701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9988384122228572053473869 3745644045835714520052701)
                ·
                  refine ⟨1404616517188392945019763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3745644045835714520052701 1404616517188392945019763)
                  ·
                    refine ⟨2106924775782589417529645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1404616517188392945019763 2106924775782589417529645)
                    ·
                      refine ⟨790096790918471031573617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2106924775782589417529645 790096790918471031573617)
                      ·
                        rfl

theorem cell23_1538708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_1538708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538708 prefixEnd_1538708 := by exact prefixLift 1538708
  have htrace : WordTrace (prefixWord ++ tailWord_1538708) baseStart_1538708 baseEnd_1538708 := by
    simpa [prefixWord, tailWord_1538708, baseEnd_1538708] using wordTrace_append hprefix tailTrace_1538708
  have hstable : (prefixWord ++ tailWord_1538708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538708).length < 2 ^ (prefixWord ++ tailWord_1538708).sum := by decide
  have hdescent : baseEnd_1538708 < baseStart_1538708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538741 : List Nat := [1, 3, 3, 3, 1, 1, 1, 2, 4, 4]
def baseStart_1538741 : Nat := 118140960795 + 1538741 * 2 ^ 59
def prefixEnd_1538741 : Nat := 4983230072969 + 3 ^ 40 * 1538741 * 2
def baseEnd_1538741 : Nat := 263371245260023134153655

theorem tailTrace_1538741 : CollatzResearch.WordTrace tailWord_1538741 prefixEnd_1538741 263371245260023134153655 := by
  unfold tailWord_1538741
  simp only [CollatzResearch.WordTrace]
  refine ⟨56122494918411627885648077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37414996612274418590432051 56122494918411627885648077)
  ·
    refine ⟨21045935594404360457118029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56122494918411627885648077 21045935594404360457118029)
    ·
      refine ⟨7892225847901635171419261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21045935594404360457118029 7892225847901635171419261)
      ·
        refine ⟨2959584692963113189282223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7892225847901635171419261 2959584692963113189282223)
        ·
          refine ⟨4439377039444669783923335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2959584692963113189282223 4439377039444669783923335)
          ·
            refine ⟨6659065559167004675885003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4439377039444669783923335 6659065559167004675885003)
            ·
              refine ⟨9988598338750507013827505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6659065559167004675885003 9988598338750507013827505)
              ·
                refine ⟨7491448754062880260370629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9988598338750507013827505 7491448754062880260370629)
                ·
                  refine ⟨1404646641386790048819493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7491448754062880260370629 1404646641386790048819493)
                  ·
                    refine ⟨263371245260023134153655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1404646641386790048819493 263371245260023134153655)
                    ·
                      rfl

theorem cell23_1538741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_1538741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538741 prefixEnd_1538741 := by exact prefixLift 1538741
  have htrace : WordTrace (prefixWord ++ tailWord_1538741) baseStart_1538741 baseEnd_1538741 := by
    simpa [prefixWord, tailWord_1538741, baseEnd_1538741] using wordTrace_append hprefix tailTrace_1538741
  have hstable : (prefixWord ++ tailWord_1538741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538741).length < 2 ^ (prefixWord ++ tailWord_1538741).sum := by decide
  have hdescent : baseEnd_1538741 < baseStart_1538741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538751 : List Nat := [1, 1, 2, 2, 2, 4, 2, 3, 1, 2, 3]
def baseStart_1538751 : Nat := 118140960795 + 1538751 * 2 ^ 59
def prefixEnd_1538751 : Nat := 4983230072969 + 3 ^ 40 * 1538751 * 2
def baseEnd_1538751 : Nat := 790118870586614363335919

theorem tailTrace_1538751 : CollatzResearch.WordTrace tailWord_1538751 prefixEnd_1538751 790118870586614363335919 := by
  unfold tailWord_1538751
  simp only [CollatzResearch.WordTrace]
  refine ⟨56122859648375399593512107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37415239765583599729008071 56122859648375399593512107)
  ·
    refine ⟨84184289472563099390268161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56122859648375399593512107 84184289472563099390268161)
    ·
      refine ⟨63138217104422324542701121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84184289472563099390268161 63138217104422324542701121)
      ·
        refine ⟨47353662828316743407025841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63138217104422324542701121 47353662828316743407025841)
        ·
          refine ⟨35515247121237557555269381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47353662828316743407025841 35515247121237557555269381)
          ·
            refine ⟨6659108835232042041613009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35515247121237557555269381 6659108835232042041613009)
            ·
              refine ⟨4994331626424031531209757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6659108835232042041613009 4994331626424031531209757)
              ·
                refine ⟨1872874359909011824203659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4994331626424031531209757 1872874359909011824203659)
                ·
                  refine ⟨2809311539863517736305489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1872874359909011824203659 2809311539863517736305489)
                  ·
                    refine ⟨2106983654897638302229117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2809311539863517736305489 2106983654897638302229117)
                    ·
                      refine ⟨790118870586614363335919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2106983654897638302229117 790118870586614363335919)
                      ·
                        rfl

theorem cell23_1538751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 2, 3].length) (baseStart_1538751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538751 prefixEnd_1538751 := by exact prefixLift 1538751
  have htrace : WordTrace (prefixWord ++ tailWord_1538751) baseStart_1538751 baseEnd_1538751 := by
    simpa [prefixWord, tailWord_1538751, baseEnd_1538751] using wordTrace_append hprefix tailTrace_1538751
  have hstable : (prefixWord ++ tailWord_1538751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538751).length < 2 ^ (prefixWord ++ tailWord_1538751).sum := by decide
  have hdescent : baseEnd_1538751 < baseStart_1538751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538757 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 4, 2, 6]
def baseStart_1538757 : Nat := 118140960795 + 1538757 * 2 ^ 59
def prefixEnd_1538757 : Nat := 4983230072969 + 3 ^ 40 * 1538757 * 2
def baseEnd_1538757 : Nat := 790121951470541339860891

theorem tailTrace_1538757 : CollatzResearch.WordTrace tailWord_1538757 prefixEnd_1538757 790121951470541339860891 := by
  unfold tailWord_1538757
  simp only [CollatzResearch.WordTrace]
  refine ⟨56123078486353662618230525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37415385657569108412153683 56123078486353662618230525)
  ·
    refine ⟨21046154432382623481836447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56123078486353662618230525 21046154432382623481836447)
    ·
      refine ⟨31569231648573935222754671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21046154432382623481836447 31569231648573935222754671)
      ·
        refine ⟨47353847472860902834132007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31569231648573935222754671 47353847472860902834132007)
        ·
          refine ⟨71030771209291354251198011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47353847472860902834132007 71030771209291354251198011)
          ·
            refine ⟨106546156813937031376797017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71030771209291354251198011 106546156813937031376797017)
            ·
              refine ⟨79909617610452773532597763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106546156813937031376797017 79909617610452773532597763)
              ·
                refine ⟨119864426415679160298896645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79909617610452773532597763 119864426415679160298896645)
                ·
                  refine ⟨22474579952939842556043121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119864426415679160298896645 22474579952939842556043121)
                  ·
                    refine ⟨16855934964704881917032341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22474579952939842556043121 16855934964704881917032341)
                    ·
                      refine ⟨790121951470541339860891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16855934964704881917032341 790121951470541339860891)
                      ·
                        rfl

theorem cell23_1538757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_1538757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538757 prefixEnd_1538757 := by exact prefixLift 1538757
  have htrace : WordTrace (prefixWord ++ tailWord_1538757) baseStart_1538757 baseEnd_1538757 := by
    simpa [prefixWord, tailWord_1538757, baseEnd_1538757] using wordTrace_append hprefix tailTrace_1538757
  have hstable : (prefixWord ++ tailWord_1538757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538757).length < 2 ^ (prefixWord ++ tailWord_1538757).sum := by decide
  have hdescent : baseEnd_1538757 < baseStart_1538757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538844 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 9]
def baseStart_1538844 : Nat := 118140960795 + 1538844 * 2 ^ 59
def prefixEnd_1538844 : Nat := 4983230072969 + 3 ^ 40 * 1538844 * 2
def baseEnd_1538844 : Nat := 87796291587498055496999

theorem tailTrace_1538844 : CollatzResearch.WordTrace tailWord_1538844 prefixEnd_1538844 87796291587498055496999 := by
  unfold tailWord_1538844
  simp only [CollatzResearch.WordTrace]
  refine ⟨28063125818519238238323793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37417501091358984317765057 28063125818519238238323793)
  ·
    refine ⟨21047344363889428678742845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28063125818519238238323793 21047344363889428678742845)
    ·
      refine ⟨7892754136458535754528567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21047344363889428678742845 7892754136458535754528567)
      ·
        refine ⟨11839131204687803631792851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7892754136458535754528567 11839131204687803631792851)
        ·
          refine ⟨17758696807031705447689277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11839131204687803631792851 17758696807031705447689277)
          ·
            refine ⟨6659511302636889542883479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17758696807031705447689277 6659511302636889542883479)
            ·
              refine ⟨9989266953955334314325219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6659511302636889542883479 9989266953955334314325219)
              ·
                refine ⟨14983900430933001471487829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9989266953955334314325219 14983900430933001471487829)
                ·
                  refine ⟨87796291587498055496999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14983900430933001471487829 87796291587498055496999)
                  ·
                    rfl

theorem cell23_1538844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 9].length) (baseStart_1538844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538844 prefixEnd_1538844 := by exact prefixLift 1538844
  have htrace : WordTrace (prefixWord ++ tailWord_1538844) baseStart_1538844 baseEnd_1538844 := by
    simpa [prefixWord, tailWord_1538844, baseEnd_1538844] using wordTrace_append hprefix tailTrace_1538844
  have hstable : (prefixWord ++ tailWord_1538844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538844).length < 2 ^ (prefixWord ++ tailWord_1538844).sum := by decide
  have hdescent : baseEnd_1538844 < baseStart_1538844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538878 : List Nat := [4, 2, 1, 2, 3, 1, 2, 1, 7]
def baseStart_1538878 : Nat := 118140960795 + 1538878 * 2 ^ 59
def prefixEnd_1538878 : Nat := 4983230072969 + 3 ^ 40 * 1538878 * 2
def baseEnd_1538878 : Nat := 87798231403303929605315

theorem tailTrace_1538878 : CollatzResearch.WordTrace tailWord_1538878 prefixEnd_1538878 87798231403303929605315 := by
  unfold tailWord_1538878
  simp only [CollatzResearch.WordTrace]
  refine ⟨7015936464864412535423161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37418327812610200188923525 7015936464864412535423161)
  ·
    refine ⟨5261952348648309401567371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7015936464864412535423161 5261952348648309401567371)
    ·
      refine ⟨7892928522972464102351057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5261952348648309401567371 7892928522972464102351057)
      ·
        refine ⟨5919696392229348076763293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7892928522972464102351057 5919696392229348076763293)
        ·
          refine ⟨2219886147086005528786235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5919696392229348076763293 2219886147086005528786235)
          ·
            refine ⟨3329829220629008293179353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2219886147086005528786235 3329829220629008293179353)
            ·
              refine ⟨2497371915471756219884515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3329829220629008293179353 2497371915471756219884515)
              ·
                refine ⟨3746057873207634329826773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2497371915471756219884515 3746057873207634329826773)
                ·
                  refine ⟨87798231403303929605315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3746057873207634329826773 87798231403303929605315)
                  ·
                    rfl

theorem cell23_1538878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_1538878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538878 prefixEnd_1538878 := by exact prefixLift 1538878
  have htrace : WordTrace (prefixWord ++ tailWord_1538878) baseStart_1538878 baseEnd_1538878 := by
    simpa [prefixWord, tailWord_1538878, baseEnd_1538878] using wordTrace_append hprefix tailTrace_1538878
  have hstable : (prefixWord ++ tailWord_1538878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538878).length < 2 ^ (prefixWord ++ tailWord_1538878).sum := by decide
  have hdescent : baseEnd_1538878 < baseStart_1538878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538911 : List Nat := [1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 4]
def baseStart_1538911 : Nat := 118140960795 + 1538911 * 2 ^ 59
def prefixEnd_1538911 : Nat := 4983230072969 + 3 ^ 40 * 1538911 * 2
def baseEnd_1538911 : Nat := 790201027491333737335183

theorem tailTrace_1538911 : CollatzResearch.WordTrace tailWord_1538911 prefixEnd_1538911 790201027491333737335183 := by
  unfold tailWord_1538911
  simp only [CollatzResearch.WordTrace]
  refine ⟨56128695327795746919336587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37419130218530497946224391 56128695327795746919336587)
  ·
    refine ⟨84193042991693620379004881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56128695327795746919336587 84193042991693620379004881)
    ·
      refine ⟨63144782243770215284253661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84193042991693620379004881 63144782243770215284253661)
      ·
        refine ⟨23679293341413830731595123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63144782243770215284253661 23679293341413830731595123)
        ·
          refine ⟨35518940012120746097392685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23679293341413830731595123 35518940012120746097392685)
          ·
            refine ⟨13319602504545279786522257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35518940012120746097392685 13319602504545279786522257)
            ·
              refine ⟨9989701878408959839891693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13319602504545279786522257 9989701878408959839891693)
              ·
                refine ⟨3746138204403359939959385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9989701878408959839891693 3746138204403359939959385)
                ·
                  refine ⟨2809603653302519954969539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3746138204403359939959385 2809603653302519954969539)
                  ·
                    refine ⟨4214405479953779932454309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2809603653302519954969539 4214405479953779932454309)
                    ·
                      refine ⟨790201027491333737335183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4214405479953779932454309 790201027491333737335183)
                      ·
                        rfl

theorem cell23_1538911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_1538911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538911 prefixEnd_1538911 := by exact prefixLift 1538911
  have htrace : WordTrace (prefixWord ++ tailWord_1538911) baseStart_1538911 baseEnd_1538911 := by
    simpa [prefixWord, tailWord_1538911, baseEnd_1538911] using wordTrace_append hprefix tailTrace_1538911
  have hstable : (prefixWord ++ tailWord_1538911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538911).length < 2 ^ (prefixWord ++ tailWord_1538911).sum := by decide
  have hdescent : baseEnd_1538911 < baseStart_1538911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538931 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 4, 2, 3]
def baseStart_1538931 : Nat := 118140960795 + 1538931 * 2 ^ 59
def prefixEnd_1538931 : Nat := 4983230072969 + 3 ^ 40 * 1538931 * 2
def baseEnd_1538931 : Nat := 790211297104423659085091

theorem tailTrace_1538931 : CollatzResearch.WordTrace tailWord_1538931 prefixEnd_1538931 790211297104423659085091 := by
  unfold tailWord_1538931
  simp only [CollatzResearch.WordTrace]
  refine ⟨56129424787723290335064647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37419616525148860223376431 56129424787723290335064647)
  ·
    refine ⟨84194137181584935502596971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56129424787723290335064647 84194137181584935502596971)
    ·
      refine ⟨126291205772377403253895457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84194137181584935502596971 126291205772377403253895457)
      ·
        refine ⟨94718404329283052440421593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126291205772377403253895457 94718404329283052440421593)
        ·
          refine ⟨71038803246962289330316195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94718404329283052440421593 71038803246962289330316195)
          ·
            refine ⟨106558204870443433995474293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71038803246962289330316195 106558204870443433995474293)
            ·
              refine ⟨9989831706604071937075715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106558204870443433995474293 9989831706604071937075715)
              ·
                refine ⟨14984747559906107905613573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9989831706604071937075715 14984747559906107905613573)
                ·
                  refine ⟨2809640167482395232302545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14984747559906107905613573 2809640167482395232302545)
                  ·
                    refine ⟨2107230125611796424226909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2809640167482395232302545 2107230125611796424226909)
                    ·
                      refine ⟨790211297104423659085091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2107230125611796424226909 790211297104423659085091)
                      ·
                        rfl

theorem cell23_1538931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 2, 3].length) (baseStart_1538931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538931 prefixEnd_1538931 := by exact prefixLift 1538931
  have htrace : WordTrace (prefixWord ++ tailWord_1538931) baseStart_1538931 baseEnd_1538931 := by
    simpa [prefixWord, tailWord_1538931, baseEnd_1538931] using wordTrace_append hprefix tailTrace_1538931
  have hstable : (prefixWord ++ tailWord_1538931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538931).length < 2 ^ (prefixWord ++ tailWord_1538931).sum := by decide
  have hdescent : baseEnd_1538931 < baseStart_1538931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538989 : List Nat := [1, 5, 2, 3, 1, 1, 1, 4, 1, 4]
def baseStart_1538989 : Nat := 118140960795 + 1538989 * 2 ^ 59
def prefixEnd_1538989 : Nat := 4983230072969 + 3 ^ 40 * 1538989 * 2
def baseEnd_1538989 : Nat := 263413692994128144053275

theorem tailTrace_1538989 : CollatzResearch.WordTrace tailWord_1538989 prefixEnd_1538989 263413692994128144053275 := by
  unfold tailWord_1538989
  simp only [CollatzResearch.WordTrace]
  refine ⟨56131540221513166240676021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37421026814342110827117347 56131540221513166240676021)
  ·
    refine ⟨5262331895766859335063377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56131540221513166240676021 5262331895766859335063377)
    ·
      refine ⟨3946748921825144501297533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5262331895766859335063377 3946748921825144501297533)
      ·
        refine ⟨1480030845684429187986575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3946748921825144501297533 1480030845684429187986575)
        ·
          refine ⟨2220046268526643781979863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1480030845684429187986575 2220046268526643781979863)
          ·
            refine ⟨3330069402789965672969795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2220046268526643781979863 3330069402789965672969795)
            ·
              refine ⟨4995104104184948509454693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3330069402789965672969795 4995104104184948509454693)
              ·
                refine ⟨936582019534677845522755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4995104104184948509454693 936582019534677845522755)
                ·
                  refine ⟨1404873029302016768284133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 936582019534677845522755 1404873029302016768284133)
                  ·
                    refine ⟨263413692994128144053275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1404873029302016768284133 263413692994128144053275)
                    ·
                      rfl

theorem cell23_1538989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_1538989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538989 prefixEnd_1538989 := by exact prefixLift 1538989
  have htrace : WordTrace (prefixWord ++ tailWord_1538989) baseStart_1538989 baseEnd_1538989 := by
    simpa [prefixWord, tailWord_1538989, baseEnd_1538989] using wordTrace_append hprefix tailTrace_1538989
  have hstable : (prefixWord ++ tailWord_1538989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538989).length < 2 ^ (prefixWord ++ tailWord_1538989).sum := by decide
  have hdescent : baseEnd_1538989 < baseStart_1538989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539018 : List Nat := [3, 1, 2, 1, 2, 1, 1, 6, 1, 1, 4]
def baseStart_1539018 : Nat := 118140960795 + 1539018 * 2 ^ 59
def prefixEnd_1539018 : Nat := 4983230072969 + 3 ^ 40 * 1539018 * 2
def baseEnd_1539018 : Nat := 790255969921364818697191

theorem tailTrace_1539018 : CollatzResearch.WordTrace tailWord_1539018 prefixEnd_1539018 790255969921364818697191 := by
  unfold tailWord_1539018
  simp only [CollatzResearch.WordTrace]
  refine ⟨14033149484602026048370427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37421731958938736128987805 14033149484602026048370427)
  ·
    refine ⟨21049724226903039072555641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14033149484602026048370427 21049724226903039072555641)
    ·
      refine ⟨15787293170177279304416731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21049724226903039072555641 15787293170177279304416731)
      ·
        refine ⟨23680939755265918956625097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15787293170177279304416731 23680939755265918956625097)
        ·
          refine ⟨17760704816449439217468823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23680939755265918956625097 17760704816449439217468823)
          ·
            refine ⟨26641057224674158826203235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17760704816449439217468823 26641057224674158826203235)
            ·
              refine ⟨39961585837011238239304853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26641057224674158826203235 39961585837011238239304853)
              ·
                refine ⟨1873199336109901792467415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39961585837011238239304853 1873199336109901792467415)
                ·
                  refine ⟨2809799004164852688701123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1873199336109901792467415 2809799004164852688701123)
                  ·
                    refine ⟨4214698506247279033051685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2809799004164852688701123 4214698506247279033051685)
                    ·
                      refine ⟨790255969921364818697191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4214698506247279033051685 790255969921364818697191)
                      ·
                        rfl

theorem cell23_1539018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_1539018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539018 prefixEnd_1539018 := by exact prefixLift 1539018
  have htrace : WordTrace (prefixWord ++ tailWord_1539018) baseStart_1539018 baseEnd_1539018 := by
    simpa [prefixWord, tailWord_1539018, baseEnd_1539018] using wordTrace_append hprefix tailTrace_1539018
  have hstable : (prefixWord ++ tailWord_1539018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539018).length < 2 ^ (prefixWord ++ tailWord_1539018).sum := by decide
  have hdescent : baseEnd_1539018 < baseStart_1539018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539022 : List Nat := [4, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2]
def baseStart_1539022 : Nat := 118140960795 + 1539022 * 2 ^ 59
def prefixEnd_1539022 : Nat := 4983230072969 + 3 ^ 40 * 1539022 * 2
def baseEnd_1539022 : Nat := 790258023843982803047173

theorem tailTrace_1539022 : CollatzResearch.WordTrace tailWord_1539022 prefixEnd_1539022 790258023843982803047173 := by
  unfold tailWord_1539022
  simp only [CollatzResearch.WordTrace]
  refine ⟨7016592978799201609578415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37421829220262408584418213 7016592978799201609578415)
  ·
    refine ⟨10524889468198802414367623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7016592978799201609578415 10524889468198802414367623)
    ·
      refine ⟨15787334202298203621551435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10524889468198802414367623 15787334202298203621551435)
      ·
        refine ⟨23681001303447305432327153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15787334202298203621551435 23681001303447305432327153)
        ·
          refine ⟨17760750977585479074245365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23681001303447305432327153 17760750977585479074245365)
          ·
            refine ⟨1665070404148638663210503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17760750977585479074245365 1665070404148638663210503)
            ·
              refine ⟨2497605606222957994815755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1665070404148638663210503 2497605606222957994815755)
              ·
                refine ⟨3746408409334436992223633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2497605606222957994815755 3746408409334436992223633)
                ·
                  refine ⟨2809806307000827744167725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3746408409334436992223633 2809806307000827744167725)
                  ·
                    refine ⟨1053677365125310404062897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2809806307000827744167725 1053677365125310404062897)
                    ·
                      refine ⟨790258023843982803047173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1053677365125310404062897 790258023843982803047173)
                      ·
                        rfl

theorem cell23_1539022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2].length) (baseStart_1539022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539022 prefixEnd_1539022 := by exact prefixLift 1539022
  have htrace : WordTrace (prefixWord ++ tailWord_1539022) baseStart_1539022 baseEnd_1539022 := by
    simpa [prefixWord, tailWord_1539022, baseEnd_1539022] using wordTrace_append hprefix tailTrace_1539022
  have hstable : (prefixWord ++ tailWord_1539022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539022).length < 2 ^ (prefixWord ++ tailWord_1539022).sum := by decide
  have hdescent : baseEnd_1539022 < baseStart_1539022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539028 : List Nat := [2, 4, 1, 2, 1, 2, 2, 2, 1, 6]
def baseStart_1539028 : Nat := 118140960795 + 1539028 * 2 ^ 59
def prefixEnd_1539028 : Nat := 4983230072969 + 3 ^ 40 * 1539028 * 2
def baseEnd_1539028 : Nat := 263420368242636593190715

theorem tailTrace_1539028 : CollatzResearch.WordTrace tailWord_1539028 prefixEnd_1539028 263420368242636593190715 := by
  unfold tailWord_1539028
  simp only [CollatzResearch.WordTrace]
  refine ⟨28066481334185937950672869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37421975112247917267563825 28066481334185937950672869)
  ·
    refine ⟨5262465250159863365751163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28066481334185937950672869 5262465250159863365751163)
    ·
      refine ⟨7893697875239795048626745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5262465250159863365751163 7893697875239795048626745)
      ·
        refine ⟨5920273406429846286470059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7893697875239795048626745 5920273406429846286470059)
        ·
          refine ⟨8880410109644769429705089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5920273406429846286470059 8880410109644769429705089)
          ·
            refine ⟨6660307582233577072278817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8880410109644769429705089 6660307582233577072278817)
            ·
              refine ⟨4995230686675182804209113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6660307582233577072278817 4995230686675182804209113)
              ·
                refine ⟨3746423015006387103156835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4995230686675182804209113 3746423015006387103156835)
                ·
                  refine ⟨5619634522509580654735253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3746423015006387103156835 5619634522509580654735253)
                  ·
                    refine ⟨263420368242636593190715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5619634522509580654735253 263420368242636593190715)
                    ·
                      rfl

theorem cell23_1539028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_1539028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539028 prefixEnd_1539028 := by exact prefixLift 1539028
  have htrace : WordTrace (prefixWord ++ tailWord_1539028) baseStart_1539028 baseEnd_1539028 := by
    simpa [prefixWord, tailWord_1539028, baseEnd_1539028] using wordTrace_append hprefix tailTrace_1539028
  have hstable : (prefixWord ++ tailWord_1539028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539028).length < 2 ^ (prefixWord ++ tailWord_1539028).sum := by decide
  have hdescent : baseEnd_1539028 < baseStart_1539028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539029 : List Nat := [1, 3, 2, 3, 3, 1, 2, 3, 1, 1, 3]
def baseStart_1539029 : Nat := 118140960795 + 1539029 * 2 ^ 59
def prefixEnd_1539029 : Nat := 4983230072969 + 3 ^ 40 * 1539029 * 2
def baseEnd_1539029 : Nat := 790261618208564275659641

theorem tailTrace_1539029 : CollatzResearch.WordTrace tailWord_1539029 prefixEnd_1539029 790261618208564275659641 := by
  unfold tailWord_1539029
  simp only [CollatzResearch.WordTrace]
  refine ⟨56132999141368253072132141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37421999427578835381421427 56132999141368253072132141)
  ·
    refine ⟨21049874678013094902049553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56132999141368253072132141 21049874678013094902049553)
    ·
      refine ⟨15787406008509821176537165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21049874678013094902049553 15787406008509821176537165)
      ·
        refine ⟨5920277253191182941201437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15787406008509821176537165 5920277253191182941201437)
        ·
          refine ⟨2220103969946693602950539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5920277253191182941201437 2220103969946693602950539)
          ·
            refine ⟨3330155954920040404425809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2220103969946693602950539 3330155954920040404425809)
            ·
              refine ⟨2497616966190030303319357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3330155954920040404425809 2497616966190030303319357)
              ·
                refine ⟨936606362321261363744759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2497616966190030303319357 936606362321261363744759)
                ·
                  refine ⟨1404909543481892045617139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 936606362321261363744759 1404909543481892045617139)
                  ·
                    refine ⟨2107364315222838068425709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1404909543481892045617139 2107364315222838068425709)
                    ·
                      refine ⟨790261618208564275659641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2107364315222838068425709 790261618208564275659641)
                      ·
                        rfl

theorem cell23_1539029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_1539029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539029 prefixEnd_1539029 := by exact prefixLift 1539029
  have htrace : WordTrace (prefixWord ++ tailWord_1539029) baseStart_1539029 baseEnd_1539029 := by
    simpa [prefixWord, tailWord_1539029, baseEnd_1539029] using wordTrace_append hprefix tailTrace_1539029
  have hstable : (prefixWord ++ tailWord_1539029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539029).length < 2 ^ (prefixWord ++ tailWord_1539029).sum := by decide
  have hdescent : baseEnd_1539029 < baseStart_1539029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539031 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 4]
def baseStart_1539031 : Nat := 118140960795 + 1539031 * 2 ^ 59
def prefixEnd_1539031 : Nat := 4983230072969 + 3 ^ 40 * 1539031 * 2
def baseEnd_1539031 : Nat := 790262645169873267834631

theorem tailTrace_1539031 : CollatzResearch.WordTrace tailWord_1539031 prefixEnd_1539031 790262645169873267834631 := by
  unfold tailWord_1539031
  simp only [CollatzResearch.WordTrace]
  refine ⟨56133072087361007413704947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37422048058240671609136631 56133072087361007413704947)
  ·
    refine ⟨84199608131041511120557421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56133072087361007413704947 84199608131041511120557421)
    ·
      refine ⟨31574853049140566670209033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84199608131041511120557421 31574853049140566670209033)
      ·
        refine ⟨23681139786855425002656775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31574853049140566670209033 23681139786855425002656775)
        ·
          refine ⟨35521709680283137503985163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23681139786855425002656775 35521709680283137503985163)
          ·
            refine ⟨53282564520424706255977745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35521709680283137503985163 53282564520424706255977745)
            ·
              refine ⟨39961923390318529691983309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53282564520424706255977745 39961923390318529691983309)
              ·
                refine ⟨14985721271369448634493741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39961923390318529691983309 14985721271369448634493741)
                ·
                  refine ⟨5619645476763543237935153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14985721271369448634493741 5619645476763543237935153)
                  ·
                    refine ⟨4214734107572657428451365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5619645476763543237935153 4214734107572657428451365)
                    ·
                      refine ⟨790262645169873267834631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4214734107572657428451365 790262645169873267834631)
                      ·
                        rfl

theorem cell23_1539031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_1539031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539031 prefixEnd_1539031 := by exact prefixLift 1539031
  have htrace : WordTrace (prefixWord ++ tailWord_1539031) baseStart_1539031 baseEnd_1539031 := by
    simpa [prefixWord, tailWord_1539031, baseEnd_1539031] using wordTrace_append hprefix tailTrace_1539031
  have hstable : (prefixWord ++ tailWord_1539031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539031).length < 2 ^ (prefixWord ++ tailWord_1539031).sum := by decide
  have hdescent : baseEnd_1539031 < baseStart_1539031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539051 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 2, 7, 3]
def baseStart_1539051 : Nat := 118140960795 + 1539051 * 2 ^ 59
def prefixEnd_1539051 : Nat := 4983230072969 + 3 ^ 40 * 1539051 * 2
def baseEnd_1539051 : Nat := 790272914782963189584539

theorem tailTrace_1539051 : CollatzResearch.WordTrace tailWord_1539051 prefixEnd_1539051 790272914782963189584539 := by
  unfold tailWord_1539051
  simp only [CollatzResearch.WordTrace]
  refine ⟨56133801547288550829433007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37422534364859033886288671 56133801547288550829433007)
  ·
    refine ⟨84200702320932826244149511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56133801547288550829433007 84200702320932826244149511)
    ·
      refine ⟨126301053481399239366224267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84200702320932826244149511 126301053481399239366224267)
      ·
        refine ⟨189451580222098859049336401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126301053481399239366224267 189451580222098859049336401)
        ·
          refine ⟨142088685166574144287002301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189451580222098859049336401 142088685166574144287002301)
          ·
            refine ⟨53283256937465304107625863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142088685166574144287002301 53283256937465304107625863)
            ·
              refine ⟨79924885406197956161438795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53283256937465304107625863 79924885406197956161438795)
              ·
                refine ⟨119887328109296934242158193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79924885406197956161438795 119887328109296934242158193)
                ·
                  refine ⟨89915496081972700681618645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119887328109296934242158193 89915496081972700681618645)
                  ·
                    refine ⟨2107394439421235172225437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 89915496081972700681618645 2107394439421235172225437)
                    ·
                      refine ⟨790272914782963189584539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2107394439421235172225437 790272914782963189584539)
                      ·
                        rfl

theorem cell23_1539051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 7, 3].length) (baseStart_1539051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539051 prefixEnd_1539051 := by exact prefixLift 1539051
  have htrace : WordTrace (prefixWord ++ tailWord_1539051) baseStart_1539051 baseEnd_1539051 := by
    simpa [prefixWord, tailWord_1539051, baseEnd_1539051] using wordTrace_append hprefix tailTrace_1539051
  have hstable : (prefixWord ++ tailWord_1539051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539051).length < 2 ^ (prefixWord ++ tailWord_1539051).sum := by decide
  have hdescent : baseEnd_1539051 < baseStart_1539051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539086 : List Nat := [4, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2]
def baseStart_1539086 : Nat := 118140960795 + 1539086 * 2 ^ 59
def prefixEnd_1539086 : Nat := 4983230072969 + 3 ^ 40 * 1539086 * 2
def baseEnd_1539086 : Nat := 790290886605870552646879

theorem tailTrace_1539086 : CollatzResearch.WordTrace tailWord_1539086 prefixEnd_1539086 790290886605870552646879 := by
  unfold tailWord_1539086
  simp only [CollatzResearch.WordTrace]
  refine ⟨7016884762770218975869639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37423385401441167871304741 7016884762770218975869639)
  ·
    refine ⟨10525327144155328463804459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7016884762770218975869639 10525327144155328463804459)
    ·
      refine ⟨15787990716232992695706689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10525327144155328463804459 15787990716232992695706689)
      ·
        refine ⟨11840993037174744521780017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15787990716232992695706689 11840993037174744521780017)
        ·
          refine ⟨8880744777881058391335013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11840993037174744521780017 8880744777881058391335013)
          ·
            refine ⟨1665139645852698448375315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8880744777881058391335013 1665139645852698448375315)
            ·
              refine ⟨2497709468779047672562973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1665139645852698448375315 2497709468779047672562973)
              ·
                refine ⟨936641050792142877211115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2497709468779047672562973 936641050792142877211115)
                ·
                  refine ⟨1404961576188214315816673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 936641050792142877211115 1404961576188214315816673)
                  ·
                    refine ⟨1053721182141160736862505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1404961576188214315816673 1053721182141160736862505)
                    ·
                      refine ⟨790290886605870552646879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1053721182141160736862505 790290886605870552646879)
                      ·
                        rfl

theorem cell23_1539086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_1539086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539086 prefixEnd_1539086 := by exact prefixLift 1539086
  have htrace : WordTrace (prefixWord ++ tailWord_1539086) baseStart_1539086 baseEnd_1539086 := by
    simpa [prefixWord, tailWord_1539086, baseEnd_1539086] using wordTrace_append hprefix tailTrace_1539086
  have hstable : (prefixWord ++ tailWord_1539086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539086).length < 2 ^ (prefixWord ++ tailWord_1539086).sum := by decide
  have hdescent : baseEnd_1539086 < baseStart_1539086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539091 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 4]
def baseStart_1539091 : Nat := 118140960795 + 1539091 * 2 ^ 59
def prefixEnd_1539091 : Nat := 4983230072969 + 3 ^ 40 * 1539091 * 2
def baseEnd_1539091 : Nat := 790293454009143033084355

theorem tailTrace_1539091 : CollatzResearch.WordTrace tailWord_1539091 prefixEnd_1539091 790293454009143033084355 := by
  unfold tailWord_1539091
  simp only [CollatzResearch.WordTrace]
  refine ⟨56135260467143637660889127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37423506978095758440592751 56135260467143637660889127)
  ·
    refine ⟨84202890700715456491333691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56135260467143637660889127 84202890700715456491333691)
    ·
      refine ⟨126304336051073184737000537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84202890700715456491333691 126304336051073184737000537)
      ·
        refine ⟨94728252038304888552750403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126304336051073184737000537 94728252038304888552750403)
        ·
          refine ⟨142092378057457332829125605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94728252038304888552750403 142092378057457332829125605)
          ·
            refine ⟨26642320885773249905461051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142092378057457332829125605 26642320885773249905461051)
            ·
              refine ⟨39963481328659874858191577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26642320885773249905461051 39963481328659874858191577)
              ·
                refine ⟨29972610996494906143643683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39963481328659874858191577 29972610996494906143643683)
                ·
                  refine ⟨44958916494742359215465525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29972610996494906143643683 44958916494742359215465525)
                  ·
                    refine ⟨4214898421382096176449893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44958916494742359215465525 4214898421382096176449893)
                    ·
                      refine ⟨790293454009143033084355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4214898421382096176449893 790293454009143033084355)
                      ·
                        rfl

theorem cell23_1539091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 4].length) (baseStart_1539091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539091 prefixEnd_1539091 := by exact prefixLift 1539091
  have htrace : WordTrace (prefixWord ++ tailWord_1539091) baseStart_1539091 baseEnd_1539091 := by
    simpa [prefixWord, tailWord_1539091, baseEnd_1539091] using wordTrace_append hprefix tailTrace_1539091
  have hstable : (prefixWord ++ tailWord_1539091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539091).length < 2 ^ (prefixWord ++ tailWord_1539091).sum := by decide
  have hdescent : baseEnd_1539091 < baseStart_1539091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539118 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 1, 8]
def baseStart_1539118 : Nat := 118140960795 + 1539118 * 2 ^ 59
def prefixEnd_1539118 : Nat := 4983230072969 + 3 ^ 40 * 1539118 * 2
def baseEnd_1539118 : Nat := 263435772662271475815577

theorem tailTrace_1539118 : CollatzResearch.WordTrace tailWord_1539118 prefixEnd_1539118 263435772662271475815577 := by
  unfold tailWord_1539118
  simp only [CollatzResearch.WordTrace]
  refine ⟨7017030654755727659015251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37424163492030547514748005 7017030654755727659015251)
  ·
    refine ⟨10525545982133591488522877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7017030654755727659015251 10525545982133591488522877)
    ·
      refine ⟨3947079743300096808196079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10525545982133591488522877 3947079743300096808196079)
      ·
        refine ⟨5920619614950145212294119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3947079743300096808196079 5920619614950145212294119)
        ·
          refine ⟨8880929422425217818441179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5920619614950145212294119 8880929422425217818441179)
          ·
            refine ⟨13321394133637826727661769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8880929422425217818441179 13321394133637826727661769)
            ·
              refine ⟨9991045600228370045746327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13321394133637826727661769 9991045600228370045746327)
              ·
                refine ⟨14986568400342555068619491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9991045600228370045746327 14986568400342555068619491)
                ·
                  refine ⟨22479852600513832602929237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14986568400342555068619491 22479852600513832602929237)
                  ·
                    refine ⟨263435772662271475815577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 22479852600513832602929237 263435772662271475815577)
                    ·
                      rfl

theorem cell23_1539118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_1539118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539118 prefixEnd_1539118 := by exact prefixLift 1539118
  have htrace : WordTrace (prefixWord ++ tailWord_1539118) baseStart_1539118 baseEnd_1539118 := by
    simpa [prefixWord, tailWord_1539118, baseEnd_1539118] using wordTrace_append hprefix tailTrace_1539118
  have hstable : (prefixWord ++ tailWord_1539118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539118).length < 2 ^ (prefixWord ++ tailWord_1539118).sum := by decide
  have hdescent : baseEnd_1539118 < baseStart_1539118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539125 : List Nat := [1, 3, 3, 1, 1, 1, 1, 5, 1, 4, 2]
def baseStart_1539125 : Nat := 118140960795 + 1539125 * 2 ^ 59
def prefixEnd_1539125 : Nat := 4983230072969 + 3 ^ 40 * 1539125 * 2
def baseEnd_1539125 : Nat := 790310912351395900059199

theorem tailTrace_1539125 : CollatzResearch.WordTrace tailWord_1539125 prefixEnd_1539125 790310912351395900059199 := by
  unfold tailWord_1539125
  simp only [CollatzResearch.WordTrace]
  refine ⟨56136500549020461467626829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37424333699346974311751219 56136500549020461467626829)
  ·
    refine ⟨21051187705882673050360061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56136500549020461467626829 21051187705882673050360061)
    ·
      refine ⟨7894195389706002393885023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21051187705882673050360061 7894195389706002393885023)
      ·
        refine ⟨11841293084559003590827535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7894195389706002393885023 11841293084559003590827535)
        ·
          refine ⟨17761939626838505386241303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11841293084559003590827535 17761939626838505386241303)
          ·
            refine ⟨26642909440257758079361955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17761939626838505386241303 26642909440257758079361955)
            ·
              refine ⟨39964364160386637119042933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26642909440257758079361955 39964364160386637119042933)
              ·
                refine ⟨3746659140036247229910275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39964364160386637119042933 3746659140036247229910275)
                ·
                  refine ⟨5619988710054370844865413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3746659140036247229910275 5619988710054370844865413)
                  ·
                    refine ⟨1053747883135194533412265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5619988710054370844865413 1053747883135194533412265)
                    ·
                      refine ⟨790310912351395900059199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1053747883135194533412265 790310912351395900059199)
                      ·
                        rfl

theorem cell23_1539125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_1539125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539125 prefixEnd_1539125 := by exact prefixLift 1539125
  have htrace : WordTrace (prefixWord ++ tailWord_1539125) baseStart_1539125 baseEnd_1539125 := by
    simpa [prefixWord, tailWord_1539125, baseEnd_1539125] using wordTrace_append hprefix tailTrace_1539125
  have hstable : (prefixWord ++ tailWord_1539125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539125).length < 2 ^ (prefixWord ++ tailWord_1539125).sum := by decide
  have hdescent : baseEnd_1539125 < baseStart_1539125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539128 : List Nat := [2, 1, 2, 1, 5, 1, 1, 2, 2, 1, 5]
def baseStart_1539128 : Nat := 118140960795 + 1539128 * 2 ^ 59
def prefixEnd_1539128 : Nat := 4983230072969 + 3 ^ 40 * 1539128 * 2
def baseEnd_1539128 : Nat := 790312452793359388321685

theorem tailTrace_1539128 : CollatzResearch.WordTrace tailWord_1539128 prefixEnd_1539128 790312452793359388321685 := by
  unfold tailWord_1539128
  simp only [CollatzResearch.WordTrace]
  refine ⟨28068304984004796489993019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37424406645339728653324025 28068304984004796489993019)
  ·
    refine ⟨42102457476007194734989529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28068304984004796489993019 42102457476007194734989529)
    ·
      refine ⟨31576843107005396051242147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42102457476007194734989529 31576843107005396051242147)
      ·
        refine ⟨47365264660508094076863221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31576843107005396051242147 47365264660508094076863221)
        ·
          refine ⟨4440493561922633819705927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47365264660508094076863221 4440493561922633819705927)
          ·
            refine ⟨6660740342883950729558891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4440493561922633819705927 6660740342883950729558891)
            ·
              refine ⟨9991110514325926094338337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6660740342883950729558891 9991110514325926094338337)
              ·
                refine ⟨7493332885744444570753753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9991110514325926094338337 7493332885744444570753753)
                ·
                  refine ⟨5619999664308333428065315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7493332885744444570753753 5619999664308333428065315)
                  ·
                    refine ⟨8429999496462500142097973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5619999664308333428065315 8429999496462500142097973)
                    ·
                      refine ⟨790312452793359388321685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8429999496462500142097973 790312452793359388321685)
                      ·
                        rfl

theorem cell23_1539128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_1539128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539128 prefixEnd_1539128 := by exact prefixLift 1539128
  have htrace : WordTrace (prefixWord ++ tailWord_1539128) baseStart_1539128 baseEnd_1539128 := by
    simpa [prefixWord, tailWord_1539128, baseEnd_1539128] using wordTrace_append hprefix tailTrace_1539128
  have hstable : (prefixWord ++ tailWord_1539128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539128).length < 2 ^ (prefixWord ++ tailWord_1539128).sum := by decide
  have hdescent : baseEnd_1539128 < baseStart_1539128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539129 : List Nat := [1, 2, 1, 5, 2, 3, 1, 2, 1, 3, 2]
def baseStart_1539129 : Nat := 118140960795 + 1539129 * 2 ^ 59
def prefixEnd_1539129 : Nat := 4983230072969 + 3 ^ 40 * 1539129 * 2
def baseEnd_1539129 : Nat := 790312966274013884409181

theorem tailTrace_1539129 : CollatzResearch.WordTrace tailWord_1539129 prefixEnd_1539129 790312966274013884409181 := by
  unfold tailWord_1539129
  simp only [CollatzResearch.WordTrace]
  refine ⟨56136646441005970150772441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37424430960670646767181627 56136646441005970150772441)
  ·
    refine ⟨42102484830754477613079331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56136646441005970150772441 42102484830754477613079331)
    ·
      refine ⟨63153727246131716419618997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42102484830754477613079331 63153727246131716419618997)
      ·
        refine ⟨5920661929324848414339281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63153727246131716419618997 5920661929324848414339281)
        ·
          refine ⟨4440496446993636310754461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5920661929324848414339281 4440496446993636310754461)
          ·
            refine ⟨1665186167622613616532923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4440496446993636310754461 1665186167622613616532923)
            ·
              refine ⟨2497779251433920424799385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1665186167622613616532923 2497779251433920424799385)
              ·
                refine ⟨1873334438575440318599539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2497779251433920424799385 1873334438575440318599539)
                ·
                  refine ⟨2810001657863160477899309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1873334438575440318599539 2810001657863160477899309)
                  ·
                    refine ⟨1053750621698685179212241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2810001657863160477899309 1053750621698685179212241)
                    ·
                      refine ⟨790312966274013884409181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1053750621698685179212241 790312966274013884409181)
                      ·
                        rfl

theorem cell23_1539129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_1539129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539129 prefixEnd_1539129 := by exact prefixLift 1539129
  have htrace : WordTrace (prefixWord ++ tailWord_1539129) baseStart_1539129 baseEnd_1539129 := by
    simpa [prefixWord, tailWord_1539129, baseEnd_1539129] using wordTrace_append hprefix tailTrace_1539129
  have hstable : (prefixWord ++ tailWord_1539129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539129).length < 2 ^ (prefixWord ++ tailWord_1539129).sum := by decide
  have hdescent : baseEnd_1539129 < baseStart_1539129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539151 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 6]
def baseStart_1539151 : Nat := 118140960795 + 1539151 * 2 ^ 59
def prefixEnd_1539151 : Nat := 4983230072969 + 3 ^ 40 * 1539151 * 2
def baseEnd_1539151 : Nat := 790324262848412798334079

theorem tailTrace_1539151 : CollatzResearch.WordTrace tailWord_1539151 prefixEnd_1539151 790324262848412798334079 := by
  unfold tailWord_1539151
  simp only [CollatzResearch.WordTrace]
  refine ⟨56137448846926267908073307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37424965897950845272048871 56137448846926267908073307)
  ·
    refine ⟨84206173270389401862109961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56137448846926267908073307 84206173270389401862109961)
    ·
      refine ⟨63154629952792051396582471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84206173270389401862109961 63154629952792051396582471)
      ·
        refine ⟨94731944929188077094873707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63154629952792051396582471 94731944929188077094873707)
        ·
          refine ⟨142097917393782115642310561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94731944929188077094873707 142097917393782115642310561)
          ·
            refine ⟨106573438045336586731732921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142097917393782115642310561 106573438045336586731732921)
            ·
              refine ⟨79930078534002440048799691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106573438045336586731732921 79930078534002440048799691)
              ·
                refine ⟨119895117801003660073199537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79930078534002440048799691 119895117801003660073199537)
                ·
                  refine ⟨89921338350752745054899653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119895117801003660073199537 89921338350752745054899653)
                  ·
                    refine ⟨16860250940766139697793685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89921338350752745054899653 16860250940766139697793685)
                    ·
                      refine ⟨790324262848412798334079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16860250940766139697793685 790324262848412798334079)
                      ·
                        rfl

theorem cell23_1539151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 6].length) (baseStart_1539151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539151 prefixEnd_1539151 := by exact prefixLift 1539151
  have htrace : WordTrace (prefixWord ++ tailWord_1539151) baseStart_1539151 baseEnd_1539151 := by
    simpa [prefixWord, tailWord_1539151, baseEnd_1539151] using wordTrace_append hprefix tailTrace_1539151
  have hstable : (prefixWord ++ tailWord_1539151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539151).length < 2 ^ (prefixWord ++ tailWord_1539151).sum := by decide
  have hdescent : baseEnd_1539151 < baseStart_1539151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539175 : List Nat := [1, 1, 5, 1, 1, 4, 1, 1, 2, 3, 3]
def baseStart_1539175 : Nat := 118140960795 + 1539175 * 2 ^ 59
def prefixEnd_1539175 : Nat := 4983230072969 + 3 ^ 40 * 1539175 * 2
def baseEnd_1539175 : Nat := 790336586384120704433969

theorem tailTrace_1539175 : CollatzResearch.WordTrace tailWord_1539175 prefixEnd_1539175 790336586384120704433969 := by
  unfold tailWord_1539175
  simp only [CollatzResearch.WordTrace]
  refine ⟨56138324198839320006946979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37425549465892880004631319 56138324198839320006946979)
  ·
    refine ⟨84207486298258980010420469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56138324198839320006946979 84207486298258980010420469)
    ·
      refine ⟨7894451840461779375976919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84207486298258980010420469 7894451840461779375976919)
      ·
        refine ⟨11841677760692669063965379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7894451840461779375976919 11841677760692669063965379)
        ·
          refine ⟨17762516641039003595948069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11841677760692669063965379 17762516641039003595948069)
          ·
            refine ⟨3330471870194813174240263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17762516641039003595948069 3330471870194813174240263)
            ·
              refine ⟨4995707805292219761360395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3330471870194813174240263 4995707805292219761360395)
              ·
                refine ⟨7493561707938329642040593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4995707805292219761360395 7493561707938329642040593)
                ·
                  refine ⟨5620171280953747231530445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7493561707938329642040593 5620171280953747231530445)
                  ·
                    refine ⟨2107564230357655211823917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5620171280953747231530445 2107564230357655211823917)
                    ·
                      refine ⟨790336586384120704433969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2107564230357655211823917 790336586384120704433969)
                      ·
                        rfl

theorem cell23_1539175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_1539175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539175 prefixEnd_1539175 := by exact prefixLift 1539175
  have htrace : WordTrace (prefixWord ++ tailWord_1539175) baseStart_1539175 baseEnd_1539175 := by
    simpa [prefixWord, tailWord_1539175, baseEnd_1539175] using wordTrace_append hprefix tailTrace_1539175
  have hstable : (prefixWord ++ tailWord_1539175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539175).length < 2 ^ (prefixWord ++ tailWord_1539175).sum := by decide
  have hdescent : baseEnd_1539175 < baseStart_1539175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539266 : List Nat := [3, 5, 1, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_1539266 : Nat := 118140960795 + 1539266 * 2 ^ 59
def prefixEnd_1539266 : Nat := 4983230072969 + 3 ^ 40 * 1539266 * 2
def baseEnd_1539266 : Nat := 790383313123679848396051

theorem tailTrace_1539266 : CollatzResearch.WordTrace tailWord_1539266 prefixEnd_1539266 790383313123679848396051 := by
  unfold tailWord_1539266
  simp only [CollatzResearch.WordTrace]
  refine ⟨14035410810377410637127413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37427762161006428365673101 14035410810377410637127413)
  ·
    refine ⟨1315819763472882247230695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14035410810377410637127413 1315819763472882247230695)
    ·
      refine ⟨1973729645209323370846043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1315819763472882247230695 1973729645209323370846043)
      ·
        refine ⟨2960594467813985056269065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1973729645209323370846043 2960594467813985056269065)
        ·
          refine ⟨2220445850860488792201799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2960594467813985056269065 2220445850860488792201799)
          ·
            refine ⟨3330668776290733188302699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2220445850860488792201799 3330668776290733188302699)
            ·
              refine ⟨4996003164436099782454049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3330668776290733188302699 4996003164436099782454049)
              ·
                refine ⟨3747002373327074836840537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4996003164436099782454049 3747002373327074836840537)
                ·
                  refine ⟨2810251779995306127630403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3747002373327074836840537 2810251779995306127630403)
                  ·
                    refine ⟨4215377669992959191445605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2810251779995306127630403 4215377669992959191445605)
                    ·
                      refine ⟨790383313123679848396051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4215377669992959191445605 790383313123679848396051)
                      ·
                        rfl

theorem cell23_1539266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_1539266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539266 prefixEnd_1539266 := by exact prefixLift 1539266
  have htrace : WordTrace (prefixWord ++ tailWord_1539266) baseStart_1539266 baseEnd_1539266 := by
    simpa [prefixWord, tailWord_1539266, baseEnd_1539266] using wordTrace_append hprefix tailTrace_1539266
  have hstable : (prefixWord ++ tailWord_1539266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539266).length < 2 ^ (prefixWord ++ tailWord_1539266).sum := by decide
  have hdescent : baseEnd_1539266 < baseStart_1539266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539275 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 3, 5, 2]
def baseStart_1539275 : Nat := 118140960795 + 1539275 * 2 ^ 59
def prefixEnd_1539275 : Nat := 4983230072969 + 3 ^ 40 * 1539275 * 2
def baseEnd_1539275 : Nat := 790387934449570313183509

theorem tailTrace_1539275 : CollatzResearch.WordTrace tailWord_1539275 prefixEnd_1539275 790387934449570313183509 := by
  unfold tailWord_1539275
  simp only [CollatzResearch.WordTrace]
  refine ⟨56141971498477037085587279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37427980998984691390391519 56141971498477037085587279)
  ·
    refine ⟨84212957247715555628380919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56141971498477037085587279 84212957247715555628380919)
    ·
      refine ⟨126319435871573333442571379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84212957247715555628380919 126319435871573333442571379)
      ·
        refine ⟨189479153807360000163857069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126319435871573333442571379 189479153807360000163857069)
        ·
          refine ⟨71054682677760000061446401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189479153807360000163857069 71054682677760000061446401)
          ·
            refine ⟨53291012008320000046084801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71054682677760000061446401 53291012008320000046084801)
            ·
              refine ⟨39968259006240000034563601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53291012008320000046084801 39968259006240000034563601)
              ·
                refine ⟨29976194254680000025922701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39968259006240000034563601 29976194254680000025922701)
                ·
                  refine ⟨11241072845505000009721013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29976194254680000025922701 11241072845505000009721013)
                  ·
                    refine ⟨1053850579266093750911345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11241072845505000009721013 1053850579266093750911345)
                    ·
                      refine ⟨790387934449570313183509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1053850579266093750911345 790387934449570313183509)
                      ·
                        rfl

theorem cell23_1539275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 5, 2].length) (baseStart_1539275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539275 prefixEnd_1539275 := by exact prefixLift 1539275
  have htrace : WordTrace (prefixWord ++ tailWord_1539275) baseStart_1539275 baseEnd_1539275 := by
    simpa [prefixWord, tailWord_1539275, baseEnd_1539275] using wordTrace_append hprefix tailTrace_1539275
  have hstable : (prefixWord ++ tailWord_1539275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539275).length < 2 ^ (prefixWord ++ tailWord_1539275).sum := by decide
  have hdescent : baseEnd_1539275 < baseStart_1539275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539309 : List Nat := [1, 5, 1, 2, 2, 1, 1, 3, 2, 3, 2]
def baseStart_1539309 : Nat := 118140960795 + 1539309 * 2 ^ 59
def prefixEnd_1539309 : Nat := 4983230072969 + 3 ^ 40 * 1539309 * 2
def baseEnd_1539309 : Nat := 790405392791823180158353

theorem tailTrace_1539309 : CollatzResearch.WordTrace tailWord_1539309 prefixEnd_1539309 790405392791823180158353 := by
  unfold tailWord_1539309
  simp only [CollatzResearch.WordTrace]
  refine ⟨56143211580353860892324981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37428807720235907261549987 56143211580353860892324981)
  ·
    refine ⟨5263426085658174458655467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56143211580353860892324981 5263426085658174458655467)
    ·
      refine ⟨7895139128487261687983201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5263426085658174458655467 7895139128487261687983201)
      ·
        refine ⟨5921354346365446265987401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7895139128487261687983201 5921354346365446265987401)
        ·
          refine ⟨4441015759774084699490551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5921354346365446265987401 4441015759774084699490551)
          ·
            refine ⟨6661523639661127049235827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4441015759774084699490551 6661523639661127049235827)
            ·
              refine ⟨9992285459491690573853741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6661523639661127049235827 9992285459491690573853741)
              ·
                refine ⟨3747107047309383965195153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9992285459491690573853741 3747107047309383965195153)
                ·
                  refine ⟨2810330285482037973896365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3747107047309383965195153 2810330285482037973896365)
                  ·
                    refine ⟨1053873857055764240211137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2810330285482037973896365 1053873857055764240211137)
                    ·
                      refine ⟨790405392791823180158353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1053873857055764240211137 790405392791823180158353)
                      ·
                        rfl

theorem cell23_1539309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_1539309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539309 prefixEnd_1539309 := by exact prefixLift 1539309
  have htrace : WordTrace (prefixWord ++ tailWord_1539309) baseStart_1539309 baseEnd_1539309 := by
    simpa [prefixWord, tailWord_1539309, baseEnd_1539309] using wordTrace_append hprefix tailTrace_1539309
  have hstable : (prefixWord ++ tailWord_1539309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539309).length < 2 ^ (prefixWord ++ tailWord_1539309).sum := by decide
  have hdescent : baseEnd_1539309 < baseStart_1539309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539315 : List Nat := [1, 1, 1, 2, 2, 6, 1, 2, 1, 6]
def baseStart_1539315 : Nat := 118140960795 + 1539315 * 2 ^ 59
def prefixEnd_1539315 : Nat := 4983230072969 + 3 ^ 40 * 1539315 * 2
def baseEnd_1539315 : Nat := 263469491225250052227775

theorem tailTrace_1539315 : CollatzResearch.WordTrace tailWord_1539315 prefixEnd_1539315 263469491225250052227775 := by
  unfold tailWord_1539315
  simp only [CollatzResearch.WordTrace]
  refine ⟨56143430418332123917043399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37428953612221415944695599 56143430418332123917043399)
  ·
    refine ⟨84215145627498185875565099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56143430418332123917043399 84215145627498185875565099)
    ·
      refine ⟨126322718441247278813347649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84215145627498185875565099 126322718441247278813347649)
      ·
        refine ⟨94742038830935459110010737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126322718441247278813347649 94742038830935459110010737)
        ·
          refine ⟨71056529123201594332508053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94742038830935459110010737 71056529123201594332508053)
          ·
            refine ⟨3330774802650074734336315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 71056529123201594332508053 3330774802650074734336315)
            ·
              refine ⟨4996162203975112101504473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3330774802650074734336315 4996162203975112101504473)
              ·
                refine ⟨3747121652981334076128355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4996162203975112101504473 3747121652981334076128355)
                ·
                  refine ⟨5620682479472001114192533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3747121652981334076128355 5620682479472001114192533)
                  ·
                    refine ⟨263469491225250052227775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5620682479472001114192533 263469491225250052227775)
                    ·
                      rfl

theorem cell23_1539315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 6].length) (baseStart_1539315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539315 prefixEnd_1539315 := by exact prefixLift 1539315
  have htrace : WordTrace (prefixWord ++ tailWord_1539315) baseStart_1539315 baseEnd_1539315 := by
    simpa [prefixWord, tailWord_1539315, baseEnd_1539315] using wordTrace_append hprefix tailTrace_1539315
  have hstable : (prefixWord ++ tailWord_1539315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539315).length < 2 ^ (prefixWord ++ tailWord_1539315).sum := by decide
  have hdescent : baseEnd_1539315 < baseStart_1539315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539342 : List Nat := [4, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3]
def baseStart_1539342 : Nat := 118140960795 + 1539342 * 2 ^ 59
def prefixEnd_1539342 : Nat := 4983230072969 + 3 ^ 40 * 1539342 * 2
def baseEnd_1539342 : Nat := 790422337653421551045701

theorem tailTrace_1539342 : CollatzResearch.WordTrace tailWord_1539342 prefixEnd_1539342 790422337653421551045701 := by
  unfold tailWord_1539342
  simp only [CollatzResearch.WordTrace]
  refine ⟨7018051898654288441034535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37429610126156205018850853 7018051898654288441034535)
  ·
    refine ⟨10527077847981432661551803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7018051898654288441034535 10527077847981432661551803)
    ·
      refine ⟨15790616771972148992327705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10527077847981432661551803 15790616771972148992327705)
      ·
        refine ⟨11842962578979111744245779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15790616771972148992327705 11842962578979111744245779)
        ·
          refine ⟨17764443868468667616368669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11842962578979111744245779 17764443868468667616368669)
          ·
            refine ⟨6661666450675750356138251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17764443868468667616368669 6661666450675750356138251)
            ·
              refine ⟨9992499676013625534207377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6661666450675750356138251 9992499676013625534207377)
              ·
                refine ⟨7494374757010219150655533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9992499676013625534207377 7494374757010219150655533)
                ·
                  refine ⟨2810390533878832181495825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7494374757010219150655533 2810390533878832181495825)
                  ·
                    refine ⟨2107792900409124136121869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2810390533878832181495825 2107792900409124136121869)
                    ·
                      refine ⟨790422337653421551045701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2107792900409124136121869 790422337653421551045701)
                      ·
                        rfl

theorem cell23_1539342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_1539342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539342 prefixEnd_1539342 := by exact prefixLift 1539342
  have htrace : WordTrace (prefixWord ++ tailWord_1539342) baseStart_1539342 baseEnd_1539342 := by
    simpa [prefixWord, tailWord_1539342, baseEnd_1539342] using wordTrace_append hprefix tailTrace_1539342
  have hstable : (prefixWord ++ tailWord_1539342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539342).length < 2 ^ (prefixWord ++ tailWord_1539342).sum := by decide
  have hdescent : baseEnd_1539342 < baseStart_1539342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539352 : List Nat := [2, 1, 2, 3, 1, 4, 2, 1, 1, 2, 4]
def baseStart_1539352 : Nat := 118140960795 + 1539352 * 2 ^ 59
def prefixEnd_1539352 : Nat := 4983230072969 + 3 ^ 40 * 1539352 * 2
def baseEnd_1539352 : Nat := 790427472459966511920655

theorem tailTrace_1539352 : CollatzResearch.WordTrace tailWord_1539352 prefixEnd_1539352 790427472459966511920655 := by
  unfold tailWord_1539352
  simp only [CollatzResearch.WordTrace]
  refine ⟨28072389959599039618070155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37429853279465386157426873 28072389959599039618070155)
  ·
    refine ⟨42108584939398559427105233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28072389959599039618070155 42108584939398559427105233)
    ·
      refine ⟨31581438704548919570328925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42108584939398559427105233 31581438704548919570328925)
      ·
        refine ⟨11843039514205844838873347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31581438704548919570328925 11843039514205844838873347)
        ·
          refine ⟨17764559271308767258310021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11843039514205844838873347 17764559271308767258310021)
          ·
            refine ⟨3330854863370393860933129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17764559271308767258310021 3330854863370393860933129)
            ·
              refine ⟨2498141147527795395699847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3330854863370393860933129 2498141147527795395699847)
              ·
                refine ⟨3747211721291693093549771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2498141147527795395699847 3747211721291693093549771)
                ·
                  refine ⟨5620817581937539640324657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3747211721291693093549771 5620817581937539640324657)
                  ·
                    refine ⟨4215613186453154730243493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5620817581937539640324657 4215613186453154730243493)
                    ·
                      refine ⟨790427472459966511920655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4215613186453154730243493 790427472459966511920655)
                      ·
                        rfl

theorem cell23_1539352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_1539352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539352 prefixEnd_1539352 := by exact prefixLift 1539352
  have htrace : WordTrace (prefixWord ++ tailWord_1539352) baseStart_1539352 baseEnd_1539352 := by
    simpa [prefixWord, tailWord_1539352, baseEnd_1539352] using wordTrace_append hprefix tailTrace_1539352
  have hstable : (prefixWord ++ tailWord_1539352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539352).length < 2 ^ (prefixWord ++ tailWord_1539352).sum := by decide
  have hdescent : baseEnd_1539352 < baseStart_1539352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539372 : List Nat := [2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 3]
def baseStart_1539372 : Nat := 118140960795 + 1539372 * 2 ^ 59
def prefixEnd_1539372 : Nat := 4983230072969 + 3 ^ 40 * 1539372 * 2
def baseEnd_1539372 : Nat := 790437742073056433670563

theorem tailTrace_1539372 : CollatzResearch.WordTrace tailWord_1539372 prefixEnd_1539372 790437742073056433670563 := by
  unfold tailWord_1539372
  simp only [CollatzResearch.WordTrace]
  refine ⟨28072754689562811325934185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37430339586083748434578913 28072754689562811325934185)
  ·
    refine ⟨21054566017172108494450639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28072754689562811325934185 21054566017172108494450639)
    ·
      refine ⟨31581849025758162741675959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21054566017172108494450639 31581849025758162741675959)
      ·
        refine ⟨47372773538637244112513939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31581849025758162741675959 47372773538637244112513939)
        ·
          refine ⟨71059160307955866168770909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47372773538637244112513939 71059160307955866168770909)
          ·
            refine ⟨26647185115483449813289091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71059160307955866168770909 26647185115483449813289091)
            ·
              refine ⟨39970777673225174719933637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26647185115483449813289091 39970777673225174719933637)
              ·
                refine ⟨7494520813729720259987557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39970777673225174719933637 7494520813729720259987557)
                ·
                  refine ⟨1405222652574322548747667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7494520813729720259987557 1405222652574322548747667)
                  ·
                    refine ⟨2107833978861483823121501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1405222652574322548747667 2107833978861483823121501)
                    ·
                      refine ⟨790437742073056433670563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2107833978861483823121501 790437742073056433670563)
                      ·
                        rfl

theorem cell23_1539372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 3].length) (baseStart_1539372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539372 prefixEnd_1539372 := by exact prefixLift 1539372
  have htrace : WordTrace (prefixWord ++ tailWord_1539372) baseStart_1539372 baseEnd_1539372 := by
    simpa [prefixWord, tailWord_1539372, baseEnd_1539372] using wordTrace_append hprefix tailTrace_1539372
  have hstable : (prefixWord ++ tailWord_1539372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539372).length < 2 ^ (prefixWord ++ tailWord_1539372).sum := by decide
  have hdescent : baseEnd_1539372 < baseStart_1539372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539373 : List Nat := [1, 5, 3, 1, 1, 3, 2, 1, 1, 1, 4]
def baseStart_1539373 : Nat := 118140960795 + 1539373 * 2 ^ 59
def prefixEnd_1539373 : Nat := 4983230072969 + 3 ^ 40 * 1539373 * 2
def baseEnd_1539373 : Nat := 790438255553710929758059

theorem tailTrace_1539373 : CollatzResearch.WordTrace tailWord_1539373 prefixEnd_1539373 790438255553710929758059 := by
  unfold tailWord_1539373
  simp only [CollatzResearch.WordTrace]
  refine ⟨56145545852121999822654773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37430363901414666548436515 56145545852121999822654773)
  ·
    refine ⟨5263644923636437483373885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56145545852121999822654773 5263644923636437483373885)
    ·
      refine ⟨1973866846363664056265207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5263644923636437483373885 1973866846363664056265207)
      ·
        refine ⟨2960800269545496084397811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1973866846363664056265207 2960800269545496084397811)
        ·
          refine ⟨4441200404318244126596717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2960800269545496084397811 4441200404318244126596717)
          ·
            refine ⟨1665450151619341547473769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4441200404318244126596717 1665450151619341547473769)
            ·
              refine ⟨1249087613714506160605327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1665450151619341547473769 1249087613714506160605327)
              ·
                refine ⟨1873631420571759240907991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1249087613714506160605327 1873631420571759240907991)
                ·
                  refine ⟨2810447130857638861361987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1873631420571759240907991 2810447130857638861361987)
                  ·
                    refine ⟨4215670696286458292042981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2810447130857638861361987 4215670696286458292042981)
                    ·
                      refine ⟨790438255553710929758059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4215670696286458292042981 790438255553710929758059)
                      ·
                        rfl

theorem cell23_1539373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_1539373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539373 prefixEnd_1539373 := by exact prefixLift 1539373
  have htrace : WordTrace (prefixWord ++ tailWord_1539373) baseStart_1539373 baseEnd_1539373 := by
    simpa [prefixWord, tailWord_1539373, baseEnd_1539373] using wordTrace_append hprefix tailTrace_1539373
  have hstable : (prefixWord ++ tailWord_1539373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539373).length < 2 ^ (prefixWord ++ tailWord_1539373).sum := by decide
  have hdescent : baseEnd_1539373 < baseStart_1539373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539406 : List Nat := [4, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3]
def baseStart_1539406 : Nat := 118140960795 + 1539406 * 2 ^ 59
def prefixEnd_1539406 : Nat := 4983230072969 + 3 ^ 40 * 1539406 * 2
def baseEnd_1539406 : Nat := 790455200415309300645407

theorem tailTrace_1539406 : CollatzResearch.WordTrace tailWord_1539406 prefixEnd_1539406 790455200415309300645407 := by
  unfold tailWord_1539406
  simp only [CollatzResearch.WordTrace]
  refine ⟨7018343682625305807325759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37431166307334964305737381 7018343682625305807325759)
  ·
    refine ⟨10527515523937958710988639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7018343682625305807325759 10527515523937958710988639)
    ·
      refine ⟨15791273285906938066482959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10527515523937958710988639 15791273285906938066482959)
      ·
        refine ⟨23686909928860407099724439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15791273285906938066482959 23686909928860407099724439)
        ·
          refine ⟨35530364893290610649586659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23686909928860407099724439 35530364893290610649586659)
          ·
            refine ⟨53295547339935915974379989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35530364893290610649586659 53295547339935915974379989)
            ·
              refine ⟨1249114390779748030649531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 53295547339935915974379989 1249114390779748030649531)
              ·
                refine ⟨1873671586169622045974297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1249114390779748030649531 1873671586169622045974297)
                ·
                  refine ⟨1405253689627216534480723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1873671586169622045974297 1405253689627216534480723)
                  ·
                    refine ⟨2107880534440824801721085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1405253689627216534480723 2107880534440824801721085)
                    ·
                      refine ⟨790455200415309300645407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2107880534440824801721085 790455200415309300645407)
                      ·
                        rfl

theorem cell23_1539406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3].length) (baseStart_1539406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539406 prefixEnd_1539406 := by exact prefixLift 1539406
  have htrace : WordTrace (prefixWord ++ tailWord_1539406) baseStart_1539406 baseEnd_1539406 := by
    simpa [prefixWord, tailWord_1539406, baseEnd_1539406] using wordTrace_append hprefix tailTrace_1539406
  have hstable : (prefixWord ++ tailWord_1539406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539406).length < 2 ^ (prefixWord ++ tailWord_1539406).sum := by decide
  have hdescent : baseEnd_1539406 < baseStart_1539406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539425 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 1, 4, 4]
def baseStart_1539425 : Nat := 118140960795 + 1539425 * 2 ^ 59
def prefixEnd_1539425 : Nat := 4983230072969 + 3 ^ 40 * 1539425 * 2
def baseEnd_1539425 : Nat := 790464956547744726307819

theorem tailTrace_1539425 : CollatzResearch.WordTrace tailWord_1539425 prefixEnd_1539425 790464956547744726307819 := by
  unfold tailWord_1539425
  simp only [CollatzResearch.WordTrace]
  refine ⟨56147442447933612703547729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37431628298622408469031819 56147442447933612703547729)
  ·
    refine ⟨42110581835950209527660797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56147442447933612703547729 42110581835950209527660797)
    ·
      refine ⟨15791468188481328572872799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42110581835950209527660797 15791468188481328572872799)
      ·
        refine ⟨23687202282721992859309199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15791468188481328572872799 23687202282721992859309199)
        ·
          refine ⟨35530803424082989288963799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23687202282721992859309199 35530803424082989288963799)
          ·
            refine ⟨53296205136124483933445699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35530803424082989288963799 53296205136124483933445699)
            ·
              refine ⟨79944307704186725900168549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53296205136124483933445699 79944307704186725900168549)
              ·
                refine ⟨14989557694535011106281603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79944307704186725900168549 14989557694535011106281603)
                ·
                  refine ⟨22484336541802516659422405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14989557694535011106281603 22484336541802516659422405)
                  ·
                    refine ⟨4215813101587971873641701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22484336541802516659422405 4215813101587971873641701)
                    ·
                      refine ⟨790464956547744726307819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4215813101587971873641701 790464956547744726307819)
                      ·
                        rfl

theorem cell23_1539425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_1539425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539425 prefixEnd_1539425 := by exact prefixLift 1539425
  have htrace : WordTrace (prefixWord ++ tailWord_1539425) baseStart_1539425 baseEnd_1539425 := by
    simpa [prefixWord, tailWord_1539425, baseEnd_1539425] using wordTrace_append hprefix tailTrace_1539425
  have hstable : (prefixWord ++ tailWord_1539425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539425).length < 2 ^ (prefixWord ++ tailWord_1539425).sum := by decide
  have hdescent : baseEnd_1539425 < baseStart_1539425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539429 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 6, 2, 2]
def baseStart_1539429 : Nat := 118140960795 + 1539429 * 2 ^ 59
def prefixEnd_1539429 : Nat := 4983230072969 + 3 ^ 40 * 1539429 * 2
def baseEnd_1539429 : Nat := 790467010470362710657801

theorem tailTrace_1539429 : CollatzResearch.WordTrace tailWord_1539429 prefixEnd_1539429 790467010470362710657801 := by
  unfold tailWord_1539429
  simp only [CollatzResearch.WordTrace]
  refine ⟨56147588339919121386693341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37431725559946080924462227 56147588339919121386693341)
  ·
    refine ⟨21055345627469670520010003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56147588339919121386693341 21055345627469670520010003)
    ·
      refine ⟨31583018441204505780015005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21055345627469670520010003 31583018441204505780015005)
      ·
        refine ⟨11843631915451689667505627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31583018441204505780015005 11843631915451689667505627)
        ·
          refine ⟨17765447873177534501258441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11843631915451689667505627 17765447873177534501258441)
          ·
            refine ⟨13324085904883150875943831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17765447873177534501258441 13324085904883150875943831)
            ·
              refine ⟨19986128857324726313915747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13324085904883150875943831 19986128857324726313915747)
              ·
                refine ⟨29979193285987089470873621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19986128857324726313915747 29979193285987089470873621)
                ·
                  refine ⟨1405274685280644818947201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29979193285987089470873621 1405274685280644818947201)
                  ·
                    refine ⟨1053956013960483614210401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1405274685280644818947201 1053956013960483614210401)
                    ·
                      refine ⟨790467010470362710657801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1053956013960483614210401 790467010470362710657801)
                      ·
                        rfl

theorem cell23_1539429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_1539429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539429 prefixEnd_1539429 := by exact prefixLift 1539429
  have htrace : WordTrace (prefixWord ++ tailWord_1539429) baseStart_1539429 baseEnd_1539429 := by
    simpa [prefixWord, tailWord_1539429, baseEnd_1539429] using wordTrace_append hprefix tailTrace_1539429
  have hstable : (prefixWord ++ tailWord_1539429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539429).length < 2 ^ (prefixWord ++ tailWord_1539429).sum := by decide
  have hdescent : baseEnd_1539429 < baseStart_1539429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539463 : List Nat := [1, 1, 4, 2, 2, 2, 4, 1, 2, 2, 2]
def baseStart_1539463 : Nat := 118140960795 + 1539463 * 2 ^ 59
def prefixEnd_1539463 : Nat := 4983230072969 + 3 ^ 40 * 1539463 * 2
def baseEnd_1539463 : Nat := 790484468812615577632645

theorem tailTrace_1539463 : CollatzResearch.WordTrace tailWord_1539463 prefixEnd_1539463 790484468812615577632645 := by
  unfold tailWord_1539463
  simp only [CollatzResearch.WordTrace]
  refine ⟨56148828421795945193431043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37432552281197296795620695 56148828421795945193431043)
  ·
    refine ⟨84223242632693917790146565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56148828421795945193431043 84223242632693917790146565)
    ·
      refine ⟨15791857993630109585652481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84223242632693917790146565 15791857993630109585652481)
      ·
        refine ⟨11843893495222582189239361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15791857993630109585652481 11843893495222582189239361)
        ·
          refine ⟨8882920121416936641929521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11843893495222582189239361 8882920121416936641929521)
          ·
            refine ⟨6662190091062702481447141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8882920121416936641929521 6662190091062702481447141)
            ·
              refine ⟨1249160642074256715271339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6662190091062702481447141 1249160642074256715271339)
              ·
                refine ⟨1873740963111385072907009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1249160642074256715271339 1873740963111385072907009)
                ·
                  refine ⟨1405305722333538804680257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1873740963111385072907009 1405305722333538804680257)
                  ·
                    refine ⟨1053979291750154103510193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1405305722333538804680257 1053979291750154103510193)
                    ·
                      refine ⟨790484468812615577632645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1053979291750154103510193 790484468812615577632645)
                      ·
                        rfl

theorem cell23_1539463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_1539463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539463 prefixEnd_1539463 := by exact prefixLift 1539463
  have htrace : WordTrace (prefixWord ++ tailWord_1539463) baseStart_1539463 baseEnd_1539463 := by
    simpa [prefixWord, tailWord_1539463, baseEnd_1539463] using wordTrace_append hprefix tailTrace_1539463
  have hstable : (prefixWord ++ tailWord_1539463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539463).length < 2 ^ (prefixWord ++ tailWord_1539463).sum := by decide
  have hdescent : baseEnd_1539463 < baseStart_1539463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539546 : List Nat := [3, 1, 1, 2, 3, 2, 1, 5, 1, 4]
def baseStart_1539546 : Nat := 118140960795 + 1539546 * 2 ^ 59
def prefixEnd_1539546 : Nat := 4983230072969 + 3 ^ 40 * 1539546 * 2
def baseEnd_1539546 : Nat := 263509029235646250964921

theorem tailTrace_1539546 : CollatzResearch.WordTrace tailWord_1539546 prefixEnd_1539546 263509029235646250964921 := by
  unfold tailWord_1539546
  simp only [CollatzResearch.WordTrace]
  refine ⟨14037963920123812592175623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37434570453663500245801661 14037963920123812592175623)
  ·
    refine ⟨21056945880185718888263435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14037963920123812592175623 21056945880185718888263435)
    ·
      refine ⟨31585418820278578332395153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21056945880185718888263435 31585418820278578332395153)
      ·
        refine ⟨23689064115208933749296365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31585418820278578332395153 23689064115208933749296365)
        ·
          refine ⟨8883399043203350155986137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23689064115208933749296365 8883399043203350155986137)
          ·
            refine ⟨6662549282402512616989603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8883399043203350155986137 6662549282402512616989603)
            ·
              refine ⟨9993823923603768925484405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6662549282402512616989603 9993823923603768925484405)
              ·
                refine ⟨936920992837853336764163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9993823923603768925484405 936920992837853336764163)
                ·
                  refine ⟨1405381489256780005146245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 936920992837853336764163 1405381489256780005146245)
                  ·
                    refine ⟨263509029235646250964921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1405381489256780005146245 263509029235646250964921)
                    ·
                      rfl

theorem cell23_1539546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 5, 1, 4].length) (baseStart_1539546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539546 prefixEnd_1539546 := by exact prefixLift 1539546
  have htrace : WordTrace (prefixWord ++ tailWord_1539546) baseStart_1539546 baseEnd_1539546 := by
    simpa [prefixWord, tailWord_1539546, baseEnd_1539546] using wordTrace_append hprefix tailTrace_1539546
  have hstable : (prefixWord ++ tailWord_1539546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539546).length < 2 ^ (prefixWord ++ tailWord_1539546).sum := by decide
  have hdescent : baseEnd_1539546 < baseStart_1539546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539559 : List Nat := [1, 1, 5, 2, 1, 2, 3, 2, 6]
def baseStart_1539559 : Nat := 118140960795 + 1539559 * 2 ^ 59
def prefixEnd_1539559 : Nat := 4983230072969 + 3 ^ 40 * 1539559 * 2
def baseEnd_1539559 : Nat := 87837084772827466892467

theorem tailTrace_1539559 : CollatzResearch.WordTrace tailWord_1539559 prefixEnd_1539559 87837084772827466892467 := by
  unfold tailWord_1539559
  simp only [CollatzResearch.WordTrace]
  refine ⟨56152329829448153588925731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37434886552965435725950487 56152329829448153588925731)
  ·
    refine ⟨84228494744172230383388597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56152329829448153588925731 84228494744172230383388597)
    ·
      refine ⟨7896421382266146598442681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84228494744172230383388597 7896421382266146598442681)
      ·
        refine ⟨5922316036699609948832011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7896421382266146598442681 5922316036699609948832011)
        ·
          refine ⟨8883474055049414923248017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5922316036699609948832011 8883474055049414923248017)
          ·
            refine ⟨6662605541287061192436013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8883474055049414923248017 6662605541287061192436013)
            ·
              refine ⟨2498477077982647947163505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6662605541287061192436013 2498477077982647947163505)
              ·
                refine ⟨1873857808486985960372629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2498477077982647947163505 1873857808486985960372629)
                ·
                  refine ⟨87837084772827466892467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1873857808486985960372629 87837084772827466892467)
                  ·
                    rfl

theorem cell23_1539559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 6].length) (baseStart_1539559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539559 prefixEnd_1539559 := by exact prefixLift 1539559
  have htrace : WordTrace (prefixWord ++ tailWord_1539559) baseStart_1539559 baseEnd_1539559 := by
    simpa [prefixWord, tailWord_1539559, baseEnd_1539559] using wordTrace_append hprefix tailTrace_1539559
  have hstable : (prefixWord ++ tailWord_1539559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539559).length < 2 ^ (prefixWord ++ tailWord_1539559).sum := by decide
  have hdescent : baseEnd_1539559 < baseStart_1539559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539579 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 4, 3, 2]
def baseStart_1539579 : Nat := 118140960795 + 1539579 * 2 ^ 59
def prefixEnd_1539579 : Nat := 4983230072969 + 3 ^ 40 * 1539579 * 2
def baseEnd_1539579 : Nat := 790544032568537123782111

theorem tailTrace_1539579 : CollatzResearch.WordTrace tailWord_1539579 prefixEnd_1539579 790544032568537123782111 := by
  unfold tailWord_1539579
  simp only [CollatzResearch.WordTrace]
  refine ⟨56153059289375697004653791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37435372859583798003102527 56153059289375697004653791)
  ·
    refine ⟨84229588934063545506980687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56153059289375697004653791 84229588934063545506980687)
    ·
      refine ⟨126344383401095318260471031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84229588934063545506980687 126344383401095318260471031)
      ·
        refine ⟨189516575101642977390706547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126344383401095318260471031 189516575101642977390706547)
        ·
          refine ⟨284274862652464466086059821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189516575101642977390706547 284274862652464466086059821)
          ·
            refine ⟨106603073494674174782272433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 284274862652464466086059821 106603073494674174782272433)
            ·
              refine ⟨79952305121005631086704325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106603073494674174782272433 79952305121005631086704325)
              ·
                refine ⟨14991057210188555828757061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79952305121005631086704325 14991057210188555828757061)
                ·
                  refine ⟨2810823226910354217891949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14991057210188555828757061 2810823226910354217891949)
                  ·
                    refine ⟨1054058710091382831709481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2810823226910354217891949 1054058710091382831709481)
                    ·
                      refine ⟨790544032568537123782111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1054058710091382831709481 790544032568537123782111)
                      ·
                        rfl

theorem cell23_1539579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 3, 2].length) (baseStart_1539579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539579 prefixEnd_1539579 := by exact prefixLift 1539579
  have htrace : WordTrace (prefixWord ++ tailWord_1539579) baseStart_1539579 baseEnd_1539579 := by
    simpa [prefixWord, tailWord_1539579, baseEnd_1539579] using wordTrace_append hprefix tailTrace_1539579
  have hstable : (prefixWord ++ tailWord_1539579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539579).length < 2 ^ (prefixWord ++ tailWord_1539579).sum := by decide
  have hdescent : baseEnd_1539579 < baseStart_1539579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539603 : List Nat := [1, 1, 1, 2, 1, 6, 3, 3, 1, 1, 3]
def baseStart_1539603 : Nat := 118140960795 + 1539603 * 2 ^ 59
def prefixEnd_1539603 : Nat := 4983230072969 + 3 ^ 40 * 1539603 * 2
def baseEnd_1539603 : Nat := 790556356104245029882001

theorem tailTrace_1539603 : CollatzResearch.WordTrace tailWord_1539603 prefixEnd_1539603 790556356104245029882001 := by
  unfold tailWord_1539603
  simp only [CollatzResearch.WordTrace]
  refine ⟨56153934641288749103527463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37435956427525832735684975 56153934641288749103527463)
  ·
    refine ⟨84230901961933123655291195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56153934641288749103527463 84230901961933123655291195)
    ·
      refine ⟨126346352942899685482936793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84230901961933123655291195 126346352942899685482936793)
      ·
        refine ⟨94759764707174764112202595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126346352942899685482936793 94759764707174764112202595)
        ·
          refine ⟨142139647060762146168303893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94759764707174764112202595 142139647060762146168303893)
          ·
            refine ⟨6662795955973225601639245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 142139647060762146168303893 6662795955973225601639245)
            ·
              refine ⟨2498548483489959600614717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6662795955973225601639245 2498548483489959600614717)
              ·
                refine ⟨936955681308734850230519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2498548483489959600614717 936955681308734850230519)
                ·
                  refine ⟨1405433521963102275345779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 936955681308734850230519 1405433521963102275345779)
                  ·
                    refine ⟨2108150282944653413018669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1405433521963102275345779 2108150282944653413018669)
                    ·
                      refine ⟨790556356104245029882001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2108150282944653413018669 790556356104245029882001)
                      ·
                        rfl

theorem cell23_1539603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 3, 1, 1, 3].length) (baseStart_1539603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539603 prefixEnd_1539603 := by exact prefixLift 1539603
  have htrace : WordTrace (prefixWord ++ tailWord_1539603) baseStart_1539603 baseEnd_1539603 := by
    simpa [prefixWord, tailWord_1539603, baseEnd_1539603] using wordTrace_append hprefix tailTrace_1539603
  have hstable : (prefixWord ++ tailWord_1539603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539603).length < 2 ^ (prefixWord ++ tailWord_1539603).sum := by decide
  have hdescent : baseEnd_1539603 < baseStart_1539603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539614 : List Nat := [4, 3, 3, 1, 2, 1, 1, 1, 3, 4]
def baseStart_1539614 : Nat := 118140960795 + 1539614 * 2 ^ 59
def prefixEnd_1539614 : Nat := 4983230072969 + 3 ^ 40 * 1539614 * 2
def baseEnd_1539614 : Nat := 263520668130481495614817

theorem tailTrace_1539614 : CollatzResearch.WordTrace tailWord_1539614 prefixEnd_1539614 263520668130481495614817 := by
  unfold tailWord_1539614
  simp only [CollatzResearch.WordTrace]
  refine ⟨7019291980531112247772237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37436223896165931988118597 7019291980531112247772237)
  ·
    refine ⟨2632234492699167092914589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7019291980531112247772237 2632234492699167092914589)
    ·
      refine ⟨987087934762187659842971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2632234492699167092914589 987087934762187659842971)
      ·
        refine ⟨1480631902143281489764457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 987087934762187659842971 1480631902143281489764457)
        ·
          refine ⟨1110473926607461117323343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1480631902143281489764457 1110473926607461117323343)
          ·
            refine ⟨1665710889911191675985015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1110473926607461117323343 1665710889911191675985015)
            ·
              refine ⟨2498566334866787513977523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1665710889911191675985015 2498566334866787513977523)
              ·
                refine ⟨3747849502300181270966285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2498566334866787513977523 3747849502300181270966285)
                ·
                  refine ⟨1405443563362567976612357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3747849502300181270966285 1405443563362567976612357)
                  ·
                    refine ⟨263520668130481495614817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1405443563362567976612357 263520668130481495614817)
                    ·
                      rfl

theorem cell23_1539614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_1539614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539614 prefixEnd_1539614 := by exact prefixLift 1539614
  have htrace : WordTrace (prefixWord ++ tailWord_1539614) baseStart_1539614 baseEnd_1539614 := by
    simpa [prefixWord, tailWord_1539614, baseEnd_1539614] using wordTrace_append hprefix tailTrace_1539614
  have hstable : (prefixWord ++ tailWord_1539614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539614).length < 2 ^ (prefixWord ++ tailWord_1539614).sum := by decide
  have hdescent : baseEnd_1539614 < baseStart_1539614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539693 : List Nat := [1, 5, 1, 1, 4, 1, 2, 1, 1, 3, 3]
def baseStart_1539693 : Nat := 118140960795 + 1539693 * 2 ^ 59
def prefixEnd_1539693 : Nat := 4983230072969 + 3 ^ 40 * 1539693 * 2
def baseEnd_1539693 : Nat := 790602569363149677756587

theorem tailTrace_1539693 : CollatzResearch.WordTrace tailWord_1539693 prefixEnd_1539693 790602569363149677756587 := by
  unfold tailWord_1539693
  simp only [CollatzResearch.WordTrace]
  refine ⟨56157217210962694474303733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37438144807308462982869155 56157217210962694474303733)
  ·
    refine ⟨5264739113527752606965975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56157217210962694474303733 5264739113527752606965975)
    ·
      refine ⟨7897108670291628910448963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5264739113527752606965975 7897108670291628910448963)
      ·
        refine ⟨11845663005437443365673445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7897108670291628910448963 11845663005437443365673445)
        ·
          refine ⟨2221061813519520631063771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11845663005437443365673445 2221061813519520631063771)
          ·
            refine ⟨3331592720279280946595657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2221061813519520631063771 3331592720279280946595657)
            ·
              refine ⟨2498694540209460709946743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3331592720279280946595657 2498694540209460709946743)
              ·
                refine ⟨3748041810314191064920115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2498694540209460709946743 3748041810314191064920115)
                ·
                  refine ⟨5622062715471286597380173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3748041810314191064920115 5622062715471286597380173)
                  ·
                    refine ⟨2108273518301732474017565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5622062715471286597380173 2108273518301732474017565)
                    ·
                      refine ⟨790602569363149677756587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2108273518301732474017565 790602569363149677756587)
                      ·
                        rfl

theorem cell23_1539693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_1539693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539693 prefixEnd_1539693 := by exact prefixLift 1539693
  have htrace : WordTrace (prefixWord ++ tailWord_1539693) baseStart_1539693 baseEnd_1539693 := by
    simpa [prefixWord, tailWord_1539693, baseEnd_1539693] using wordTrace_append hprefix tailTrace_1539693
  have hstable : (prefixWord ++ tailWord_1539693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539693).length < 2 ^ (prefixWord ++ tailWord_1539693).sum := by decide
  have hdescent : baseEnd_1539693 < baseStart_1539693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539769 : List Nat := [1, 2, 1, 4, 1, 1, 4, 1, 1, 7]
def baseStart_1539769 : Nat := 118140960795 + 1539769 * 2 ^ 59
def prefixEnd_1539769 : Nat := 4983230072969 + 3 ^ 40 * 1539769 * 2
def baseEnd_1539769 : Nat := 263547197964297126802079

theorem tailTrace_1539769 : CollatzResearch.WordTrace tailWord_1539769 prefixEnd_1539769 263547197964297126802079 := by
  unfold tailWord_1539769
  simp only [CollatzResearch.WordTrace]
  refine ⟨56159989158687359454070361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37439992772458239636046907 56159989158687359454070361)
  ·
    refine ⟨42119991869015519590552771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56159989158687359454070361 42119991869015519590552771)
    ·
      refine ⟨63179987803523279385829157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42119991869015519590552771 63179987803523279385829157)
      ·
        refine ⟨11846247713160614884842967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63179987803523279385829157 11846247713160614884842967)
        ·
          refine ⟨17769371569740922327264451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11846247713160614884842967 17769371569740922327264451)
          ·
            refine ⟨26654057354611383490896677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17769371569740922327264451 26654057354611383490896677)
            ·
              refine ⟨4997635753989634404543127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26654057354611383490896677 4997635753989634404543127)
              ·
                refine ⟨7496453630984451606814691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4997635753989634404543127 7496453630984451606814691)
                ·
                  refine ⟨11244680446476677410222037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7496453630984451606814691 11244680446476677410222037)
                  ·
                    refine ⟨263547197964297126802079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11244680446476677410222037 263547197964297126802079)
                    ·
                      rfl

theorem cell23_1539769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 7].length) (baseStart_1539769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539769 prefixEnd_1539769 := by exact prefixLift 1539769
  have htrace : WordTrace (prefixWord ++ tailWord_1539769) baseStart_1539769 baseEnd_1539769 := by
    simpa [prefixWord, tailWord_1539769, baseEnd_1539769] using wordTrace_append hprefix tailTrace_1539769
  have hstable : (prefixWord ++ tailWord_1539769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539769).length < 2 ^ (prefixWord ++ tailWord_1539769).sum := by decide
  have hdescent : baseEnd_1539769 < baseStart_1539769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539796 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 1, 1, 7]
def baseStart_1539796 : Nat := 118140960795 + 1539796 * 2 ^ 59
def prefixEnd_1539796 : Nat := 4983230072969 + 3 ^ 40 * 1539796 * 2
def baseEnd_1539796 : Nat := 790655457870562774768613

theorem tailTrace_1539796 : CollatzResearch.WordTrace tailWord_1539796 prefixEnd_1539796 790655457870562774768613 := by
  unfold tailWord_1539796
  simp only [CollatzResearch.WordTrace]
  refine ⟨28080486964794771532651621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37440649286393028710202161 28080486964794771532651621)
  ·
    refine ⟨5265091305899019662372179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28080486964794771532651621 5265091305899019662372179)
    ·
      refine ⟨7897636958848529493558269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5265091305899019662372179 7897636958848529493558269)
      ·
        refine ⟨2961613859568198560084351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7897636958848529493558269 2961613859568198560084351)
        ·
          refine ⟨4442420789352297840126527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2961613859568198560084351 4442420789352297840126527)
          ·
            refine ⟨6663631184028446760189791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4442420789352297840126527 6663631184028446760189791)
            ·
              refine ⟨9995446776042670140284687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6663631184028446760189791 9995446776042670140284687)
              ·
                refine ⟨14993170164064005210427031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9995446776042670140284687 14993170164064005210427031)
                ·
                  refine ⟨22489755246096007815640547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14993170164064005210427031 22489755246096007815640547)
                  ·
                    refine ⟨33734632869144011723460821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22489755246096007815640547 33734632869144011723460821)
                    ·
                      refine ⟨790655457870562774768613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 33734632869144011723460821 790655457870562774768613)
                      ·
                        rfl

theorem cell23_1539796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_1539796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539796 prefixEnd_1539796 := by exact prefixLift 1539796
  have htrace : WordTrace (prefixWord ++ tailWord_1539796) baseStart_1539796 baseEnd_1539796 := by
    simpa [prefixWord, tailWord_1539796, baseEnd_1539796] using wordTrace_append hprefix tailTrace_1539796
  have hstable : (prefixWord ++ tailWord_1539796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539796).length < 2 ^ (prefixWord ++ tailWord_1539796).sum := by decide
  have hdescent : baseEnd_1539796 < baseStart_1539796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539819 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 4]
def baseStart_1539819 : Nat := 118140960795 + 1539819 * 2 ^ 59
def prefixEnd_1539819 : Nat := 4983230072969 + 3 ^ 40 * 1539819 * 2
def baseEnd_1539819 : Nat := 790667267925616184781007

theorem tailTrace_1539819 : CollatzResearch.WordTrace tailWord_1539819 prefixEnd_1539819 790667267925616184781007 := by
  unfold tailWord_1539819
  simp only [CollatzResearch.WordTrace]
  refine ⟨56161812808506217993390511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37441208539004145328927007 56161812808506217993390511)
  ·
    refine ⟨84242719212759326990085767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56161812808506217993390511 84242719212759326990085767)
    ·
      refine ⟨126364078819138990485128651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84242719212759326990085767 126364078819138990485128651)
      ·
        refine ⟨189546118228708485727692977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126364078819138990485128651 189546118228708485727692977)
        ·
          refine ⟨142159588671531364295769733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189546118228708485727692977 142159588671531364295769733)
          ·
            refine ⟨26654922875912130805456825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142159588671531364295769733 26654922875912130805456825)
            ·
              refine ⟨19991192156934098104092619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26654922875912130805456825 19991192156934098104092619)
              ·
                refine ⟨29986788235401147156138929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19991192156934098104092619 29986788235401147156138929)
                ·
                  refine ⟨22490091176550860367104197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29986788235401147156138929 22490091176550860367104197)
                  ·
                    refine ⟨4216892095603286318832037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22490091176550860367104197 4216892095603286318832037)
                    ·
                      refine ⟨790667267925616184781007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4216892095603286318832037 790667267925616184781007)
                      ·
                        rfl

theorem cell23_1539819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 4].length) (baseStart_1539819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539819 prefixEnd_1539819 := by exact prefixLift 1539819
  have htrace : WordTrace (prefixWord ++ tailWord_1539819) baseStart_1539819 baseEnd_1539819 := by
    simpa [prefixWord, tailWord_1539819, baseEnd_1539819] using wordTrace_append hprefix tailTrace_1539819
  have hstable : (prefixWord ++ tailWord_1539819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539819).length < 2 ^ (prefixWord ++ tailWord_1539819).sum := by decide
  have hdescent : baseEnd_1539819 < baseStart_1539819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539849 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 1, 2, 6]
def baseStart_1539849 : Nat := 118140960795 + 1539849 * 2 ^ 59
def prefixEnd_1539849 : Nat := 4983230072969 + 3 ^ 40 * 1539849 * 2
def baseEnd_1539849 : Nat := 790682672345251067405869

theorem tailTrace_1539849 : CollatzResearch.WordTrace tailWord_1539849 prefixEnd_1539849 790682672345251067405869 := by
  unfold tailWord_1539849
  simp only [CollatzResearch.WordTrace]
  refine ⟨56162906998397533116982601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37441937998931688744655067 56162906998397533116982601)
  ·
    refine ⟨42122180248798149837736951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56162906998397533116982601 42122180248798149837736951)
    ·
      refine ⟨63183270373197224756605427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42122180248798149837736951 63183270373197224756605427)
      ·
        refine ⟨94774905559795837134908141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63183270373197224756605427 94774905559795837134908141)
        ·
          refine ⟨35540589584923438925590553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94774905559795837134908141 35540589584923438925590553)
          ·
            refine ⟨26655442188692579194192915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35540589584923438925590553 26655442188692579194192915)
            ·
              refine ⟨39983163283038868791289373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26655442188692579194192915 39983163283038868791289373)
              ·
                refine ⟨14993686231139575796733515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39983163283038868791289373 14993686231139575796733515)
                ·
                  refine ⟨22490529346709363695100273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14993686231139575796733515 22490529346709363695100273)
                  ·
                    refine ⟨16867897010032022771325205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22490529346709363695100273 16867897010032022771325205)
                    ·
                      refine ⟨790682672345251067405869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16867897010032022771325205 790682672345251067405869)
                      ·
                        rfl

theorem cell23_1539849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 2, 6].length) (baseStart_1539849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539849 prefixEnd_1539849 := by exact prefixLift 1539849
  have htrace : WordTrace (prefixWord ++ tailWord_1539849) baseStart_1539849 baseEnd_1539849 := by
    simpa [prefixWord, tailWord_1539849, baseEnd_1539849] using wordTrace_append hprefix tailTrace_1539849
  have hstable : (prefixWord ++ tailWord_1539849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539849).length < 2 ^ (prefixWord ++ tailWord_1539849).sum := by decide
  have hdescent : baseEnd_1539849 < baseStart_1539849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539850 : List Nat := [3, 1, 2, 2, 1, 4, 1, 4, 1, 4]
def baseStart_1539850 : Nat := 118140960795 + 1539850 * 2 ^ 59
def prefixEnd_1539850 : Nat := 4983230072969 + 3 ^ 40 * 1539850 * 2
def baseEnd_1539850 : Nat := 263561061941968521164455

theorem tailTrace_1539850 : CollatzResearch.WordTrace tailWord_1539850 prefixEnd_1539850 263561061941968521164455 := by
  unfold tailWord_1539850
  simp only [CollatzResearch.WordTrace]
  refine ⟨14040735867848477571942251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37441962314262606858512669 14040735867848477571942251)
  ·
    refine ⟨21061103801772716357913377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14040735867848477571942251 21061103801772716357913377)
    ·
      refine ⟨15795827851329537268435033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21061103801772716357913377 15795827851329537268435033)
      ·
        refine ⟨11846870888497152951326275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15795827851329537268435033 11846870888497152951326275)
        ·
          refine ⟨17770306332745729426989413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11846870888497152951326275 17770306332745729426989413)
          ·
            refine ⟨3331932437389824267560515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17770306332745729426989413 3331932437389824267560515)
            ·
              refine ⟨4997898656084736401340773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3331932437389824267560515 4997898656084736401340773)
              ·
                refine ⟨937105998015888075251395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4997898656084736401340773 937105998015888075251395)
                ·
                  refine ⟨1405658997023832112877093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 937105998015888075251395 1405658997023832112877093)
                  ·
                    refine ⟨263561061941968521164455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1405658997023832112877093 263561061941968521164455)
                    ·
                      rfl

theorem cell23_1539850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_1539850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539850 prefixEnd_1539850 := by exact prefixLift 1539850
  have htrace : WordTrace (prefixWord ++ tailWord_1539850) baseStart_1539850 baseEnd_1539850 := by
    simpa [prefixWord, tailWord_1539850, baseEnd_1539850] using wordTrace_append hprefix tailTrace_1539850
  have hstable : (prefixWord ++ tailWord_1539850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539850).length < 2 ^ (prefixWord ++ tailWord_1539850).sum := by decide
  have hdescent : baseEnd_1539850 < baseStart_1539850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539873 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 5, 1, 3]
def baseStart_1539873 : Nat := 118140960795 + 1539873 * 2 ^ 59
def prefixEnd_1539873 : Nat := 4983230072969 + 3 ^ 40 * 1539873 * 2
def baseEnd_1539873 : Nat := 790694995880958973505759

theorem tailTrace_1539873 : CollatzResearch.WordTrace tailWord_1539873 prefixEnd_1539873 790694995880958973505759 := by
  unfold tailWord_1539873
  simp only [CollatzResearch.WordTrace]
  refine ⟨56163782350310585215856273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37442521566873723477237515 56163782350310585215856273)
  ·
    refine ⟨42122836762732938911892205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56163782350310585215856273 42122836762732938911892205)
    ·
      refine ⟨15796063786024852091959577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42122836762732938911892205 15796063786024852091959577)
      ·
        refine ⟨11847047839518639068969683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15796063786024852091959577 11847047839518639068969683)
        ·
          refine ⟨17770571759277958603454525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11847047839518639068969683 17770571759277958603454525)
          ·
            refine ⟨6663964409729234476295447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17770571759277958603454525 6663964409729234476295447)
            ·
              refine ⟨9995946614593851714443171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6663964409729234476295447 9995946614593851714443171)
              ·
                refine ⟨14993919921890777571664757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9995946614593851714443171 14993919921890777571664757)
                ·
                  refine ⟨1405679992677260397343571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14993919921890777571664757 1405679992677260397343571)
                  ·
                    refine ⟨2108519989015890596015357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1405679992677260397343571 2108519989015890596015357)
                    ·
                      refine ⟨790694995880958973505759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2108519989015890596015357 790694995880958973505759)
                      ·
                        rfl

theorem cell23_1539873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_1539873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539873 prefixEnd_1539873 := by exact prefixLift 1539873
  have htrace : WordTrace (prefixWord ++ tailWord_1539873) baseStart_1539873 baseEnd_1539873 := by
    simpa [prefixWord, tailWord_1539873, baseEnd_1539873] using wordTrace_append hprefix tailTrace_1539873
  have hstable : (prefixWord ++ tailWord_1539873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539873).length < 2 ^ (prefixWord ++ tailWord_1539873).sum := by decide
  have hdescent : baseEnd_1539873 < baseStart_1539873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539897 : List Nat := [1, 2, 1, 7, 2, 1, 1, 2, 6]
def baseStart_1539897 : Nat := 118140960795 + 1539897 * 2 ^ 59
def prefixEnd_1539897 : Nat := 4983230072969 + 3 ^ 40 * 1539897 * 2
def baseEnd_1539897 : Nat := 87856368824074097733961

theorem tailTrace_1539897 : CollatzResearch.WordTrace tailWord_1539897 prefixEnd_1539897 87856368824074097733961 := by
  unfold tailWord_1539897
  simp only [CollatzResearch.WordTrace]
  refine ⟨56164657702223637314729945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37443105134815758209819963 56164657702223637314729945)
  ·
    refine ⟨42123493276667727986047459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56164657702223637314729945 42123493276667727986047459)
    ·
      refine ⟨63185239915001591979071189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42123493276667727986047459 63185239915001591979071189)
      ·
        refine ⟨1480904060507849812009481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 63185239915001591979071189 1480904060507849812009481)
        ·
          refine ⟨1110678045380887359007111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1480904060507849812009481 1110678045380887359007111)
          ·
            refine ⟨1666017068071331038510667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1110678045380887359007111 1666017068071331038510667)
            ·
              refine ⟨2499025602106996557766001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1666017068071331038510667 2499025602106996557766001)
              ·
                refine ⟨1874269201580247418324501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2499025602106996557766001 1874269201580247418324501)
                ·
                  refine ⟨87856368824074097733961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1874269201580247418324501 87856368824074097733961)
                  ·
                    rfl

theorem cell23_1539897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 6].length) (baseStart_1539897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539897 prefixEnd_1539897 := by exact prefixLift 1539897
  have htrace : WordTrace (prefixWord ++ tailWord_1539897) baseStart_1539897 baseEnd_1539897 := by
    simpa [prefixWord, tailWord_1539897, baseEnd_1539897] using wordTrace_append hprefix tailTrace_1539897
  have hstable : (prefixWord ++ tailWord_1539897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539897).length < 2 ^ (prefixWord ++ tailWord_1539897).sum := by decide
  have hdescent : baseEnd_1539897 < baseStart_1539897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539930 : List Nat := [3, 1, 1, 2, 1, 3, 1, 4, 3, 2, 2]
def baseStart_1539930 : Nat := 118140960795 + 1539930 * 2 ^ 59
def prefixEnd_1539930 : Nat := 4983230072969 + 3 ^ 40 * 1539930 * 2
def baseEnd_1539930 : Nat := 790724264278265250492997

theorem tailTrace_1539930 : CollatzResearch.WordTrace tailWord_1539930 prefixEnd_1539930 790724264278265250492997 := by
  unfold tailWord_1539930
  simp only [CollatzResearch.WordTrace]
  refine ⟨14041465327776020987670311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37443907540736055967120829 14041465327776020987670311)
  ·
    refine ⟨21062197991664031481505467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14041465327776020987670311 21062197991664031481505467)
    ·
      refine ⟨31593296987496047222258201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21062197991664031481505467 31593296987496047222258201)
      ·
        refine ⟨23694972740622035416693651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31593296987496047222258201 23694972740622035416693651)
        ·
          refine ⟨35542459110933053125040477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23694972740622035416693651 35542459110933053125040477)
          ·
            refine ⟨13328422166599894921890179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35542459110933053125040477 13328422166599894921890179)
            ·
              refine ⟨19992633249899842382835269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13328422166599894921890179 19992633249899842382835269)
              ·
                refine ⟨3748618734356220446781613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19992633249899842382835269 3748618734356220446781613)
                ·
                  refine ⟨1405732025383582667543105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3748618734356220446781613 1405732025383582667543105)
                  ·
                    refine ⟨1054299019037687000657329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1405732025383582667543105 1054299019037687000657329)
                    ·
                      refine ⟨790724264278265250492997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1054299019037687000657329 790724264278265250492997)
                      ·
                        rfl

theorem cell23_1539930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 3, 2, 2].length) (baseStart_1539930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539930 prefixEnd_1539930 := by exact prefixLift 1539930
  have htrace : WordTrace (prefixWord ++ tailWord_1539930) baseStart_1539930 baseEnd_1539930 := by
    simpa [prefixWord, tailWord_1539930, baseEnd_1539930] using wordTrace_append hprefix tailTrace_1539930
  have hstable : (prefixWord ++ tailWord_1539930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539930).length < 2 ^ (prefixWord ++ tailWord_1539930).sum := by decide
  have hdescent : baseEnd_1539930 < baseStart_1539930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539936 : List Nat := [2, 1, 1, 3, 3, 3, 1, 9]
def baseStart_1539936 : Nat := 118140960795 + 1539936 * 2 ^ 59
def prefixEnd_1539936 : Nat := 4983230072969 + 3 ^ 40 * 1539936 * 2
def baseEnd_1539936 : Nat := 29286197968970082482147

theorem tailTrace_1539936 : CollatzResearch.WordTrace tailWord_1539936 prefixEnd_1539936 29286197968970082482147 := by
  unfold tailWord_1539936
  simp only [CollatzResearch.WordTrace]
  refine ⟨28083040074541173487699831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37444053432721564650266441 28083040074541173487699831)
  ·
    refine ⟨42124560111811760231549747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28083040074541173487699831 42124560111811760231549747)
    ·
      refine ⟨63186840167717640347324621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42124560111811760231549747 63186840167717640347324621)
      ·
        refine ⟨23695065062894115130246733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63186840167717640347324621 23695065062894115130246733)
        ·
          refine ⟨8885649398585293173842525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23695065062894115130246733 8885649398585293173842525)
          ·
            refine ⟨3332118524469484940190947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8885649398585293173842525 3332118524469484940190947)
            ·
              refine ⟨4998177786704227410286421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3332118524469484940190947 4998177786704227410286421)
              ·
                refine ⟨29286197968970082482147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4998177786704227410286421 29286197968970082482147)
                ·
                  rfl

theorem cell23_1539936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 9].length) (baseStart_1539936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539936 prefixEnd_1539936 := by exact prefixLift 1539936
  have htrace : WordTrace (prefixWord ++ tailWord_1539936) baseStart_1539936 baseEnd_1539936 := by
    simpa [prefixWord, tailWord_1539936, baseEnd_1539936] using wordTrace_append hprefix tailTrace_1539936
  have hstable : (prefixWord ++ tailWord_1539936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539936).length < 2 ^ (prefixWord ++ tailWord_1539936).sum := by decide
  have hdescent : baseEnd_1539936 < baseStart_1539936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539950 : List Nat := [4, 1, 2, 3, 1, 2, 2, 1, 1, 1, 5]
def baseStart_1539950 : Nat := 118140960795 + 1539950 * 2 ^ 59
def prefixEnd_1539950 : Nat := 4983230072969 + 3 ^ 40 * 1539950 * 2
def baseEnd_1539950 : Nat := 790734533891355172242905

theorem tailTrace_1539950 : CollatzResearch.WordTrace tailWord_1539950 prefixEnd_1539950 790734533891355172242905 := by
  unfold tailWord_1539950
  simp only [CollatzResearch.WordTrace]
  refine ⟨7020823846378953420801163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37444393847354418244272869 7020823846378953420801163)
  ·
    refine ⟨10531235769568430131201745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7020823846378953420801163 10531235769568430131201745)
    ·
      refine ⟨7898426827176322598401309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10531235769568430131201745 7898426827176322598401309)
      ·
        refine ⟨2961910060191120974400491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7898426827176322598401309 2961910060191120974400491)
        ·
          refine ⟨4442865090286681461600737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2961910060191120974400491 4442865090286681461600737)
          ·
            refine ⟨3332148817715011096200553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4442865090286681461600737 3332148817715011096200553)
            ·
              refine ⟨2499111613286258322150415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3332148817715011096200553 2499111613286258322150415)
              ·
                refine ⟨3748667419929387483225623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2499111613286258322150415 3748667419929387483225623)
                ·
                  refine ⟨5623001129894081224838435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3748667419929387483225623 5623001129894081224838435)
                  ·
                    refine ⟨8434501694841121837257653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5623001129894081224838435 8434501694841121837257653)
                    ·
                      refine ⟨790734533891355172242905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8434501694841121837257653 790734533891355172242905)
                      ·
                        rfl

theorem cell23_1539950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_1539950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1539950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1539950 prefixEnd_1539950 := by exact prefixLift 1539950
  have htrace : WordTrace (prefixWord ++ tailWord_1539950) baseStart_1539950 baseEnd_1539950 := by
    simpa [prefixWord, tailWord_1539950, baseEnd_1539950] using wordTrace_append hprefix tailTrace_1539950
  have hstable : (prefixWord ++ tailWord_1539950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539950).length < 2 ^ (prefixWord ++ tailWord_1539950).sum := by decide
  have hdescent : baseEnd_1539950 < baseStart_1539950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540016 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 4]
def baseStart_1540016 : Nat := 118140960795 + 1540016 * 2 ^ 59
def prefixEnd_1540016 : Nat := 4983230072969 + 3 ^ 40 * 1540016 * 2
def baseEnd_1540016 : Nat := 790768423614551914017601

theorem tailTrace_1540016 : CollatzResearch.WordTrace tailWord_1540016 prefixEnd_1540016 790768423614551914017601 := by
  unfold tailWord_1540016
  simp only [CollatzResearch.WordTrace]
  refine ⟨28084498994396260319155951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37445998659195013758874601 28084498994396260319155951)
  ·
    refine ⟨42126748491594390478733927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28084498994396260319155951 42126748491594390478733927)
    ·
      refine ⟨63190122737391585718100891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42126748491594390478733927 63190122737391585718100891)
      ·
        refine ⟨94785184106087378577151337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63190122737391585718100891 94785184106087378577151337)
        ·
          refine ⟨71088888079565533932863503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94785184106087378577151337 71088888079565533932863503)
          ·
            refine ⟨106633332119348300899295255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71088888079565533932863503 106633332119348300899295255)
            ·
              refine ⟨159949998179022451348942883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106633332119348300899295255 159949998179022451348942883)
              ·
                refine ⟨239924997268533677023414325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159949998179022451348942883 239924997268533677023414325)
                ·
                  refine ⟨22492968493925032220945093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 239924997268533677023414325 22492968493925032220945093)
                  ·
                    refine ⟨4217431592610943541427205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22492968493925032220945093 4217431592610943541427205)
                    ·
                      refine ⟨790768423614551914017601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4217431592610943541427205 790768423614551914017601)
                      ·
                        rfl

theorem cell23_1540016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 4].length) (baseStart_1540016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540016 prefixEnd_1540016 := by exact prefixLift 1540016
  have htrace : WordTrace (prefixWord ++ tailWord_1540016) baseStart_1540016 baseEnd_1540016 := by
    simpa [prefixWord, tailWord_1540016, baseEnd_1540016] using wordTrace_append hprefix tailTrace_1540016
  have hstable : (prefixWord ++ tailWord_1540016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540016).length < 2 ^ (prefixWord ++ tailWord_1540016).sum := by decide
  have hdescent : baseEnd_1540016 < baseStart_1540016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540071 : List Nat := [1, 1, 5, 2, 3, 2, 1, 2, 2, 2, 2]
def baseStart_1540071 : Nat := 118140960795 + 1540071 * 2 ^ 59
def prefixEnd_1540071 : Nat := 4983230072969 + 3 ^ 40 * 1540071 * 2
def baseEnd_1540071 : Nat := 790796665050549198829849

theorem tailTrace_1540071 : CollatzResearch.WordTrace tailWord_1540071 prefixEnd_1540071 790796665050549198829849 := by
  unfold tailWord_1540071
  simp only [CollatzResearch.WordTrace]
  refine ⟨56171004003593265031564067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37447336002395510021042711 56171004003593265031564067)
  ·
    refine ⟨84256506005389897547346101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56171004003593265031564067 84256506005389897547346101)
    ·
      refine ⟨7899047438005302895063697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84256506005389897547346101 7899047438005302895063697)
      ·
        refine ⟨5924285578503977171297773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7899047438005302895063697 5924285578503977171297773)
        ·
          refine ⟨2221607091938991439236665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5924285578503977171297773 2221607091938991439236665)
          ·
            refine ⟨1666205318954243579427499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2221607091938991439236665 1666205318954243579427499)
            ·
              refine ⟨2499307978431365369141249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1666205318954243579427499 2499307978431365369141249)
              ·
                refine ⟨1874480983823524026855937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2499307978431365369141249 1874480983823524026855937)
                ·
                  refine ⟨1405860737867643020141953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1874480983823524026855937 1405860737867643020141953)
                  ·
                    refine ⟨1054395553400732265106465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1405860737867643020141953 1054395553400732265106465)
                    ·
                      refine ⟨790796665050549198829849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1054395553400732265106465 790796665050549198829849)
                      ·
                        rfl

theorem cell23_1540071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_1540071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540071 prefixEnd_1540071 := by exact prefixLift 1540071
  have htrace : WordTrace (prefixWord ++ tailWord_1540071) baseStart_1540071 baseEnd_1540071 := by
    simpa [prefixWord, tailWord_1540071, baseEnd_1540071] using wordTrace_append hprefix tailTrace_1540071
  have hstable : (prefixWord ++ tailWord_1540071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540071).length < 2 ^ (prefixWord ++ tailWord_1540071).sum := by decide
  have hdescent : baseEnd_1540071 < baseStart_1540071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540077 : List Nat := [1, 5, 1, 4, 1, 1, 2, 1, 7]
def baseStart_1540077 : Nat := 118140960795 + 1540077 * 2 ^ 59
def prefixEnd_1540077 : Nat := 4983230072969 + 3 ^ 40 * 1540077 * 2
def baseEnd_1540077 : Nat := 87866638437164019483869

theorem tailTrace_1540077 : CollatzResearch.WordTrace tailWord_1540077 prefixEnd_1540077 87866638437164019483869 := by
  unfold tailWord_1540077
  simp only [CollatzResearch.WordTrace]
  refine ⟨56171222841571528056282485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37447481894381018704188323 56171222841571528056282485)
  ·
    refine ⟨5266052141397330755276483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56171222841571528056282485 5266052141397330755276483)
    ·
      refine ⟨7899078212095996132914725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5266052141397330755276483 7899078212095996132914725)
      ·
        refine ⟨1481077164767999274921511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7899078212095996132914725 1481077164767999274921511)
        ·
          refine ⟨2221615747151998912382267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1481077164767999274921511 2221615747151998912382267)
          ·
            refine ⟨3332423620727998368573401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2221615747151998912382267 3332423620727998368573401)
            ·
              refine ⟨2499317715545998776430051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3332423620727998368573401 2499317715545998776430051)
              ·
                refine ⟨3748976573318998164645077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2499317715545998776430051 3748976573318998164645077)
                ·
                  refine ⟨87866638437164019483869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3748976573318998164645077 87866638437164019483869)
                  ·
                    rfl

theorem cell23_1540077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_1540077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540077 prefixEnd_1540077 := by exact prefixLift 1540077
  have htrace : WordTrace (prefixWord ++ tailWord_1540077) baseStart_1540077 baseEnd_1540077 := by
    simpa [prefixWord, tailWord_1540077, baseEnd_1540077] using wordTrace_append hprefix tailTrace_1540077
  have hstable : (prefixWord ++ tailWord_1540077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540077).length < 2 ^ (prefixWord ++ tailWord_1540077).sum := by decide
  have hdescent : baseEnd_1540077 < baseStart_1540077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540093 : List Nat := [1, 4, 1, 1, 1, 2, 3, 2, 1, 3, 4]
def baseStart_1540093 : Nat := 118140960795 + 1540093 * 2 ^ 59
def prefixEnd_1540093 : Nat := 4983230072969 + 3 ^ 40 * 1540093 * 2
def baseEnd_1540093 : Nat := 790807961624948112754747

theorem tailTrace_1540093 : CollatzResearch.WordTrace tailWord_1540093 prefixEnd_1540093 790807961624948112754747 := by
  unfold tailWord_1540093
  simp only [CollatzResearch.WordTrace]
  refine ⟨56171806409513562788864933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37447870939675708525909955 56171806409513562788864933)
  ·
    refine ⟨10532213701783793022912175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56171806409513562788864933 10532213701783793022912175)
    ·
      refine ⟨15798320552675689534368263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10532213701783793022912175 15798320552675689534368263)
      ·
        refine ⟨23697480829013534301552395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15798320552675689534368263 23697480829013534301552395)
        ·
          refine ⟨35546221243520301452328593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23697480829013534301552395 35546221243520301452328593)
          ·
            refine ⟨26659665932640226089246445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35546221243520301452328593 26659665932640226089246445)
            ·
              refine ⟨9997374724740084783467417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26659665932640226089246445 9997374724740084783467417)
              ·
                refine ⟨7498031043555063587600563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9997374724740084783467417 7498031043555063587600563)
                ·
                  refine ⟨11247046565332595381400845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7498031043555063587600563 11247046565332595381400845)
                  ·
                    refine ⟨4217642461999723268025317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11247046565332595381400845 4217642461999723268025317)
                    ·
                      refine ⟨790807961624948112754747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4217642461999723268025317 790807961624948112754747)
                      ·
                        rfl

theorem cell23_1540093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_1540093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540093 prefixEnd_1540093 := by exact prefixLift 1540093
  have htrace : WordTrace (prefixWord ++ tailWord_1540093) baseStart_1540093 baseEnd_1540093 := by
    simpa [prefixWord, tailWord_1540093, baseEnd_1540093] using wordTrace_append hprefix tailTrace_1540093
  have hstable : (prefixWord ++ tailWord_1540093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540093).length < 2 ^ (prefixWord ++ tailWord_1540093).sum := by decide
  have hdescent : baseEnd_1540093 < baseStart_1540093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540110 : List Nat := [4, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4]
def baseStart_1540110 : Nat := 118140960795 + 1540110 * 2 ^ 59
def prefixEnd_1540110 : Nat := 4983230072969 + 3 ^ 40 * 1540110 * 2
def baseEnd_1540110 : Nat := 790816690796074546242169

theorem tailTrace_1540110 : CollatzResearch.WordTrace tailWord_1540110 prefixEnd_1540110 790816690796074546242169 := by
  unfold tailWord_1540110
  simp only [CollatzResearch.WordTrace]
  refine ⟨7021553306306496836529223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37448284300301316461489189 7021553306306496836529223)
  ·
    refine ⟨10532329959459745254793835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7021553306306496836529223 10532329959459745254793835)
    ·
      refine ⟨15798494939189617882190753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10532329959459745254793835 15798494939189617882190753)
      ·
        refine ⟨11848871204392213411643065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15798494939189617882190753 11848871204392213411643065)
        ·
          refine ⟨8886653403294160058732299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11848871204392213411643065 8886653403294160058732299)
          ·
            refine ⟨13329980104941240088098449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8886653403294160058732299 13329980104941240088098449)
            ·
              refine ⟨9997485078705930066073837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13329980104941240088098449 9997485078705930066073837)
              ·
                refine ⟨3749056904514723774777689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9997485078705930066073837 3749056904514723774777689)
                ·
                  refine ⟨2811792678386042831083267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3749056904514723774777689 2811792678386042831083267)
                  ·
                    refine ⟨4217689017579064246624901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2811792678386042831083267 4217689017579064246624901)
                    ·
                      refine ⟨790816690796074546242169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4217689017579064246624901 790816690796074546242169)
                      ·
                        rfl

theorem cell23_1540110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_1540110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540110 prefixEnd_1540110 := by exact prefixLift 1540110
  have htrace : WordTrace (prefixWord ++ tailWord_1540110) baseStart_1540110 baseEnd_1540110 := by
    simpa [prefixWord, tailWord_1540110, baseEnd_1540110] using wordTrace_append hprefix tailTrace_1540110
  have hstable : (prefixWord ++ tailWord_1540110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540110).length < 2 ^ (prefixWord ++ tailWord_1540110).sum := by decide
  have hdescent : baseEnd_1540110 < baseStart_1540110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540133 : List Nat := [1, 3, 1, 2, 2, 3, 2, 1, 8]
def baseStart_1540133 : Nat := 118140960795 + 1540133 * 2 ^ 59
def prefixEnd_1540133 : Nat := 4983230072969 + 3 ^ 40 * 1540133 * 2
def baseEnd_1540133 : Nat := 87869833427903106250507

theorem tailTrace_1540133 : CollatzResearch.WordTrace tailWord_1540133 prefixEnd_1540133 87869833427903106250507 := by
  unfold tailWord_1540133
  simp only [CollatzResearch.WordTrace]
  refine ⟨56173265329368649620321053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37448843552912433080214035 56173265329368649620321053)
  ·
    refine ⟨21064974498513243607620395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56173265329368649620321053 21064974498513243607620395)
    ·
      refine ⟨31597461747769865411430593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21064974498513243607620395 31597461747769865411430593)
      ·
        refine ⟨23698096310827399058572945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31597461747769865411430593 23698096310827399058572945)
        ·
          refine ⟨17773572233120549293929709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23698096310827399058572945 17773572233120549293929709)
          ·
            refine ⟨6665089587420205985223641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17773572233120549293929709 6665089587420205985223641)
            ·
              refine ⟨4998817190565154488917731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6665089587420205985223641 4998817190565154488917731)
              ·
                refine ⟨7498225785847731733376597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4998817190565154488917731 7498225785847731733376597)
                ·
                  refine ⟨87869833427903106250507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7498225785847731733376597 87869833427903106250507)
                  ·
                    rfl

theorem cell23_1540133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 8].length) (baseStart_1540133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540133 prefixEnd_1540133 := by exact prefixLift 1540133
  have htrace : WordTrace (prefixWord ++ tailWord_1540133) baseStart_1540133 baseEnd_1540133 := by
    simpa [prefixWord, tailWord_1540133, baseEnd_1540133] using wordTrace_append hprefix tailTrace_1540133
  have hstable : (prefixWord ++ tailWord_1540133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540133).length < 2 ^ (prefixWord ++ tailWord_1540133).sum := by decide
  have hdescent : baseEnd_1540133 < baseStart_1540133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540143 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 2, 5, 3]
def baseStart_1540143 : Nat := 118140960795 + 1540143 * 2 ^ 59
def prefixEnd_1540143 : Nat := 4983230072969 + 3 ^ 40 * 1540143 * 2
def baseEnd_1540143 : Nat := 790833635657672917129517

theorem tailTrace_1540143 : CollatzResearch.WordTrace tailWord_1540143 prefixEnd_1540143 790833635657672917129517 := by
  unfold tailWord_1540143
  simp only [CollatzResearch.WordTrace]
  refine ⟨56173630059332421328185083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37449086706221614218790055 56173630059332421328185083)
  ·
    refine ⟨84260445088998631992277625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56173630059332421328185083 84260445088998631992277625)
    ·
      refine ⟨63195333816748973994208219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84260445088998631992277625 63195333816748973994208219)
      ·
        refine ⟨94793000725123460991312329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63195333816748973994208219 94793000725123460991312329)
        ·
          refine ⟨71094750543842595743484247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94793000725123460991312329 71094750543842595743484247)
          ·
            refine ⟨106642125815763893615226371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71094750543842595743484247 106642125815763893615226371)
            ·
              refine ⟨159963188723645840422839557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106642125815763893615226371 159963188723645840422839557)
              ·
                refine ⟨29993097885683595079282417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159963188723645840422839557 29993097885683595079282417)
                ·
                  refine ⟨22494823414262696309461813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29993097885683595079282417 22494823414262696309461813)
                  ·
                    refine ⟨2108889695087127779012045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22494823414262696309461813 2108889695087127779012045)
                    ·
                      refine ⟨790833635657672917129517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2108889695087127779012045 790833635657672917129517)
                      ·
                        rfl

theorem cell23_1540143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 5, 3].length) (baseStart_1540143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540143 prefixEnd_1540143 := by exact prefixLift 1540143
  have htrace : WordTrace (prefixWord ++ tailWord_1540143) baseStart_1540143 baseEnd_1540143 := by
    simpa [prefixWord, tailWord_1540143, baseEnd_1540143] using wordTrace_append hprefix tailTrace_1540143
  have hstable : (prefixWord ++ tailWord_1540143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540143).length < 2 ^ (prefixWord ++ tailWord_1540143).sum := by decide
  have hdescent : baseEnd_1540143 < baseStart_1540143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540193 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 5, 6]
def baseStart_1540193 : Nat := 118140960795 + 1540193 * 2 ^ 59
def prefixEnd_1540193 : Nat := 4983230072969 + 3 ^ 40 * 1540193 * 2
def baseEnd_1540193 : Nat := 263619769896799240501429

theorem tailTrace_1540193 : CollatzResearch.WordTrace tailWord_1540193 prefixEnd_1540193 263619769896799240501429 := by
  unfold tailWord_1540193
  simp only [CollatzResearch.WordTrace]
  refine ⟨56175453709151279867505233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37450302472767519911670155 56175453709151279867505233)
  ·
    refine ⟨42131590281863459900628925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56175453709151279867505233 42131590281863459900628925)
    ·
      refine ⟨15799346355698797462735847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42131590281863459900628925 15799346355698797462735847)
      ·
        refine ⟨23699019533548196194103771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15799346355698797462735847 23699019533548196194103771)
        ·
          refine ⟨35548529300322294291155657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23699019533548196194103771 35548529300322294291155657)
          ·
            refine ⟨26661396975241720718366743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35548529300322294291155657 26661396975241720718366743)
            ·
              refine ⟨39992095462862581077550115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26661396975241720718366743 39992095462862581077550115)
              ·
                refine ⟨59988143194293871616325173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39992095462862581077550115 59988143194293871616325173)
                ·
                  refine ⟨5623888424465050464030485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59988143194293871616325173 5623888424465050464030485)
                  ·
                    refine ⟨263619769896799240501429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5623888424465050464030485 263619769896799240501429)
                    ·
                      rfl

theorem cell23_1540193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_1540193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540193 prefixEnd_1540193 := by exact prefixLift 1540193
  have htrace : WordTrace (prefixWord ++ tailWord_1540193) baseStart_1540193 baseEnd_1540193 := by
    simpa [prefixWord, tailWord_1540193, baseEnd_1540193] using wordTrace_append hprefix tailTrace_1540193
  have hstable : (prefixWord ++ tailWord_1540193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540193).length < 2 ^ (prefixWord ++ tailWord_1540193).sum := by decide
  have hdescent : baseEnd_1540193 < baseStart_1540193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540210 : List Nat := [3, 2, 1, 2, 2, 2, 1, 3, 1, 6]
def baseStart_1540210 : Nat := 118140960795 + 1540210 * 2 ^ 59
def prefixEnd_1540210 : Nat := 4983230072969 + 3 ^ 40 * 1540210 * 2
def baseEnd_1540210 : Nat := 263622679620508051663903

theorem tailTrace_1540210 : CollatzResearch.WordTrace tailWord_1540210 prefixEnd_1540210 263622679620508051663903 := by
  unfold tailWord_1540210
  simp only [CollatzResearch.WordTrace]
  refine ⟨14044018437522422942718521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37450715833393127847249389 14044018437522422942718521)
  ·
    refine ⟨10533013828141817207038891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14044018437522422942718521 10533013828141817207038891)
    ·
      refine ⟨15799520742212725810558337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10533013828141817207038891 15799520742212725810558337)
      ·
        refine ⟨11849640556659544357918753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15799520742212725810558337 11849640556659544357918753)
        ·
          refine ⟨8887230417494658268439065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11849640556659544357918753 8887230417494658268439065)
          ·
            refine ⟨6665422813120993701329299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8887230417494658268439065 6665422813120993701329299)
            ·
              refine ⟨9998134219681490551993949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6665422813120993701329299 9998134219681490551993949)
              ·
                refine ⟨3749300332380558956997731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9998134219681490551993949 3749300332380558956997731)
                ·
                  refine ⟨5623950498570838435496597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3749300332380558956997731 5623950498570838435496597)
                  ·
                    refine ⟨263622679620508051663903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5623950498570838435496597 263622679620508051663903)
                    ·
                      rfl

theorem cell23_1540210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_1540210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540210 prefixEnd_1540210 := by exact prefixLift 1540210
  have htrace : WordTrace (prefixWord ++ tailWord_1540210) baseStart_1540210 baseEnd_1540210 := by
    simpa [prefixWord, tailWord_1540210, baseEnd_1540210] using wordTrace_append hprefix tailTrace_1540210
  have hstable : (prefixWord ++ tailWord_1540210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540210).length < 2 ^ (prefixWord ++ tailWord_1540210).sum := by decide
  have hdescent : baseEnd_1540210 < baseStart_1540210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540234 : List Nat := [3, 1, 2, 3, 1, 2, 4, 1, 1, 1, 4]
def baseStart_1540234 : Nat := 118140960795 + 1540234 * 2 ^ 59
def prefixEnd_1540234 : Nat := 4983230072969 + 3 ^ 40 * 1540234 * 2
def baseEnd_1540234 : Nat := 790880362397232061091599

theorem tailTrace_1540234 : CollatzResearch.WordTrace tailWord_1540234 prefixEnd_1540234 790880362397232061091599 := by
  unfold tailWord_1540234
  simp only [CollatzResearch.WordTrace]
  refine ⟨14044237275500685967436939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37451299401335162579831837 14044237275500685967436939)
  ·
    refine ⟨21066355913251028951155409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14044237275500685967436939 21066355913251028951155409)
    ·
      refine ⟨15799766934938271713366557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21066355913251028951155409 15799766934938271713366557)
      ·
        refine ⟨5924912600601851892512459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15799766934938271713366557 5924912600601851892512459)
        ·
          refine ⟨8887368900902777838768689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5924912600601851892512459 8887368900902777838768689)
          ·
            refine ⟨6665526675677083379076517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8887368900902777838768689 6665526675677083379076517)
            ·
              refine ⟨1249786251689453133576847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6665526675677083379076517 1249786251689453133576847)
              ·
                refine ⟨1874679377534179700365271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1249786251689453133576847 1874679377534179700365271)
                ·
                  refine ⟨2812019066301269550547907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1874679377534179700365271 2812019066301269550547907)
                  ·
                    refine ⟨4218028599451904325821861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2812019066301269550547907 4218028599451904325821861)
                    ·
                      refine ⟨790880362397232061091599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4218028599451904325821861 790880362397232061091599)
                      ·
                        rfl

theorem cell23_1540234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_1540234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540234 prefixEnd_1540234 := by exact prefixLift 1540234
  have htrace : WordTrace (prefixWord ++ tailWord_1540234) baseStart_1540234 baseEnd_1540234 := by
    simpa [prefixWord, tailWord_1540234, baseEnd_1540234] using wordTrace_append hprefix tailTrace_1540234
  have hstable : (prefixWord ++ tailWord_1540234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540234).length < 2 ^ (prefixWord ++ tailWord_1540234).sum := by decide
  have hdescent : baseEnd_1540234 < baseStart_1540234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540243 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 6]
def baseStart_1540243 : Nat := 118140960795 + 1540243 * 2 ^ 59
def prefixEnd_1540243 : Nat := 4983230072969 + 3 ^ 40 * 1540243 * 2
def baseEnd_1540243 : Nat := 790884983723122525879057

theorem tailTrace_1540243 : CollatzResearch.WordTrace tailWord_1540243 prefixEnd_1540243 790884983723122525879057 := by
  unfold tailWord_1540243
  simp only [CollatzResearch.WordTrace]
  refine ⟨56177277358970138406825383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37451518239313425604550255 56177277358970138406825383)
  ·
    refine ⟨84265916038455207610238075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56177277358970138406825383 84265916038455207610238075)
    ·
      refine ⟨126398874057682811415357113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84265916038455207610238075 126398874057682811415357113)
      ·
        refine ⟨94799155543262108561517835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126398874057682811415357113 94799155543262108561517835)
        ·
          refine ⟨142198733314893162842276753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94799155543262108561517835 142198733314893162842276753)
          ·
            refine ⟨106649049986169872131707565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142198733314893162842276753 106649049986169872131707565)
            ·
              refine ⟨39993393744813702049390337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106649049986169872131707565 39993393744813702049390337)
              ·
                refine ⟨29995045308610276537042753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39993393744813702049390337 29995045308610276537042753)
                ·
                  refine ⟨22496283981457707402782065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29995045308610276537042753 22496283981457707402782065)
                  ·
                    refine ⟨16872212986093280552086549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22496283981457707402782065 16872212986093280552086549)
                    ·
                      refine ⟨790884983723122525879057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16872212986093280552086549 790884983723122525879057)
                      ·
                        rfl

theorem cell23_1540243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 6].length) (baseStart_1540243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540243 prefixEnd_1540243 := by exact prefixLift 1540243
  have htrace : WordTrace (prefixWord ++ tailWord_1540243) baseStart_1540243 baseEnd_1540243 := by
    simpa [prefixWord, tailWord_1540243, baseEnd_1540243] using wordTrace_append hprefix tailTrace_1540243
  have hstable : (prefixWord ++ tailWord_1540243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540243).length < 2 ^ (prefixWord ++ tailWord_1540243).sum := by decide
  have hdescent : baseEnd_1540243 < baseStart_1540243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540254 : List Nat := [4, 3, 1, 1, 3, 1, 1, 2, 1, 1, 5]
def baseStart_1540254 : Nat := 118140960795 + 1540254 * 2 ^ 59
def prefixEnd_1540254 : Nat := 4983230072969 + 3 ^ 40 * 1540254 * 2
def baseEnd_1540254 : Nat := 790890632010321982841507

theorem tailTrace_1540254 : CollatzResearch.WordTrace tailWord_1540254 prefixEnd_1540254 790890632010321982841507 := by
  unfold tailWord_1540254
  simp only [CollatzResearch.WordTrace]
  refine ⟨7022209820241285910684477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37451785707953524856983877 7022209820241285910684477)
  ·
    refine ⟨2633328682590482216506679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7022209820241285910684477 2633328682590482216506679)
    ·
      refine ⟨3949993023885723324760019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2633328682590482216506679 3949993023885723324760019)
      ·
        refine ⟨5924989535828584987140029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3949993023885723324760019 5924989535828584987140029)
        ·
          refine ⟨2221871075935719370177511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5924989535828584987140029 2221871075935719370177511)
          ·
            refine ⟨3332806613903579055266267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2221871075935719370177511 3332806613903579055266267)
            ·
              refine ⟨4999209920855368582899401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3332806613903579055266267 4999209920855368582899401)
              ·
                refine ⟨3749407440641526437174551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4999209920855368582899401 3749407440641526437174551)
                ·
                  refine ⟨5624111160962289655761827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3749407440641526437174551 5624111160962289655761827)
                  ·
                    refine ⟨8436166741443434483642741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5624111160962289655761827 8436166741443434483642741)
                    ·
                      refine ⟨790890632010321982841507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8436166741443434483642741 790890632010321982841507)
                      ·
                        rfl

theorem cell23_1540254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_1540254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540254 prefixEnd_1540254 := by exact prefixLift 1540254
  have htrace : WordTrace (prefixWord ++ tailWord_1540254) baseStart_1540254 baseEnd_1540254 := by
    simpa [prefixWord, tailWord_1540254, baseEnd_1540254] using wordTrace_append hprefix tailTrace_1540254
  have hstable : (prefixWord ++ tailWord_1540254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540254).length < 2 ^ (prefixWord ++ tailWord_1540254).sum := by decide
  have hdescent : baseEnd_1540254 < baseStart_1540254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540320 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 4]
def baseStart_1540320 : Nat := 118140960795 + 1540320 * 2 ^ 59
def prefixEnd_1540320 : Nat := 4983230072969 + 3 ^ 40 * 1540320 * 2
def baseEnd_1540320 : Nat := 790924521733518724616203

theorem tailTrace_1540320 : CollatzResearch.WordTrace tailWord_1540320 prefixEnd_1540320 790924521733518724616203 := by
  unfold tailWord_1540320
  simp only [CollatzResearch.WordTrace]
  refine ⟨28090042889845590278689207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37453390519794120371585609 28090042889845590278689207)
  ·
    refine ⟨42135064334768385418033811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28090042889845590278689207 42135064334768385418033811)
    ·
      refine ⟨63202596502152578127050717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42135064334768385418033811 63202596502152578127050717)
      ·
        refine ⟨23700973688307216797644019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63202596502152578127050717 23700973688307216797644019)
        ·
          refine ⟨35551460532460825196466029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23700973688307216797644019 35551460532460825196466029)
          ·
            refine ⟨13331797699672809448674761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35551460532460825196466029 13331797699672809448674761)
            ·
              refine ⟨9998848274754607086506071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13331797699672809448674761 9998848274754607086506071)
              ·
                refine ⟨14998272412131910629759107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9998848274754607086506071 14998272412131910629759107)
                ·
                  refine ⟨22497408618197865944638661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14998272412131910629759107 22497408618197865944638661)
                  ·
                    refine ⟨4218264115912099864619749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22497408618197865944638661 4218264115912099864619749)
                    ·
                      refine ⟨790924521733518724616203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4218264115912099864619749 790924521733518724616203)
                      ·
                        rfl

theorem cell23_1540320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_1540320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540320 prefixEnd_1540320 := by exact prefixLift 1540320
  have htrace : WordTrace (prefixWord ++ tailWord_1540320) baseStart_1540320 baseEnd_1540320 := by
    simpa [prefixWord, tailWord_1540320, baseEnd_1540320] using wordTrace_append hprefix tailTrace_1540320
  have hstable : (prefixWord ++ tailWord_1540320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540320).length < 2 ^ (prefixWord ++ tailWord_1540320).sum := by decide
  have hdescent : baseEnd_1540320 < baseStart_1540320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540322 : List Nat := [3, 3, 4, 1, 2, 1, 1, 2, 1, 2, 3]
def baseStart_1540322 : Nat := 118140960795 + 1540322 * 2 ^ 59
def prefixEnd_1540322 : Nat := 4983230072969 + 3 ^ 40 * 1540322 * 2
def baseEnd_1540322 : Nat := 790925548694827716791195

theorem tailTrace_1540322 : CollatzResearch.WordTrace tailWord_1540322 prefixEnd_1540322 790925548694827716791195 := by
  unfold tailWord_1540322
  simp only [CollatzResearch.WordTrace]
  refine ⟨14045039681420983724737805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37453439150455956599300813 14045039681420983724737805)
  ·
    refine ⟨5266889880532868896776677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14045039681420983724737805 5266889880532868896776677)
    ·
      refine ⟨987541852599912918145627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5266889880532868896776677 987541852599912918145627)
      ·
        refine ⟨1481312778899869377218441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 987541852599912918145627 1481312778899869377218441)
        ·
          refine ⟨1110984584174902032913831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1481312778899869377218441 1110984584174902032913831)
          ·
            refine ⟨1666476876262353049370747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1110984584174902032913831 1666476876262353049370747)
            ·
              refine ⟨2499715314393529574056121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1666476876262353049370747 2499715314393529574056121)
              ·
                refine ⟨1874786485795147180542091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2499715314393529574056121 1874786485795147180542091)
                ·
                  refine ⟨2812179728692720770813137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1874786485795147180542091 2812179728692720770813137)
                  ·
                    refine ⟨2109134796519540578109853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2812179728692720770813137 2109134796519540578109853)
                    ·
                      refine ⟨790925548694827716791195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2109134796519540578109853 790925548694827716791195)
                      ·
                        rfl

theorem cell23_1540322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_1540322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540322 prefixEnd_1540322 := by exact prefixLift 1540322
  have htrace : WordTrace (prefixWord ++ tailWord_1540322) baseStart_1540322 baseEnd_1540322 := by
    simpa [prefixWord, tailWord_1540322, baseEnd_1540322] using wordTrace_append hprefix tailTrace_1540322
  have hstable : (prefixWord ++ tailWord_1540322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540322).length < 2 ^ (prefixWord ++ tailWord_1540322).sum := by decide
  have hdescent : baseEnd_1540322 < baseStart_1540322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540327 : List Nat := [1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 5]
def baseStart_1540327 : Nat := 118140960795 + 1540327 * 2 ^ 59
def prefixEnd_1540327 : Nat := 4983230072969 + 3 ^ 40 * 1540327 * 2
def baseEnd_1540327 : Nat := 790928116098100197228671

theorem tailTrace_1540327 : CollatzResearch.WordTrace tailWord_1540327 prefixEnd_1540327 790928116098100197228671 := by
  unfold tailWord_1540327
  simp only [CollatzResearch.WordTrace]
  refine ⟨56180341090665820752883235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37453560727110547168588823 56180341090665820752883235)
  ·
    refine ⟨84270511635998731129324853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56180341090665820752883235 84270511635998731129324853)
    ·
      refine ⟨7900360465874881043374205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84270511635998731129324853 7900360465874881043374205)
      ·
        refine ⟨2962635174703080391265327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7900360465874881043374205 2962635174703080391265327)
        ·
          refine ⟨4443952762054620586897991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2962635174703080391265327 4443952762054620586897991)
          ·
            refine ⟨6665929143081930880346987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4443952762054620586897991 6665929143081930880346987)
            ·
              refine ⟨9998893714622896320520481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6665929143081930880346987 9998893714622896320520481)
              ·
                refine ⟨7499170285967172240390361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9998893714622896320520481 7499170285967172240390361)
                ·
                  refine ⟨5624377714475379180292771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7499170285967172240390361 5624377714475379180292771)
                  ·
                    refine ⟨8436566571713068770439157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5624377714475379180292771 8436566571713068770439157)
                    ·
                      refine ⟨790928116098100197228671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8436566571713068770439157 790928116098100197228671)
                      ·
                        rfl

theorem cell23_1540327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_1540327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540327 prefixEnd_1540327 := by exact prefixLift 1540327
  have htrace : WordTrace (prefixWord ++ tailWord_1540327) baseStart_1540327 baseEnd_1540327 := by
    simpa [prefixWord, tailWord_1540327, baseEnd_1540327] using wordTrace_append hprefix tailTrace_1540327
  have hstable : (prefixWord ++ tailWord_1540327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540327).length < 2 ^ (prefixWord ++ tailWord_1540327).sum := by decide
  have hdescent : baseEnd_1540327 < baseStart_1540327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540330 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 9]
def baseStart_1540330 : Nat := 118140960795 + 1540330 * 2 ^ 59
def prefixEnd_1540330 : Nat := 4983230072969 + 3 ^ 40 * 1540330 * 2
def baseEnd_1540330 : Nat := 87881072948895965054573

theorem tailTrace_1540330 : CollatzResearch.WordTrace tailWord_1540330 prefixEnd_1540330 87881072948895965054573 := by
  unfold tailWord_1540330
  simp only [CollatzResearch.WordTrace]
  refine ⟨14045112627413738066310611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37453633673103301510161629 14045112627413738066310611)
  ·
    refine ⟨21067668941120607099465917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14045112627413738066310611 21067668941120607099465917)
    ·
      refine ⟨7900375852920227662299719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21067668941120607099465917 7900375852920227662299719)
      ·
        refine ⟨11850563779380341493449579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7900375852920227662299719 11850563779380341493449579)
        ·
          refine ⟨17775845669070512240174369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11850563779380341493449579 17775845669070512240174369)
          ·
            refine ⟨13331884251802884180130777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17775845669070512240174369 13331884251802884180130777)
            ·
              refine ⟨9998913188852163135098083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13331884251802884180130777 9998913188852163135098083)
              ·
                refine ⟨14998369783278244702647125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9998913188852163135098083 14998369783278244702647125)
                ·
                  refine ⟨87881072948895965054573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14998369783278244702647125 87881072948895965054573)
                  ·
                    rfl

theorem cell23_1540330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 9].length) (baseStart_1540330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540330 prefixEnd_1540330 := by exact prefixLift 1540330
  have htrace : WordTrace (prefixWord ++ tailWord_1540330) baseStart_1540330 baseEnd_1540330 := by
    simpa [prefixWord, tailWord_1540330, baseEnd_1540330] using wordTrace_append hprefix tailTrace_1540330
  have hstable : (prefixWord ++ tailWord_1540330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540330).length < 2 ^ (prefixWord ++ tailWord_1540330).sum := by decide
  have hdescent : baseEnd_1540330 < baseStart_1540330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540394 : List Nat := [3, 1, 4, 2, 2, 1, 1, 1, 1, 7]
def baseStart_1540394 : Nat := 118140960795 + 1540394 * 2 ^ 59
def prefixEnd_1540394 : Nat := 4983230072969 + 3 ^ 40 * 1540394 * 2
def baseEnd_1540394 : Nat := 263654173100650478363621

theorem tailTrace_1540394 : CollatzResearch.WordTrace tailWord_1540394 prefixEnd_1540394 263654173100650478363621 := by
  unfold tailWord_1540394
  simp only [CollatzResearch.WordTrace]
  refine ⟨14045696195355772798893059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37455189854282060797048157 14045696195355772798893059)
  ·
    refine ⟨21068544293033659198339589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14045696195355772798893059 21068544293033659198339589)
    ·
      refine ⟨3950352054943811099688673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21068544293033659198339589 3950352054943811099688673)
      ·
        refine ⟨2962764041207858324766505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3950352054943811099688673 2962764041207858324766505)
        ·
          refine ⟨2222073030905893743574879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2962764041207858324766505 2222073030905893743574879)
          ·
            refine ⟨3333109546358840615362319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2222073030905893743574879 3333109546358840615362319)
            ·
              refine ⟨4999664319538260923043479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3333109546358840615362319 4999664319538260923043479)
              ·
                refine ⟨7499496479307391384565219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4999664319538260923043479 7499496479307391384565219)
                ·
                  refine ⟨11249244718961087076847829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7499496479307391384565219 11249244718961087076847829)
                  ·
                    refine ⟨263654173100650478363621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11249244718961087076847829 263654173100650478363621)
                    ·
                      rfl

theorem cell23_1540394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_1540394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540394 prefixEnd_1540394 := by exact prefixLift 1540394
  have htrace : WordTrace (prefixWord ++ tailWord_1540394) baseStart_1540394 baseEnd_1540394 := by
    simpa [prefixWord, tailWord_1540394, baseEnd_1540394] using wordTrace_append hprefix tailTrace_1540394
  have hstable : (prefixWord ++ tailWord_1540394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540394).length < 2 ^ (prefixWord ++ tailWord_1540394).sum := by decide
  have hdescent : baseEnd_1540394 < baseStart_1540394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540398 : List Nat := [4, 1, 3, 3, 1, 1, 2, 3, 5]
def baseStart_1540398 : Nat := 118140960795 + 1540398 * 2 ^ 59
def prefixEnd_1540398 : Nat := 4983230072969 + 3 ^ 40 * 1540398 * 2
def baseEnd_1540398 : Nat := 87884952580507713271205

theorem tailTrace_1540398 : CollatzResearch.WordTrace tailWord_1540398 prefixEnd_1540398 87884952580507713271205 := by
  unfold tailWord_1540398
  simp only [CollatzResearch.WordTrace]
  refine ⟨7022866334176074984839731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37455287115605733252478565 7022866334176074984839731)
  ·
    refine ⟨10534299501264112477259597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7022866334176074984839731 10534299501264112477259597)
    ·
      refine ⟨3950362312974042178972349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10534299501264112477259597 3950362312974042178972349)
      ·
        refine ⟨1481385867365265817114631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3950362312974042178972349 1481385867365265817114631)
        ·
          refine ⟨2222078801047898725671947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1481385867365265817114631 2222078801047898725671947)
          ·
            refine ⟨3333118201571848088507921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2222078801047898725671947 3333118201571848088507921)
            ·
              refine ⟨2499838651178886066380941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3333118201571848088507921 2499838651178886066380941)
              ·
                refine ⟨937439494192082274892853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2499838651178886066380941 937439494192082274892853)
                ·
                  refine ⟨87884952580507713271205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 937439494192082274892853 87884952580507713271205)
                  ·
                    rfl

theorem cell23_1540398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 3, 5].length) (baseStart_1540398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540398 prefixEnd_1540398 := by exact prefixLift 1540398
  have htrace : WordTrace (prefixWord ++ tailWord_1540398) baseStart_1540398 baseEnd_1540398 := by
    simpa [prefixWord, tailWord_1540398, baseEnd_1540398] using wordTrace_append hprefix tailTrace_1540398
  have hstable : (prefixWord ++ tailWord_1540398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540398).length < 2 ^ (prefixWord ++ tailWord_1540398).sum := by decide
  have hdescent : baseEnd_1540398 < baseStart_1540398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540400 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 5]
def baseStart_1540400 : Nat := 118140960795 + 1540400 * 2 ^ 59
def prefixEnd_1540400 : Nat := 4983230072969 + 3 ^ 40 * 1540400 * 2
def baseEnd_1540400 : Nat := 790965600185878411615835

theorem tailTrace_1540400 : CollatzResearch.WordTrace tailWord_1540400 prefixEnd_1540400 790965600185878411615835 := by
  unfold tailWord_1540400
  simp only [CollatzResearch.WordTrace]
  refine ⟨28091501809700677110145327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37455335746267569480193769 28091501809700677110145327)
  ·
    refine ⟨42137252714551015665217991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28091501809700677110145327 42137252714551015665217991)
    ·
      refine ⟨63205879071826523497826987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42137252714551015665217991 63205879071826523497826987)
      ·
        refine ⟨94808818607739785246740481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63205879071826523497826987 94808818607739785246740481)
        ·
          refine ⟨71106613955804838935055361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94808818607739785246740481 71106613955804838935055361)
          ·
            refine ⟨53329960466853629201291521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71106613955804838935055361 53329960466853629201291521)
            ·
              refine ⟨39997470350140221900968641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53329960466853629201291521 39997470350140221900968641)
              ·
                refine ⟨29998102762605166425726481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39997470350140221900968641 29998102762605166425726481)
                ·
                  refine ⟨22498577071953874819294861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29998102762605166425726481 22498577071953874819294861)
                  ·
                    refine ⟨8436966401982703057235573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22498577071953874819294861 8436966401982703057235573)
                    ·
                      refine ⟨790965600185878411615835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8436966401982703057235573 790965600185878411615835)
                      ·
                        rfl

theorem cell23_1540400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 5].length) (baseStart_1540400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540400 prefixEnd_1540400 := by exact prefixLift 1540400
  have htrace : WordTrace (prefixWord ++ tailWord_1540400) baseStart_1540400 baseEnd_1540400 := by
    simpa [prefixWord, tailWord_1540400, baseEnd_1540400] using wordTrace_append hprefix tailTrace_1540400
  have hstable : (prefixWord ++ tailWord_1540400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540400).length < 2 ^ (prefixWord ++ tailWord_1540400).sum := by decide
  have hdescent : baseEnd_1540400 < baseStart_1540400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540458 : List Nat := [3, 1, 3, 3, 1, 1, 3, 3, 1, 4]
def baseStart_1540458 : Nat := 118140960795 + 1540458 * 2 ^ 59
def prefixEnd_1540458 : Nat := 4983230072969 + 3 ^ 40 * 1540458 * 2
def baseEnd_1540458 : Nat := 263665127354613061563523

theorem tailTrace_1540458 : CollatzResearch.WordTrace tailWord_1540458 prefixEnd_1540458 263665127354613061563523 := by
  unfold tailWord_1540458
  simp only [CollatzResearch.WordTrace]
  refine ⟨14046279763297807531475507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37456746035460820083934685 14046279763297807531475507)
  ·
    refine ⟨21069419644946711297213261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14046279763297807531475507 21069419644946711297213261)
    ·
      refine ⟨7901032366855016736454973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21069419644946711297213261 7901032366855016736454973)
      ·
        refine ⟨2962887137570631276170615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7901032366855016736454973 2962887137570631276170615)
        ·
          refine ⟨4444330706355946914255923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2962887137570631276170615 4444330706355946914255923)
          ·
            refine ⟨6666496059533920371383885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4444330706355946914255923 6666496059533920371383885)
            ·
              refine ⟨2499936022325220139268957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6666496059533920371383885 2499936022325220139268957)
              ·
                refine ⟨937476008371957552225859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2499936022325220139268957 937476008371957552225859)
                ·
                  refine ⟨1406214012557936328338789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 937476008371957552225859 1406214012557936328338789)
                  ·
                    refine ⟨263665127354613061563523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1406214012557936328338789 263665127354613061563523)
                    ·
                      rfl

theorem cell23_1540458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_1540458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540458 prefixEnd_1540458 := by exact prefixLift 1540458
  have htrace : WordTrace (prefixWord ++ tailWord_1540458) baseStart_1540458 baseEnd_1540458 := by
    simpa [prefixWord, tailWord_1540458, baseEnd_1540458] using wordTrace_append hprefix tailTrace_1540458
  have hstable : (prefixWord ++ tailWord_1540458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540458).length < 2 ^ (prefixWord ++ tailWord_1540458).sum := by decide
  have hdescent : baseEnd_1540458 < baseStart_1540458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540502 : List Nat := [5, 3, 1, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_1540502 : Nat := 118140960795 + 1540502 * 2 ^ 59
def prefixEnd_1540502 : Nat := 4983230072969 + 3 ^ 40 * 1540502 * 2
def baseEnd_1540502 : Nat := 791017975212637012540367

theorem tailTrace_1540502 : CollatzResearch.WordTrace tailWord_1540502 prefixEnd_1540502 791017975212637012540367 := by
  unfold tailWord_1540502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3511670241564489102531485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37457815910021217093669173 3511670241564489102531485)
  ·
    refine ⟨1316876340586683413449307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3511670241564489102531485 1316876340586683413449307)
    ·
      refine ⟨1975314510880025120173961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1316876340586683413449307 1975314510880025120173961)
      ·
        refine ⟨1481485883160018840130471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1975314510880025120173961 1481485883160018840130471)
        ·
          refine ⟨2222228824740028260195707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1481485883160018840130471 2222228824740028260195707)
          ·
            refine ⟨3333343237110042390293561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2222228824740028260195707 3333343237110042390293561)
            ·
              refine ⟨2500007427832531792720171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3333343237110042390293561 2500007427832531792720171)
              ·
                refine ⟨3750011141748797689080257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2500007427832531792720171 3750011141748797689080257)
                ·
                  refine ⟨2812508356311598266810193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3750011141748797689080257 2812508356311598266810193)
                  ·
                    refine ⟨2109381267233698700107645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2812508356311598266810193 2109381267233698700107645)
                    ·
                      refine ⟨791017975212637012540367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2109381267233698700107645 791017975212637012540367)
                      ·
                        rfl

theorem cell23_1540502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_1540502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540502 prefixEnd_1540502 := by exact prefixLift 1540502
  have htrace : WordTrace (prefixWord ++ tailWord_1540502) baseStart_1540502 baseEnd_1540502 := by
    simpa [prefixWord, tailWord_1540502, baseEnd_1540502] using wordTrace_append hprefix tailTrace_1540502
  have hstable : (prefixWord ++ tailWord_1540502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540502).length < 2 ^ (prefixWord ++ tailWord_1540502).sum := by decide
  have hdescent : baseEnd_1540502 < baseStart_1540502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540514 : List Nat := [3, 3, 1, 2, 1, 1, 3, 2, 1, 6]
def baseStart_1540514 : Nat := 118140960795 + 1540514 * 2 ^ 59
def prefixEnd_1540514 : Nat := 4983230072969 + 3 ^ 40 * 1540514 * 2
def baseEnd_1540514 : Nat := 263674712326830321863437

theorem tailTrace_1540514 : CollatzResearch.WordTrace tailWord_1540514 prefixEnd_1540514 263674712326830321863437 := by
  unfold tailWord_1540514
  simp only [CollatzResearch.WordTrace]
  refine ⟨14046790385247087922485149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37458107693992234459960397 14046790385247087922485149)
  ·
    refine ⟨5267546394467657970931931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14046790385247087922485149 5267546394467657970931931)
    ·
      refine ⟨7901319591701486956397897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5267546394467657970931931 7901319591701486956397897)
      ·
        refine ⟨5925989693776115217298423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7901319591701486956397897 5925989693776115217298423)
        ·
          refine ⟨8888984540664172825947635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5925989693776115217298423 8888984540664172825947635)
          ·
            refine ⟨13333476810996259238921453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8888984540664172825947635 13333476810996259238921453)
            ·
              refine ⟨5000053804123597214595545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13333476810996259238921453 5000053804123597214595545)
              ·
                refine ⟨3750040353092697910946659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5000053804123597214595545 3750040353092697910946659)
                ·
                  refine ⟨5625060529639046866419989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3750040353092697910946659 5625060529639046866419989)
                  ·
                    refine ⟨263674712326830321863437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5625060529639046866419989 263674712326830321863437)
                    ·
                      rfl

theorem cell23_1540514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_1540514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540514 prefixEnd_1540514 := by exact prefixLift 1540514
  have htrace : WordTrace (prefixWord ++ tailWord_1540514) baseStart_1540514 baseEnd_1540514 := by
    simpa [prefixWord, tailWord_1540514, baseEnd_1540514] using wordTrace_append hprefix tailTrace_1540514
  have hstable : (prefixWord ++ tailWord_1540514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540514).length < 2 ^ (prefixWord ++ tailWord_1540514).sum := by decide
  have hdescent : baseEnd_1540514 < baseStart_1540514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540587 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 4, 6]
def baseStart_1540587 : Nat := 118140960795 + 1540587 * 2 ^ 59
def prefixEnd_1540587 : Nat := 4983230072969 + 3 ^ 40 * 1540587 * 2
def baseEnd_1540587 : Nat := 263687207022756393325825

theorem tailTrace_1540587 : CollatzResearch.WordTrace tailWord_1540587 prefixEnd_1540587 263687207022756393325825 := by
  unfold tailWord_1540587
  simp only [CollatzResearch.WordTrace]
  refine ⟨56189824069723885157348015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37459882713149256771565343 56189824069723885157348015)
  ·
    refine ⟨84284736104585827736022023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56189824069723885157348015 84284736104585827736022023)
    ·
      refine ⟨126427104156878741604033035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84284736104585827736022023 126427104156878741604033035)
      ·
        refine ⟨189640656235318112406049553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126427104156878741604033035 189640656235318112406049553)
        ·
          refine ⟨142230492176488584304537165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189640656235318112406049553 142230492176488584304537165)
          ·
            refine ⟨53336434566183219114201437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142230492176488584304537165 53336434566183219114201437)
            ·
              refine ⟨20001162962318707167825539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53336434566183219114201437 20001162962318707167825539)
              ·
                refine ⟨30001744443478060751738309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20001162962318707167825539 30001744443478060751738309)
                ·
                  refine ⟨5625327083152136390950933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30001744443478060751738309 5625327083152136390950933)
                  ·
                    refine ⟨263687207022756393325825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5625327083152136390950933 263687207022756393325825)
                    ·
                      rfl

theorem cell23_1540587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 6].length) (baseStart_1540587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540587 prefixEnd_1540587 := by exact prefixLift 1540587
  have htrace : WordTrace (prefixWord ++ tailWord_1540587) baseStart_1540587 baseEnd_1540587 := by
    simpa [prefixWord, tailWord_1540587, baseEnd_1540587] using wordTrace_append hprefix tailTrace_1540587
  have hstable : (prefixWord ++ tailWord_1540587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540587).length < 2 ^ (prefixWord ++ tailWord_1540587).sum := by decide
  have hdescent : baseEnd_1540587 < baseStart_1540587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540615 : List Nat := [1, 1, 4, 3, 3, 1, 2, 2, 1, 3, 2]
def baseStart_1540615 : Nat := 118140960795 + 1540615 * 2 ^ 59
def prefixEnd_1540615 : Nat := 4983230072969 + 3 ^ 40 * 1540615 * 2
def baseEnd_1540615 : Nat := 791075998526595070427347

theorem tailTrace_1540615 : CollatzResearch.WordTrace tailWord_1540615 prefixEnd_1540615 791075998526595070427347 := by
  unfold tailWord_1540615
  simp only [CollatzResearch.WordTrace]
  refine ⟨56190845313622445939367299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37460563542414963959578199 56190845313622445939367299)
  ·
    refine ⟨84286267970433668909050949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56190845313622445939367299 84286267970433668909050949)
    ·
      refine ⟨15803675244456312920447053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84286267970433668909050949 15803675244456312920447053)
      ·
        refine ⟨5926378216671117345167645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15803675244456312920447053 5926378216671117345167645)
        ·
          refine ⟨2222391831251669004437867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5926378216671117345167645 2222391831251669004437867)
          ·
            refine ⟨3333587746877503506656801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2222391831251669004437867 3333587746877503506656801)
            ·
              refine ⟨2500190810158127629992601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3333587746877503506656801 2500190810158127629992601)
              ·
                refine ⟨1875143107618595722494451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2500190810158127629992601 1875143107618595722494451)
                ·
                  refine ⟨2812714661427893583741677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1875143107618595722494451 2812714661427893583741677)
                  ·
                    refine ⟨1054767998035460093903129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2812714661427893583741677 1054767998035460093903129)
                    ·
                      refine ⟨791075998526595070427347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1054767998035460093903129 791075998526595070427347)
                      ·
                        rfl

theorem cell23_1540615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_1540615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540615 prefixEnd_1540615 := by exact prefixLift 1540615
  have htrace : WordTrace (prefixWord ++ tailWord_1540615) baseStart_1540615 baseEnd_1540615 := by
    simpa [prefixWord, tailWord_1540615, baseEnd_1540615] using wordTrace_append hprefix tailTrace_1540615
  have hstable : (prefixWord ++ tailWord_1540615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540615).length < 2 ^ (prefixWord ++ tailWord_1540615).sum := by decide
  have hdescent : baseEnd_1540615 < baseStart_1540615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540617 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 9]
def baseStart_1540617 : Nat := 118140960795 + 1540617 * 2 ^ 59
def prefixEnd_1540617 : Nat := 4983230072969 + 3 ^ 40 * 1540617 * 2
def baseEnd_1540617 : Nat := 87897447276433784733593

theorem tailTrace_1540617 : CollatzResearch.WordTrace tailWord_1540617 prefixEnd_1540617 87897447276433784733593 := by
  unfold tailWord_1540617
  simp only [CollatzResearch.WordTrace]
  refine ⟨56190918259615200280940105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37460612173076800187293403 56190918259615200280940105)
  ·
    refine ⟨42143188694711400210705079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56190918259615200280940105 42143188694711400210705079)
    ·
      refine ⟨63214783042067100316057619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42143188694711400210705079 63214783042067100316057619)
      ·
        refine ⟨94822174563100650474086429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63214783042067100316057619 94822174563100650474086429)
        ·
          refine ⟨35558315461162743927782411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94822174563100650474086429 35558315461162743927782411)
          ·
            refine ⟨53337473191744115891673617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35558315461162743927782411 53337473191744115891673617)
            ·
              refine ⟨40003104893808086918755213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53337473191744115891673617 40003104893808086918755213)
              ·
                refine ⟨15001164335178032594533205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40003104893808086918755213 15001164335178032594533205)
                ·
                  refine ⟨87897447276433784733593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15001164335178032594533205 87897447276433784733593)
                  ·
                    rfl

theorem cell23_1540617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 9].length) (baseStart_1540617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540617 prefixEnd_1540617 := by exact prefixLift 1540617
  have htrace : WordTrace (prefixWord ++ tailWord_1540617) baseStart_1540617 baseEnd_1540617 := by
    simpa [prefixWord, tailWord_1540617, baseEnd_1540617] using wordTrace_append hprefix tailTrace_1540617
  have hstable : (prefixWord ++ tailWord_1540617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540617).length < 2 ^ (prefixWord ++ tailWord_1540617).sum := by decide
  have hdescent : baseEnd_1540617 < baseStart_1540617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540662 : List Nat := [5, 1, 2, 1, 2, 2, 1, 3, 2, 2, 2]
def baseStart_1540662 : Nat := 118140960795 + 1540662 * 2 ^ 59
def prefixEnd_1540662 : Nat := 4983230072969 + 3 ^ 40 * 1540662 * 2
def baseEnd_1540662 : Nat := 791100132117356386539631

theorem tailTrace_1540662 : CollatzResearch.WordTrace tailWord_1540662 prefixEnd_1540662 791100132117356386539631 := by
  unfold tailWord_1540662
  simp only [CollatzResearch.WordTrace]
  refine ⟨3512034971528260810395515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37461706362968115310885493 3512034971528260810395515)
  ·
    refine ⟨5268052457292391215593273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3512034971528260810395515 5268052457292391215593273)
    ·
      refine ⟨3951039342969293411694955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5268052457292391215593273 3951039342969293411694955)
      ·
        refine ⟨5926559014453940117542433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3951039342969293411694955 5926559014453940117542433)
        ·
          refine ⟨4444919260840455088156825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5926559014453940117542433 4444919260840455088156825)
          ·
            refine ⟨3333689445630341316117619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4444919260840455088156825 3333689445630341316117619)
            ·
              refine ⟨5000534168445511974176429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3333689445630341316117619 5000534168445511974176429)
              ·
                refine ⟨1875200313167066990316161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5000534168445511974176429 1875200313167066990316161)
                ·
                  refine ⟨1406400234875300242737121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1875200313167066990316161 1406400234875300242737121)
                  ·
                    refine ⟨1054800176156475182052841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1406400234875300242737121 1054800176156475182052841)
                    ·
                      refine ⟨791100132117356386539631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1054800176156475182052841 791100132117356386539631)
                      ·
                        rfl

theorem cell23_1540662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_1540662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540662 prefixEnd_1540662 := by exact prefixLift 1540662
  have htrace : WordTrace (prefixWord ++ tailWord_1540662) baseStart_1540662 baseEnd_1540662 := by
    simpa [prefixWord, tailWord_1540662, baseEnd_1540662] using wordTrace_append hprefix tailTrace_1540662
  have hstable : (prefixWord ++ tailWord_1540662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540662).length < 2 ^ (prefixWord ++ tailWord_1540662).sum := by decide
  have hdescent : baseEnd_1540662 < baseStart_1540662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540664 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 4, 5]
def baseStart_1540664 : Nat := 118140960795 + 1540664 * 2 ^ 59
def prefixEnd_1540664 : Nat := 4983230072969 + 3 ^ 40 * 1540664 * 2
def baseEnd_1540664 : Nat := 263700386359555126238207

theorem tailTrace_1540664 : CollatzResearch.WordTrace tailWord_1540664 prefixEnd_1540664 263700386359555126238207 := by
  unfold tailWord_1540664
  simp only [CollatzResearch.WordTrace]
  refine ⟨28096316245222463653950523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37461754993629951538600697 28096316245222463653950523)
  ·
    refine ⟨42144474367833695480925785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28096316245222463653950523 42144474367833695480925785)
    ·
      refine ⟨31608355775875271610694339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42144474367833695480925785 31608355775875271610694339)
      ·
        refine ⟨47412533663812907416041509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31608355775875271610694339 47412533663812907416041509)
        ·
          refine ⟨8889850061964920140507783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47412533663812907416041509 8889850061964920140507783)
          ·
            refine ⟨13334775092947380210761675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8889850061964920140507783 13334775092947380210761675)
            ·
              refine ⟨20002162639421070316142513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13334775092947380210761675 20002162639421070316142513)
              ·
                refine ⟨15001621979565802737106885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20002162639421070316142513 15001621979565802737106885)
                ·
                  refine ⟨2812804121168588013207541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15001621979565802737106885 2812804121168588013207541)
                  ·
                    refine ⟨263700386359555126238207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2812804121168588013207541 263700386359555126238207)
                    ·
                      rfl

theorem cell23_1540664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 4, 5].length) (baseStart_1540664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540664 prefixEnd_1540664 := by exact prefixLift 1540664
  have htrace : WordTrace (prefixWord ++ tailWord_1540664) baseStart_1540664 baseEnd_1540664 := by
    simpa [prefixWord, tailWord_1540664, baseEnd_1540664] using wordTrace_append hprefix tailTrace_1540664
  have hstable : (prefixWord ++ tailWord_1540664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540664).length < 2 ^ (prefixWord ++ tailWord_1540664).sum := by decide
  have hdescent : baseEnd_1540664 < baseStart_1540664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540711 : List Nat := [1, 1, 5, 1, 1, 1, 1, 5, 3, 4]
def baseStart_1540711 : Nat := 118140960795 + 1540711 * 2 ^ 59
def prefixEnd_1540711 : Nat := 4983230072969 + 3 ^ 40 * 1540711 * 2
def baseEnd_1540711 : Nat := 263708430889808898275635

theorem tailTrace_1540711 : CollatzResearch.WordTrace tailWord_1540711 prefixEnd_1540711 263708430889808898275635 := by
  unfold tailWord_1540711
  simp only [CollatzResearch.WordTrace]
  refine ⟨56194346721274654334861987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37462897814183102889907991 56194346721274654334861987)
  ·
    refine ⟨84291520081911981502292981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56194346721274654334861987 84291520081911981502292981)
    ·
      refine ⟨7902330007679248265839967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84291520081911981502292981 7902330007679248265839967)
      ·
        refine ⟨11853495011518872398759951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7902330007679248265839967 11853495011518872398759951)
        ·
          refine ⟨17780242517278308598139927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11853495011518872398759951 17780242517278308598139927)
          ·
            refine ⟨26670363775917462897209891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17780242517278308598139927 26670363775917462897209891)
            ·
              refine ⟨40005545663876194345814837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26670363775917462897209891 40005545663876194345814837)
              ·
                refine ⟨3750519905988393219920141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40005545663876194345814837 3750519905988393219920141)
                ·
                  refine ⟨1406444964745647457470053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3750519905988393219920141 1406444964745647457470053)
                  ·
                    refine ⟨263708430889808898275635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1406444964745647457470053 263708430889808898275635)
                    ·
                      rfl

theorem cell23_1540711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_1540711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540711 prefixEnd_1540711 := by exact prefixLift 1540711
  have htrace : WordTrace (prefixWord ++ tailWord_1540711) baseStart_1540711 baseEnd_1540711 := by
    simpa [prefixWord, tailWord_1540711, baseEnd_1540711] using wordTrace_append hprefix tailTrace_1540711
  have hstable : (prefixWord ++ tailWord_1540711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540711).length < 2 ^ (prefixWord ++ tailWord_1540711).sum := by decide
  have hdescent : baseEnd_1540711 < baseStart_1540711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540718 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 1, 6, 2]
def baseStart_1540718 : Nat := 118140960795 + 1540718 * 2 ^ 59
def prefixEnd_1540718 : Nat := 4983230072969 + 3 ^ 40 * 1540718 * 2
def baseEnd_1540718 : Nat := 791128887034008167439373

theorem tailTrace_1540718 : CollatzResearch.WordTrace tailWord_1540718 prefixEnd_1540718 791128887034008167439373 := by
  unfold tailWord_1540718
  simp only [CollatzResearch.WordTrace]
  refine ⟨7024325254031161816295851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37463068021499529686911205 7024325254031161816295851)
  ·
    refine ⟨10536487881046742724443777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7024325254031161816295851 10536487881046742724443777)
    ·
      refine ⟨7902365910785057043332833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10536487881046742724443777 7902365910785057043332833)
      ·
        refine ⟨5926774433088792782499625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7902365910785057043332833 5926774433088792782499625)
        ·
          refine ⟨4445080824816594586874719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5926774433088792782499625 4445080824816594586874719)
          ·
            refine ⟨6667621237224891880312079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4445080824816594586874719 6667621237224891880312079)
            ·
              refine ⟨10001431855837337820468119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6667621237224891880312079 10001431855837337820468119)
              ·
                refine ⟨15002147783756006730702179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10001431855837337820468119 15002147783756006730702179)
                ·
                  refine ⟨22503221675634010096053269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15002147783756006730702179 22503221675634010096053269)
                  ·
                    refine ⟨1054838516045344223252497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22503221675634010096053269 1054838516045344223252497)
                    ·
                      refine ⟨791128887034008167439373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1054838516045344223252497 791128887034008167439373)
                      ·
                        rfl

theorem cell23_1540718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_1540718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540718 prefixEnd_1540718 := by exact prefixLift 1540718
  have htrace : WordTrace (prefixWord ++ tailWord_1540718) baseStart_1540718 baseEnd_1540718 := by
    simpa [prefixWord, tailWord_1540718, baseEnd_1540718] using wordTrace_append hprefix tailTrace_1540718
  have hstable : (prefixWord ++ tailWord_1540718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540718).length < 2 ^ (prefixWord ++ tailWord_1540718).sum := by decide
  have hdescent : baseEnd_1540718 < baseStart_1540718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540808 : List Nat := [2, 1, 3, 1, 2, 3, 2, 3, 1, 1, 4]
def baseStart_1540808 : Nat := 118140960795 + 1540808 * 2 ^ 59
def prefixEnd_1540808 : Nat := 4983230072969 + 3 ^ 40 * 1540808 * 2
def baseEnd_1540808 : Nat := 791175100292912815313959

theorem tailTrace_1540808 : CollatzResearch.WordTrace tailWord_1540808 prefixEnd_1540808 791175100292912815313959 := by
  unfold tailWord_1540808
  simp only [CollatzResearch.WordTrace]
  refine ⟨28098942300961619950571539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37465256401282159934095385 28098942300961619950571539)
  ·
    refine ⟨42148413451442429925857309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28098942300961619950571539 42148413451442429925857309)
    ·
      refine ⟨15805655044290911222196491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42148413451442429925857309 15805655044290911222196491)
      ·
        refine ⟨23708482566436366833294737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15805655044290911222196491 23708482566436366833294737)
        ·
          refine ⟨17781361924827275124971053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23708482566436366833294737 17781361924827275124971053)
          ·
            refine ⟨6668010721810228171864145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17781361924827275124971053 6668010721810228171864145)
            ·
              refine ⟨5001008041357671128898109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6668010721810228171864145 5001008041357671128898109)
              ·
                refine ⟨1875378015509126673336791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5001008041357671128898109 1875378015509126673336791)
                ·
                  refine ⟨2813067023263690010005187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1875378015509126673336791 2813067023263690010005187)
                  ·
                    refine ⟨4219600534895535015007781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2813067023263690010005187 4219600534895535015007781)
                    ·
                      refine ⟨791175100292912815313959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4219600534895535015007781 791175100292912815313959)
                      ·
                        rfl

theorem cell23_1540808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_1540808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540808 prefixEnd_1540808 := by exact prefixLift 1540808
  have htrace : WordTrace (prefixWord ++ tailWord_1540808) baseStart_1540808 baseEnd_1540808 := by
    simpa [prefixWord, tailWord_1540808, baseEnd_1540808] using wordTrace_append hprefix tailTrace_1540808
  have hstable : (prefixWord ++ tailWord_1540808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540808).length < 2 ^ (prefixWord ++ tailWord_1540808).sum := by decide
  have hdescent : baseEnd_1540808 < baseStart_1540808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540811 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 7, 2, 3]
def baseStart_1540811 : Nat := 118140960795 + 1540811 * 2 ^ 59
def prefixEnd_1540811 : Nat := 4983230072969 + 3 ^ 40 * 1540811 * 2
def baseEnd_1540811 : Nat := 791176640734876303576445

theorem tailTrace_1540811 : CollatzResearch.WordTrace tailWord_1540811 prefixEnd_1540811 791176640734876303576445 := by
  unfold tailWord_1540811
  simp only [CollatzResearch.WordTrace]
  refine ⟨56197994020912371413502287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37465329347274914275668191 56197994020912371413502287)
  ·
    refine ⟨84296991031368557120253431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56197994020912371413502287 84296991031368557120253431)
    ·
      refine ⟨126445486547052835680380147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84296991031368557120253431 126445486547052835680380147)
      ·
        refine ⟨189668229820579253520570221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126445486547052835680380147 189668229820579253520570221)
        ·
          refine ⟨71125586182717220070213833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189668229820579253520570221 71125586182717220070213833)
          ·
            refine ⟨53344189637037915052660375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71125586182717220070213833 53344189637037915052660375)
            ·
              refine ⟨80016284455556872578990563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53344189637037915052660375 80016284455556872578990563)
              ·
                refine ⟨120024426683335308868485845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80016284455556872578990563 120024426683335308868485845)
                ·
                  refine ⟨2813072500390671301605137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 120024426683335308868485845 2813072500390671301605137)
                  ·
                    refine ⟨2109804375293003476203853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2813072500390671301605137 2109804375293003476203853)
                    ·
                      refine ⟨791176640734876303576445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2109804375293003476203853 791176640734876303576445)
                      ·
                        rfl

theorem cell23_1540811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 2, 3].length) (baseStart_1540811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540811 prefixEnd_1540811 := by exact prefixLift 1540811
  have htrace : WordTrace (prefixWord ++ tailWord_1540811) baseStart_1540811 baseEnd_1540811 := by
    simpa [prefixWord, tailWord_1540811, baseEnd_1540811] using wordTrace_append hprefix tailTrace_1540811
  have hstable : (prefixWord ++ tailWord_1540811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540811).length < 2 ^ (prefixWord ++ tailWord_1540811).sum := by decide
  have hdescent : baseEnd_1540811 < baseStart_1540811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540831 : List Nat := [1, 1, 2, 3, 2, 4, 2, 8]
def baseStart_1540831 : Nat := 118140960795 + 1540831 * 2 ^ 59
def prefixEnd_1540831 : Nat := 4983230072969 + 3 ^ 40 * 1540831 * 2
def baseEnd_1540831 : Nat := 29303218901776526863939

theorem tailTrace_1540831 : CollatzResearch.WordTrace tailWord_1540831 prefixEnd_1540831 29303218901776526863939 := by
  unfold tailWord_1540831
  simp only [CollatzResearch.WordTrace]
  refine ⟨56198723480839914829230347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37465815653893276552820231 56198723480839914829230347)
  ·
    refine ⟨84298085221259872243845521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56198723480839914829230347 84298085221259872243845521)
    ·
      refine ⟨63223563915944904182884141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84298085221259872243845521 63223563915944904182884141)
      ·
        refine ⟨23708836468479339068581553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63223563915944904182884141 23708836468479339068581553)
        ·
          refine ⟨17781627351359504301436165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23708836468479339068581553 17781627351359504301436165)
          ·
            refine ⟨3334055128379907056519281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17781627351359504301436165 3334055128379907056519281)
            ·
              refine ⟨2500541346284930292389461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3334055128379907056519281 2500541346284930292389461)
              ·
                refine ⟨29303218901776526863939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2500541346284930292389461 29303218901776526863939)
                ·
                  rfl

theorem cell23_1540831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 8].length) (baseStart_1540831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540831 prefixEnd_1540831 := by exact prefixLift 1540831
  have htrace : WordTrace (prefixWord ++ tailWord_1540831) baseStart_1540831 baseEnd_1540831 := by
    simpa [prefixWord, tailWord_1540831, baseEnd_1540831] using wordTrace_append hprefix tailTrace_1540831
  have hstable : (prefixWord ++ tailWord_1540831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540831).length < 2 ^ (prefixWord ++ tailWord_1540831).sum := by decide
  have hdescent : baseEnd_1540831 < baseStart_1540831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540835 : List Nat := [1, 1, 1, 7, 1, 2, 1, 3, 2, 4]
def baseStart_1540835 : Nat := 118140960795 + 1540835 * 2 ^ 59
def prefixEnd_1540835 : Nat := 4983230072969 + 3 ^ 40 * 1540835 * 2
def baseEnd_1540835 : Nat := 263729654756861403225445

theorem tailTrace_1540835 : CollatzResearch.WordTrace tailWord_1540835 prefixEnd_1540835 263729654756861403225445 := by
  unfold tailWord_1540835
  simp only [CollatzResearch.WordTrace]
  refine ⟨56198869372825423512375959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37465912915216949008250639 56198869372825423512375959)
  ·
    refine ⟨84298304059238135268563939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56198869372825423512375959 84298304059238135268563939)
    ·
      refine ⟨126447456088857202902845909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84298304059238135268563939 126447456088857202902845909)
      ·
        refine ⟨2963612252082590693035451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 126447456088857202902845909 2963612252082590693035451)
        ·
          refine ⟨4445418378123886039553177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2963612252082590693035451 4445418378123886039553177)
          ·
            refine ⟨3334063783592914529664883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4445418378123886039553177 3334063783592914529664883)
            ·
              refine ⟨5001095675389371794497325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3334063783592914529664883 5001095675389371794497325)
              ·
                refine ⟨1875410878271014422936497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5001095675389371794497325 1875410878271014422936497)
                ·
                  refine ⟨1406558158703260817202373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1875410878271014422936497 1406558158703260817202373)
                  ·
                    refine ⟨263729654756861403225445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1406558158703260817202373 263729654756861403225445)
                    ·
                      rfl

theorem cell23_1540835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 2, 4].length) (baseStart_1540835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540835 prefixEnd_1540835 := by exact prefixLift 1540835
  have htrace : WordTrace (prefixWord ++ tailWord_1540835) baseStart_1540835 baseEnd_1540835 := by
    simpa [prefixWord, tailWord_1540835, baseEnd_1540835] using wordTrace_append hprefix tailTrace_1540835
  have hstable : (prefixWord ++ tailWord_1540835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540835).length < 2 ^ (prefixWord ++ tailWord_1540835).sum := by decide
  have hdescent : baseEnd_1540835 < baseStart_1540835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540852 : List Nat := [2, 6, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_1540852 : Nat := 118140960795 + 1540852 * 2 ^ 59
def prefixEnd_1540852 : Nat := 4983230072969 + 3 ^ 40 * 1540852 * 2
def baseEnd_1540852 : Nat := 263732564480570214387919

theorem tailTrace_1540852 : CollatzResearch.WordTrace tailWord_1540852 prefixEnd_1540852 263732564480570214387919 := by
  unfold tailWord_1540852
  simp only [CollatzResearch.WordTrace]
  refine ⟨28099744706881917707872405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37466326275842556943829873 28099744706881917707872405)
  ·
    refine ⟨1317175533135089892556519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28099744706881917707872405 1317175533135089892556519)
    ·
      refine ⟨1975763299702634838834779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1317175533135089892556519 1975763299702634838834779)
      ·
        refine ⟨2963644949553952258252169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1975763299702634838834779 2963644949553952258252169)
        ·
          refine ⟨2222733712165464193689127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2963644949553952258252169 2222733712165464193689127)
          ·
            refine ⟨3334100568248196290533691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2222733712165464193689127 3334100568248196290533691)
            ·
              refine ⟨5001150852372294435800537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3334100568248196290533691 5001150852372294435800537)
              ·
                refine ⟨3750863139279220826850403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5001150852372294435800537 3750863139279220826850403)
                ·
                  refine ⟨5626294708918831240275605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3750863139279220826850403 5626294708918831240275605)
                  ·
                    refine ⟨263732564480570214387919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5626294708918831240275605 263732564480570214387919)
                    ·
                      rfl

theorem cell23_1540852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_1540852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540852 prefixEnd_1540852 := by exact prefixLift 1540852
  have htrace : WordTrace (prefixWord ++ tailWord_1540852) baseStart_1540852 baseEnd_1540852 := by
    simpa [prefixWord, tailWord_1540852, baseEnd_1540852] using wordTrace_append hprefix tailTrace_1540852
  have hstable : (prefixWord ++ tailWord_1540852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540852).length < 2 ^ (prefixWord ++ tailWord_1540852).sum := by decide
  have hdescent : baseEnd_1540852 < baseStart_1540852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540858 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 6, 1, 3]
def baseStart_1540858 : Nat := 118140960795 + 1540858 * 2 ^ 59
def prefixEnd_1540858 : Nat := 4983230072969 + 3 ^ 40 * 1540858 * 2
def baseEnd_1540858 : Nat := 791200774325637619688729

theorem tailTrace_1540858 : CollatzResearch.WordTrace tailWord_1540858 prefixEnd_1540858 791200774325637619688729 := by
  unfold tailWord_1540858
  simp only [CollatzResearch.WordTrace]
  refine ⟨14049927062935524610115807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37466472167828065626975485 14049927062935524610115807)
  ·
    refine ⟨21074890594403286915173711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14049927062935524610115807 21074890594403286915173711)
    ·
      refine ⟨31612335891604930372760567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21074890594403286915173711 31612335891604930372760567)
      ·
        refine ⟨47418503837407395559140851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31612335891604930372760567 47418503837407395559140851)
        ·
          refine ⟨71127755756111093338711277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47418503837407395559140851 71127755756111093338711277)
          ·
            refine ⟨26672908408541660002016729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71127755756111093338711277 26672908408541660002016729)
            ·
              refine ⟨20004681306406245001512547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26672908408541660002016729 20004681306406245001512547)
              ·
                refine ⟨30007021959609367502268821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20004681306406245001512547 30007021959609367502268821)
                ·
                  refine ⟨1406579154356689101668851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30007021959609367502268821 1406579154356689101668851)
                  ·
                    refine ⟨2109868731535033652503277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1406579154356689101668851 2109868731535033652503277)
                    ·
                      refine ⟨791200774325637619688729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2109868731535033652503277 791200774325637619688729)
                      ·
                        rfl

theorem cell23_1540858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 6, 1, 3].length) (baseStart_1540858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540858 prefixEnd_1540858 := by exact prefixLift 1540858
  have htrace : WordTrace (prefixWord ++ tailWord_1540858) baseStart_1540858 baseEnd_1540858 := by
    simpa [prefixWord, tailWord_1540858, baseEnd_1540858] using wordTrace_append hprefix tailTrace_1540858
  have hstable : (prefixWord ++ tailWord_1540858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540858).length < 2 ^ (prefixWord ++ tailWord_1540858).sum := by decide
  have hdescent : baseEnd_1540858 < baseStart_1540858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540881 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 4]
def baseStart_1540881 : Nat := 118140960795 + 1540881 * 2 ^ 59
def prefixEnd_1540881 : Nat := 4983230072969 + 3 ^ 40 * 1540881 * 2
def baseEnd_1540881 : Nat := 791212584380691029701123

theorem tailTrace_1540881 : CollatzResearch.WordTrace tailWord_1540881 prefixEnd_1540881 791212584380691029701123 := by
  unfold tailWord_1540881
  simp only [CollatzResearch.WordTrace]
  refine ⟨56200547130658773368550497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37467031420439182245700331 56200547130658773368550497)
  ·
    refine ⟨42150410347994080026412873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56200547130658773368550497 42150410347994080026412873)
    ·
      refine ⟨31612807760995560019809655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42150410347994080026412873 31612807760995560019809655)
      ·
        refine ⟨47419211641493340029714483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31612807760995560019809655 47419211641493340029714483)
        ·
          refine ⟨71128817462240010044571725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47419211641493340029714483 71128817462240010044571725)
          ·
            refine ⟨26673306548340003766714397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71128817462240010044571725 26673306548340003766714397)
            ·
              refine ⟨10002489955627501412517899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26673306548340003766714397 10002489955627501412517899)
              ·
                refine ⟨15003734933441252118776849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10002489955627501412517899 15003734933441252118776849)
                ·
                  refine ⟨11252801200080939089082637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15003734933441252118776849 11252801200080939089082637)
                  ·
                    refine ⟨4219800450030352158405989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11252801200080939089082637 4219800450030352158405989)
                    ·
                      refine ⟨791212584380691029701123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4219800450030352158405989 791212584380691029701123)
                      ·
                        rfl

theorem cell23_1540881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_1540881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540881 prefixEnd_1540881 := by exact prefixLift 1540881
  have htrace : WordTrace (prefixWord ++ tailWord_1540881) baseStart_1540881 baseEnd_1540881 := by
    simpa [prefixWord, tailWord_1540881, baseEnd_1540881] using wordTrace_append hprefix tailTrace_1540881
  have hstable : (prefixWord ++ tailWord_1540881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540881).length < 2 ^ (prefixWord ++ tailWord_1540881).sum := by decide
  have hdescent : baseEnd_1540881 < baseStart_1540881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540882 : List Nat := [3, 2, 4, 1, 3, 1, 1, 8]
def baseStart_1540882 : Nat := 118140960795 + 1540882 * 2 ^ 59
def prefixEnd_1540882 : Nat := 4983230072969 + 3 ^ 40 * 1540882 * 2
def baseEnd_1540882 : Nat := 29304188809679463918097

theorem tailTrace_1540882 : CollatzResearch.WordTrace tailWord_1540882 prefixEnd_1540882 29304188809679463918097 := by
  unfold tailWord_1540882
  simp only [CollatzResearch.WordTrace]
  refine ⟨14050145900913787634834225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37467055735770100359557933 14050145900913787634834225)
  ·
    refine ⟨10537609425685340726125669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14050145900913787634834225 10537609425685340726125669)
    ·
      refine ⟨1975801767316001386148563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10537609425685340726125669 1975801767316001386148563)
      ·
        refine ⟨2963702650974002079222845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1975801767316001386148563 2963702650974002079222845)
        ·
          refine ⟨1111388494115250779708567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2963702650974002079222845 1111388494115250779708567)
          ·
            refine ⟨1667082741172876169562851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1111388494115250779708567 1667082741172876169562851)
            ·
              refine ⟨2500624111759314254344277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1667082741172876169562851 2500624111759314254344277)
              ·
                refine ⟨29304188809679463918097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2500624111759314254344277 29304188809679463918097)
                ·
                  rfl

theorem cell23_1540882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 8].length) (baseStart_1540882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540882 prefixEnd_1540882 := by exact prefixLift 1540882
  have htrace : WordTrace (prefixWord ++ tailWord_1540882) baseStart_1540882 baseEnd_1540882 := by
    simpa [prefixWord, tailWord_1540882, baseEnd_1540882] using wordTrace_append hprefix tailTrace_1540882
  have hstable : (prefixWord ++ tailWord_1540882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540882).length < 2 ^ (prefixWord ++ tailWord_1540882).sum := by decide
  have hdescent : baseEnd_1540882 < baseStart_1540882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540911 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 4]
def baseStart_1540911 : Nat := 118140960795 + 1540911 * 2 ^ 59
def prefixEnd_1540911 : Nat := 4983230072969 + 3 ^ 40 * 1540911 * 2
def baseEnd_1540911 : Nat := 791227988800325912325985

theorem tailTrace_1540911 : CollatzResearch.WordTrace tailWord_1540911 prefixEnd_1540911 791227988800325912325985 := by
  unfold tailWord_1540911
  simp only [CollatzResearch.WordTrace]
  refine ⟨56201641320550088492142587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37467760880366725661428391 56201641320550088492142587)
  ·
    refine ⟨84302461980825132738213881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56201641320550088492142587 84302461980825132738213881)
    ·
      refine ⟨63226846485618849553660411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84302461980825132738213881 63226846485618849553660411)
      ·
        refine ⟨94840269728428274330490617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63226846485618849553660411 94840269728428274330490617)
        ·
          refine ⟨71130202296321205747867963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94840269728428274330490617 71130202296321205747867963)
          ·
            refine ⟨106695303444481808621801945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71130202296321205747867963 106695303444481808621801945)
            ·
              refine ⟨80021477583361356466351459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106695303444481808621801945 80021477583361356466351459)
              ·
                refine ⟨120032216375042034699527189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80021477583361356466351459 120032216375042034699527189)
                ·
                  refine ⟨5626510142580095376540337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 120032216375042034699527189 5626510142580095376540337)
                  ·
                    refine ⟨4219882606935071532405253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5626510142580095376540337 4219882606935071532405253)
                    ·
                      refine ⟨791227988800325912325985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4219882606935071532405253 791227988800325912325985)
                      ·
                        rfl

theorem cell23_1540911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 4].length) (baseStart_1540911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540911 prefixEnd_1540911 := by exact prefixLift 1540911
  have htrace : WordTrace (prefixWord ++ tailWord_1540911) baseStart_1540911 baseEnd_1540911 := by
    simpa [prefixWord, tailWord_1540911, baseEnd_1540911] using wordTrace_append hprefix tailTrace_1540911
  have hstable : (prefixWord ++ tailWord_1540911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540911).length < 2 ^ (prefixWord ++ tailWord_1540911).sum := by decide
  have hdescent : baseEnd_1540911 < baseStart_1540911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540915 : List Nat := [1, 1, 1, 2, 6, 1, 2, 2, 1, 4, 2]
def baseStart_1540915 : Nat := 118140960795 + 1540915 * 2 ^ 59
def prefixEnd_1540915 : Nat := 4983230072969 + 3 ^ 40 * 1540915 * 2
def baseEnd_1540915 : Nat := 791230042722943896675967

theorem tailTrace_1540915 : CollatzResearch.WordTrace tailWord_1540915 prefixEnd_1540915 791230042722943896675967 := by
  unfold tailWord_1540915
  simp only [CollatzResearch.WordTrace]
  refine ⟨56201787212535597175288199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37467858141690398116858799 56201787212535597175288199)
  ·
    refine ⟨84302680818803395762932299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56201787212535597175288199 84302680818803395762932299)
    ·
      refine ⟨126454021228205093644398449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84302680818803395762932299 126454021228205093644398449)
      ·
        refine ⟨94840515921153820233298837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126454021228205093644398449 94840515921153820233298837)
        ·
          refine ⟨4445649183804085323435883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 94840515921153820233298837 4445649183804085323435883)
          ·
            refine ⟨6668473775706127985153825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4445649183804085323435883 6668473775706127985153825)
            ·
              refine ⟨5001355331779595988865369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6668473775706127985153825 5001355331779595988865369)
              ·
                refine ⟨3751016498834696991649027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5001355331779595988865369 3751016498834696991649027)
                ·
                  refine ⟨5626524748252045487473541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3751016498834696991649027 5626524748252045487473541)
                  ·
                    refine ⟨1054973390297258528901289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5626524748252045487473541 1054973390297258528901289)
                    ·
                      refine ⟨791230042722943896675967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1054973390297258528901289 791230042722943896675967)
                      ·
                        rfl

theorem cell23_1540915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 4, 2].length) (baseStart_1540915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540915 prefixEnd_1540915 := by exact prefixLift 1540915
  have htrace : WordTrace (prefixWord ++ tailWord_1540915) baseStart_1540915 baseEnd_1540915 := by
    simpa [prefixWord, tailWord_1540915, baseEnd_1540915] using wordTrace_append hprefix tailTrace_1540915
  have hstable : (prefixWord ++ tailWord_1540915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540915).length < 2 ^ (prefixWord ++ tailWord_1540915).sum := by decide
  have hdescent : baseEnd_1540915 < baseStart_1540915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540926 : List Nat := [4, 2, 1, 2, 4, 1, 1, 2, 2, 1, 3]
def baseStart_1540926 : Nat := 118140960795 + 1540926 * 2 ^ 59
def prefixEnd_1540926 : Nat := 4983230072969 + 3 ^ 40 * 1540926 * 2
def baseEnd_1540926 : Nat := 791235691010143353638417

theorem tailTrace_1540926 : CollatzResearch.WordTrace tailWord_1540926 prefixEnd_1540926 791235691010143353638417 := by
  unfold tailWord_1540926
  simp only [CollatzResearch.WordTrace]
  refine ⟨7025273551936968256742329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37468125610330497369292421 7025273551936968256742329)
  ·
    refine ⟨5268955163952726192556747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7025273551936968256742329 5268955163952726192556747)
    ·
      refine ⟨7903432745929089288835121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5268955163952726192556747 7903432745929089288835121)
      ·
        refine ⟨5927574559446816966626341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7903432745929089288835121 5927574559446816966626341)
        ·
          refine ⟨1111420229896278181242439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5927574559446816966626341 1111420229896278181242439)
          ·
            refine ⟨1667130344844417271863659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1111420229896278181242439 1667130344844417271863659)
            ·
              refine ⟨2500695517266625907795489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1667130344844417271863659 2500695517266625907795489)
              ·
                refine ⟨1875521637949969430846617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2500695517266625907795489 1875521637949969430846617)
                ·
                  refine ⟨1406641228462477073134963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1875521637949969430846617 1406641228462477073134963)
                  ·
                    refine ⟨2109961842693715609702445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1406641228462477073134963 2109961842693715609702445)
                    ·
                      refine ⟨791235691010143353638417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2109961842693715609702445 791235691010143353638417)
                      ·
                        rfl

theorem cell23_1540926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_1540926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540926 prefixEnd_1540926 := by exact prefixLift 1540926
  have htrace : WordTrace (prefixWord ++ tailWord_1540926) baseStart_1540926 baseEnd_1540926 := by
    simpa [prefixWord, tailWord_1540926, baseEnd_1540926] using wordTrace_append hprefix tailTrace_1540926
  have hstable : (prefixWord ++ tailWord_1540926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540926).length < 2 ^ (prefixWord ++ tailWord_1540926).sum := by decide
  have hdescent : baseEnd_1540926 < baseStart_1540926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540949 : List Nat := [1, 3, 2, 2, 2, 1, 5, 1, 2, 2, 2]
def baseStart_1540949 : Nat := 118140960795 + 1540949 * 2 ^ 59
def prefixEnd_1540949 : Nat := 4983230072969 + 3 ^ 40 * 1540949 * 2
def baseEnd_1540949 : Nat := 791247501065196763650811

theorem tailTrace_1540949 : CollatzResearch.WordTrace tailWord_1540949 prefixEnd_1540949 791247501065196763650811 := by
  unfold tailWord_1540949
  simp only [CollatzResearch.WordTrace]
  refine ⟨56203027294412420982025901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37468684862941613988017267 56203027294412420982025901)
  ·
    refine ⟨21076135235404657868259713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56203027294412420982025901 21076135235404657868259713)
    ·
      refine ⟨15807101426553493401194785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21076135235404657868259713 15807101426553493401194785)
      ·
        refine ⟨11855326069915120050896089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15807101426553493401194785 11855326069915120050896089)
        ·
          refine ⟨8891494552436340038172067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11855326069915120050896089 8891494552436340038172067)
          ·
            refine ⟨13337241828654510057258101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8891494552436340038172067 13337241828654510057258101)
            ·
              refine ⟨1250366421436360317867947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13337241828654510057258101 1250366421436360317867947)
              ·
                refine ⟨1875549632154540476801921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1250366421436360317867947 1875549632154540476801921)
                ·
                  refine ⟨1406662224115905357601441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1875549632154540476801921 1406662224115905357601441)
                  ·
                    refine ⟨1054996668086929018201081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1406662224115905357601441 1054996668086929018201081)
                    ·
                      refine ⟨791247501065196763650811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1054996668086929018201081 791247501065196763650811)
                      ·
                        rfl

theorem cell23_1540949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_1540949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540949 prefixEnd_1540949 := by exact prefixLift 1540949
  have htrace : WordTrace (prefixWord ++ tailWord_1540949) baseStart_1540949 baseEnd_1540949 := by
    simpa [prefixWord, tailWord_1540949, baseEnd_1540949] using wordTrace_append hprefix tailTrace_1540949
  have hstable : (prefixWord ++ tailWord_1540949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540949).length < 2 ^ (prefixWord ++ tailWord_1540949).sum := by decide
  have hdescent : baseEnd_1540949 < baseStart_1540949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540961 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 3, 1, 7]
def baseStart_1540961 : Nat := 118140960795 + 1540961 * 2 ^ 59
def prefixEnd_1540961 : Nat := 4983230072969 + 3 ^ 40 * 1540961 * 2
def baseEnd_1540961 : Nat := 791253662833050716700755

theorem tailTrace_1540961 : CollatzResearch.WordTrace tailWord_1540961 prefixEnd_1540961 791253662833050716700755 := by
  unfold tailWord_1540961
  simp only [CollatzResearch.WordTrace]
  refine ⟨56203464970368947031462737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37468976646912631354308491 56203464970368947031462737)
  ·
    refine ⟨42152598727776710273597053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56203464970368947031462737 42152598727776710273597053)
    ·
      refine ⟨15807224522916266352598895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42152598727776710273597053 15807224522916266352598895)
      ·
        refine ⟨23710836784374399528898343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15807224522916266352598895 23710836784374399528898343)
        ·
          refine ⟨35566255176561599293347515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23710836784374399528898343 35566255176561599293347515)
          ·
            refine ⟨53349382764842398940021273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35566255176561599293347515 53349382764842398940021273)
            ·
              refine ⟨40012037073631799205015955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53349382764842398940021273 40012037073631799205015955)
              ·
                refine ⟨60018055610447698807523933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40012037073631799205015955 60018055610447698807523933)
                ·
                  refine ⟨22506770853917887052821475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60018055610447698807523933 22506770853917887052821475)
                  ·
                    refine ⟨33760156280876830579232213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22506770853917887052821475 33760156280876830579232213)
                    ·
                      refine ⟨791253662833050716700755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 33760156280876830579232213 791253662833050716700755)
                      ·
                        rfl

theorem cell23_1540961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_1540961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540961 prefixEnd_1540961 := by exact prefixLift 1540961
  have htrace : WordTrace (prefixWord ++ tailWord_1540961) baseStart_1540961 baseEnd_1540961 := by
    simpa [prefixWord, tailWord_1540961, baseEnd_1540961] using wordTrace_append hprefix tailTrace_1540961
  have hstable : (prefixWord ++ tailWord_1540961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540961).length < 2 ^ (prefixWord ++ tailWord_1540961).sum := by decide
  have hdescent : baseEnd_1540961 < baseStart_1540961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540968 : List Nat := [2, 1, 4, 2, 1, 2, 2, 1, 1, 7]
def baseStart_1540968 : Nat := 118140960795 + 1540968 * 2 ^ 59
def prefixEnd_1540968 : Nat := 4983230072969 + 3 ^ 40 * 1540968 * 2
def baseEnd_1540968 : Nat := 263752419065877396437741

theorem tailTrace_1540968 : CollatzResearch.WordTrace tailWord_1540968 prefixEnd_1540968 263752419065877396437741 := by
  unfold tailWord_1540968
  simp only [CollatzResearch.WordTrace]
  refine ⟨28101860140671793613483779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37469146854229058151311705 28101860140671793613483779)
  ·
    refine ⟨42152790211007690420225669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28101860140671793613483779 42152790211007690420225669)
    ·
      refine ⟨7903648164563941953792313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42152790211007690420225669 7903648164563941953792313)
      ·
        refine ⟨5927736123422956465344235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7903648164563941953792313 5927736123422956465344235)
        ·
          refine ⟨8891604185134434698016353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5927736123422956465344235 8891604185134434698016353)
          ·
            refine ⟨6668703138850826023512265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8891604185134434698016353 6668703138850826023512265)
            ·
              refine ⟨5001527354138119517634199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6668703138850826023512265 5001527354138119517634199)
              ·
                refine ⟨7502291031207179276451299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5001527354138119517634199 7502291031207179276451299)
                ·
                  refine ⟨11253436546810768914676949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7502291031207179276451299 11253436546810768914676949)
                  ·
                    refine ⟨263752419065877396437741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11253436546810768914676949 263752419065877396437741)
                    ·
                      rfl

theorem cell23_1540968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_1540968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1540968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1540968 prefixEnd_1540968 := by exact prefixLift 1540968
  have htrace : WordTrace (prefixWord ++ tailWord_1540968) baseStart_1540968 baseEnd_1540968 := by
    simpa [prefixWord, tailWord_1540968, baseEnd_1540968] using wordTrace_append hprefix tailTrace_1540968
  have hstable : (prefixWord ++ tailWord_1540968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540968).length < 2 ^ (prefixWord ++ tailWord_1540968).sum := by decide
  have hdescent : baseEnd_1540968 < baseStart_1540968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541011 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 10]
def baseStart_1541011 : Nat := 118140960795 + 1541011 * 2 ^ 59
def prefixEnd_1541011 : Nat := 4983230072969 + 3 ^ 40 * 1541011 * 2
def baseEnd_1541011 : Nat := 87919926318419502341725

theorem tailTrace_1541011 : CollatzResearch.WordTrace tailWord_1541011 prefixEnd_1541011 87919926318419502341725 := by
  unfold tailWord_1541011
  simp only [CollatzResearch.WordTrace]
  refine ⟨56205288620187805570782887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37470192413458537047188591 56205288620187805570782887)
  ·
    refine ⟨84307932930281708356174331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56205288620187805570782887 84307932930281708356174331)
    ·
      refine ⟨126461899395422562534261497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84307932930281708356174331 126461899395422562534261497)
      ·
        refine ⟨94846424546566921900696123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126461899395422562534261497 94846424546566921900696123)
        ·
          refine ⟨142269636819850382851044185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94846424546566921900696123 142269636819850382851044185)
          ·
            refine ⟨106702227614887787138283139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142269636819850382851044185 106702227614887787138283139)
            ·
              refine ⟨160053341422331680707424709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106702227614887787138283139 160053341422331680707424709)
              ·
                refine ⟨30010001516687190132642133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160053341422331680707424709 30010001516687190132642133)
                ·
                  refine ⟨87919926318419502341725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 30010001516687190132642133 87919926318419502341725)
                  ·
                    rfl

theorem cell23_1541011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 10].length) (baseStart_1541011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541011 prefixEnd_1541011 := by exact prefixLift 1541011
  have htrace : WordTrace (prefixWord ++ tailWord_1541011) baseStart_1541011 baseEnd_1541011 := by
    simpa [prefixWord, tailWord_1541011, baseEnd_1541011] using wordTrace_append hprefix tailTrace_1541011
  have hstable : (prefixWord ++ tailWord_1541011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541011).length < 2 ^ (prefixWord ++ tailWord_1541011).sum := by decide
  have hdescent : baseEnd_1541011 < baseStart_1541011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541045 : List Nat := [1, 3, 3, 2, 1, 1, 4, 2, 6]
def baseStart_1541045 : Nat := 118140960795 + 1541045 * 2 ^ 59
def prefixEnd_1541045 : Nat := 4983230072969 + 3 ^ 40 * 1541045 * 2
def baseEnd_1541045 : Nat := 87921866134225376450041

theorem tailTrace_1541045 : CollatzResearch.WordTrace tailWord_1541045 prefixEnd_1541045 87921866134225376450041 := by
  unfold tailWord_1541045
  simp only [CollatzResearch.WordTrace]
  refine ⟨56206528702064629377520589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37471019134709752918347059 56206528702064629377520589)
  ·
    refine ⟨21077448263274236016570221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56206528702064629377520589 21077448263274236016570221)
    ·
      refine ⟨7904043098727838506213833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21077448263274236016570221 7904043098727838506213833)
      ·
        refine ⟨5928032324045878879660375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7904043098727838506213833 5928032324045878879660375)
        ·
          refine ⟨8892048486068818319490563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5928032324045878879660375 8892048486068818319490563)
          ·
            refine ⟨13338072729103227479235845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8892048486068818319490563 13338072729103227479235845)
            ·
              refine ⟨2500888636706855152356721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13338072729103227479235845 2500888636706855152356721)
              ·
                refine ⟨1875666477530141364267541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2500888636706855152356721 1875666477530141364267541)
                ·
                  refine ⟨87921866134225376450041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1875666477530141364267541 87921866134225376450041)
                  ·
                    rfl

theorem cell23_1541045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 6].length) (baseStart_1541045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541045 prefixEnd_1541045 := by exact prefixLift 1541045
  have htrace : WordTrace (prefixWord ++ tailWord_1541045) baseStart_1541045 baseEnd_1541045 := by
    simpa [prefixWord, tailWord_1541045, baseEnd_1541045] using wordTrace_append hprefix tailTrace_1541045
  have hstable : (prefixWord ++ tailWord_1541045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541045).length < 2 ^ (prefixWord ++ tailWord_1541045).sum := by decide
  have hdescent : baseEnd_1541045 < baseStart_1541045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541049 : List Nat := [1, 2, 1, 4, 2, 2, 4, 2, 1, 4]
def baseStart_1541049 : Nat := 118140960795 + 1541049 * 2 ^ 59
def prefixEnd_1541049 : Nat := 4983230072969 + 3 ^ 40 * 1541049 * 2
def baseEnd_1541049 : Nat := 263766283043548790800117

theorem tailTrace_1541049 : CollatzResearch.WordTrace tailWord_1541049 prefixEnd_1541049 263766283043548790800117 := by
  unfold tailWord_1541049
  simp only [CollatzResearch.WordTrace]
  refine ⟨56206674594050138060666201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37471116396033425373777467 56206674594050138060666201)
  ·
    refine ⟨42155005945537603545499651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56206674594050138060666201 42155005945537603545499651)
    ·
      refine ⟨63232508918306405318249477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42155005945537603545499651 63232508918306405318249477)
      ·
        refine ⟨11856095422182450997171777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63232508918306405318249477 11856095422182450997171777)
        ·
          refine ⟨8892071566636838247878833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11856095422182450997171777 8892071566636838247878833)
          ·
            refine ⟨6669053674977628685909125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8892071566636838247878833 6669053674977628685909125)
            ·
              refine ⟨1250447564058305378607961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6669053674977628685909125 1250447564058305378607961)
              ·
                refine ⟨937835673043729033955971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1250447564058305378607961 937835673043729033955971)
                ·
                  refine ⟨1406753509565593550933957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 937835673043729033955971 1406753509565593550933957)
                  ·
                    refine ⟨263766283043548790800117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1406753509565593550933957 263766283043548790800117)
                    ·
                      rfl

theorem cell23_1541049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 2, 1, 4].length) (baseStart_1541049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541049 prefixEnd_1541049 := by exact prefixLift 1541049
  have htrace : WordTrace (prefixWord ++ tailWord_1541049) baseStart_1541049 baseEnd_1541049 := by
    simpa [prefixWord, tailWord_1541049, baseEnd_1541049] using wordTrace_append hprefix tailTrace_1541049
  have hstable : (prefixWord ++ tailWord_1541049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541049).length < 2 ^ (prefixWord ++ tailWord_1541049).sum := by decide
  have hdescent : baseEnd_1541049 < baseStart_1541049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541068 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 2, 1, 7]
def baseStart_1541068 : Nat := 118140960795 + 1541068 * 2 ^ 59
def prefixEnd_1541068 : Nat := 4983230072969 + 3 ^ 40 * 1541068 * 2
def baseEnd_1541068 : Nat := 791308605263081798062763

theorem tailTrace_1541068 : CollatzResearch.WordTrace tailWord_1541068 prefixEnd_1541068 791308605263081798062763 := by
  unfold tailWord_1541068
  simp only [CollatzResearch.WordTrace]
  refine ⟨28103683790490652152803929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37471578387320869537071905 28103683790490652152803929)
  ·
    refine ⟨21077762842867989114602947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28103683790490652152803929 21077762842867989114602947)
    ·
      refine ⟨31616644264301983671904421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21077762842867989114602947 31616644264301983671904421)
      ·
        refine ⟨5928120799556621938482079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31616644264301983671904421 5928120799556621938482079)
        ·
          refine ⟨8892181199334932907723119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5928120799556621938482079 8892181199334932907723119)
          ·
            refine ⟨13338271799002399361584679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8892181199334932907723119 13338271799002399361584679)
            ·
              refine ⟨20007407698503599042377019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13338271799002399361584679 20007407698503599042377019)
              ·
                refine ⟨30011111547755398563565529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20007407698503599042377019 30011111547755398563565529)
                ·
                  refine ⟨22508333660816548922674147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30011111547755398563565529 22508333660816548922674147)
                  ·
                    refine ⟨33762500491224823384011221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22508333660816548922674147 33762500491224823384011221)
                    ·
                      refine ⟨791308605263081798062763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 33762500491224823384011221 791308605263081798062763)
                      ·
                        rfl

theorem cell23_1541068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_1541068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541068 prefixEnd_1541068 := by exact prefixLift 1541068
  have htrace : WordTrace (prefixWord ++ tailWord_1541068) baseStart_1541068 baseEnd_1541068 := by
    simpa [prefixWord, tailWord_1541068, baseEnd_1541068] using wordTrace_append hprefix tailTrace_1541068
  have hstable : (prefixWord ++ tailWord_1541068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541068).length < 2 ^ (prefixWord ++ tailWord_1541068).sum := by decide
  have hdescent : baseEnd_1541068 < baseStart_1541068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541082 : List Nat := [3, 1, 1, 2, 4, 2, 1, 1, 1, 5, 2]
def baseStart_1541082 : Nat := 118140960795 + 1541082 * 2 ^ 59
def prefixEnd_1541082 : Nat := 4983230072969 + 3 ^ 40 * 1541082 * 2
def baseEnd_1541082 : Nat := 791315793992244743287699

theorem tailTrace_1541082 : CollatzResearch.WordTrace tailWord_1541082 prefixEnd_1541082 791315793992244743287699 := by
  unfold tailWord_1541082
  simp only [CollatzResearch.WordTrace]
  refine ⟨14051969550732646174154375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37471918801953723131078333 14051969550732646174154375)
  ·
    refine ⟨21077954326098969261231563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14051969550732646174154375 21077954326098969261231563)
    ·
      refine ⟨31616931489148453891847345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21077954326098969261231563 31616931489148453891847345)
      ·
        refine ⟨23712698616861340418885509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31616931489148453891847345 23712698616861340418885509)
        ·
          refine ⟨4446130990661501328541033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23712698616861340418885509 4446130990661501328541033)
          ·
            refine ⟨3334598242996125996405775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4446130990661501328541033 3334598242996125996405775)
            ·
              refine ⟨5001897364494188994608663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3334598242996125996405775 5001897364494188994608663)
              ·
                refine ⟨7502846046741283491912995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5001897364494188994608663 7502846046741283491912995)
                ·
                  refine ⟨11254269070111925237869493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7502846046741283491912995 11254269070111925237869493)
                  ·
                    refine ⟨1055087725322992991050265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11254269070111925237869493 1055087725322992991050265)
                    ·
                      refine ⟨791315793992244743287699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1055087725322992991050265 791315793992244743287699)
                      ·
                        rfl

theorem cell23_1541082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 1, 5, 2].length) (baseStart_1541082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541082 prefixEnd_1541082 := by exact prefixLift 1541082
  have htrace : WordTrace (prefixWord ++ tailWord_1541082) baseStart_1541082 baseEnd_1541082 := by
    simpa [prefixWord, tailWord_1541082, baseEnd_1541082] using wordTrace_append hprefix tailTrace_1541082
  have hstable : (prefixWord ++ tailWord_1541082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541082).length < 2 ^ (prefixWord ++ tailWord_1541082).sum := by decide
  have hdescent : baseEnd_1541082 < baseStart_1541082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541106 : List Nat := [3, 2, 1, 5, 1, 1, 2, 1, 3, 1, 3]
def baseStart_1541106 : Nat := 118140960795 + 1541106 * 2 ^ 59
def prefixEnd_1541106 : Nat := 4983230072969 + 3 ^ 40 * 1541106 * 2
def baseEnd_1541106 : Nat := 791328117527952649387589

theorem tailTrace_1541106 : CollatzResearch.WordTrace tailWord_1541106 prefixEnd_1541106 791328117527952649387589 := by
  unfold tailWord_1541106
  simp only [CollatzResearch.WordTrace]
  refine ⟨14052188388710909198872793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37472502369895757863660781 14052188388710909198872793)
  ·
    refine ⟨10539141291533181899154595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14052188388710909198872793 10539141291533181899154595)
    ·
      refine ⟨15808711937299772848731893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10539141291533181899154595 15808711937299772848731893)
      ·
        refine ⟨1482066744121853704568615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15808711937299772848731893 1482066744121853704568615)
        ·
          refine ⟨2223100116182780556852923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1482066744121853704568615 2223100116182780556852923)
          ·
            refine ⟨3334650174274170835279385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2223100116182780556852923 3334650174274170835279385)
            ·
              refine ⟨2500987630705628126459539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3334650174274170835279385 2500987630705628126459539)
              ·
                refine ⟨3751481446058442189689309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2500987630705628126459539 3751481446058442189689309)
                ·
                  refine ⟨1406805542271915821133491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3751481446058442189689309 1406805542271915821133491)
                  ·
                    refine ⟨2110208313407873731700237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1406805542271915821133491 2110208313407873731700237)
                    ·
                      refine ⟨791328117527952649387589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2110208313407873731700237 791328117527952649387589)
                      ·
                        rfl

theorem cell23_1541106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_1541106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541106 prefixEnd_1541106 := by exact prefixLift 1541106
  have htrace : WordTrace (prefixWord ++ tailWord_1541106) baseStart_1541106 baseEnd_1541106 := by
    simpa [prefixWord, tailWord_1541106, baseEnd_1541106] using wordTrace_append hprefix tailTrace_1541106
  have hstable : (prefixWord ++ tailWord_1541106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541106).length < 2 ^ (prefixWord ++ tailWord_1541106).sum := by decide
  have hdescent : baseEnd_1541106 < baseStart_1541106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541132 : List Nat := [2, 2, 1, 2, 3, 2, 1, 4, 1, 2, 3]
def baseStart_1541132 : Nat := 118140960795 + 1541132 * 2 ^ 59
def prefixEnd_1541132 : Nat := 4983230072969 + 3 ^ 40 * 1541132 * 2
def baseEnd_1541132 : Nat := 791341468024969547662469

theorem tailTrace_1541132 : CollatzResearch.WordTrace tailWord_1541132 prefixEnd_1541132 791341468024969547662469 := by
  unfold tailWord_1541132
  simp only [CollatzResearch.WordTrace]
  refine ⟨28104850926374721617968825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37473134568499628823958433 28104850926374721617968825)
  ·
    refine ⟨21078638194781041213476619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28104850926374721617968825 21078638194781041213476619)
    ·
      refine ⟨31617957292171561820214929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21078638194781041213476619 31617957292171561820214929)
      ·
        refine ⟨23713467969128671365161197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31617957292171561820214929 23713467969128671365161197)
        ·
          refine ⟨8892550488423251761935449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23713467969128671365161197 8892550488423251761935449)
          ·
            refine ⟨6669412866317438821451587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8892550488423251761935449 6669412866317438821451587)
            ·
              refine ⟨10004119299476158232177381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6669412866317438821451587 10004119299476158232177381)
              ·
                refine ⟨1875772368651779668533259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10004119299476158232177381 1875772368651779668533259)
                ·
                  refine ⟨2813658552977669502799889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1875772368651779668533259 2813658552977669502799889)
                  ·
                    refine ⟨2110243914733252127099917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2813658552977669502799889 2110243914733252127099917)
                    ·
                      refine ⟨791341468024969547662469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2110243914733252127099917 791341468024969547662469)
                      ·
                        rfl

theorem cell23_1541132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_1541132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541132 prefixEnd_1541132 := by exact prefixLift 1541132
  have htrace : WordTrace (prefixWord ++ tailWord_1541132) baseStart_1541132 baseEnd_1541132 := by
    simpa [prefixWord, tailWord_1541132, baseEnd_1541132] using wordTrace_append hprefix tailTrace_1541132
  have hstable : (prefixWord ++ tailWord_1541132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541132).length < 2 ^ (prefixWord ++ tailWord_1541132).sum := by decide
  have hdescent : baseEnd_1541132 < baseStart_1541132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541145 : List Nat := [1, 2, 1, 2, 1, 1, 4, 4, 1, 3, 3]
def baseStart_1541145 : Nat := 118140960795 + 1541145 * 2 ^ 59
def prefixEnd_1541145 : Nat := 4983230072969 + 3 ^ 40 * 1541145 * 2
def baseEnd_1541145 : Nat := 791348143273477996799909

theorem tailTrace_1541145 : CollatzResearch.WordTrace tailWord_1541145 prefixEnd_1541145 791348143273477996799909 := by
  unfold tailWord_1541145
  simp only [CollatzResearch.WordTrace]
  refine ⟨56210176001702346456160889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37473450667801564304107259 56210176001702346456160889)
  ·
    refine ⟨42157632001276759842120667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56210176001702346456160889 42157632001276759842120667)
    ·
      refine ⟨63236448001915139763181001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42157632001276759842120667 63236448001915139763181001)
      ·
        refine ⟨47427336001436354822385751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63236448001915139763181001 47427336001436354822385751)
        ·
          refine ⟨71141004002154532233578627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47427336001436354822385751 71141004002154532233578627)
          ·
            refine ⟨106711506003231798350367941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71141004002154532233578627 106711506003231798350367941)
            ·
              refine ⟨20008407375605962190693989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106711506003231798350367941 20008407375605962190693989)
              ·
                refine ⟨3751576382926117910755123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20008407375605962190693989 3751576382926117910755123)
                ·
                  refine ⟨5627364574389176866132685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3751576382926117910755123 5627364574389176866132685)
                  ·
                    refine ⟨2110261715395941324799757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5627364574389176866132685 2110261715395941324799757)
                    ·
                      refine ⟨791348143273477996799909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2110261715395941324799757 791348143273477996799909)
                      ·
                        rfl

theorem cell23_1541145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 3, 3].length) (baseStart_1541145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541145 prefixEnd_1541145 := by exact prefixLift 1541145
  have htrace : WordTrace (prefixWord ++ tailWord_1541145) baseStart_1541145 baseEnd_1541145 := by
    simpa [prefixWord, tailWord_1541145, baseEnd_1541145] using wordTrace_append hprefix tailTrace_1541145
  have hstable : (prefixWord ++ tailWord_1541145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541145).length < 2 ^ (prefixWord ++ tailWord_1541145).sum := by decide
  have hdescent : baseEnd_1541145 < baseStart_1541145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541152 : List Nat := [2, 1, 1, 7, 1, 2, 9]
def baseStart_1541152 : Nat := 118140960795 + 1541152 * 2 ^ 59
def prefixEnd_1541152 : Nat := 4983230072969 + 3 ^ 40 * 1541152 * 2
def baseEnd_1541152 : Nat := 9769774538741474931017

theorem tailTrace_1541152 : CollatzResearch.WordTrace tailWord_1541152 prefixEnd_1541152 9769774538741474931017 := by
  unfold tailWord_1541152
  simp only [CollatzResearch.WordTrace]
  refine ⟨28105215656338493325832855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37473620875117991101110473 28105215656338493325832855)
  ·
    refine ⟨42157823484507739988749283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28105215656338493325832855 42157823484507739988749283)
    ·
      refine ⟨63236735226761609983123925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42157823484507739988749283 63236735226761609983123925)
      ·
        refine ⟨1482110981877225233979467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 63236735226761609983123925 1482110981877225233979467)
        ·
          refine ⟨2223166472815837850969201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1482110981877225233979467 2223166472815837850969201)
          ·
            refine ⟨1667374854611878388226901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2223166472815837850969201 1667374854611878388226901)
            ·
              refine ⟨9769774538741474931017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1667374854611878388226901 9769774538741474931017)
              ·
                rfl

theorem cell23_1541152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 9].length) (baseStart_1541152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541152 prefixEnd_1541152 := by exact prefixLift 1541152
  have htrace : WordTrace (prefixWord ++ tailWord_1541152) baseStart_1541152 baseEnd_1541152 := by
    simpa [prefixWord, tailWord_1541152, baseEnd_1541152] using wordTrace_append hprefix tailTrace_1541152
  have hstable : (prefixWord ++ tailWord_1541152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541152).length < 2 ^ (prefixWord ++ tailWord_1541152).sum := by decide
  have hdescent : baseEnd_1541152 < baseStart_1541152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541189 : List Nat := [1, 3, 1, 1, 1, 3, 5, 2, 1, 3, 2]
def baseStart_1541189 : Nat := 118140960795 + 1541189 * 2 ^ 59
def prefixEnd_1541189 : Nat := 4983230072969 + 3 ^ 40 * 1541189 * 2
def baseEnd_1541189 : Nat := 791370736422275824649707

theorem tailTrace_1541189 : CollatzResearch.WordTrace tailWord_1541189 prefixEnd_1541189 791370736422275824649707 := by
  unfold tailWord_1541189
  simp only [CollatzResearch.WordTrace]
  refine ⟨56211780813542941970762621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37474520542361961313841747 56211780813542941970762621)
  ·
    refine ⟨21079417805078603239035983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56211780813542941970762621 21079417805078603239035983)
    ·
      refine ⟨31619126707617904858553975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21079417805078603239035983 31619126707617904858553975)
      ·
        refine ⟨47428690061426857287830963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31619126707617904858553975 47428690061426857287830963)
        ·
          refine ⟨71143035092140285931746445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47428690061426857287830963 71143035092140285931746445)
          ·
            refine ⟨26678638159552607224404917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71143035092140285931746445 26678638159552607224404917)
            ·
              refine ⟨2501122327458056927287961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26678638159552607224404917 2501122327458056927287961)
              ·
                refine ⟨1875841745593542695465971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2501122327458056927287961 1875841745593542695465971)
                ·
                  refine ⟨2813762618390314043198957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1875841745593542695465971 2813762618390314043198957)
                  ·
                    refine ⟨1055160981896367766199609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2813762618390314043198957 1055160981896367766199609)
                    ·
                      refine ⟨791370736422275824649707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1055160981896367766199609 791370736422275824649707)
                      ·
                        rfl

theorem cell23_1541189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 3, 2].length) (baseStart_1541189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541189 prefixEnd_1541189 := by exact prefixLift 1541189
  have htrace : WordTrace (prefixWord ++ tailWord_1541189) baseStart_1541189 baseEnd_1541189 := by
    simpa [prefixWord, tailWord_1541189, baseEnd_1541189] using wordTrace_append hprefix tailTrace_1541189
  have hstable : (prefixWord ++ tailWord_1541189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541189).length < 2 ^ (prefixWord ++ tailWord_1541189).sum := by decide
  have hdescent : baseEnd_1541189 < baseStart_1541189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541205 : List Nat := [1, 3, 2, 2, 1, 2, 1, 3, 2, 1, 5]
def baseStart_1541205 : Nat := 118140960795 + 1541205 * 2 ^ 59
def prefixEnd_1541205 : Nat := 4983230072969 + 3 ^ 40 * 1541205 * 2
def baseEnd_1541205 : Nat := 791378952112747762049633

theorem tailTrace_1541205 : CollatzResearch.WordTrace tailWord_1541205 prefixEnd_1541205 791378952112747762049633 := by
  unfold tailWord_1541205
  simp only [CollatzResearch.WordTrace]
  refine ⟨56212364381484976703345069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37474909587656651135563379 56212364381484976703345069)
  ·
    refine ⟨21079636643056866263754401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56212364381484976703345069 21079636643056866263754401)
    ·
      refine ⟨15809727482292649697815801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21079636643056866263754401 15809727482292649697815801)
      ·
        refine ⟨11857295611719487273361851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15809727482292649697815801 11857295611719487273361851)
        ·
          refine ⟨17785943417579230910042777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11857295611719487273361851 17785943417579230910042777)
          ·
            refine ⟨13339457563184423182532083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17785943417579230910042777 13339457563184423182532083)
            ·
              refine ⟨20009186344776634773798125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13339457563184423182532083 20009186344776634773798125)
              ·
                refine ⟨7503444879291238040174297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20009186344776634773798125 7503444879291238040174297)
                ·
                  refine ⟨5627583659468428530130723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7503444879291238040174297 5627583659468428530130723)
                  ·
                    refine ⟨8441375489202642795196085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5627583659468428530130723 8441375489202642795196085)
                    ·
                      refine ⟨791378952112747762049633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8441375489202642795196085 791378952112747762049633)
                      ·
                        rfl

theorem cell23_1541205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_1541205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541205 prefixEnd_1541205 := by exact prefixLift 1541205
  have htrace : WordTrace (prefixWord ++ tailWord_1541205) baseStart_1541205 baseEnd_1541205 := by
    simpa [prefixWord, tailWord_1541205, baseEnd_1541205] using wordTrace_append hprefix tailTrace_1541205
  have hstable : (prefixWord ++ tailWord_1541205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541205).length < 2 ^ (prefixWord ++ tailWord_1541205).sum := by decide
  have hdescent : baseEnd_1541205 < baseStart_1541205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541213 : List Nat := [1, 4, 4, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_1541213 : Nat := 118140960795 + 1541213 * 2 ^ 59
def prefixEnd_1541213 : Nat := 4983230072969 + 3 ^ 40 * 1541213 * 2
def baseEnd_1541213 : Nat := 791383059957983730749597

theorem tailTrace_1541213 : CollatzResearch.WordTrace tailWord_1541213 prefixEnd_1541213 791383059957983730749597 := by
  unfold tailWord_1541213
  simp only [CollatzResearch.WordTrace]
  refine ⟨56212656165455994069636293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37475104110303996046424195 56212656165455994069636293)
  ·
    refine ⟨10539873031022998888056805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56212656165455994069636293 10539873031022998888056805)
    ·
      refine ⟨1976226193316812291510651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10539873031022998888056805 1976226193316812291510651)
      ·
        refine ⟨2964339289975218437265977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1976226193316812291510651 2964339289975218437265977)
        ·
          refine ⟨2223254467481413827949483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2964339289975218437265977 2223254467481413827949483)
          ·
            refine ⟨3334881701222120741924225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2223254467481413827949483 3334881701222120741924225)
            ·
              refine ⟨2501161275916590556443169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3334881701222120741924225 2501161275916590556443169)
              ·
                refine ⟨1875870956937442917332377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2501161275916590556443169 1875870956937442917332377)
                ·
                  refine ⟨1406903217703082187999283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1875870956937442917332377 1406903217703082187999283)
                  ·
                    refine ⟨2110354826554623281998925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1406903217703082187999283 2110354826554623281998925)
                    ·
                      refine ⟨791383059957983730749597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2110354826554623281998925 791383059957983730749597)
                      ·
                        rfl

theorem cell23_1541213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_1541213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541213 prefixEnd_1541213 := by exact prefixLift 1541213
  have htrace : WordTrace (prefixWord ++ tailWord_1541213) baseStart_1541213 baseEnd_1541213 := by
    simpa [prefixWord, tailWord_1541213, baseEnd_1541213] using wordTrace_append hprefix tailTrace_1541213
  have hstable : (prefixWord ++ tailWord_1541213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541213).length < 2 ^ (prefixWord ++ tailWord_1541213).sum := by decide
  have hdescent : baseEnd_1541213 < baseStart_1541213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541214 : List Nat := [4, 4, 1, 1, 1, 3, 2, 2, 1, 2, 2]
def baseStart_1541214 : Nat := 118140960795 + 1541214 * 2 ^ 59
def prefixEnd_1541214 : Nat := 4983230072969 + 3 ^ 40 * 1541214 * 2
def baseEnd_1541214 : Nat := 791383573438638226837093

theorem tailTrace_1541214 : CollatzResearch.WordTrace tailWord_1541214 prefixEnd_1541214 791383573438638226837093 := by
  unfold tailWord_1541214
  simp only [CollatzResearch.WordTrace]
  refine ⟨7026586579806546405052837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37475128425634914160281797 7026586579806546405052837)
  ·
    refine ⟨1317484983713727450947407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7026586579806546405052837 1317484983713727450947407)
    ·
      refine ⟨1976227475570591176421111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1317484983713727450947407 1976227475570591176421111)
      ·
        refine ⟨2964341213355886764631667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1976227475570591176421111 2964341213355886764631667)
        ·
          refine ⟨4446511820033830146947501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2964341213355886764631667 4446511820033830146947501)
          ·
            refine ⟨1667441932512686305105313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4446511820033830146947501 1667441932512686305105313)
            ·
              refine ⟨1250581449384514728828985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1667441932512686305105313 1250581449384514728828985)
              ·
                refine ⟨937936087038386046621739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1250581449384514728828985 937936087038386046621739)
                ·
                  refine ⟨1406904130557579069932609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 937936087038386046621739 1406904130557579069932609)
                  ·
                    refine ⟨1055178097918184302449457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1406904130557579069932609 1055178097918184302449457)
                    ·
                      refine ⟨791383573438638226837093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1055178097918184302449457 791383573438638226837093)
                      ·
                        rfl

theorem cell23_1541214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_1541214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541214 prefixEnd_1541214 := by exact prefixLift 1541214
  have htrace : WordTrace (prefixWord ++ tailWord_1541214) baseStart_1541214 baseEnd_1541214 := by
    simpa [prefixWord, tailWord_1541214, baseEnd_1541214] using wordTrace_append hprefix tailTrace_1541214
  have hstable : (prefixWord ++ tailWord_1541214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541214).length < 2 ^ (prefixWord ++ tailWord_1541214).sum := by decide
  have hdescent : baseEnd_1541214 < baseStart_1541214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541215 : List Nat := [1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 4]
def baseStart_1541215 : Nat := 118140960795 + 1541215 * 2 ^ 59
def prefixEnd_1541215 : Nat := 4983230072969 + 3 ^ 40 * 1541215 * 2
def baseEnd_1541215 : Nat := 791384086919292722924587

theorem tailTrace_1541215 : CollatzResearch.WordTrace tailWord_1541215 prefixEnd_1541215 791384086919292722924587 := by
  unfold tailWord_1541215
  simp only [CollatzResearch.WordTrace]
  refine ⟨56212729111448748411209099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37475152740965832274139399 56212729111448748411209099)
  ·
    refine ⟨84319093667173122616813649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56212729111448748411209099 84319093667173122616813649)
    ·
      refine ⟨63239320250379841962610237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84319093667173122616813649 63239320250379841962610237)
      ·
        refine ⟨23714745093892440735978839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63239320250379841962610237 23714745093892440735978839)
        ·
          refine ⟨35572117640838661103968259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23714745093892440735978839 35572117640838661103968259)
          ·
            refine ⟨53358176461257991655952389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35572117640838661103968259 53358176461257991655952389)
            ·
              refine ⟨10004658086485873435491073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53358176461257991655952389 10004658086485873435491073)
              ·
                refine ⟨7503493564864405076618305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10004658086485873435491073 7503493564864405076618305)
                ·
                  refine ⟨5627620173648303807463729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7503493564864405076618305 5627620173648303807463729)
                  ·
                    refine ⟨4220715130236227855597797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5627620173648303807463729 4220715130236227855597797)
                    ·
                      refine ⟨791384086919292722924587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4220715130236227855597797 791384086919292722924587)
                      ·
                        rfl

theorem cell23_1541215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_1541215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541215 prefixEnd_1541215 := by exact prefixLift 1541215
  have htrace : WordTrace (prefixWord ++ tailWord_1541215) baseStart_1541215 baseEnd_1541215 := by
    simpa [prefixWord, tailWord_1541215, baseEnd_1541215] using wordTrace_append hprefix tailTrace_1541215
  have hstable : (prefixWord ++ tailWord_1541215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541215).length < 2 ^ (prefixWord ++ tailWord_1541215).sum := by decide
  have hdescent : baseEnd_1541215 < baseStart_1541215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541292 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 1, 6, 2]
def baseStart_1541292 : Nat := 118140960795 + 1541292 * 2 ^ 59
def prefixEnd_1541292 : Nat := 4983230072969 + 3 ^ 40 * 1541292 * 2
def baseEnd_1541292 : Nat := 791423624929688921661733

theorem tailTrace_1541292 : CollatzResearch.WordTrace tailWord_1541292 prefixEnd_1541292 791423624929688921661733 := by
  unfold tailWord_1541292
  simp only [CollatzResearch.WordTrace]
  refine ⟨28107768766084895280881065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37477025021446527041174753 28107768766084895280881065)
  ·
    refine ⟨21080826574563671460660799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28107768766084895280881065 21080826574563671460660799)
    ·
      refine ⟨31621239861845507190991199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21080826574563671460660799 31621239861845507190991199)
      ·
        refine ⟨47431859792768260786486799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31621239861845507190991199 47431859792768260786486799)
        ·
          refine ⟨71147789689152391179730199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47431859792768260786486799 71147789689152391179730199)
          ·
            refine ⟨106721684533728586769595299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71147789689152391179730199 106721684533728586769595299)
            ·
              refine ⟨160082526800592880154392949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106721684533728586769595299 160082526800592880154392949)
              ·
                refine ⟨15007736887555582514474339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 160082526800592880154392949 15007736887555582514474339)
                ·
                  refine ⟨22511605331333373771711509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15007736887555582514474339 22511605331333373771711509)
                  ·
                    refine ⟨1055231499906251895548977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22511605331333373771711509 1055231499906251895548977)
                    ·
                      refine ⟨791423624929688921661733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1055231499906251895548977 791423624929688921661733)
                      ·
                        rfl

theorem cell23_1541292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 6, 2].length) (baseStart_1541292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541292 prefixEnd_1541292 := by exact prefixLift 1541292
  have htrace : WordTrace (prefixWord ++ tailWord_1541292) baseStart_1541292 baseEnd_1541292 := by
    simpa [prefixWord, tailWord_1541292, baseEnd_1541292] using wordTrace_append hprefix tailTrace_1541292
  have hstable : (prefixWord ++ tailWord_1541292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541292).length < 2 ^ (prefixWord ++ tailWord_1541292).sum := by decide
  have hdescent : baseEnd_1541292 < baseStart_1541292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541335 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 8]
def baseStart_1541335 : Nat := 118140960795 + 1541335 * 2 ^ 59
def prefixEnd_1541335 : Nat := 4983230072969 + 3 ^ 40 * 1541335 * 2
def baseEnd_1541335 : Nat := 791445704597832253424035

theorem tailTrace_1541335 : CollatzResearch.WordTrace tailWord_1541335 prefixEnd_1541335 791445704597832253424035 := by
  unfold tailWord_1541335
  simp only [CollatzResearch.WordTrace]
  refine ⟨56217105871014008905577459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37478070580676005937051639 56217105871014008905577459)
  ·
    refine ⟨84325658806521013358366189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56217105871014008905577459 84325658806521013358366189)
    ·
      refine ⟨31622122052445380009387321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84325658806521013358366189 31622122052445380009387321)
      ·
        refine ⟨23716591539334035007040491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31622122052445380009387321 23716591539334035007040491)
        ·
          refine ⟨35574887309001052510560737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23716591539334035007040491 35574887309001052510560737)
          ·
            refine ⟨26681165481750789382920553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35574887309001052510560737 26681165481750789382920553)
            ·
              refine ⟨20010874111313092037190415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26681165481750789382920553 20010874111313092037190415)
              ·
                refine ⟨30016311166969638055785623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20010874111313092037190415 30016311166969638055785623)
                ·
                  refine ⟨45024466750454457083678435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30016311166969638055785623 45024466750454457083678435)
                  ·
                    refine ⟨67536700125681685625517653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45024466750454457083678435 67536700125681685625517653)
                    ·
                      refine ⟨791445704597832253424035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 67536700125681685625517653 791445704597832253424035)
                      ·
                        rfl

theorem cell23_1541335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_1541335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541335 prefixEnd_1541335 := by exact prefixLift 1541335
  have htrace : WordTrace (prefixWord ++ tailWord_1541335) baseStart_1541335 baseEnd_1541335 := by
    simpa [prefixWord, tailWord_1541335, baseEnd_1541335] using wordTrace_append hprefix tailTrace_1541335
  have hstable : (prefixWord ++ tailWord_1541335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541335).length < 2 ^ (prefixWord ++ tailWord_1541335).sum := by decide
  have hdescent : baseEnd_1541335 < baseStart_1541335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541336 : List Nat := [2, 1, 2, 2, 5, 2, 1, 1, 3, 4]
def baseStart_1541336 : Nat := 118140960795 + 1541336 * 2 ^ 59
def prefixEnd_1541336 : Nat := 4983230072969 + 3 ^ 40 * 1541336 * 2
def baseEnd_1541336 : Nat := 263815406026162249837177

theorem tailTrace_1541336 : CollatzResearch.WordTrace tailWord_1541336 prefixEnd_1541336 263815406026162249837177 := by
  unfold tailWord_1541336
  simp only [CollatzResearch.WordTrace]
  refine ⟨28108571172005193038181931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37478094896006924050909241 28108571172005193038181931)
  ·
    refine ⟨42162856758007789557272897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28108571172005193038181931 42162856758007789557272897)
    ·
      refine ⟨31622142568505842167954673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42162856758007789557272897 31622142568505842167954673)
      ·
        refine ⟨23716606926379381625966005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31622142568505842167954673 23716606926379381625966005)
        ·
          refine ⟨2223431899348067027434313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23716606926379381625966005 2223431899348067027434313)
          ·
            refine ⟨1667573924511050270575735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2223431899348067027434313 1667573924511050270575735)
            ·
              refine ⟨2501360886766575405863603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1667573924511050270575735 2501360886766575405863603)
              ·
                refine ⟨3752041330149863108795405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2501360886766575405863603 3752041330149863108795405)
                ·
                  refine ⟨1407015498806198665798277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3752041330149863108795405 1407015498806198665798277)
                  ·
                    refine ⟨263815406026162249837177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1407015498806198665798277 263815406026162249837177)
                    ·
                      rfl

theorem cell23_1541336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 3, 4].length) (baseStart_1541336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541336 prefixEnd_1541336 := by exact prefixLift 1541336
  have htrace : WordTrace (prefixWord ++ tailWord_1541336) baseStart_1541336 baseEnd_1541336 := by
    simpa [prefixWord, tailWord_1541336, baseEnd_1541336] using wordTrace_append hprefix tailTrace_1541336
  have hstable : (prefixWord ++ tailWord_1541336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541336).length < 2 ^ (prefixWord ++ tailWord_1541336).sum := by decide
  have hdescent : baseEnd_1541336 < baseStart_1541336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541349 : List Nat := [1, 3, 1, 4, 3, 1, 1, 3, 6]
def baseStart_1541349 : Nat := 118140960795 + 1541349 * 2 ^ 59
def prefixEnd_1541349 : Nat := 4983230072969 + 3 ^ 40 * 1541349 * 2
def baseEnd_1541349 : Nat := 87939210369666133183219

theorem tailTrace_1541349 : CollatzResearch.WordTrace tailWord_1541349 prefixEnd_1541349 87939210369666133183219 := by
  unfold tailWord_1541349
  simp only [CollatzResearch.WordTrace]
  refine ⟨56217616492963289296587101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37478410995308859531058067 56217616492963289296587101)
  ·
    refine ⟨21081606184861233486220163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56217616492963289296587101 21081606184861233486220163)
    ·
      refine ⟨31622409277291850229330245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21081606184861233486220163 31622409277291850229330245)
      ·
        refine ⟨5929201739492221917999421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31622409277291850229330245 5929201739492221917999421)
        ·
          refine ⟨2223450652309583219249783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5929201739492221917999421 2223450652309583219249783)
          ·
            refine ⟨3335175978464374828874675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2223450652309583219249783 3335175978464374828874675)
            ·
              refine ⟨5002763967696562243312013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3335175978464374828874675 5002763967696562243312013)
              ·
                refine ⟨1876036487886210841242005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5002763967696562243312013 1876036487886210841242005)
                ·
                  refine ⟨87939210369666133183219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1876036487886210841242005 87939210369666133183219)
                  ·
                    rfl

theorem cell23_1541349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 6].length) (baseStart_1541349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541349 prefixEnd_1541349 := by exact prefixLift 1541349
  have htrace : WordTrace (prefixWord ++ tailWord_1541349) baseStart_1541349 baseEnd_1541349 := by
    simpa [prefixWord, tailWord_1541349, baseEnd_1541349] using wordTrace_append hprefix tailTrace_1541349
  have hstable : (prefixWord ++ tailWord_1541349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541349).length < 2 ^ (prefixWord ++ tailWord_1541349).sum := by decide
  have hdescent : baseEnd_1541349 < baseStart_1541349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541376 : List Nat := [2, 1, 1, 2, 1, 1, 3, 7, 1, 1, 3]
def baseStart_1541376 : Nat := 118140960795 + 1541376 * 2 ^ 59
def prefixEnd_1541376 : Nat := 4983230072969 + 3 ^ 40 * 1541376 * 2
def baseEnd_1541376 : Nat := 791466757304666593011347

theorem tailTrace_1541376 : CollatzResearch.WordTrace tailWord_1541376 prefixEnd_1541376 791466757304666593011347 := by
  unfold tailWord_1541376
  simp only [CollatzResearch.WordTrace]
  refine ⟨28109300631932736453909991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37479067509243648605213321 28109300631932736453909991)
  ·
    refine ⟨42163950947899104680864987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28109300631932736453909991 42163950947899104680864987)
    ·
      refine ⟨63245926421848657021297481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42163950947899104680864987 63245926421848657021297481)
      ·
        refine ⟨47434444816386492765973111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63245926421848657021297481 47434444816386492765973111)
        ·
          refine ⟨71151667224579739148959667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47434444816386492765973111 71151667224579739148959667)
          ·
            refine ⟨106727500836869608723439501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71151667224579739148959667 106727500836869608723439501)
            ·
              refine ⟨40022812813826103271289813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106727500836869608723439501 40022812813826103271289813)
              ·
                refine ⟨938034675324049295420855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 40022812813826103271289813 938034675324049295420855)
                ·
                  refine ⟨1407052012986073943131283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 938034675324049295420855 1407052012986073943131283)
                  ·
                    refine ⟨2110578019479110914696925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1407052012986073943131283 2110578019479110914696925)
                    ·
                      refine ⟨791466757304666593011347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2110578019479110914696925 791466757304666593011347)
                      ·
                        rfl

theorem cell23_1541376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 7, 1, 1, 3].length) (baseStart_1541376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541376 prefixEnd_1541376 := by exact prefixLift 1541376
  have htrace : WordTrace (prefixWord ++ tailWord_1541376) baseStart_1541376 baseEnd_1541376 := by
    simpa [prefixWord, tailWord_1541376, baseEnd_1541376] using wordTrace_append hprefix tailTrace_1541376
  have hstable : (prefixWord ++ tailWord_1541376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541376).length < 2 ^ (prefixWord ++ tailWord_1541376).sum := by decide
  have hdescent : baseEnd_1541376 < baseStart_1541376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541392 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 10, 4]
def baseStart_1541392 : Nat := 118140960795 + 1541392 * 2 ^ 59
def prefixEnd_1541392 : Nat := 4983230072969 + 3 ^ 40 * 1541392 * 2
def baseEnd_1541392 : Nat := 263824990998379510137091

theorem tailTrace_1541392 : CollatzResearch.WordTrace tailWord_1541392 prefixEnd_1541392 263824990998379510137091 := by
  unfold tailWord_1541392
  simp only [CollatzResearch.WordTrace]
  refine ⟨28109592415903753820201215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37479456554538338426934953 28109592415903753820201215)
  ·
    refine ⟨42164388623855630730301823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28109592415903753820201215 42164388623855630730301823)
    ·
      refine ⟨63246582935783446095452735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42164388623855630730301823 63246582935783446095452735)
      ·
        refine ⟨94869874403675169143179103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63246582935783446095452735 94869874403675169143179103)
        ·
          refine ⟨142304811605512753714768655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94869874403675169143179103 142304811605512753714768655)
          ·
            refine ⟨213457217408269130572152983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142304811605512753714768655 213457217408269130572152983)
            ·
              refine ⟨320185826112403695858229475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213457217408269130572152983 320185826112403695858229475)
              ·
                refine ⟨480278739168605543787344213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320185826112403695858229475 480278739168605543787344213)
                ·
                  refine ⟨1407066618658024054064485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 480278739168605543787344213 1407066618658024054064485)
                  ·
                    refine ⟨263824990998379510137091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1407066618658024054064485 263824990998379510137091)
                    ·
                      rfl

theorem cell23_1541392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 10, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 10, 4].length) (baseStart_1541392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541392 prefixEnd_1541392 := by exact prefixLift 1541392
  have htrace : WordTrace (prefixWord ++ tailWord_1541392) baseStart_1541392 baseEnd_1541392 := by
    simpa [prefixWord, tailWord_1541392, baseEnd_1541392] using wordTrace_append hprefix tailTrace_1541392
  have hstable : (prefixWord ++ tailWord_1541392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541392).length < 2 ^ (prefixWord ++ tailWord_1541392).sum := by decide
  have hdescent : baseEnd_1541392 < baseStart_1541392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541429 : List Nat := [1, 3, 3, 1, 2, 2, 2, 2, 1, 2, 4]
def baseStart_1541429 : Nat := 118140960795 + 1541429 * 2 ^ 59
def prefixEnd_1541429 : Nat := 4983230072969 + 3 ^ 40 * 1541429 * 2
def baseEnd_1541429 : Nat := 791493971779354885648603

theorem tailTrace_1541429 : CollatzResearch.WordTrace tailWord_1541429 prefixEnd_1541429 791493971779354885648603 := by
  unfold tailWord_1541429
  simp only [CollatzResearch.WordTrace]
  refine ⟨56220534332673462959499341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37480356221782308639666227 56220534332673462959499341)
  ·
    refine ⟨21082700374752548609812253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56220534332673462959499341 21082700374752548609812253)
    ·
      refine ⟨7906012640532205728679595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21082700374752548609812253 7906012640532205728679595)
      ·
        refine ⟨11859018960798308593019393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7906012640532205728679595 11859018960798308593019393)
        ·
          refine ⟨8894264220598731444764545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11859018960798308593019393 8894264220598731444764545)
          ·
            refine ⟨6670698165449048583573409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8894264220598731444764545 6670698165449048583573409)
            ·
              refine ⟨5003023624086786437680057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6670698165449048583573409 5003023624086786437680057)
              ·
                refine ⟨3752267718065089828260043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5003023624086786437680057 3752267718065089828260043)
                ·
                  refine ⟨5628401577097634742390065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3752267718065089828260043 5628401577097634742390065)
                  ·
                    refine ⟨4221301182823226056792549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5628401577097634742390065 4221301182823226056792549)
                    ·
                      refine ⟨791493971779354885648603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4221301182823226056792549 791493971779354885648603)
                      ·
                        rfl

theorem cell23_1541429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_1541429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541429 prefixEnd_1541429 := by exact prefixLift 1541429
  have htrace : WordTrace (prefixWord ++ tailWord_1541429) baseStart_1541429 baseEnd_1541429 := by
    simpa [prefixWord, tailWord_1541429, baseEnd_1541429] using wordTrace_append hprefix tailTrace_1541429
  have hstable : (prefixWord ++ tailWord_1541429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541429).length < 2 ^ (prefixWord ++ tailWord_1541429).sum := by decide
  have hdescent : baseEnd_1541429 < baseStart_1541429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541436 : List Nat := [2, 2, 2, 2, 1, 4, 1, 3, 1, 2, 3]
def baseStart_1541436 : Nat := 118140960795 + 1541436 * 2 ^ 59
def prefixEnd_1541436 : Nat := 4983230072969 + 3 ^ 40 * 1541436 * 2
def baseEnd_1541436 : Nat := 791497566143936358261071

theorem tailTrace_1541436 : CollatzResearch.WordTrace tailWord_1541436 prefixEnd_1541436 791497566143936358261071 := by
  unfold tailWord_1541436
  simp only [CollatzResearch.WordTrace]
  refine ⟨28110394821824051577502081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37480526429098735436669441 28110394821824051577502081)
  ·
    refine ⟨21082796116368038683126561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28110394821824051577502081 21082796116368038683126561)
    ·
      refine ⟨15812097087276029012344921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21082796116368038683126561 15812097087276029012344921)
      ·
        refine ⟨11859072815457021759258691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15812097087276029012344921 11859072815457021759258691)
        ·
          refine ⟨17788609223185532638888037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11859072815457021759258691 17788609223185532638888037)
          ·
            refine ⟨3335364229347287369791507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17788609223185532638888037 3335364229347287369791507)
            ·
              refine ⟨5003046344020931054687261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3335364229347287369791507 5003046344020931054687261)
              ·
                refine ⟨1876142379007849145507723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5003046344020931054687261 1876142379007849145507723)
                ·
                  refine ⟨2814213568511773718261585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1876142379007849145507723 2814213568511773718261585)
                  ·
                    refine ⟨2110660176383830288696189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2814213568511773718261585 2110660176383830288696189)
                    ·
                      refine ⟨791497566143936358261071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2110660176383830288696189 791497566143936358261071)
                      ·
                        rfl

theorem cell23_1541436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_1541436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541436 prefixEnd_1541436 := by exact prefixLift 1541436
  have htrace : WordTrace (prefixWord ++ tailWord_1541436) baseStart_1541436 baseEnd_1541436 := by
    simpa [prefixWord, tailWord_1541436, baseEnd_1541436] using wordTrace_append hprefix tailTrace_1541436
  have hstable : (prefixWord ++ tailWord_1541436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541436).length < 2 ^ (prefixWord ++ tailWord_1541436).sum := by decide
  have hdescent : baseEnd_1541436 < baseStart_1541436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541453 : List Nat := [1, 6, 1, 3, 1, 1, 1, 2, 1, 1, 5]
def baseStart_1541453 : Nat := 118140960795 + 1541453 * 2 ^ 59
def prefixEnd_1541453 : Nat := 4983230072969 + 3 ^ 40 * 1541453 * 2
def baseEnd_1541453 : Nat := 791506295315062791748493

theorem tailTrace_1541453 : CollatzResearch.WordTrace tailWord_1541453 prefixEnd_1541453 791506295315062791748493 := by
  unfold tailWord_1541453
  simp only [CollatzResearch.WordTrace]
  refine ⟨56221409684586515058373013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37480939789724343372248675 56221409684586515058373013)
  ·
    refine ⟨2635378578964992893361235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 56221409684586515058373013 2635378578964992893361235)
    ·
      refine ⟨3953067868447489340041853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2635378578964992893361235 3953067868447489340041853)
      ·
        refine ⟨1482400450667808502515695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3953067868447489340041853 1482400450667808502515695)
        ·
          refine ⟨2223600676001712753773543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1482400450667808502515695 2223600676001712753773543)
          ·
            refine ⟨3335401014002569130660315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2223600676001712753773543 3335401014002569130660315)
            ·
              refine ⟨5003101521003853695990473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3335401014002569130660315 5003101521003853695990473)
              ·
                refine ⟨3752326140752890271992855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5003101521003853695990473 3752326140752890271992855)
                ·
                  refine ⟨5628489211129335407989283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3752326140752890271992855 5628489211129335407989283)
                  ·
                    refine ⟨8442733816694003111983925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5628489211129335407989283 8442733816694003111983925)
                    ·
                      refine ⟨791506295315062791748493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8442733816694003111983925 791506295315062791748493)
                      ·
                        rfl

theorem cell23_1541453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_1541453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541453 prefixEnd_1541453 := by exact prefixLift 1541453
  have htrace : WordTrace (prefixWord ++ tailWord_1541453) baseStart_1541453 baseEnd_1541453 := by
    simpa [prefixWord, tailWord_1541453, baseEnd_1541453] using wordTrace_append hprefix tailTrace_1541453
  have hstable : (prefixWord ++ tailWord_1541453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541453).length < 2 ^ (prefixWord ++ tailWord_1541453).sum := by decide
  have hdescent : baseEnd_1541453 < baseStart_1541453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541466 : List Nat := [3, 1, 1, 2, 1, 2, 2, 5, 2, 1, 3]
def baseStart_1541466 : Nat := 118140960795 + 1541466 * 2 ^ 59
def prefixEnd_1541466 : Nat := 4983230072969 + 3 ^ 40 * 1541466 * 2
def baseEnd_1541466 : Nat := 791512970563571240885933

theorem tailTrace_1541466 : CollatzResearch.WordTrace tailWord_1541466 prefixEnd_1541466 791512970563571240885933 := by
  unfold tailWord_1541466
  simp only [CollatzResearch.WordTrace]
  refine ⟨14055470958384854569649063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37481255889026278852397501 14055470958384854569649063)
  ·
    refine ⟨21083206437577281854473595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14055470958384854569649063 21083206437577281854473595)
    ·
      refine ⟨31624809656365922781710393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21083206437577281854473595 31624809656365922781710393)
      ·
        refine ⟨23718607242274442086282795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31624809656365922781710393 23718607242274442086282795)
        ·
          refine ⟨35577910863411663129424193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23718607242274442086282795 35577910863411663129424193)
          ·
            refine ⟨26683433147558747347068145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35577910863411663129424193 26683433147558747347068145)
            ·
              refine ⟨20012574860669060510301109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26683433147558747347068145 20012574860669060510301109)
              ·
                refine ⟨1876178893187724422840729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20012574860669060510301109 1876178893187724422840729)
                ·
                  refine ⟨1407134169890793317130547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1876178893187724422840729 1407134169890793317130547)
                  ·
                    refine ⟨2110701254836189975695821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1407134169890793317130547 2110701254836189975695821)
                    ·
                      refine ⟨791512970563571240885933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2110701254836189975695821 791512970563571240885933)
                      ·
                        rfl

theorem cell23_1541466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_1541466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541466 prefixEnd_1541466 := by exact prefixLift 1541466
  have htrace : WordTrace (prefixWord ++ tailWord_1541466) baseStart_1541466 baseEnd_1541466 := by
    simpa [prefixWord, tailWord_1541466, baseEnd_1541466] using wordTrace_append hprefix tailTrace_1541466
  have hstable : (prefixWord ++ tailWord_1541466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541466).length < 2 ^ (prefixWord ++ tailWord_1541466).sum := by decide
  have hdescent : baseEnd_1541466 < baseStart_1541466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541559 : List Nat := [1, 1, 3, 1, 3, 2, 1, 4, 2, 5]
def baseStart_1541559 : Nat := 118140960795 + 1541559 * 2 ^ 59
def prefixEnd_1541559 : Nat := 4983230072969 + 3 ^ 40 * 1541559 * 2
def baseEnd_1541559 : Nat := 263853574754813125674335

theorem tailTrace_1541559 : CollatzResearch.WordTrace tailWord_1541559 prefixEnd_1541559 263853574754813125674335 := by
  unfold tailWord_1541559
  simp only [CollatzResearch.WordTrace]
  refine ⟨56225275822202495161731731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37483517214801663441154487 56225275822202495161731731)
  ·
    refine ⟨84337913733303742742597597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56225275822202495161731731 84337913733303742742597597)
    ·
      refine ⟨31626717649988903528474099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84337913733303742742597597 31626717649988903528474099)
      ·
        refine ⟨47440076474983355292711149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31626717649988903528474099 47440076474983355292711149)
        ·
          refine ⟨17790028678118758234766681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47440076474983355292711149 17790028678118758234766681)
          ·
            refine ⟨13342521508589068676075011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17790028678118758234766681 13342521508589068676075011)
            ·
              refine ⟨20013782262883603014112517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13342521508589068676075011 20013782262883603014112517)
              ·
                refine ⟨3752584174290675565146097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20013782262883603014112517 3752584174290675565146097)
                ·
                  refine ⟨2814438130718006673859573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3752584174290675565146097 2814438130718006673859573)
                  ·
                    refine ⟨263853574754813125674335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2814438130718006673859573 263853574754813125674335)
                    ·
                      rfl

theorem cell23_1541559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 5].length) (baseStart_1541559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541559 prefixEnd_1541559 := by exact prefixLift 1541559
  have htrace : WordTrace (prefixWord ++ tailWord_1541559) baseStart_1541559 baseEnd_1541559 := by
    simpa [prefixWord, tailWord_1541559, baseEnd_1541559] using wordTrace_append hprefix tailTrace_1541559
  have hstable : (prefixWord ++ tailWord_1541559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541559).length < 2 ^ (prefixWord ++ tailWord_1541559).sum := by decide
  have hdescent : baseEnd_1541559 < baseStart_1541559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541579 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 4]
def baseStart_1541579 : Nat := 118140960795 + 1541579 * 2 ^ 59
def prefixEnd_1541579 : Nat := 4983230072969 + 3 ^ 40 * 1541579 * 2
def baseEnd_1541579 : Nat := 791570993877529298772913

theorem tailTrace_1541579 : CollatzResearch.WordTrace tailWord_1541579 prefixEnd_1541579 791570993877529298772913 := by
  unfold tailWord_1541579
  simp only [CollatzResearch.WordTrace]
  refine ⟨56226005282130038577459791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37484003521420025718306527 56226005282130038577459791)
  ·
    refine ⟨84339007923195057866189687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56226005282130038577459791 84339007923195057866189687)
    ·
      refine ⟨126508511884792586799284531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84339007923195057866189687 126508511884792586799284531)
      ·
        refine ⟨189762767827188880198926797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126508511884792586799284531 189762767827188880198926797)
        ·
          refine ⟨71161037935195830074597549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189762767827188880198926797 71161037935195830074597549)
          ·
            refine ⟨26685389225698436277974081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71161037935195830074597549 26685389225698436277974081)
            ·
              refine ⟨20014041919273827208480561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26685389225698436277974081 20014041919273827208480561)
              ·
                refine ⟨15010531439455370406360421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20014041919273827208480561 15010531439455370406360421)
                ·
                  refine ⟨2814474644897881951192579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15010531439455370406360421 2814474644897881951192579)
                  ·
                    refine ⟨4221711967346822926788869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2814474644897881951192579 4221711967346822926788869)
                    ·
                      refine ⟨791570993877529298772913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4221711967346822926788869 791570993877529298772913)
                      ·
                        rfl

theorem cell23_1541579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 4].length) (baseStart_1541579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541579 prefixEnd_1541579 := by exact prefixLift 1541579
  have htrace : WordTrace (prefixWord ++ tailWord_1541579) baseStart_1541579 baseEnd_1541579 := by
    simpa [prefixWord, tailWord_1541579, baseEnd_1541579] using wordTrace_append hprefix tailTrace_1541579
  have hstable : (prefixWord ++ tailWord_1541579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541579).length < 2 ^ (prefixWord ++ tailWord_1541579).sum := by decide
  have hdescent : baseEnd_1541579 < baseStart_1541579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541619 : List Nat := [1, 1, 1, 2, 2, 2, 2, 6, 6]
def baseStart_1541619 : Nat := 118140960795 + 1541619 * 2 ^ 59
def prefixEnd_1541619 : Nat := 4983230072969 + 3 ^ 40 * 1541619 * 2
def baseEnd_1541619 : Nat := 87954614789301015808081

theorem tailTrace_1541619 : CollatzResearch.WordTrace tailWord_1541619 prefixEnd_1541619 87954614789301015808081 := by
  unfold tailWord_1541619
  simp only [CollatzResearch.WordTrace]
  refine ⟨56227464201985125408915911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37484976134656750272610607 56227464201985125408915911)
  ·
    refine ⟨84341196302977688113373867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56227464201985125408915911 84341196302977688113373867)
    ·
      refine ⟨126511794454466532170060801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84341196302977688113373867 126511794454466532170060801)
      ·
        refine ⟨94883845840849899127545601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126511794454466532170060801 94883845840849899127545601)
        ·
          refine ⟨71162884380637424345659201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94883845840849899127545601 71162884380637424345659201)
          ·
            refine ⟨53372163285478068259244401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71162884380637424345659201 53372163285478068259244401)
            ·
              refine ⟨40029122464108551194433301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53372163285478068259244401 40029122464108551194433301)
              ·
                refine ⟨1876365115505088337239061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40029122464108551194433301 1876365115505088337239061)
                ·
                  refine ⟨87954614789301015808081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1876365115505088337239061 87954614789301015808081)
                  ·
                    rfl

theorem cell23_1541619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 6].length) (baseStart_1541619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541619 prefixEnd_1541619 := by exact prefixLift 1541619
  have htrace : WordTrace (prefixWord ++ tailWord_1541619) baseStart_1541619 baseEnd_1541619 := by
    simpa [prefixWord, tailWord_1541619, baseEnd_1541619] using wordTrace_append hprefix tailTrace_1541619
  have hstable : (prefixWord ++ tailWord_1541619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541619).length < 2 ^ (prefixWord ++ tailWord_1541619).sum := by decide
  have hdescent : baseEnd_1541619 < baseStart_1541619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541703 : List Nat := [1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 4]
def baseStart_1541703 : Nat := 118140960795 + 1541703 * 2 ^ 59
def prefixEnd_1541703 : Nat := 4983230072969 + 3 ^ 40 * 1541703 * 2
def baseEnd_1541703 : Nat := 791634665478686813622343

theorem tailTrace_1541703 : CollatzResearch.WordTrace tailWord_1541703 prefixEnd_1541703 791634665478686813622343 := by
  unfold tailWord_1541703
  simp only [CollatzResearch.WordTrace]
  refine ⟨56230527933680807754973763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37487018622453871836649175 56230527933680807754973763)
  ·
    refine ⟨84345791900521211632460645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56230527933680807754973763 84345791900521211632460645)
    ·
      refine ⟨15814835981347727181086371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84345791900521211632460645 15814835981347727181086371)
      ·
        refine ⟨23722253972021590771629557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15814835981347727181086371 23722253972021590771629557)
        ·
          refine ⟨2223961309877024134840271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23722253972021590771629557 2223961309877024134840271)
          ·
            refine ⟨3335941964815536202260407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2223961309877024134840271 3335941964815536202260407)
            ·
              refine ⟨5003912947223304303390611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3335941964815536202260407 5003912947223304303390611)
              ·
                refine ⟨7505869420834956455085917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5003912947223304303390611 7505869420834956455085917)
                ·
                  refine ⟨2814701032813108670657219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7505869420834956455085917 2814701032813108670657219)
                  ·
                    refine ⟨4222051549219663005985829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2814701032813108670657219 4222051549219663005985829)
                    ·
                      refine ⟨791634665478686813622343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4222051549219663005985829 791634665478686813622343)
                      ·
                        rfl

theorem cell23_1541703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_1541703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541703 prefixEnd_1541703 := by exact prefixLift 1541703
  have htrace : WordTrace (prefixWord ++ tailWord_1541703) baseStart_1541703 baseEnd_1541703 := by
    simpa [prefixWord, tailWord_1541703, baseEnd_1541703] using wordTrace_append hprefix tailTrace_1541703
  have hstable : (prefixWord ++ tailWord_1541703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541703).length < 2 ^ (prefixWord ++ tailWord_1541703).sum := by decide
  have hdescent : baseEnd_1541703 < baseStart_1541703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541750 : List Nat := [5, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4]
def baseStart_1541750 : Nat := 118140960795 + 1541750 * 2 ^ 59
def prefixEnd_1541750 : Nat := 4983230072969 + 3 ^ 40 * 1541750 * 2
def baseEnd_1541750 : Nat := 791658799069448129734627

theorem tailTrace_1541750 : CollatzResearch.WordTrace tailWord_1541750 prefixEnd_1541750 791658799069448129734627 := by
  unfold tailWord_1541750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3514515135281908423870919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37488161443007023187956469 3514515135281908423870919)
  ·
    refine ⟨5271772702922862635806379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3514515135281908423870919 5271772702922862635806379)
    ·
      refine ⟨7907659054384293953709569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5271772702922862635806379 7907659054384293953709569)
      ·
        refine ⟨5930744290788220465282177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7907659054384293953709569 5930744290788220465282177)
        ·
          refine ⟨4448058218091165348961633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5930744290788220465282177 4448058218091165348961633)
          ·
            refine ⟨3336043663568374011721225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4448058218091165348961633 3336043663568374011721225)
            ·
              refine ⟨2502032747676280508790919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3336043663568374011721225 2502032747676280508790919)
              ·
                refine ⟨3753049121514420763186379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2502032747676280508790919 3753049121514420763186379)
                ·
                  refine ⟨5629573682271631144779569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3753049121514420763186379 5629573682271631144779569)
                  ·
                    refine ⟨4222180261703723358584677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5629573682271631144779569 4222180261703723358584677)
                    ·
                      refine ⟨791658799069448129734627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4222180261703723358584677 791658799069448129734627)
                      ·
                        rfl

theorem cell23_1541750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_1541750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541750 prefixEnd_1541750 := by exact prefixLift 1541750
  have htrace : WordTrace (prefixWord ++ tailWord_1541750) baseStart_1541750 baseEnd_1541750 := by
    simpa [prefixWord, tailWord_1541750, baseEnd_1541750] using wordTrace_append hprefix tailTrace_1541750
  have hstable : (prefixWord ++ tailWord_1541750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541750).length < 2 ^ (prefixWord ++ tailWord_1541750).sum := by decide
  have hdescent : baseEnd_1541750 < baseStart_1541750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541753 : List Nat := [1, 2, 1, 3, 3, 1, 4, 1, 1, 3, 3]
def baseStart_1541753 : Nat := 118140960795 + 1541753 * 2 ^ 59
def prefixEnd_1541753 : Nat := 4983230072969 + 3 ^ 40 * 1541753 * 2
def baseEnd_1541753 : Nat := 791660339511411617997113

theorem tailTrace_1541753 : CollatzResearch.WordTrace tailWord_1541753 prefixEnd_1541753 791660339511411617997113 := by
  unfold tailWord_1541753
  simp only [CollatzResearch.WordTrace]
  refine ⟨56232351583499666294293913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37488234388999777529529275 56232351583499666294293913)
  ·
    refine ⟨42174263687624749720720435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56232351583499666294293913 42174263687624749720720435)
    ·
      refine ⟨63261395531437124581080653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42174263687624749720720435 63261395531437124581080653)
      ·
        refine ⟨23723023324288921717905245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63261395531437124581080653 23723023324288921717905245)
        ·
          refine ⟨8896133746608345644214467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23723023324288921717905245 8896133746608345644214467)
          ·
            refine ⟨13344200619912518466321701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8896133746608345644214467 13344200619912518466321701)
            ·
              refine ⟨2502037616233597212435319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13344200619912518466321701 2502037616233597212435319)
              ·
                refine ⟨3753056424350395818652979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2502037616233597212435319 3753056424350395818652979)
                ·
                  refine ⟨5629584636525593727979469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3753056424350395818652979 5629584636525593727979469)
                  ·
                    refine ⟨2111094238697097647992301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5629584636525593727979469 2111094238697097647992301)
                    ·
                      refine ⟨791660339511411617997113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2111094238697097647992301 791660339511411617997113)
                      ·
                        rfl

theorem cell23_1541753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_1541753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541753 prefixEnd_1541753 := by exact prefixLift 1541753
  have htrace : WordTrace (prefixWord ++ tailWord_1541753) baseStart_1541753 baseEnd_1541753 := by
    simpa [prefixWord, tailWord_1541753, baseEnd_1541753] using wordTrace_append hprefix tailTrace_1541753
  have hstable : (prefixWord ++ tailWord_1541753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541753).length < 2 ^ (prefixWord ++ tailWord_1541753).sum := by decide
  have hdescent : baseEnd_1541753 < baseStart_1541753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541810 : List Nat := [3, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2]
def baseStart_1541810 : Nat := 118140960795 + 1541810 * 2 ^ 59
def prefixEnd_1541810 : Nat := 4983230072969 + 3 ^ 40 * 1541810 * 2
def baseEnd_1541810 : Nat := 791689607908717894984351

theorem tailTrace_1541810 : CollatzResearch.WordTrace tailWord_1541810 prefixEnd_1541810 791689607908717894984351 := by
  unfold tailWord_1541810
  simp only [CollatzResearch.WordTrace]
  refine ⟨14058607636073291257279721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37489620362862110019412589 14058607636073291257279721)
  ·
    refine ⟨10543955727054968442959791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14058607636073291257279721 10543955727054968442959791)
    ·
      refine ⟨15815933590582452664439687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10543955727054968442959791 15815933590582452664439687)
      ·
        refine ⟨23723900385873678996659531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15815933590582452664439687 23723900385873678996659531)
        ·
          refine ⟨35585850578810518494989297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23723900385873678996659531 35585850578810518494989297)
          ·
            refine ⟨26689387934107888871241973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35585850578810518494989297 26689387934107888871241973)
            ·
              refine ⟨2502130118822614581678935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26689387934107888871241973 2502130118822614581678935)
              ·
                refine ⟨3753195178233921872518403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2502130118822614581678935 3753195178233921872518403)
                ·
                  refine ⟨5629792767350882808777605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3753195178233921872518403 5629792767350882808777605)
                  ·
                    refine ⟨1055586143878290526645801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5629792767350882808777605 1055586143878290526645801)
                    ·
                      refine ⟨791689607908717894984351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1055586143878290526645801 791689607908717894984351)
                      ·
                        rfl

theorem cell23_1541810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2].length) (baseStart_1541810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541810 prefixEnd_1541810 := by exact prefixLift 1541810
  have htrace : WordTrace (prefixWord ++ tailWord_1541810) baseStart_1541810 baseEnd_1541810 := by
    simpa [prefixWord, tailWord_1541810, baseEnd_1541810] using wordTrace_append hprefix tailTrace_1541810
  have hstable : (prefixWord ++ tailWord_1541810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541810).length < 2 ^ (prefixWord ++ tailWord_1541810).sum := by decide
  have hdescent : baseEnd_1541810 < baseStart_1541810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541814 : List Nat := [5, 1, 3, 1, 1, 1, 1, 4, 1, 3, 2]
def baseStart_1541814 : Nat := 118140960795 + 1541814 * 2 ^ 59
def prefixEnd_1541814 : Nat := 4983230072969 + 3 ^ 40 * 1541814 * 2
def baseEnd_1541814 : Nat := 791691661831335879334333

theorem tailTrace_1541814 : CollatzResearch.WordTrace tailWord_1541814 prefixEnd_1541814 791691661831335879334333 := by
  unfold tailWord_1541814
  simp only [CollatzResearch.WordTrace]
  refine ⟨3514661027267417107016531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37489717624185782474842997 3514661027267417107016531)
  ·
    refine ⟨5271991540901125660524797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3514661027267417107016531 5271991540901125660524797)
    ·
      refine ⟨1976996827837922122696799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5271991540901125660524797 1976996827837922122696799)
      ·
        refine ⟨2965495241756883184045199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1976996827837922122696799 2965495241756883184045199)
        ·
          refine ⟨4448242862635324776067799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2965495241756883184045199 4448242862635324776067799)
          ·
            refine ⟨6672364293952987164101699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4448242862635324776067799 6672364293952987164101699)
            ·
              refine ⟨10008546440929480746152549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6672364293952987164101699 10008546440929480746152549)
              ·
                refine ⟨1876602457674277639903603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10008546440929480746152549 1876602457674277639903603)
                ·
                  refine ⟨2814903686511416459855405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1876602457674277639903603 2814903686511416459855405)
                  ·
                    refine ⟨1055588882441781172445777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2814903686511416459855405 1055588882441781172445777)
                    ·
                      refine ⟨791691661831335879334333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1055588882441781172445777 791691661831335879334333)
                      ·
                        rfl

theorem cell23_1541814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_1541814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541814 prefixEnd_1541814 := by exact prefixLift 1541814
  have htrace : WordTrace (prefixWord ++ tailWord_1541814) baseStart_1541814 baseEnd_1541814 := by
    simpa [prefixWord, tailWord_1541814, baseEnd_1541814] using wordTrace_append hprefix tailTrace_1541814
  have hstable : (prefixWord ++ tailWord_1541814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541814).length < 2 ^ (prefixWord ++ tailWord_1541814).sum := by decide
  have hdescent : baseEnd_1541814 < baseStart_1541814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541856 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 7]
def baseStart_1541856 : Nat := 118140960795 + 1541856 * 2 ^ 59
def prefixEnd_1541856 : Nat := 4983230072969 + 3 ^ 40 * 1541856 * 2
def baseEnd_1541856 : Nat := 791713228018824715009139

theorem tailTrace_1541856 : CollatzResearch.WordTrace tailWord_1541856 prefixEnd_1541856 791713228018824715009139 := by
  unfold tailWord_1541856
  simp only [CollatzResearch.WordTrace]
  refine ⟨28118054151063257442646711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37490738868084343256862281 28118054151063257442646711)
  ·
    refine ⟨42177081226594886163970067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28118054151063257442646711 42177081226594886163970067)
    ·
      refine ⟨63265621839892329245955101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42177081226594886163970067 63265621839892329245955101)
      ·
        refine ⟨23724608189959623467233163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63265621839892329245955101 23724608189959623467233163)
        ·
          refine ⟨35586912284939435200849745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23724608189959623467233163 35586912284939435200849745)
          ·
            refine ⟨26690184213704576400637309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35586912284939435200849745 26690184213704576400637309)
            ·
              refine ⟨10008819080139216150238991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26690184213704576400637309 10008819080139216150238991)
              ·
                refine ⟨15013228620208824225358487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10008819080139216150238991 15013228620208824225358487)
                ·
                  refine ⟨22519842930313236338037731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15013228620208824225358487 22519842930313236338037731)
                  ·
                    refine ⟨33779764395469854507056597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22519842930313236338037731 33779764395469854507056597)
                    ·
                      refine ⟨791713228018824715009139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 33779764395469854507056597 791713228018824715009139)
                      ·
                        rfl

theorem cell23_1541856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_1541856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541856 prefixEnd_1541856 := by exact prefixLift 1541856
  have htrace : WordTrace (prefixWord ++ tailWord_1541856) baseStart_1541856 baseEnd_1541856 := by
    simpa [prefixWord, tailWord_1541856, baseEnd_1541856] using wordTrace_append hprefix tailTrace_1541856
  have hstable : (prefixWord ++ tailWord_1541856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541856).length < 2 ^ (prefixWord ++ tailWord_1541856).sum := by decide
  have hdescent : baseEnd_1541856 < baseStart_1541856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541883 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 3, 6, 2]
def baseStart_1541883 : Nat := 118140960795 + 1541883 * 2 ^ 59
def prefixEnd_1541883 : Nat := 4983230072969 + 3 ^ 40 * 1541883 * 2
def baseEnd_1541883 : Nat := 791727091996496109371515

theorem tailTrace_1541883 : CollatzResearch.WordTrace tailWord_1541883 prefixEnd_1541883 791727091996496109371515 := by
  unfold tailWord_1541883
  simp only [CollatzResearch.WordTrace]
  refine ⟨56237093073028698496526303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37491395382019132331017535 56237093073028698496526303)
  ·
    refine ⟨84355639609543047744789455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56237093073028698496526303 84355639609543047744789455)
    ·
      refine ⟨126533459414314571617184183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84355639609543047744789455 126533459414314571617184183)
      ·
        refine ⟨189800189121471857425776275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126533459414314571617184183 189800189121471857425776275)
        ·
          refine ⟨284700283682207786138664413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189800189121471857425776275 284700283682207786138664413)
          ·
            refine ⟨106762606380827919801999155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 284700283682207786138664413 106762606380827919801999155)
            ·
              refine ⟨160143909571241879702998733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106762606380827919801999155 160143909571241879702998733)
              ·
                refine ⟨60053966089215704888624525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160143909571241879702998733 60053966089215704888624525)
                ·
                  refine ⟨22520237283455889333234197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60053966089215704888624525 22520237283455889333234197)
                  ·
                    refine ⟨1055636122661994812495353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22520237283455889333234197 1055636122661994812495353)
                    ·
                      refine ⟨791727091996496109371515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1055636122661994812495353 791727091996496109371515)
                      ·
                        rfl

theorem cell23_1541883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 6, 2].length) (baseStart_1541883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541883 prefixEnd_1541883 := by exact prefixLift 1541883
  have htrace : WordTrace (prefixWord ++ tailWord_1541883) baseStart_1541883 baseEnd_1541883 := by
    simpa [prefixWord, tailWord_1541883, baseEnd_1541883] using wordTrace_append hprefix tailTrace_1541883
  have hstable : (prefixWord ++ tailWord_1541883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541883).length < 2 ^ (prefixWord ++ tailWord_1541883).sum := by decide
  have hdescent : baseEnd_1541883 < baseStart_1541883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541903 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 4, 2, 3]
def baseStart_1541903 : Nat := 118140960795 + 1541903 * 2 ^ 59
def prefixEnd_1541903 : Nat := 4983230072969 + 3 ^ 40 * 1541903 * 2
def baseEnd_1541903 : Nat := 791737361609586031121423

theorem tailTrace_1541903 : CollatzResearch.WordTrace tailWord_1541903 prefixEnd_1541903 791737361609586031121423 := by
  unfold tailWord_1541903
  simp only [CollatzResearch.WordTrace]
  refine ⟨56237822532956241912254363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37491881688637494608169575 56237822532956241912254363)
  ·
    refine ⟨84356733799434362868381545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56237822532956241912254363 84356733799434362868381545)
    ·
      refine ⟨63267550349575772151286159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84356733799434362868381545 63267550349575772151286159)
      ·
        refine ⟨94901325524363658226929239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63267550349575772151286159 94901325524363658226929239)
        ·
          refine ⟨142351988286545487340393859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94901325524363658226929239 142351988286545487340393859)
          ·
            refine ⟨213527982429818231010590789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142351988286545487340393859 213527982429818231010590789)
            ·
              refine ⟨40036496705590918314485773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 213527982429818231010590789 40036496705590918314485773)
              ·
                refine ⟨15013686264596594367932165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40036496705590918314485773 15013686264596594367932165)
                ·
                  refine ⟨2815066174611861443987281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15013686264596594367932165 2815066174611861443987281)
                  ·
                    refine ⟨2111299630958896082990461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2815066174611861443987281 2111299630958896082990461)
                    ·
                      refine ⟨791737361609586031121423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2111299630958896082990461 791737361609586031121423)
                      ·
                        rfl

theorem cell23_1541903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 2, 3].length) (baseStart_1541903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541903 prefixEnd_1541903 := by exact prefixLift 1541903
  have htrace : WordTrace (prefixWord ++ tailWord_1541903) baseStart_1541903 baseEnd_1541903 := by
    simpa [prefixWord, tailWord_1541903, baseEnd_1541903] using wordTrace_append hprefix tailTrace_1541903
  have hstable : (prefixWord ++ tailWord_1541903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541903).length < 2 ^ (prefixWord ++ tailWord_1541903).sum := by decide
  have hdescent : baseEnd_1541903 < baseStart_1541903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541923 : List Nat := [1, 1, 1, 4, 2, 1, 4, 3, 6]
def baseStart_1541923 : Nat := 118140960795 + 1541923 * 2 ^ 59
def prefixEnd_1541923 : Nat := 4983230072969 + 3 ^ 40 * 1541923 * 2
def baseEnd_1541923 : Nat := 87971959024741772541259

theorem tailTrace_1541923 : CollatzResearch.WordTrace tailWord_1541923 prefixEnd_1541923 87971959024741772541259 := by
  unfold tailWord_1541923
  simp only [CollatzResearch.WordTrace]
  refine ⟨56238551992883785327982423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37492367995255856885321615 56238551992883785327982423)
  ·
    refine ⟨84357827989325677991973635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56238551992883785327982423 84357827989325677991973635)
    ·
      refine ⟨126536741983988516987960453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84357827989325677991973635 126536741983988516987960453)
      ·
        refine ⟨23725639121997846935242585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126536741983988516987960453 23725639121997846935242585)
        ·
          refine ⟨17794229341498385201431939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23725639121997846935242585 17794229341498385201431939)
          ·
            refine ⟨26691344012247577802147909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17794229341498385201431939 26691344012247577802147909)
            ·
              refine ⟨5004627002296420837902733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26691344012247577802147909 5004627002296420837902733)
              ·
                refine ⟨1876735125861157814213525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5004627002296420837902733 1876735125861157814213525)
                ·
                  refine ⟨87971959024741772541259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1876735125861157814213525 87971959024741772541259)
                  ·
                    rfl

theorem cell23_1541923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 6].length) (baseStart_1541923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541923 prefixEnd_1541923 := by exact prefixLift 1541923
  have htrace : WordTrace (prefixWord ++ tailWord_1541923) baseStart_1541923 baseEnd_1541923 := by
    simpa [prefixWord, tailWord_1541923, baseEnd_1541923] using wordTrace_append hprefix tailTrace_1541923
  have hstable : (prefixWord ++ tailWord_1541923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541923).length < 2 ^ (prefixWord ++ tailWord_1541923).sum := by decide
  have hdescent : baseEnd_1541923 < baseStart_1541923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541934 : List Nat := [4, 1, 3, 2, 2, 2, 1, 1, 2, 1, 4]
def baseStart_1541934 : Nat := 118140960795 + 1541934 * 2 ^ 59
def prefixEnd_1541934 : Nat := 4983230072969 + 3 ^ 40 * 1541934 * 2
def baseEnd_1541934 : Nat := 791753279509875409833781

theorem tailTrace_1541934 : CollatzResearch.WordTrace tailWord_1541934 prefixEnd_1541934 791753279509875409833781 := by
  unfold tailWord_1541934
  simp only [CollatzResearch.WordTrace]
  refine ⟨7029869149480491775829107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37492635463895956137755237 7029869149480491775829107)
  ·
    refine ⟨10544803724220737663743661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7029869149480491775829107 10544803724220737663743661)
    ·
      refine ⟨3954301396582776623903873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10544803724220737663743661 3954301396582776623903873)
      ·
        refine ⟨2965726047437082467927905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3954301396582776623903873 2965726047437082467927905)
        ·
          refine ⟨2224294535577811850945929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2965726047437082467927905 2224294535577811850945929)
          ·
            refine ⟨1668220901683358888209447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2224294535577811850945929 1668220901683358888209447)
            ·
              refine ⟨2502331352525038332314171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1668220901683358888209447 2502331352525038332314171)
              ·
                refine ⟨3753497028787557498471257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2502331352525038332314171 3753497028787557498471257)
                ·
                  refine ⟨2815122771590668123853443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3753497028787557498471257 2815122771590668123853443)
                  ·
                    refine ⟨4222684157386002185780165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2815122771590668123853443 4222684157386002185780165)
                    ·
                      refine ⟨791753279509875409833781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4222684157386002185780165 791753279509875409833781)
                      ·
                        rfl

theorem cell23_1541934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_1541934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541934 prefixEnd_1541934 := by exact prefixLift 1541934
  have htrace : WordTrace (prefixWord ++ tailWord_1541934) baseStart_1541934 baseEnd_1541934 := by
    simpa [prefixWord, tailWord_1541934, baseEnd_1541934] using wordTrace_append hprefix tailTrace_1541934
  have hstable : (prefixWord ++ tailWord_1541934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541934).length < 2 ^ (prefixWord ++ tailWord_1541934).sum := by decide
  have hdescent : baseEnd_1541934 < baseStart_1541934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541937 : List Nat := [1, 2, 2, 3, 2, 4, 1, 1, 2, 2, 3]
def baseStart_1541937 : Nat := 118140960795 + 1541937 * 2 ^ 59
def prefixEnd_1541937 : Nat := 4983230072969 + 3 ^ 40 * 1541937 * 2
def baseEnd_1541937 : Nat := 791754819951838898096267

theorem tailTrace_1541937 : CollatzResearch.WordTrace tailWord_1541937 prefixEnd_1541937 791754819951838898096267 := by
  unfold tailWord_1541937
  simp only [CollatzResearch.WordTrace]
  refine ⟨56239062614833065718992065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37492708409888710479328043 56239062614833065718992065)
  ·
    refine ⟨42179296961124799289244049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56239062614833065718992065 42179296961124799289244049)
    ·
      refine ⟨31634472720843599466933037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42179296961124799289244049 31634472720843599466933037)
      ·
        refine ⟨11862927270316349800099889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31634472720843599466933037 11862927270316349800099889)
        ·
          refine ⟨8897195452737262350074917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11862927270316349800099889 8897195452737262350074917)
          ·
            refine ⟨1668224147388236690639047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8897195452737262350074917 1668224147388236690639047)
            ·
              refine ⟨2502336221082355035958571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1668224147388236690639047 2502336221082355035958571)
              ·
                refine ⟨3753504331623532553937857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2502336221082355035958571 3753504331623532553937857)
                ·
                  refine ⟨2815128248717649415453393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3753504331623532553937857 2815128248717649415453393)
                  ·
                    refine ⟨2111346186538237061590045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2815128248717649415453393 2111346186538237061590045)
                    ·
                      refine ⟨791754819951838898096267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2111346186538237061590045 791754819951838898096267)
                      ·
                        rfl

theorem cell23_1541937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_1541937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541937 prefixEnd_1541937 := by exact prefixLift 1541937
  have htrace : WordTrace (prefixWord ++ tailWord_1541937) baseStart_1541937 baseEnd_1541937 := by
    simpa [prefixWord, tailWord_1541937, baseEnd_1541937] using wordTrace_append hprefix tailTrace_1541937
  have hstable : (prefixWord ++ tailWord_1541937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541937).length < 2 ^ (prefixWord ++ tailWord_1541937).sum := by decide
  have hdescent : baseEnd_1541937 < baseStart_1541937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541987 : List Nat := [1, 1, 1, 5, 4, 1, 2, 2, 1, 5]
def baseStart_1541987 : Nat := 118140960795 + 1541987 * 2 ^ 59
def prefixEnd_1541987 : Nat := 4983230072969 + 3 ^ 40 * 1541987 * 2
def baseEnd_1541987 : Nat := 263926831328187900823679

theorem tailTrace_1541987 : CollatzResearch.WordTrace tailWord_1541987 prefixEnd_1541987 263926831328187900823679 := by
  unfold tailWord_1541987
  simp only [CollatzResearch.WordTrace]
  refine ⟨56240886264651924258312215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37493924176434616172208143 56240886264651924258312215)
  ·
    refine ⟨84361329396977886387468323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56240886264651924258312215 84361329396977886387468323)
    ·
      refine ⟨126541994095466829581202485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84361329396977886387468323 126541994095466829581202485)
      ·
        refine ⟨11863311946450015273237733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126541994095466829581202485 11863311946450015273237733)
        ·
          refine ⟨2224370989959377863732075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11863311946450015273237733 2224370989959377863732075)
          ·
            refine ⟨3336556484939066795598113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2224370989959377863732075 3336556484939066795598113)
            ·
              refine ⟨2502417363704300096698585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3336556484939066795598113 2502417363704300096698585)
              ·
                refine ⟨1876813022778225072523939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2502417363704300096698585 1876813022778225072523939)
                ·
                  refine ⟨2815219534167337608785909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1876813022778225072523939 2815219534167337608785909)
                  ·
                    refine ⟨263926831328187900823679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2815219534167337608785909 263926831328187900823679)
                    ·
                      rfl

theorem cell23_1541987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 5].length) (baseStart_1541987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541987 prefixEnd_1541987 := by exact prefixLift 1541987
  have htrace : WordTrace (prefixWord ++ tailWord_1541987) baseStart_1541987 baseEnd_1541987 := by
    simpa [prefixWord, tailWord_1541987, baseEnd_1541987] using wordTrace_append hprefix tailTrace_1541987
  have hstable : (prefixWord ++ tailWord_1541987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541987).length < 2 ^ (prefixWord ++ tailWord_1541987).sum := by decide
  have hdescent : baseEnd_1541987 < baseStart_1541987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541993 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 2, 6, 3]
def baseStart_1541993 : Nat := 118140960795 + 1541993 * 2 ^ 59
def prefixEnd_1541993 : Nat := 4983230072969 + 3 ^ 40 * 1541993 * 2
def baseEnd_1541993 : Nat := 791783574868490678996009

theorem tailTrace_1541993 : CollatzResearch.WordTrace tailWord_1541993 prefixEnd_1541993 791783574868490678996009 := by
  unfold tailWord_1541993
  simp only [CollatzResearch.WordTrace]
  refine ⟨56241105102630187283030633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37494070068420124855353755 56241105102630187283030633)
  ·
    refine ⟨42180828826972640462272975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56241105102630187283030633 42180828826972640462272975)
    ·
      refine ⟨63271243240458960693409463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42180828826972640462272975 63271243240458960693409463)
      ·
        refine ⟨94906864860688441040114195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63271243240458960693409463 94906864860688441040114195)
        ·
          refine ⟨142360297291032661560171293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94906864860688441040114195 142360297291032661560171293)
          ·
            refine ⟨53385111484137248085064235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142360297291032661560171293 53385111484137248085064235)
            ·
              refine ⟨80077667226205872127596353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53385111484137248085064235 80077667226205872127596353)
              ·
                refine ⟨60058250419654404095697265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80077667226205872127596353 60058250419654404095697265)
                ·
                  refine ⟨45043687814740803071772949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60058250419654404095697265 45043687814740803071772949)
                  ·
                    refine ⟨2111422866315975143989357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45043687814740803071772949 2111422866315975143989357)
                    ·
                      refine ⟨791783574868490678996009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2111422866315975143989357 791783574868490678996009)
                      ·
                        rfl

theorem cell23_1541993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 6, 3].length) (baseStart_1541993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1541993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1541993 prefixEnd_1541993 := by exact prefixLift 1541993
  have htrace : WordTrace (prefixWord ++ tailWord_1541993) baseStart_1541993 baseEnd_1541993 := by
    simpa [prefixWord, tailWord_1541993, baseEnd_1541993] using wordTrace_append hprefix tailTrace_1541993
  have hstable : (prefixWord ++ tailWord_1541993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541993).length < 2 ^ (prefixWord ++ tailWord_1541993).sum := by decide
  have hdescent : baseEnd_1541993 < baseStart_1541993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542003 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 4]
def baseStart_1542003 : Nat := 118140960795 + 1542003 * 2 ^ 59
def prefixEnd_1542003 : Nat := 4983230072969 + 3 ^ 40 * 1542003 * 2
def baseEnd_1542003 : Nat := 791788709675035639870963

theorem tailTrace_1542003 : CollatzResearch.WordTrace tailWord_1542003 prefixEnd_1542003 791788709675035639870963 := by
  unfold tailWord_1542003
  simp only [CollatzResearch.WordTrace]
  refine ⟨56241469832593958990894663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37494313221729305993929775 56241469832593958990894663)
  ·
    refine ⟨84362204748890938486341995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56241469832593958990894663 84362204748890938486341995)
    ·
      refine ⟨126543307123336407729512993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84362204748890938486341995 126543307123336407729512993)
      ·
        refine ⟨94907480342502305797134745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126543307123336407729512993 94907480342502305797134745)
        ·
          refine ⟨71180610256876729347851059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94907480342502305797134745 71180610256876729347851059)
          ·
            refine ⟨106770915385315094021776589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71180610256876729347851059 106770915385315094021776589)
            ·
              refine ⟨40039093269493160258166221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106770915385315094021776589 40039093269493160258166221)
              ·
                refine ⟨15014659976059935096812333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40039093269493160258166221 15014659976059935096812333)
                ·
                  refine ⟨5630497491022475661304625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15014659976059935096812333 5630497491022475661304625)
                  ·
                    refine ⟨4222873118266856745978469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5630497491022475661304625 4222873118266856745978469)
                    ·
                      refine ⟨791788709675035639870963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4222873118266856745978469 791788709675035639870963)
                      ·
                        rfl

theorem cell23_1542003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 4].length) (baseStart_1542003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542003 prefixEnd_1542003 := by exact prefixLift 1542003
  have htrace : WordTrace (prefixWord ++ tailWord_1542003) baseStart_1542003 baseEnd_1542003 := by
    simpa [prefixWord, tailWord_1542003, baseEnd_1542003] using wordTrace_append hprefix tailTrace_1542003
  have hstable : (prefixWord ++ tailWord_1542003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542003).length < 2 ^ (prefixWord ++ tailWord_1542003).sum := by decide
  have hdescent : baseEnd_1542003 < baseStart_1542003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542034 : List Nat := [3, 2, 3, 2, 1, 2, 1, 3, 2, 4]
def baseStart_1542034 : Nat := 118140960795 + 1542034 * 2 ^ 59
def prefixEnd_1542034 : Nat := 4983230072969 + 3 ^ 40 * 1542034 * 2
def baseEnd_1542034 : Nat := 263934875858441672861107

theorem tailTrace_1542034 : CollatzResearch.WordTrace tailWord_1542034 prefixEnd_1542034 263934875858441672861107 := by
  unfold tailWord_1542034
  simp only [CollatzResearch.WordTrace]
  refine ⟨14060650123870412821318289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37495066996987767523515437 14060650123870412821318289)
  ·
    refine ⟨10545487592902809615988717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14060650123870412821318289 10545487592902809615988717)
    ·
      refine ⟨3954557847338553605995769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10545487592902809615988717 3954557847338553605995769)
      ·
        refine ⟨2965918385503915204496827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3954557847338553605995769 2965918385503915204496827)
        ·
          refine ⟨4448877578255872806745241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2965918385503915204496827 4448877578255872806745241)
          ·
            refine ⟨3336658183691904605058931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4448877578255872806745241 3336658183691904605058931)
            ·
              refine ⟨5004987275537856907588397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3336658183691904605058931 5004987275537856907588397)
              ·
                refine ⟨1876870228326696340345649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5004987275537856907588397 1876870228326696340345649)
                ·
                  refine ⟨1407652671245022255259237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1876870228326696340345649 1407652671245022255259237)
                  ·
                    refine ⟨263934875858441672861107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1407652671245022255259237 263934875858441672861107)
                    ·
                      rfl

theorem cell23_1542034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_1542034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542034 prefixEnd_1542034 := by exact prefixLift 1542034
  have htrace : WordTrace (prefixWord ++ tailWord_1542034) baseStart_1542034 baseEnd_1542034 := by
    simpa [prefixWord, tailWord_1542034, baseEnd_1542034] using wordTrace_append hprefix tailTrace_1542034
  have hstable : (prefixWord ++ tailWord_1542034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542034).length < 2 ^ (prefixWord ++ tailWord_1542034).sum := by decide
  have hdescent : baseEnd_1542034 < baseStart_1542034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542038 : List Nat := [5, 3, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_1542038 : Nat := 118140960795 + 1542038 * 2 ^ 59
def prefixEnd_1542038 : Nat := 4983230072969 + 3 ^ 40 * 1542038 * 2
def baseEnd_1542038 : Nat := 263935560499314334311101

theorem tailTrace_1542038 : CollatzResearch.WordTrace tailWord_1542038 prefixEnd_1542038 263935560499314334311101 := by
  unfold tailWord_1542038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3515171649216697498026173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37495164258311439978945845 3515171649216697498026173)
  ·
    refine ⟨1318189368456261561759815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3515171649216697498026173 1318189368456261561759815)
    ·
      refine ⟨1977284052684392342639723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1318189368456261561759815 1977284052684392342639723)
      ·
        refine ⟨2965926079026588513959585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1977284052684392342639723 2965926079026588513959585)
        ·
          refine ⟨2224444559269941385469689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2965926079026588513959585 2224444559269941385469689)
          ·
            refine ⟨1668333419452456039102267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2224444559269941385469689 1668333419452456039102267)
            ·
              refine ⟨2502500129178684058653401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1668333419452456039102267 2502500129178684058653401)
              ·
                refine ⟨1876875096884013043990051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2502500129178684058653401 1876875096884013043990051)
                ·
                  refine ⟨2815312645326019565985077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1876875096884013043990051 2815312645326019565985077)
                  ·
                    refine ⟨263935560499314334311101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2815312645326019565985077 263935560499314334311101)
                    ·
                      rfl

theorem cell23_1542038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_1542038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542038 prefixEnd_1542038 := by exact prefixLift 1542038
  have htrace : WordTrace (prefixWord ++ tailWord_1542038) baseStart_1542038 baseEnd_1542038 := by
    simpa [prefixWord, tailWord_1542038, baseEnd_1542038] using wordTrace_append hprefix tailTrace_1542038
  have hstable : (prefixWord ++ tailWord_1542038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542038).length < 2 ^ (prefixWord ++ tailWord_1542038).sum := by decide
  have hdescent : baseEnd_1542038 < baseStart_1542038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542044 : List Nat := [2, 2, 3, 3, 1, 1, 3, 2, 1, 2, 3]
def baseStart_1542044 : Nat := 118140960795 + 1542044 * 2 ^ 59
def prefixEnd_1542044 : Nat := 4983230072969 + 3 ^ 40 * 1542044 * 2
def baseEnd_1542044 : Nat := 791809762381869979458275

theorem tailTrace_1542044 : CollatzResearch.WordTrace tailWord_1542044 prefixEnd_1542044 791809762381869979458275 := by
  unfold tailWord_1542044
  simp only [CollatzResearch.WordTrace]
  refine ⟨28121482612722711496568593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37495310150296948662091457 28121482612722711496568593)
  ·
    refine ⟨21091111959542033622426445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28121482612722711496568593 21091111959542033622426445)
    ·
      refine ⟨7909166984828262608409917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21091111959542033622426445 7909166984828262608409917)
      ·
        refine ⟨2965937619310598478153719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7909166984828262608409917 2965937619310598478153719)
        ·
          refine ⟨4448906428965897717230579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2965937619310598478153719 4448906428965897717230579)
          ·
            refine ⟨6673359643448846575845869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4448906428965897717230579 6673359643448846575845869)
            ·
              refine ⟨2502509866293317465942201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6673359643448846575845869 2502509866293317465942201)
              ·
                refine ⟨1876882399719988099456651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2502509866293317465942201 1876882399719988099456651)
                ·
                  refine ⟨2815323599579982149184977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1876882399719988099456651 2815323599579982149184977)
                  ·
                    refine ⟨2111492699684986611888733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2815323599579982149184977 2111492699684986611888733)
                    ·
                      refine ⟨791809762381869979458275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2111492699684986611888733 791809762381869979458275)
                      ·
                        rfl

theorem cell23_1542044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_1542044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542044 prefixEnd_1542044 := by exact prefixLift 1542044
  have htrace : WordTrace (prefixWord ++ tailWord_1542044) baseStart_1542044 baseEnd_1542044 := by
    simpa [prefixWord, tailWord_1542044, baseEnd_1542044] using wordTrace_append hprefix tailTrace_1542044
  have hstable : (prefixWord ++ tailWord_1542044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542044).length < 2 ^ (prefixWord ++ tailWord_1542044).sum := by decide
  have hdescent : baseEnd_1542044 < baseStart_1542044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542053 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 1, 4, 5]
def baseStart_1542053 : Nat := 118140960795 + 1542053 * 2 ^ 59
def prefixEnd_1542053 : Nat := 4983230072969 + 3 ^ 40 * 1542053 * 2
def baseEnd_1542053 : Nat := 791814383707760444245733

theorem tailTrace_1542053 : CollatzResearch.WordTrace tailWord_1542053 prefixEnd_1542053 791814383707760444245733 := by
  unfold tailWord_1542053
  simp only [CollatzResearch.WordTrace]
  refine ⟨56243293482412817530214813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37495528988275211686809875 56243293482412817530214813)
  ·
    refine ⟨21091235055904806573830555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56243293482412817530214813 21091235055904806573830555)
    ·
      refine ⟨31636852583857209860745833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21091235055904806573830555 31636852583857209860745833)
      ·
        refine ⟨23727639437892907395559375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31636852583857209860745833 23727639437892907395559375)
        ·
          refine ⟨35591459156839361093339063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23727639437892907395559375 35591459156839361093339063)
          ·
            refine ⟨53387188735259041640008595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35591459156839361093339063 53387188735259041640008595)
            ·
              refine ⟨80080783102888562460012893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53387188735259041640008595 80080783102888562460012893)
              ·
                refine ⟨30030293663583210922504835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80080783102888562460012893 30030293663583210922504835)
                ·
                  refine ⟨45045440495374816383757253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30030293663583210922504835 45045440495374816383757253)
                  ·
                    refine ⟨8446020092882778071954485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45045440495374816383757253 8446020092882778071954485)
                    ·
                      refine ⟨791814383707760444245733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8446020092882778071954485 791814383707760444245733)
                      ·
                        rfl

theorem cell23_1542053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_1542053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542053 prefixEnd_1542053 := by exact prefixLift 1542053
  have htrace : WordTrace (prefixWord ++ tailWord_1542053) baseStart_1542053 baseEnd_1542053 := by
    simpa [prefixWord, tailWord_1542053, baseEnd_1542053] using wordTrace_append hprefix tailTrace_1542053
  have hstable : (prefixWord ++ tailWord_1542053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542053).length < 2 ^ (prefixWord ++ tailWord_1542053).sum := by decide
  have hdescent : baseEnd_1542053 < baseStart_1542053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542125 : List Nat := [1, 5, 1, 4, 2, 1, 1, 2, 2, 1, 3]
def baseStart_1542125 : Nat := 118140960795 + 1542125 * 2 ^ 59
def prefixEnd_1542125 : Nat := 4983230072969 + 3 ^ 40 * 1542125 * 2
def baseEnd_1542125 : Nat := 791851354314884162545403

theorem tailTrace_1542125 : CollatzResearch.WordTrace tailWord_1542125 prefixEnd_1542125 791851354314884162545403 := by
  unfold tailWord_1542125
  simp only [CollatzResearch.WordTrace]
  refine ⟨56245919538151973826835829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37497279692101315884557219 56245919538151973826835829)
  ·
    refine ⟨5273054956701747546265859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56245919538151973826835829 5273054956701747546265859)
    ·
      refine ⟨7909582435052621319398789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5273054956701747546265859 7909582435052621319398789)
      ·
        refine ⟨1483046706572366497387273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7909582435052621319398789 1483046706572366497387273)
        ·
          refine ⟨1112285029929274873040455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1483046706572366497387273 1112285029929274873040455)
          ·
            refine ⟨1668427544893912309560683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1112285029929274873040455 1668427544893912309560683)
            ·
              refine ⟨2502641317340868464341025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1668427544893912309560683 2502641317340868464341025)
              ·
                refine ⟨1876980988005651348255769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2502641317340868464341025 1876980988005651348255769)
                ·
                  refine ⟨1407735741004238511191827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1876980988005651348255769 1407735741004238511191827)
                  ·
                    refine ⟨2111603611506357766787741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1407735741004238511191827 2111603611506357766787741)
                    ·
                      refine ⟨791851354314884162545403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2111603611506357766787741 791851354314884162545403)
                      ·
                        rfl

theorem cell23_1542125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_1542125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542125 prefixEnd_1542125 := by exact prefixLift 1542125
  have htrace : WordTrace (prefixWord ++ tailWord_1542125) baseStart_1542125 baseEnd_1542125 := by
    simpa [prefixWord, tailWord_1542125, baseEnd_1542125] using wordTrace_append hprefix tailTrace_1542125
  have hstable : (prefixWord ++ tailWord_1542125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542125).length < 2 ^ (prefixWord ++ tailWord_1542125).sum := by decide
  have hdescent : baseEnd_1542125 < baseStart_1542125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542137 : List Nat := [1, 2, 1, 3, 1, 4, 2, 4, 5]
def baseStart_1542137 : Nat := 118140960795 + 1542137 * 2 ^ 59
def prefixEnd_1542137 : Nat := 4983230072969 + 3 ^ 40 * 1542137 * 2
def baseEnd_1542137 : Nat := 87984168453637568399483

theorem tailTrace_1542137 : CollatzResearch.WordTrace tailWord_1542137 prefixEnd_1542137 87984168453637568399483 := by
  unfold tailWord_1542137
  simp only [CollatzResearch.WordTrace]
  refine ⟨56246357214108499876272665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37497571476072333250848443 56246357214108499876272665)
  ·
    refine ⟨42184767910581374907204499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56246357214108499876272665 42184767910581374907204499)
    ·
      refine ⟨63277151865872062360806749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42184767910581374907204499 63277151865872062360806749)
      ·
        refine ⟨23728931949702023385302531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63277151865872062360806749 23728931949702023385302531)
        ·
          refine ⟨35593397924553035077953797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23728931949702023385302531 35593397924553035077953797)
          ·
            refine ⟨6673762110853694077116337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35593397924553035077953797 6673762110853694077116337)
            ·
              refine ⟨5005321583140270557837253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6673762110853694077116337 5005321583140270557837253)
              ·
                refine ⟨938497796838800729594485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5005321583140270557837253 938497796838800729594485)
                ·
                  refine ⟨87984168453637568399483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 938497796838800729594485 87984168453637568399483)
                  ·
                    rfl

theorem cell23_1542137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 4, 5].length) (baseStart_1542137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542137 prefixEnd_1542137 := by exact prefixLift 1542137
  have htrace : WordTrace (prefixWord ++ tailWord_1542137) baseStart_1542137 baseEnd_1542137 := by
    simpa [prefixWord, tailWord_1542137, baseEnd_1542137] using wordTrace_append hprefix tailTrace_1542137
  have hstable : (prefixWord ++ tailWord_1542137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542137).length < 2 ^ (prefixWord ++ tailWord_1542137).sum := by decide
  have hdescent : baseEnd_1542137 < baseStart_1542137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542148 : List Nat := [2, 3, 2, 4, 1, 2, 1, 1, 1, 4, 2]
def baseStart_1542148 : Nat := 118140960795 + 1542148 * 2 ^ 59
def prefixEnd_1542148 : Nat := 4983230072969 + 3 ^ 40 * 1542148 * 2
def baseEnd_1542148 : Nat := 791863164369937572557797

theorem tailTrace_1542148 : CollatzResearch.WordTrace tailWord_1542148 prefixEnd_1542148 791863164369937572557797 := by
  unfold tailWord_1542148
  simp only [CollatzResearch.WordTrace]
  refine ⟨28123379208534324377461549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37497838944712432503282065 28123379208534324377461549)
  ·
    refine ⟨10546267203200371641548081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28123379208534324377461549 10546267203200371641548081)
    ·
      refine ⟨7909700402400278731161061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10546267203200371641548081 7909700402400278731161061)
      ·
        refine ⟨1483068825450052262092699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7909700402400278731161061 1483068825450052262092699)
        ·
          refine ⟨2224603238175078393139049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1483068825450052262092699 2224603238175078393139049)
          ·
            refine ⟨1668452428631308794854287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2224603238175078393139049 1668452428631308794854287)
            ·
              refine ⟨2502678642946963192281431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1668452428631308794854287 2502678642946963192281431)
              ·
                refine ⟨3754017964420444788422147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2502678642946963192281431 3754017964420444788422147)
                ·
                  refine ⟨5631026946630667182633221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3754017964420444788422147 5631026946630667182633221)
                  ·
                    refine ⟨1055817552493250096743729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5631026946630667182633221 1055817552493250096743729)
                    ·
                      refine ⟨791863164369937572557797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1055817552493250096743729 791863164369937572557797)
                      ·
                        rfl

theorem cell23_1542148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_1542148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542148 prefixEnd_1542148 := by exact prefixLift 1542148
  have htrace : WordTrace (prefixWord ++ tailWord_1542148) baseStart_1542148 baseEnd_1542148 := by
    simpa [prefixWord, tailWord_1542148, baseEnd_1542148] using wordTrace_append hprefix tailTrace_1542148
  have hstable : (prefixWord ++ tailWord_1542148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542148).length < 2 ^ (prefixWord ++ tailWord_1542148).sum := by decide
  have hdescent : baseEnd_1542148 < baseStart_1542148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542187 : List Nat := [1, 1, 1, 1, 2, 1, 4, 4, 2, 4, 2]
def baseStart_1542187 : Nat := 118140960795 + 1542187 * 2 ^ 59
def prefixEnd_1542187 : Nat := 4983230072969 + 3 ^ 40 * 1542187 * 2
def baseEnd_1542187 : Nat := 791883190115462919970117

theorem tailTrace_1542187 : CollatzResearch.WordTrace tailWord_1542187 prefixEnd_1542187 791883190115462919970117 := by
  unfold tailWord_1542187
  simp only [CollatzResearch.WordTrace]
  refine ⟨56248180863927358415592815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37498787242618238943728543 56248180863927358415592815)
  ·
    refine ⟨84372271295891037623389223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56248180863927358415592815 84372271295891037623389223)
    ·
      refine ⟨126558406943836556435083835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84372271295891037623389223 126558406943836556435083835)
      ·
        refine ⟨189837610415754834652625753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126558406943836556435083835 189837610415754834652625753)
        ·
          refine ⟨142378207811816125989469315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189837610415754834652625753 142378207811816125989469315)
          ·
            refine ⟨213567311717724188984203973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142378207811816125989469315 213567311717724188984203973)
            ·
              refine ⟨40043870947073285434538245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 213567311717724188984203973 40043870947073285434538245)
              ·
                refine ⟨7508225802576241018975921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40043870947073285434538245 7508225802576241018975921)
                ·
                  refine ⟨5631169351932180764231941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7508225802576241018975921 5631169351932180764231941)
                  ·
                    refine ⟨1055844253487283893293489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5631169351932180764231941 1055844253487283893293489)
                    ·
                      refine ⟨791883190115462919970117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1055844253487283893293489 791883190115462919970117)
                      ·
                        rfl

theorem cell23_1542187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 4, 2].length) (baseStart_1542187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542187 prefixEnd_1542187 := by exact prefixLift 1542187
  have htrace : WordTrace (prefixWord ++ tailWord_1542187) baseStart_1542187 baseEnd_1542187 := by
    simpa [prefixWord, tailWord_1542187, baseEnd_1542187] using wordTrace_append hprefix tailTrace_1542187
  have hstable : (prefixWord ++ tailWord_1542187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542187).length < 2 ^ (prefixWord ++ tailWord_1542187).sum := by decide
  have hdescent : baseEnd_1542187 < baseStart_1542187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542304 : List Nat := [2, 1, 1, 4, 2, 3, 1, 1, 4, 4]
def baseStart_1542304 : Nat := 118140960795 + 1542304 * 2 ^ 59
def prefixEnd_1542304 : Nat := 4983230072969 + 3 ^ 40 * 1542304 * 2
def baseEnd_1542304 : Nat := 263981089117346320735693

theorem tailTrace_1542304 : CollatzResearch.WordTrace tailWord_1542304 prefixEnd_1542304 263981089117346320735693 := by
  unfold tailWord_1542304
  simp only [CollatzResearch.WordTrace]
  refine ⟨28126224102251743698800983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37501632136335658265067977 28126224102251743698800983)
  ·
    refine ⟨42189336153377615548201475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28126224102251743698800983 42189336153377615548201475)
    ·
      refine ⟨63284004230066423322302213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42189336153377615548201475 63284004230066423322302213)
      ·
        refine ⟨11865750793137454372931665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63284004230066423322302213 11865750793137454372931665)
        ·
          refine ⟨8899313094853090779698749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11865750793137454372931665 8899313094853090779698749)
          ·
            refine ⟨3337242410569909042387031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8899313094853090779698749 3337242410569909042387031)
            ·
              refine ⟨5005863615854863563580547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3337242410569909042387031 5005863615854863563580547)
              ·
                refine ⟨7508795423782295345370821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5005863615854863563580547 7508795423782295345370821)
                ·
                  refine ⟨1407899141959180377257029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7508795423782295345370821 1407899141959180377257029)
                  ·
                    refine ⟨263981089117346320735693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1407899141959180377257029 263981089117346320735693)
                    ·
                      rfl

theorem cell23_1542304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 4, 4].length) (baseStart_1542304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542304 prefixEnd_1542304 := by exact prefixLift 1542304
  have htrace : WordTrace (prefixWord ++ tailWord_1542304) baseStart_1542304 baseEnd_1542304 := by
    simpa [prefixWord, tailWord_1542304, baseEnd_1542304] using wordTrace_append hprefix tailTrace_1542304
  have hstable : (prefixWord ++ tailWord_1542304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542304).length < 2 ^ (prefixWord ++ tailWord_1542304).sum := by decide
  have hdescent : baseEnd_1542304 < baseStart_1542304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542321 : List Nat := [1, 2, 2, 5, 2, 2, 1, 1, 1, 6]
def baseStart_1542321 : Nat := 118140960795 + 1542321 * 2 ^ 59
def prefixEnd_1542321 : Nat := 4983230072969 + 3 ^ 40 * 1542321 * 2
def baseEnd_1542321 : Nat := 263983998841055131898167

theorem tailTrace_1542321 : CollatzResearch.WordTrace tailWord_1542321 prefixEnd_1542321 263983998841055131898167 := by
  unfold tailWord_1542321
  simp only [CollatzResearch.WordTrace]
  refine ⟨56253068245441899300970817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37502045496961266200647211 56253068245441899300970817)
  ·
    refine ⟨42189801184081424475728113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56253068245441899300970817 42189801184081424475728113)
    ·
      refine ⟨31642350888061068356796085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42189801184081424475728113 31642350888061068356796085)
      ·
        refine ⟨2966470395755725158449633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31642350888061068356796085 2966470395755725158449633)
        ·
          refine ⟨2224852796816793868837225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2966470395755725158449633 2224852796816793868837225)
          ·
            refine ⟨1668639597612595401627919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2224852796816793868837225 1668639597612595401627919)
            ·
              refine ⟨2502959396418893102441879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1668639597612595401627919 2502959396418893102441879)
              ·
                refine ⟨3754439094628339653662819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2502959396418893102441879 3754439094628339653662819)
                ·
                  refine ⟨5631658641942509480494229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3754439094628339653662819 5631658641942509480494229)
                  ·
                    refine ⟨263983998841055131898167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5631658641942509480494229 263983998841055131898167)
                    ·
                      rfl

theorem cell23_1542321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 6].length) (baseStart_1542321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542321 prefixEnd_1542321 := by exact prefixLift 1542321
  have htrace : WordTrace (prefixWord ++ tailWord_1542321) baseStart_1542321 baseEnd_1542321 := by
    simpa [prefixWord, tailWord_1542321, baseEnd_1542321] using wordTrace_append hprefix tailTrace_1542321
  have hstable : (prefixWord ++ tailWord_1542321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542321).length < 2 ^ (prefixWord ++ tailWord_1542321).sum := by decide
  have hdescent : baseEnd_1542321 < baseStart_1542321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542334 : List Nat := [4, 2, 1, 1, 4, 1, 1, 9]
def baseStart_1542334 : Nat := 118140960795 + 1542334 * 2 ^ 59
def prefixEnd_1542334 : Nat := 4983230072969 + 3 ^ 40 * 1542334 * 2
def baseEnd_1542334 : Nat := 29331802658210142401183

theorem tailTrace_1542334 : CollatzResearch.WordTrace tailWord_1542334 prefixEnd_1542334 29331802658210142401183 := by
  unfold tailWord_1542334
  simp only [CollatzResearch.WordTrace]
  refine ⟨7031692799299350315149257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37502361596263201680796037 7031692799299350315149257)
  ·
    refine ⟨5273769599474512736361943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7031692799299350315149257 5273769599474512736361943)
    ·
      refine ⟨7910654399211769104542915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5273769599474512736361943 7910654399211769104542915)
      ·
        refine ⟨11865981598817653656814373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7910654399211769104542915 11865981598817653656814373)
        ·
          refine ⟨2224871549778310060652695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11865981598817653656814373 2224871549778310060652695)
          ·
            refine ⟨3337307324667465090979043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2224871549778310060652695 3337307324667465090979043)
            ·
              refine ⟨5005960987001197636468565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3337307324667465090979043 5005960987001197636468565)
              ·
                refine ⟨29331802658210142401183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5005960987001197636468565 29331802658210142401183)
                ·
                  rfl

theorem cell23_1542334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 9].length) (baseStart_1542334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542334 prefixEnd_1542334 := by exact prefixLift 1542334
  have htrace : WordTrace (prefixWord ++ tailWord_1542334) baseStart_1542334 baseEnd_1542334 := by
    simpa [prefixWord, tailWord_1542334, baseEnd_1542334] using wordTrace_append hprefix tailTrace_1542334
  have hstable : (prefixWord ++ tailWord_1542334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542334).length < 2 ^ (prefixWord ++ tailWord_1542334).sum := by decide
  have hdescent : baseEnd_1542334 < baseStart_1542334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542338 : List Nat := [3, 5, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_1542338 : Nat := 118140960795 + 1542338 * 2 ^ 59
def prefixEnd_1542338 : Nat := 4983230072969 + 3 ^ 40 * 1542338 * 2
def baseEnd_1542338 : Nat := 263986908564763943060641

theorem tailTrace_1542338 : CollatzResearch.WordTrace tailWord_1542338 prefixEnd_1542338 263986908564763943060641 := by
  unfold tailWord_1542338
  simp only [CollatzResearch.WordTrace]
  refine ⟨14063422071595077801084917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37502458857586874136226445 14063422071595077801084917)
  ·
    refine ⟨1318445819212038543851711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14063422071595077801084917 1318445819212038543851711)
    ·
      refine ⟨1977668728818057815777567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1318445819212038543851711 1977668728818057815777567)
      ·
        refine ⟨2966503093227086723666351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1977668728818057815777567 2966503093227086723666351)
        ·
          refine ⟨4449754639840630085499527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2966503093227086723666351 4449754639840630085499527)
          ·
            refine ⟨6674631959760945128249291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4449754639840630085499527 6674631959760945128249291)
            ·
              refine ⟨10011947939641417692373937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6674631959760945128249291 10011947939641417692373937)
              ·
                refine ⟨7508960954731063269280453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10011947939641417692373937 7508960954731063269280453)
                ·
                  refine ⟨1407930179012074362990085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7508960954731063269280453 1407930179012074362990085)
                  ·
                    refine ⟨263986908564763943060641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1407930179012074362990085 263986908564763943060641)
                    ·
                      rfl

theorem cell23_1542338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_1542338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542338 prefixEnd_1542338 := by exact prefixLift 1542338
  have htrace : WordTrace (prefixWord ++ tailWord_1542338) baseStart_1542338 baseEnd_1542338 := by
    simpa [prefixWord, tailWord_1542338, baseEnd_1542338] using wordTrace_append hprefix tailTrace_1542338
  have hstable : (prefixWord ++ tailWord_1542338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542338).length < 2 ^ (prefixWord ++ tailWord_1542338).sum := by decide
  have hdescent : baseEnd_1542338 < baseStart_1542338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542367 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 4]
def baseStart_1542367 : Nat := 118140960795 + 1542367 * 2 ^ 59
def prefixEnd_1542367 : Nat := 4983230072969 + 3 ^ 40 * 1542367 * 2
def baseEnd_1542367 : Nat := 791975616633272215719289

theorem tailTrace_1542367 : CollatzResearch.WordTrace tailWord_1542367 prefixEnd_1542367 791975616633272215719289 := by
  unfold tailWord_1542367
  simp only [CollatzResearch.WordTrace]
  refine ⟨56254746003275249157145355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37503164002183499438096903 56254746003275249157145355)
  ·
    refine ⟨84382119004912873735718033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56254746003275249157145355 84382119004912873735718033)
    ·
      refine ⟨63286589253684655301788525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84382119004912873735718033 63286589253684655301788525)
      ·
        refine ⟨23732470970131745738170697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63286589253684655301788525 23732470970131745738170697)
        ·
          refine ⟨17799353227598809303628023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23732470970131745738170697 17799353227598809303628023)
          ·
            refine ⟨26699029841398213955442035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17799353227598809303628023 26699029841398213955442035)
            ·
              refine ⟨40048544762097320933163053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26699029841398213955442035 40048544762097320933163053)
              ·
                refine ⟨15018204285786495349936145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40048544762097320933163053 15018204285786495349936145)
                ·
                  refine ⟨11263653214339871512452109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15018204285786495349936145 11263653214339871512452109)
                  ·
                    refine ⟨4223869955377451817169541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11263653214339871512452109 4223869955377451817169541)
                    ·
                      refine ⟨791975616633272215719289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4223869955377451817169541 791975616633272215719289)
                      ·
                        rfl

theorem cell23_1542367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_1542367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542367 prefixEnd_1542367 := by exact prefixLift 1542367
  have htrace : WordTrace (prefixWord ++ tailWord_1542367) baseStart_1542367 baseEnd_1542367 := by
    simpa [prefixWord, tailWord_1542367, baseEnd_1542367] using wordTrace_append hprefix tailTrace_1542367
  have hstable : (prefixWord ++ tailWord_1542367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542367).length < 2 ^ (prefixWord ++ tailWord_1542367).sum := by decide
  have hdescent : baseEnd_1542367 < baseStart_1542367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542384 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 5, 4, 2]
def baseStart_1542384 : Nat := 118140960795 + 1542384 * 2 ^ 59
def prefixEnd_1542384 : Nat := 4983230072969 + 3 ^ 40 * 1542384 * 2
def baseEnd_1542384 : Nat := 791984345804398649206711

theorem tailTrace_1542384 : CollatzResearch.WordTrace tailWord_1542384 prefixEnd_1542384 791984345804398649206711 := by
  unfold tailWord_1542384
  simp only [CollatzResearch.WordTrace]
  refine ⟨28127683022106830530257103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37503577362809107373676137 28127683022106830530257103)
  ·
    refine ⟨42191524533160245795385655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28127683022106830530257103 42191524533160245795385655)
    ·
      refine ⟨63287286799740368693078483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42191524533160245795385655 63287286799740368693078483)
      ·
        refine ⟨94930930199610553039617725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63287286799740368693078483 94930930199610553039617725)
        ·
          refine ⟨35599098824853957389856647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94930930199610553039617725 35599098824853957389856647)
          ·
            refine ⟨53398648237280936084784971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35599098824853957389856647 53398648237280936084784971)
            ·
              refine ⟨80097972355921404127177457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53398648237280936084784971 80097972355921404127177457)
              ·
                refine ⟨60073479266941053095383093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80097972355921404127177457 60073479266941053095383093)
                ·
                  refine ⟨5631888681275723727692165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60073479266941053095383093 5631888681275723727692165)
                  ·
                    refine ⟨1055979127739198198942281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5631888681275723727692165 1055979127739198198942281)
                    ·
                      refine ⟨791984345804398649206711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1055979127739198198942281 791984345804398649206711)
                      ·
                        rfl

theorem cell23_1542384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 5, 4, 2].length) (baseStart_1542384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542384 prefixEnd_1542384 := by exact prefixLift 1542384
  have htrace : WordTrace (prefixWord ++ tailWord_1542384) baseStart_1542384 baseEnd_1542384 := by
    simpa [prefixWord, tailWord_1542384, baseEnd_1542384] using wordTrace_append hprefix tailTrace_1542384
  have hstable : (prefixWord ++ tailWord_1542384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542384).length < 2 ^ (prefixWord ++ tailWord_1542384).sum := by decide
  have hdescent : baseEnd_1542384 < baseStart_1542384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542387 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 5]
def baseStart_1542387 : Nat := 118140960795 + 1542387 * 2 ^ 59
def prefixEnd_1542387 : Nat := 4983230072969 + 3 ^ 40 * 1542387 * 2
def baseEnd_1542387 : Nat := 791985886246362137469197

theorem tailTrace_1542387 : CollatzResearch.WordTrace tailWord_1542387 prefixEnd_1542387 791985886246362137469197 := by
  unfold tailWord_1542387
  simp only [CollatzResearch.WordTrace]
  refine ⟨56255475463202792572873415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37503650308801861715248943 56255475463202792572873415)
  ·
    refine ⟨84383213194804188859310123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56255475463202792572873415 84383213194804188859310123)
    ·
      refine ⟨126574819792206283288965185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84383213194804188859310123 126574819792206283288965185)
      ·
        refine ⟨94931114844154712466723889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126574819792206283288965185 94931114844154712466723889)
        ·
          refine ⟨71198336133116034350042917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94931114844154712466723889 71198336133116034350042917)
          ·
            refine ⟨13349688024959256440633047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71198336133116034350042917 13349688024959256440633047)
            ·
              refine ⟨20024532037438884660949571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13349688024959256440633047 20024532037438884660949571)
              ·
                refine ⟨30036798056158326991424357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20024532037438884660949571 30036798056158326991424357)
                ·
                  refine ⟨5631899635529686310892067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30036798056158326991424357 5631899635529686310892067)
                  ·
                    refine ⟨8447849453294529466338101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5631899635529686310892067 8447849453294529466338101)
                    ·
                      refine ⟨791985886246362137469197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8447849453294529466338101 791985886246362137469197)
                      ·
                        rfl

theorem cell23_1542387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 5].length) (baseStart_1542387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542387 prefixEnd_1542387 := by exact prefixLift 1542387
  have htrace : WordTrace (prefixWord ++ tailWord_1542387) baseStart_1542387 baseEnd_1542387 := by
    simpa [prefixWord, tailWord_1542387, baseEnd_1542387] using wordTrace_append hprefix tailTrace_1542387
  have hstable : (prefixWord ++ tailWord_1542387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542387).length < 2 ^ (prefixWord ++ tailWord_1542387).sum := by decide
  have hdescent : baseEnd_1542387 < baseStart_1542387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542401 : List Nat := [1, 2, 4, 1, 1, 2, 3, 2, 1, 4, 2]
def baseStart_1542401 : Nat := 118140960795 + 1542401 * 2 ^ 59
def prefixEnd_1542401 : Nat := 4983230072969 + 3 ^ 40 * 1542401 * 2
def baseEnd_1542401 : Nat := 791993074975525082694133

theorem tailTrace_1542401 : CollatzResearch.WordTrace tailWord_1542401 prefixEnd_1542401 791993074975525082694133 := by
  unfold tailWord_1542401
  simp only [CollatzResearch.WordTrace]
  refine ⟨56255986085152072963883057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37503990723434715309255371 56255986085152072963883057)
  ·
    refine ⟨42191989563864054722912293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56255986085152072963883057 42191989563864054722912293)
    ·
      refine ⟨7910998043224510260546055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42191989563864054722912293 7910998043224510260546055)
      ·
        refine ⟨11866497064836765390819083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7910998043224510260546055 11866497064836765390819083)
        ·
          refine ⟨17799745597255148086228625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11866497064836765390819083 17799745597255148086228625)
          ·
            refine ⟨13349809197941361064671469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17799745597255148086228625 13349809197941361064671469)
            ·
              refine ⟨5006178449228010399251801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13349809197941361064671469 5006178449228010399251801)
              ·
                refine ⟨3754633836921007799438851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5006178449228010399251801 3754633836921007799438851)
                ·
                  refine ⟨5631950755381511699158277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3754633836921007799438851 5631950755381511699158277)
                  ·
                    refine ⟨1055990766634033443592177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5631950755381511699158277 1055990766634033443592177)
                    ·
                      refine ⟨791993074975525082694133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1055990766634033443592177 791993074975525082694133)
                      ·
                        rfl

theorem cell23_1542401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_1542401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542401 prefixEnd_1542401 := by exact prefixLift 1542401
  have htrace : WordTrace (prefixWord ++ tailWord_1542401) baseStart_1542401 baseEnd_1542401 := by
    simpa [prefixWord, tailWord_1542401, baseEnd_1542401] using wordTrace_append hprefix tailTrace_1542401
  have hstable : (prefixWord ++ tailWord_1542401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542401).length < 2 ^ (prefixWord ++ tailWord_1542401).sum := by decide
  have hdescent : baseEnd_1542401 < baseStart_1542401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542414 : List Nat := [4, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4]
def baseStart_1542414 : Nat := 118140960795 + 1542414 * 2 ^ 59
def prefixEnd_1542414 : Nat := 4983230072969 + 3 ^ 40 * 1542414 * 2
def baseEnd_1542414 : Nat := 791999750224033531831573

theorem tailTrace_1542414 : CollatzResearch.WordTrace tailWord_1542414 prefixEnd_1542414 791999750224033531831573 := by
  unfold tailWord_1542414
  simp only [CollatzResearch.WordTrace]
  refine ⟨7032057529263122023013287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37504306822736650789404197 7032057529263122023013287)
  ·
    refine ⟨10548086293894683034519931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7032057529263122023013287 10548086293894683034519931)
    ·
      refine ⟨15822129440842024551779897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10548086293894683034519931 15822129440842024551779897)
      ·
        refine ⟨11866597080631518413834923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15822129440842024551779897 11866597080631518413834923)
        ·
          refine ⟨17799895620947277620752385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11866597080631518413834923 17799895620947277620752385)
          ·
            refine ⟨13349921715710458215564289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17799895620947277620752385 13349921715710458215564289)
            ·
              refine ⟨10012441286782843661673217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13349921715710458215564289 10012441286782843661673217)
              ·
                refine ⟨7509330965087132746254913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10012441286782843661673217 7509330965087132746254913)
                ·
                  refine ⟨5631998223815349559691185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7509330965087132746254913 5631998223815349559691185)
                  ·
                    refine ⟨4223998667861512169768389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5631998223815349559691185 4223998667861512169768389)
                    ·
                      refine ⟨791999750224033531831573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4223998667861512169768389 791999750224033531831573)
                      ·
                        rfl

theorem cell23_1542414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_1542414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542414 prefixEnd_1542414 := by exact prefixLift 1542414
  have htrace : WordTrace (prefixWord ++ tailWord_1542414) baseStart_1542414 baseEnd_1542414 := by
    simpa [prefixWord, tailWord_1542414, baseEnd_1542414] using wordTrace_append hprefix tailTrace_1542414
  have hstable : (prefixWord ++ tailWord_1542414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542414).length < 2 ^ (prefixWord ++ tailWord_1542414).sum := by decide
  have hdescent : baseEnd_1542414 < baseStart_1542414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542447 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 7]
def baseStart_1542447 : Nat := 118140960795 + 1542447 * 2 ^ 59
def prefixEnd_1542447 : Nat := 4983230072969 + 3 ^ 40 * 1542447 * 2
def baseEnd_1542447 : Nat := 792016695085631902718921

theorem tailTrace_1542447 : CollatzResearch.WordTrace tailWord_1542447 prefixEnd_1542447 792016695085631902718921 := by
  unfold tailWord_1542447
  simp only [CollatzResearch.WordTrace]
  refine ⟨56257663842985422820057595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37505109228656948546705063 56257663842985422820057595)
  ·
    refine ⟨84386495764478134230086393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56257663842985422820057595 84386495764478134230086393)
    ·
      refine ⟨63289871823358600672564795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84386495764478134230086393 63289871823358600672564795)
      ·
        refine ⟨94934807735037901008847193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63289871823358600672564795 94934807735037901008847193)
        ·
          refine ⟨71201105801278425756635395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94934807735037901008847193 71201105801278425756635395)
          ·
            refine ⟨106801658701917638634953093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71201105801278425756635395 106801658701917638634953093)
            ·
              refine ⟨20025311006609557244053705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106801658701917638634953093 20025311006609557244053705)
              ·
                refine ⟨15018983254957167933040279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20025311006609557244053705 15018983254957167933040279)
                ·
                  refine ⟨22528474882435751899560419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15018983254957167933040279 22528474882435751899560419)
                  ·
                    refine ⟨33792712323653627849340629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22528474882435751899560419 33792712323653627849340629)
                    ·
                      refine ⟨792016695085631902718921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 33792712323653627849340629 792016695085631902718921)
                      ·
                        rfl

theorem cell23_1542447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 7].length) (baseStart_1542447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542447 prefixEnd_1542447 := by exact prefixLift 1542447
  have htrace : WordTrace (prefixWord ++ tailWord_1542447) baseStart_1542447 baseEnd_1542447 := by
    simpa [prefixWord, tailWord_1542447, baseEnd_1542447] using wordTrace_append hprefix tailTrace_1542447
  have hstable : (prefixWord ++ tailWord_1542447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542447).length < 2 ^ (prefixWord ++ tailWord_1542447).sum := by decide
  have hdescent : baseEnd_1542447 < baseStart_1542447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542501 : List Nat := [1, 3, 1, 3, 1, 3, 2, 2, 3, 4]
def baseStart_1542501 : Nat := 118140960795 + 1542501 * 2 ^ 59
def prefixEnd_1542501 : Nat := 4983230072969 + 3 ^ 40 * 1542501 * 2
def baseEnd_1542501 : Nat := 264014807680324897147891

theorem tailTrace_1542501 : CollatzResearch.WordTrace tailWord_1542501 prefixEnd_1542501 264014807680324897147891 := by
  unfold tailWord_1542501
  simp only [CollatzResearch.WordTrace]
  refine ⟨56259633384789790042523357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37506422256526526695015571 56259633384789790042523357)
  ·
    refine ⟨21097362519296171265946259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56259633384789790042523357 21097362519296171265946259)
    ·
      refine ⟨31646043778944256898919389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21097362519296171265946259 31646043778944256898919389)
      ·
        refine ⟨11867266417104096337094771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31646043778944256898919389 11867266417104096337094771)
        ·
          refine ⟨17800899625656144505642157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11867266417104096337094771 17800899625656144505642157)
          ·
            refine ⟨6675337359621054189615809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17800899625656144505642157 6675337359621054189615809)
            ·
              refine ⟨5006503019715790642211857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6675337359621054189615809 5006503019715790642211857)
              ·
                refine ⟨3754877264786842981658893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5006503019715790642211857 3754877264786842981658893)
                ·
                  refine ⟨1408078974295066118122085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3754877264786842981658893 1408078974295066118122085)
                  ·
                    refine ⟨264014807680324897147891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1408078974295066118122085 264014807680324897147891)
                    ·
                      rfl

theorem cell23_1542501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 3, 4].length) (baseStart_1542501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542501 prefixEnd_1542501 := by exact prefixLift 1542501
  have htrace : WordTrace (prefixWord ++ tailWord_1542501) baseStart_1542501 baseEnd_1542501 := by
    simpa [prefixWord, tailWord_1542501, baseEnd_1542501] using wordTrace_append hprefix tailTrace_1542501
  have hstable : (prefixWord ++ tailWord_1542501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542501).length < 2 ^ (prefixWord ++ tailWord_1542501).sum := by decide
  have hdescent : baseEnd_1542501 < baseStart_1542501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542514 : List Nat := [3, 2, 1, 2, 1, 3, 1, 2, 8]
def baseStart_1542514 : Nat := 118140960795 + 1542514 * 2 ^ 59
def prefixEnd_1542514 : Nat := 4983230072969 + 3 ^ 40 * 1542514 * 2
def baseEnd_1542514 : Nat := 88005677587720348953457

theorem tailTrace_1542514 : CollatzResearch.WordTrace tailWord_1542514 prefixEnd_1542514 88005677587720348953457 := by
  unfold tailWord_1542514
  simp only [CollatzResearch.WordTrace]
  refine ⟨14065026883435673315686649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37506738355828462175164397 14065026883435673315686649)
  ·
    refine ⟨10548770162576754986764987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14065026883435673315686649 10548770162576754986764987)
    ·
      refine ⟨15823155243865132480147481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10548770162576754986764987 15823155243865132480147481)
      ·
        refine ⟨11867366432898849360110611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15823155243865132480147481 11867366432898849360110611)
        ·
          refine ⟨17801049649348274040165917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11867366432898849360110611 17801049649348274040165917)
          ·
            refine ⟨6675393618505602765062219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17801049649348274040165917 6675393618505602765062219)
            ·
              refine ⟨10013090427758404147593329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6675393618505602765062219 10013090427758404147593329)
              ·
                refine ⟨7509817820818803110694997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10013090427758404147593329 7509817820818803110694997)
                ·
                  refine ⟨88005677587720348953457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7509817820818803110694997 88005677587720348953457)
                  ·
                    rfl

theorem cell23_1542514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 8].length) (baseStart_1542514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542514 prefixEnd_1542514 := by exact prefixLift 1542514
  have htrace : WordTrace (prefixWord ++ tailWord_1542514) baseStart_1542514 baseEnd_1542514 := by
    simpa [prefixWord, tailWord_1542514, baseEnd_1542514] using wordTrace_append hprefix tailTrace_1542514
  have hstable : (prefixWord ++ tailWord_1542514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542514).length < 2 ^ (prefixWord ++ tailWord_1542514).sum := by decide
  have hdescent : baseEnd_1542514 < baseStart_1542514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542535 : List Nat := [1, 1, 4, 2, 2, 1, 5, 2, 1, 4]
def baseStart_1542535 : Nat := 118140960795 + 1542535 * 2 ^ 59
def prefixEnd_1542535 : Nat := 4983230072969 + 3 ^ 40 * 1542535 * 2
def baseEnd_1542535 : Nat := 264020627127742519472839

theorem tailTrace_1542535 : CollatzResearch.WordTrace tailWord_1542535 prefixEnd_1542535 264020627127742519472839 := by
  unfold tailWord_1542535
  simp only [CollatzResearch.WordTrace]
  refine ⟨56260873466666613849261059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37507248977777742566174039 56260873466666613849261059)
  ·
    refine ⟨84391310199999920773891589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56260873466666613849261059 84391310199999920773891589)
    ·
      refine ⟨15823370662499985145104673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84391310199999920773891589 15823370662499985145104673)
      ·
        refine ⟨11867527996874988858828505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15823370662499985145104673 11867527996874988858828505)
        ·
          refine ⟨8900645997656241644121379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11867527996874988858828505 8900645997656241644121379)
          ·
            refine ⟨13350968996484362466182069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8900645997656241644121379 13350968996484362466182069)
            ·
              refine ⟨1251653343420408981204569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13350968996484362466182069 1251653343420408981204569)
              ·
                refine ⟨938740007565306735903427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1251653343420408981204569 938740007565306735903427)
                ·
                  refine ⟨1408110011347960103855141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 938740007565306735903427 1408110011347960103855141)
                  ·
                    refine ⟨264020627127742519472839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1408110011347960103855141 264020627127742519472839)
                    ·
                      rfl

theorem cell23_1542535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_1542535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542535 prefixEnd_1542535 := by exact prefixLift 1542535
  have htrace : WordTrace (prefixWord ++ tailWord_1542535) baseStart_1542535 baseEnd_1542535 := by
    simpa [prefixWord, tailWord_1542535, baseEnd_1542535] using wordTrace_append hprefix tailTrace_1542535
  have hstable : (prefixWord ++ tailWord_1542535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542535).length < 2 ^ (prefixWord ++ tailWord_1542535).sum := by decide
  have hdescent : baseEnd_1542535 < baseStart_1542535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542548 : List Nat := [2, 4, 2, 1, 3, 1, 1, 3, 6]
def baseStart_1542548 : Nat := 118140960795 + 1542548 * 2 ^ 59
def prefixEnd_1542548 : Nat := 4983230072969 + 3 ^ 40 * 1542548 * 2
def baseEnd_1542548 : Nat := 88007617403526223061773

theorem tailTrace_1542548 : CollatzResearch.WordTrace tailWord_1542548 prefixEnd_1542548 88007617403526223061773 := by
  unfold tailWord_1542548
  simp only [CollatzResearch.WordTrace]
  refine ⟨28130673807809758534742149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37507565077079678046322865 28130673807809758534742149)
  ·
    refine ⟨5274501338964329725264153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28130673807809758534742149 5274501338964329725264153)
    ·
      refine ⟨3955876004223247293948115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5274501338964329725264153 3955876004223247293948115)
      ·
        refine ⟨5933814006334870940922173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3955876004223247293948115 5933814006334870940922173)
        ·
          refine ⟨2225180252375576602845815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5933814006334870940922173 2225180252375576602845815)
          ·
            refine ⟨3337770378563364904268723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2225180252375576602845815 3337770378563364904268723)
            ·
              refine ⟨5006655567845047356403085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3337770378563364904268723 5006655567845047356403085)
              ·
                refine ⟨1877495837941892758651157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5006655567845047356403085 1877495837941892758651157)
                ·
                  refine ⟨88007617403526223061773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1877495837941892758651157 88007617403526223061773)
                  ·
                    rfl

theorem cell23_1542548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_1542548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542548 prefixEnd_1542548 := by exact prefixLift 1542548
  have htrace : WordTrace (prefixWord ++ tailWord_1542548) baseStart_1542548 baseEnd_1542548 := by
    simpa [prefixWord, tailWord_1542548, baseEnd_1542548] using wordTrace_append hprefix tailTrace_1542548
  have hstable : (prefixWord ++ tailWord_1542548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542548).length < 2 ^ (prefixWord ++ tailWord_1542548).sum := by decide
  have hdescent : baseEnd_1542548 < baseStart_1542548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542551 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 3, 5, 2]
def baseStart_1542551 : Nat := 118140960795 + 1542551 * 2 ^ 59
def prefixEnd_1542551 : Nat := 4983230072969 + 3 ^ 40 * 1542551 * 2
def baseEnd_1542551 : Nat := 792070097073699495818443

theorem tailTrace_1542551 : CollatzResearch.WordTrace tailWord_1542551 prefixEnd_1542551 792070097073699495818443 := by
  unfold tailWord_1542551
  simp only [CollatzResearch.WordTrace]
  refine ⟨56261457034608648581843507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37507638023072432387895671 56261457034608648581843507)
  ·
    refine ⟨84392185551912972872765261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56261457034608648581843507 84392185551912972872765261)
    ·
      refine ⟨31647069581967364827286973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84392185551912972872765261 31647069581967364827286973)
      ·
        refine ⟨11867651093237761810232615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31647069581967364827286973 11867651093237761810232615)
        ·
          refine ⟨17801476639856642715348923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11867651093237761810232615 17801476639856642715348923)
          ·
            refine ⟨26702214959784964073023385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17801476639856642715348923 26702214959784964073023385)
            ·
              refine ⟨20026661219838723054767539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26702214959784964073023385 20026661219838723054767539)
              ·
                refine ⟨30039991829758084582151309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20026661219838723054767539 30039991829758084582151309)
                ·
                  refine ⟨11264996936159281718306741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30039991829758084582151309 11264996936159281718306741)
                  ·
                    refine ⟨1056093462764932661091257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11264996936159281718306741 1056093462764932661091257)
                    ·
                      refine ⟨792070097073699495818443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1056093462764932661091257 792070097073699495818443)
                      ·
                        rfl

theorem cell23_1542551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_1542551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542551 prefixEnd_1542551 := by exact prefixLift 1542551
  have htrace : WordTrace (prefixWord ++ tailWord_1542551) baseStart_1542551 baseEnd_1542551 := by
    simpa [prefixWord, tailWord_1542551, baseEnd_1542551] using wordTrace_append hprefix tailTrace_1542551
  have hstable : (prefixWord ++ tailWord_1542551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542551).length < 2 ^ (prefixWord ++ tailWord_1542551).sum := by decide
  have hdescent : baseEnd_1542551 < baseStart_1542551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542578 : List Nat := [3, 2, 1, 1, 1, 1, 7, 1, 1, 5]
def baseStart_1542578 : Nat := 118140960795 + 1542578 * 2 ^ 59
def prefixEnd_1542578 : Nat := 4983230072969 + 3 ^ 40 * 1542578 * 2
def baseEnd_1542578 : Nat := 264027987017123630060273

theorem tailTrace_1542578 : CollatzResearch.WordTrace tailWord_1542578 prefixEnd_1542578 264027987017123630060273 := by
  unfold tailWord_1542578
  simp only [CollatzResearch.WordTrace]
  refine ⟨14065610451377708048269097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37508294537007221462050925 14065610451377708048269097)
  ·
    refine ⟨10549207838533281036201823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14065610451377708048269097 10549207838533281036201823)
    ·
      refine ⟨15823811757799921554302735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10549207838533281036201823 15823811757799921554302735)
      ·
        refine ⟨23735717636699882331454103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15823811757799921554302735 23735717636699882331454103)
        ·
          refine ⟨35603576455049823497181155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23735717636699882331454103 35603576455049823497181155)
          ·
            refine ⟨53405364682574735245771733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35603576455049823497181155 53405364682574735245771733)
            ·
              refine ⟨1251688234747845357322775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 53405364682574735245771733 1251688234747845357322775)
              ·
                refine ⟨1877532352121768035984163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1251688234747845357322775 1877532352121768035984163)
                ·
                  refine ⟨2816298528182652053976245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1877532352121768035984163 2816298528182652053976245)
                  ·
                    refine ⟨264027987017123630060273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2816298528182652053976245 264027987017123630060273)
                    ·
                      rfl

theorem cell23_1542578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_1542578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542578 prefixEnd_1542578 := by exact prefixLift 1542578
  have htrace : WordTrace (prefixWord ++ tailWord_1542578) baseStart_1542578 baseEnd_1542578 := by
    simpa [prefixWord, tailWord_1542578, baseEnd_1542578] using wordTrace_append hprefix tailTrace_1542578
  have hstable : (prefixWord ++ tailWord_1542578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542578).length < 2 ^ (prefixWord ++ tailWord_1542578).sum := by decide
  have hdescent : baseEnd_1542578 < baseStart_1542578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542601 : List Nat := [1, 2, 1, 1, 2, 1, 5, 2, 3, 2, 3]
def baseStart_1542601 : Nat := 118140960795 + 1542601 * 2 ^ 59
def prefixEnd_1542601 : Nat := 4983230072969 + 3 ^ 40 * 1542601 * 2
def baseEnd_1542601 : Nat := 792095771106424300193213

theorem tailTrace_1542601 : CollatzResearch.WordTrace tailWord_1542601 prefixEnd_1542601 792095771106424300193213 := by
  unfold tailWord_1542601
  simp only [CollatzResearch.WordTrace]
  refine ⟨56263280684427507121163657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37508853789618338080775771 56263280684427507121163657)
  ·
    refine ⟨42197460513320630340872743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56263280684427507121163657 42197460513320630340872743)
    ·
      refine ⟨63296190769980945511309115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42197460513320630340872743 63296190769980945511309115)
      ·
        refine ⟨94944286154971418266963673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63296190769980945511309115 94944286154971418266963673)
        ·
          refine ⟨71208214616228563700222755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94944286154971418266963673 71208214616228563700222755)
          ·
            refine ⟨106812321924342845550334133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71208214616228563700222755 106812321924342845550334133)
            ·
              refine ⟨10013655180407141770343825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106812321924342845550334133 10013655180407141770343825)
              ·
                refine ⟨7510241385305356327757869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10013655180407141770343825 7510241385305356327757869)
                ·
                  refine ⟨2816340519489508622909201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7510241385305356327757869 2816340519489508622909201)
                  ·
                    refine ⟨2112255389617131467181901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2816340519489508622909201 2112255389617131467181901)
                    ·
                      refine ⟨792095771106424300193213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2112255389617131467181901 792095771106424300193213)
                      ·
                        rfl

theorem cell23_1542601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 2, 3].length) (baseStart_1542601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542601 prefixEnd_1542601 := by exact prefixLift 1542601
  have htrace : WordTrace (prefixWord ++ tailWord_1542601) baseStart_1542601 baseEnd_1542601 := by
    simpa [prefixWord, tailWord_1542601, baseEnd_1542601] using wordTrace_append hprefix tailTrace_1542601
  have hstable : (prefixWord ++ tailWord_1542601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542601).length < 2 ^ (prefixWord ++ tailWord_1542601).sum := by decide
  have hdescent : baseEnd_1542601 < baseStart_1542601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542618 : List Nat := [3, 1, 1, 2, 3, 1, 2, 4, 1, 2, 3]
def baseStart_1542618 : Nat := 118140960795 + 1542618 * 2 ^ 59
def prefixEnd_1542618 : Nat := 4983230072969 + 3 ^ 40 * 1542618 * 2
def baseEnd_1542618 : Nat := 792104500277550733680635

theorem tailTrace_1542618 : CollatzResearch.WordTrace tailWord_1542618 prefixEnd_1542618 792104500277550733680635 := by
  unfold tailWord_1542618
  simp only [CollatzResearch.WordTrace]
  refine ⟨14065975181341479756133127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37509267150243946016355005 14065975181341479756133127)
  ·
    refine ⟨21098962772012219634199691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14065975181341479756133127 21098962772012219634199691)
    ·
      refine ⟨31648444158018329451299537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21098962772012219634199691 31648444158018329451299537)
      ·
        refine ⟨23736333118513747088474653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31648444158018329451299537 23736333118513747088474653)
        ·
          refine ⟨8901124919442655158177995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23736333118513747088474653 8901124919442655158177995)
          ·
            refine ⟨13351687379163982737266993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8901124919442655158177995 13351687379163982737266993)
            ·
              refine ⟨10013765534372987052950245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13351687379163982737266993 10013765534372987052950245)
              ·
                refine ⟨1877581037694935072428171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10013765534372987052950245 1877581037694935072428171)
                ·
                  refine ⟨2816371556542402608642257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1877581037694935072428171 2816371556542402608642257)
                  ·
                    refine ⟨2112278667406801956481693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2816371556542402608642257 2112278667406801956481693)
                    ·
                      refine ⟨792104500277550733680635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2112278667406801956481693 792104500277550733680635)
                      ·
                        rfl

theorem cell23_1542618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_1542618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542618 prefixEnd_1542618 := by exact prefixLift 1542618
  have htrace : WordTrace (prefixWord ++ tailWord_1542618) baseStart_1542618 baseEnd_1542618 := by
    simpa [prefixWord, tailWord_1542618, baseEnd_1542618] using wordTrace_append hprefix tailTrace_1542618
  have hstable : (prefixWord ++ tailWord_1542618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542618).length < 2 ^ (prefixWord ++ tailWord_1542618).sum := by decide
  have hdescent : baseEnd_1542618 < baseStart_1542618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542626 : List Nat := [3, 3, 3, 2, 1, 1, 2, 3, 1, 1, 3]
def baseStart_1542626 : Nat := 118140960795 + 1542626 * 2 ^ 59
def prefixEnd_1542626 : Nat := 4983230072969 + 3 ^ 40 * 1542626 * 2
def baseEnd_1542626 : Nat := 792108608122786702380599

theorem tailTrace_1542626 : CollatzResearch.WordTrace tailWord_1542626 prefixEnd_1542626 792108608122786702380599 := by
  unfold tailWord_1542626
  simp only [CollatzResearch.WordTrace]
  refine ⟨14066048127334234097705933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37509461672891290927215821 14066048127334234097705933)
  ·
    refine ⟨5274768047750337786639725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14066048127334234097705933 5274768047750337786639725)
    ·
      refine ⟨1978038017906376669989897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5274768047750337786639725 1978038017906376669989897)
      ·
        refine ⟨1483528513429782502492423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1978038017906376669989897 1483528513429782502492423)
        ·
          refine ⟨2225292770144673753738635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1483528513429782502492423 2225292770144673753738635)
          ·
            refine ⟨3337939155217010630607953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2225292770144673753738635 3337939155217010630607953)
            ·
              refine ⟨2503454366412757972955965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3337939155217010630607953 2503454366412757972955965)
              ·
                refine ⟨938795387404784239858487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2503454366412757972955965 938795387404784239858487)
                ·
                  refine ⟨1408193081107176359787731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 938795387404784239858487 1408193081107176359787731)
                  ·
                    refine ⟨2112289621660764539681597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1408193081107176359787731 2112289621660764539681597)
                    ·
                      refine ⟨792108608122786702380599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2112289621660764539681597 792108608122786702380599)
                      ·
                        rfl

theorem cell23_1542626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_1542626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542626 prefixEnd_1542626 := by exact prefixLift 1542626
  have htrace : WordTrace (prefixWord ++ tailWord_1542626) baseStart_1542626 baseEnd_1542626 := by
    simpa [prefixWord, tailWord_1542626, baseEnd_1542626] using wordTrace_append hprefix tailTrace_1542626
  have hstable : (prefixWord ++ tailWord_1542626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542626).length < 2 ^ (prefixWord ++ tailWord_1542626).sum := by decide
  have hdescent : baseEnd_1542626 < baseStart_1542626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542632 : List Nat := [2, 1, 4, 1, 1, 3, 1, 5, 1, 2, 2]
def baseStart_1542632 : Nat := 118140960795 + 1542632 * 2 ^ 59
def prefixEnd_1542632 : Nat := 4983230072969 + 3 ^ 40 * 1542632 * 2
def baseEnd_1542632 : Nat := 792111689006713678905571

theorem tailTrace_1542632 : CollatzResearch.WordTrace tailWord_1542632 prefixEnd_1542632 792111689006713678905571 := by
  unfold tailWord_1542632
  simp only [CollatzResearch.WordTrace]
  refine ⟨28132205673657599707771075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37509607564876799610361433 28132205673657599707771075)
  ·
    refine ⟨42198308510486399561656613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28132205673657599707771075 42198308510486399561656613)
    ·
      refine ⟨7912182845716199917810615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42198308510486399561656613 7912182845716199917810615)
      ·
        refine ⟨11868274268574299876715923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7912182845716199917810615 11868274268574299876715923)
        ·
          refine ⟨17802411402861449815073885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11868274268574299876715923 17802411402861449815073885)
          ·
            refine ⟨6675904276073043680652707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17802411402861449815073885 6675904276073043680652707)
            ·
              refine ⟨10013856414109565520979061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6675904276073043680652707 10013856414109565520979061)
              ·
                refine ⟨938799038822771767591787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10013856414109565520979061 938799038822771767591787)
                ·
                  refine ⟨1408198558234157651387681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 938799038822771767591787 1408198558234157651387681)
                  ·
                    refine ⟨1056148918675618238540761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1408198558234157651387681 1056148918675618238540761)
                    ·
                      refine ⟨792111689006713678905571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1056148918675618238540761 792111689006713678905571)
                      ·
                        rfl

theorem cell23_1542632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_1542632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542632 prefixEnd_1542632 := by exact prefixLift 1542632
  have htrace : WordTrace (prefixWord ++ tailWord_1542632) baseStart_1542632 baseEnd_1542632 := by
    simpa [prefixWord, tailWord_1542632, baseEnd_1542632] using wordTrace_append hprefix tailTrace_1542632
  have hstable : (prefixWord ++ tailWord_1542632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542632).length < 2 ^ (prefixWord ++ tailWord_1542632).sum := by decide
  have hdescent : baseEnd_1542632 < baseStart_1542632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542642 : List Nat := [3, 2, 1, 4, 2, 2, 1, 2, 2, 4]
def baseStart_1542642 : Nat := 118140960795 + 1542642 * 2 ^ 59
def prefixEnd_1542642 : Nat := 4983230072969 + 3 ^ 40 * 1542642 * 2
def baseEnd_1542642 : Nat := 264038941271086213260175

theorem tailTrace_1542642 : CollatzResearch.WordTrace tailWord_1542642 prefixEnd_1542642 264038941271086213260175 := by
  unfold tailWord_1542642
  simp only [CollatzResearch.WordTrace]
  refine ⟨14066194019319742780851545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37509850718185980748937453 14066194019319742780851545)
  ·
    refine ⟨10549645514489807085638659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14066194019319742780851545 10549645514489807085638659)
    ·
      refine ⟨15824468271734710628457989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10549645514489807085638659 15824468271734710628457989)
      ·
        refine ⟨2967087800950258242835873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15824468271734710628457989 2967087800950258242835873)
        ·
          refine ⟨2225315850712693682126905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2967087800950258242835873 2225315850712693682126905)
          ·
            refine ⟨1668986888034520261595179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2225315850712693682126905 1668986888034520261595179)
            ·
              refine ⟨2503480332051780392392769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1668986888034520261595179 2503480332051780392392769)
              ·
                refine ⟨1877610249038835294294577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2503480332051780392392769 1877610249038835294294577)
                ·
                  refine ⟨1408207686779126470720933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1877610249038835294294577 1408207686779126470720933)
                  ·
                    refine ⟨264038941271086213260175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1408207686779126470720933 264038941271086213260175)
                    ·
                      rfl

theorem cell23_1542642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_1542642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542642 prefixEnd_1542642 := by exact prefixLift 1542642
  have htrace : WordTrace (prefixWord ++ tailWord_1542642) baseStart_1542642 baseEnd_1542642 := by
    simpa [prefixWord, tailWord_1542642, baseEnd_1542642] using wordTrace_append hprefix tailTrace_1542642
  have hstable : (prefixWord ++ tailWord_1542642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542642).length < 2 ^ (prefixWord ++ tailWord_1542642).sum := by decide
  have hdescent : baseEnd_1542642 < baseStart_1542642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542648 : List Nat := [2, 1, 2, 1, 1, 4, 3, 1, 4, 1, 3]
def baseStart_1542648 : Nat := 118140960795 + 1542648 * 2 ^ 59
def prefixEnd_1542648 : Nat := 4983230072969 + 3 ^ 40 * 1542648 * 2
def baseEnd_1542648 : Nat := 792119904697185616305497

theorem tailTrace_1542648 : CollatzResearch.WordTrace tailWord_1542648 prefixEnd_1542648 792119904697185616305497 := by
  unfold tailWord_1542648
  simp only [CollatzResearch.WordTrace]
  refine ⟨28132497457628617074062299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37509996610171489432083065 28132497457628617074062299)
  ·
    refine ⟨42198746186442925611093449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28132497457628617074062299 42198746186442925611093449)
    ·
      refine ⟨31649059639832194208320087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42198746186442925611093449 31649059639832194208320087)
      ·
        refine ⟨47473589459748291312480131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31649059639832194208320087 47473589459748291312480131)
        ·
          refine ⟨71210384189622436968720197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47473589459748291312480131 71210384189622436968720197)
          ·
            refine ⟨13351947035554206931635037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71210384189622436968720197 13351947035554206931635037)
            ·
              refine ⟨5006980138332827599363139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13351947035554206931635037 5006980138332827599363139)
              ·
                refine ⟨7510470207499241399044709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5006980138332827599363139 7510470207499241399044709)
                ·
                  refine ⟨1408213163906107762320883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7510470207499241399044709 1408213163906107762320883)
                  ·
                    refine ⟨2112319745859161643481325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1408213163906107762320883 2112319745859161643481325)
                    ·
                      refine ⟨792119904697185616305497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2112319745859161643481325 792119904697185616305497)
                      ·
                        rfl

theorem cell23_1542648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 4, 1, 3].length) (baseStart_1542648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542648 prefixEnd_1542648 := by exact prefixLift 1542648
  have htrace : WordTrace (prefixWord ++ tailWord_1542648) baseStart_1542648 baseEnd_1542648 := by
    simpa [prefixWord, tailWord_1542648, baseEnd_1542648] using wordTrace_append hprefix tailTrace_1542648
  have hstable : (prefixWord ++ tailWord_1542648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542648).length < 2 ^ (prefixWord ++ tailWord_1542648).sum := by decide
  have hdescent : baseEnd_1542648 < baseStart_1542648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542662 : List Nat := [6, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_1542662 : Nat := 118140960795 + 1542662 * 2 ^ 59
def prefixEnd_1542662 : Nat := 4983230072969 + 3 ^ 40 * 1542662 * 2
def baseEnd_1542662 : Nat := 792127093426348561530433

theorem tailTrace_1542662 : CollatzResearch.WordTrace tailWord_1542662 prefixEnd_1542662 792127093426348561530433 := by
  unfold tailWord_1542662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1758297048037703579347945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37510337024804343026089493 1758297048037703579347945)
  ·
    refine ⟨1318722786028277684510959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1758297048037703579347945 1318722786028277684510959)
    ·
      refine ⟨1978084179042416526766439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1318722786028277684510959 1978084179042416526766439)
      ·
        refine ⟨2967126268563624790149659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1978084179042416526766439 2967126268563624790149659)
        ·
          refine ⟨4450689402845437185224489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2967126268563624790149659 4450689402845437185224489)
          ·
            refine ⟨3338017052134077888918367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4450689402845437185224489 3338017052134077888918367)
            ·
              refine ⟨5007025578201116833377551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3338017052134077888918367 5007025578201116833377551)
              ·
                refine ⟨7510538367301675250066327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5007025578201116833377551 7510538367301675250066327)
                ·
                  refine ⟨11265807550952512875099491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7510538367301675250066327 11265807550952512875099491)
                  ·
                    refine ⟨16898711326428769312649237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11265807550952512875099491 16898711326428769312649237)
                    ·
                      refine ⟨792127093426348561530433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16898711326428769312649237 792127093426348561530433)
                      ·
                        rfl

theorem cell23_1542662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_1542662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542662 prefixEnd_1542662 := by exact prefixLift 1542662
  have htrace : WordTrace (prefixWord ++ tailWord_1542662) baseStart_1542662 baseEnd_1542662 := by
    simpa [prefixWord, tailWord_1542662, baseEnd_1542662] using wordTrace_append hprefix tailTrace_1542662
  have hstable : (prefixWord ++ tailWord_1542662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542662).length < 2 ^ (prefixWord ++ tailWord_1542662).sum := by decide
  have hdescent : baseEnd_1542662 < baseStart_1542662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542669 : List Nat := [1, 7, 1, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_1542669 : Nat := 118140960795 + 1542669 * 2 ^ 59
def prefixEnd_1542669 : Nat := 4983230072969 + 3 ^ 40 * 1542669 * 2
def baseEnd_1542669 : Nat := 792130687790930034142901

theorem tailTrace_1542669 : CollatzResearch.WordTrace tailWord_1542669 prefixEnd_1542669 792130687790930034142901 := by
  unfold tailWord_1542669
  simp only [CollatzResearch.WordTrace]
  refine ⟨56265760848181154734639061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37510507232120769823092707 56265760848181154734639061)
  ·
    refine ⟨1318728769879245814093103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 56265760848181154734639061 1318728769879245814093103)
    ·
      refine ⟨1978093154818868721139655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1318728769879245814093103 1978093154818868721139655)
      ·
        refine ⟨2967139732228303081709483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1978093154818868721139655 2967139732228303081709483)
        ·
          refine ⟨4450709598342454622564225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2967139732228303081709483 4450709598342454622564225)
          ·
            refine ⟨3338032198756840966923169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4450709598342454622564225 3338032198756840966923169)
            ·
              refine ⟨2503524149067630725192377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3338032198756840966923169 2503524149067630725192377)
              ·
                refine ⟨1877643111800723043894283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2503524149067630725192377 1877643111800723043894283)
                ·
                  refine ⟨2816464667701084565841425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1877643111800723043894283 2816464667701084565841425)
                  ·
                    refine ⟨2112348500775813424381069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2816464667701084565841425 2112348500775813424381069)
                    ·
                      refine ⟨792130687790930034142901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2112348500775813424381069 792130687790930034142901)
                      ·
                        rfl

theorem cell23_1542669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_1542669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542669 prefixEnd_1542669 := by exact prefixLift 1542669
  have htrace : WordTrace (prefixWord ++ tailWord_1542669) baseStart_1542669 baseEnd_1542669 := by
    simpa [prefixWord, tailWord_1542669, baseEnd_1542669] using wordTrace_append hprefix tailTrace_1542669
  have hstable : (prefixWord ++ tailWord_1542669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542669).length < 2 ^ (prefixWord ++ tailWord_1542669).sum := by decide
  have hdescent : baseEnd_1542669 < baseStart_1542669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542675 : List Nat := [1, 1, 1, 2, 1, 5, 4, 2, 1, 3, 2]
def baseStart_1542675 : Nat := 118140960795 + 1542675 * 2 ^ 59
def prefixEnd_1542675 : Nat := 4983230072969 + 3 ^ 40 * 1542675 * 2
def baseEnd_1542675 : Nat := 792133768674857010667873

theorem tailTrace_1542675 : CollatzResearch.WordTrace tailWord_1542675 prefixEnd_1542675 792133768674857010667873 := by
  unfold tailWord_1542675
  simp only [CollatzResearch.WordTrace]
  refine ⟨56265979686159417759357479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37510653124106278506238319 56265979686159417759357479)
  ·
    refine ⟨84398969529239126639036219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56265979686159417759357479 84398969529239126639036219)
    ·
      refine ⟨126598454293858689958554329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84398969529239126639036219 126598454293858689958554329)
      ·
        refine ⟨94948840720394017468915747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126598454293858689958554329 94948840720394017468915747)
        ·
          refine ⟨142423261080591026203373621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94948840720394017468915747 142423261080591026203373621)
          ·
            refine ⟨13352180726305408706566277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142423261080591026203373621 13352180726305408706566277)
            ·
              refine ⟨2503533886182264132481177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13352180726305408706566277 2503533886182264132481177)
              ·
                refine ⟨1877650414636698099360883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2503533886182264132481177 1877650414636698099360883)
                ·
                  refine ⟨2816475621955047149041325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1877650414636698099360883 2816475621955047149041325)
                  ·
                    refine ⟨1056178358233142680890497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2816475621955047149041325 1056178358233142680890497)
                    ·
                      refine ⟨792133768674857010667873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1056178358233142680890497 792133768674857010667873)
                      ·
                        rfl

theorem cell23_1542675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 3, 2].length) (baseStart_1542675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542675 prefixEnd_1542675 := by exact prefixLift 1542675
  have htrace : WordTrace (prefixWord ++ tailWord_1542675) baseStart_1542675 baseEnd_1542675 := by
    simpa [prefixWord, tailWord_1542675, baseEnd_1542675] using wordTrace_append hprefix tailTrace_1542675
  have hstable : (prefixWord ++ tailWord_1542675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542675).length < 2 ^ (prefixWord ++ tailWord_1542675).sum := by decide
  have hdescent : baseEnd_1542675 < baseStart_1542675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542691 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 5]
def baseStart_1542691 : Nat := 118140960795 + 1542691 * 2 ^ 59
def prefixEnd_1542691 : Nat := 4983230072969 + 3 ^ 40 * 1542691 * 2
def baseEnd_1542691 : Nat := 792141984365328948067799

theorem tailTrace_1542691 : CollatzResearch.WordTrace tailWord_1542691 prefixEnd_1542691 792141984365328948067799 := by
  unfold tailWord_1542691
  simp only [CollatzResearch.WordTrace]
  refine ⟨56266563254101452491939927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37511042169400968327959951 56266563254101452491939927)
  ·
    refine ⟨84399844881152178737909891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56266563254101452491939927 84399844881152178737909891)
    ·
      refine ⟨126599767321728268106864837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84399844881152178737909891 126599767321728268106864837)
      ·
        refine ⟨23737456372824050270037157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126599767321728268106864837 23737456372824050270037157)
        ·
          refine ⟨4450773069904509425631967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23737456372824050270037157 4450773069904509425631967)
          ·
            refine ⟨6676159604856764138447951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4450773069904509425631967 6676159604856764138447951)
            ·
              refine ⟨10014239407285146207671927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6676159604856764138447951 10014239407285146207671927)
              ·
                refine ⟨15021359110927719311507891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10014239407285146207671927 15021359110927719311507891)
                ·
                  refine ⟨22532038666391578967261837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15021359110927719311507891 22532038666391578967261837)
                  ·
                    refine ⟨8449514499896842112723189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22532038666391578967261837 8449514499896842112723189)
                    ·
                      refine ⟨792141984365328948067799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8449514499896842112723189 792141984365328948067799)
                      ·
                        rfl

theorem cell23_1542691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_1542691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542691 prefixEnd_1542691 := by exact prefixLift 1542691
  have htrace : WordTrace (prefixWord ++ tailWord_1542691) baseStart_1542691 baseEnd_1542691 := by
    simpa [prefixWord, tailWord_1542691, baseEnd_1542691] using wordTrace_append hprefix tailTrace_1542691
  have hstable : (prefixWord ++ tailWord_1542691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542691).length < 2 ^ (prefixWord ++ tailWord_1542691).sum := by decide
  have hdescent : baseEnd_1542691 < baseStart_1542691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542705 : List Nat := [1, 2, 2, 3, 1, 1, 4, 1, 4, 2, 2]
def baseStart_1542705 : Nat := 118140960795 + 1542705 * 2 ^ 59
def prefixEnd_1542705 : Nat := 4983230072969 + 3 ^ 40 * 1542705 * 2
def baseEnd_1542705 : Nat := 792149173094491893292735

theorem tailTrace_1542705 : CollatzResearch.WordTrace tailWord_1542705 prefixEnd_1542705 792149173094491893292735 := by
  unfold tailWord_1542705
  simp only [CollatzResearch.WordTrace]
  refine ⟨56267073876050732882949569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37511382584033821921966379 56267073876050732882949569)
  ·
    refine ⟨42200305407038049662212177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56267073876050732882949569 42200305407038049662212177)
    ·
      refine ⟨31650229055278537246659133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42200305407038049662212177 31650229055278537246659133)
      ·
        refine ⟨11868835895729451467497175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31650229055278537246659133 11868835895729451467497175)
        ·
          refine ⟨17803253843594177201245763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11868835895729451467497175 17803253843594177201245763)
          ·
            refine ⟨26704880765391265801868645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17803253843594177201245763 26704880765391265801868645)
            ·
              refine ⟨5007165143510862337850371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26704880765391265801868645 5007165143510862337850371)
              ·
                refine ⟨7510747715266293506775557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5007165143510862337850371 7510747715266293506775557)
                ·
                  refine ⟨1408265196612430032520417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7510747715266293506775557 1408265196612430032520417)
                  ·
                    refine ⟨1056198897459322524390313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1408265196612430032520417 1056198897459322524390313)
                    ·
                      refine ⟨792149173094491893292735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1056198897459322524390313 792149173094491893292735)
                      ·
                        rfl

theorem cell23_1542705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_1542705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542705 prefixEnd_1542705 := by exact prefixLift 1542705
  have htrace : WordTrace (prefixWord ++ tailWord_1542705) baseStart_1542705 baseEnd_1542705 := by
    simpa [prefixWord, tailWord_1542705, baseEnd_1542705] using wordTrace_append hprefix tailTrace_1542705
  have hstable : (prefixWord ++ tailWord_1542705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542705).length < 2 ^ (prefixWord ++ tailWord_1542705).sum := by decide
  have hdescent : baseEnd_1542705 < baseStart_1542705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542726 : List Nat := [6, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2]
def baseStart_1542726 : Nat := 118140960795 + 1542726 * 2 ^ 59
def prefixEnd_1542726 : Nat := 4983230072969 + 3 ^ 40 * 1542726 * 2
def baseEnd_1542726 : Nat := 792159956188236311130139

theorem tailTrace_1542726 : CollatzResearch.WordTrace tailWord_1542726 prefixEnd_1542726 792159956188236311130139 := by
  unfold tailWord_1542726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1758369994030457920920751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37511893205983102312976021 1758369994030457920920751)
  ·
    refine ⟨2637554991045686881381127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1758369994030457920920751 2637554991045686881381127)
    ·
      refine ⟨3956332486568530322071691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2637554991045686881381127 3956332486568530322071691)
      ·
        refine ⟨5934498729852795483107537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3956332486568530322071691 5934498729852795483107537)
        ·
          refine ⟨4450874047389596612330653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5934498729852795483107537 4450874047389596612330653)
          ·
            refine ⟨1669077767771098729623995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4450874047389596612330653 1669077767771098729623995)
            ·
              refine ⟨2503616651656648094435993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1669077767771098729623995 2503616651656648094435993)
              ·
                refine ⟨1877712488742486070826995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2503616651656648094435993 1877712488742486070826995)
                ·
                  refine ⟨2816568733113729106240493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1877712488742486070826995 2816568733113729106240493)
                  ·
                    refine ⟨1056213274917648414840185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2816568733113729106240493 1056213274917648414840185)
                    ·
                      refine ⟨792159956188236311130139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1056213274917648414840185 792159956188236311130139)
                      ·
                        rfl

theorem cell23_1542726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_1542726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542726 prefixEnd_1542726 := by exact prefixLift 1542726
  have htrace : WordTrace (prefixWord ++ tailWord_1542726) baseStart_1542726 baseEnd_1542726 := by
    simpa [prefixWord, tailWord_1542726, baseEnd_1542726] using wordTrace_append hprefix tailTrace_1542726
  have hstable : (prefixWord ++ tailWord_1542726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542726).length < 2 ^ (prefixWord ++ tailWord_1542726).sum := by decide
  have hdescent : baseEnd_1542726 < baseStart_1542726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542741 : List Nat := [1, 3, 2, 2, 1, 1, 2, 3, 1, 7]
def baseStart_1542741 : Nat := 118140960795 + 1542741 * 2 ^ 59
def prefixEnd_1542741 : Nat := 4983230072969 + 3 ^ 40 * 1542741 * 2
def baseEnd_1542741 : Nat := 264055886132684584147523

theorem tailTrace_1542741 : CollatzResearch.WordTrace tailWord_1542741 prefixEnd_1542741 264055886132684584147523 := by
  unfold tailWord_1542741
  simp only [CollatzResearch.WordTrace]
  refine ⟨56268386903920311031260077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37512257935946874020840051 56268386903920311031260077)
  ·
    refine ⟨21100645088970116636722529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56268386903920311031260077 21100645088970116636722529)
    ·
      refine ⟨15825483816727587477541897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21100645088970116636722529 15825483816727587477541897)
      ·
        refine ⟨11869112862545690608156423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15825483816727587477541897 11869112862545690608156423)
        ·
          refine ⟨17803669293818535912234635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11869112862545690608156423 17803669293818535912234635)
          ·
            refine ⟨26705503940727803868351953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17803669293818535912234635 26705503940727803868351953)
            ·
              refine ⟨20029127955545852901263965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26705503940727803868351953 20029127955545852901263965)
              ·
                refine ⟨7510922983329694837973987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20029127955545852901263965 7510922983329694837973987)
                ·
                  refine ⟨11266384474994542256960981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7510922983329694837973987 11266384474994542256960981)
                  ·
                    refine ⟨264055886132684584147523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11266384474994542256960981 264055886132684584147523)
                    ·
                      rfl

theorem cell23_1542741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_1542741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542741 prefixEnd_1542741 := by exact prefixLift 1542741
  have htrace : WordTrace (prefixWord ++ tailWord_1542741) baseStart_1542741 baseEnd_1542741 := by
    simpa [prefixWord, tailWord_1542741, baseEnd_1542741] using wordTrace_append hprefix tailTrace_1542741
  have hstable : (prefixWord ++ tailWord_1542741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542741).length < 2 ^ (prefixWord ++ tailWord_1542741).sum := by decide
  have hdescent : baseEnd_1542741 < baseStart_1542741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542761 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 3, 3, 4]
def baseStart_1542761 : Nat := 118140960795 + 1542761 * 2 ^ 59
def prefixEnd_1542761 : Nat := 4983230072969 + 3 ^ 40 * 1542761 * 2
def baseEnd_1542761 : Nat := 792177928011143674192477

theorem tailTrace_1542761 : CollatzResearch.WordTrace tailWord_1542761 prefixEnd_1542761 792177928011143674192477 := by
  unfold tailWord_1542761
  simp only [CollatzResearch.WordTrace]
  refine ⟨56269116363847854446988137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37512744242565236297992091 56269116363847854446988137)
  ·
    refine ⟨42201837272885890835241103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56269116363847854446988137 42201837272885890835241103)
    ·
      refine ⟨63302755909328836252861655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42201837272885890835241103 63302755909328836252861655)
      ·
        refine ⟨94954133863993254379292483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63302755909328836252861655 94954133863993254379292483)
        ·
          refine ⟨142431200795989881568938725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94954133863993254379292483 142431200795989881568938725)
          ·
            refine ⟨26705850149248102794176011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142431200795989881568938725 26705850149248102794176011)
            ·
              refine ⟨40058775223872154191264017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26705850149248102794176011 40058775223872154191264017)
              ·
                refine ⟨30044081417904115643448013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40058775223872154191264017 30044081417904115643448013)
                ·
                  refine ⟨11266530531714043366293005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30044081417904115643448013 11266530531714043366293005)
                  ·
                    refine ⟨4224948949392766262359877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11266530531714043366293005 4224948949392766262359877)
                    ·
                      refine ⟨792177928011143674192477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4224948949392766262359877 792177928011143674192477)
                      ·
                        rfl

theorem cell23_1542761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 3, 4].length) (baseStart_1542761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542761 prefixEnd_1542761 := by exact prefixLift 1542761
  have htrace : WordTrace (prefixWord ++ tailWord_1542761) baseStart_1542761 baseEnd_1542761 := by
    simpa [prefixWord, tailWord_1542761, baseEnd_1542761] using wordTrace_append hprefix tailTrace_1542761
  have hstable : (prefixWord ++ tailWord_1542761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542761).length < 2 ^ (prefixWord ++ tailWord_1542761).sum := by decide
  have hdescent : baseEnd_1542761 < baseStart_1542761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542765 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 2, 5, 2]
def baseStart_1542765 : Nat := 118140960795 + 1542765 * 2 ^ 59
def prefixEnd_1542765 : Nat := 4983230072969 + 3 ^ 40 * 1542765 * 2
def baseEnd_1542765 : Nat := 792179981933761658542459

theorem tailTrace_1542765 : CollatzResearch.WordTrace tailWord_1542765 prefixEnd_1542765 792179981933761658542459 := by
  unfold tailWord_1542765
  simp only [CollatzResearch.WordTrace]
  refine ⟨56269262255833363130133749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37512841503888908753422499 56269262255833363130133749)
  ·
    refine ⟨5275243336484377793450039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56269262255833363130133749 5275243336484377793450039)
    ·
      refine ⟨7912865004726566690175059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5275243336484377793450039 7912865004726566690175059)
      ·
        refine ⟨11869297507089850035262589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7912865004726566690175059 11869297507089850035262589)
        ·
          refine ⟨4450986565158693763223471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11869297507089850035262589 4450986565158693763223471)
          ·
            refine ⟨6676479847738040644835207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4450986565158693763223471 6676479847738040644835207)
            ·
              refine ⟨10014719771607060967252811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6676479847738040644835207 10014719771607060967252811)
              ·
                refine ⟨15022079657410591450879217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10014719771607060967252811 15022079657410591450879217)
                ·
                  refine ⟨11266559743057943588159413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15022079657410591450879217 11266559743057943588159413)
                  ·
                    refine ⟨1056239975911682211389945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11266559743057943588159413 1056239975911682211389945)
                    ·
                      refine ⟨792179981933761658542459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1056239975911682211389945 792179981933761658542459)
                      ·
                        rfl

theorem cell23_1542765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_1542765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542765 prefixEnd_1542765 := by exact prefixLift 1542765
  have htrace : WordTrace (prefixWord ++ tailWord_1542765) baseStart_1542765 baseEnd_1542765 := by
    simpa [prefixWord, tailWord_1542765, baseEnd_1542765] using wordTrace_append hprefix tailTrace_1542765
  have hstable : (prefixWord ++ tailWord_1542765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542765).length < 2 ^ (prefixWord ++ tailWord_1542765).sum := by decide
  have hdescent : baseEnd_1542765 < baseStart_1542765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542835 : List Nat := [1, 1, 1, 2, 3, 5, 3, 1, 6]
def baseStart_1542835 : Nat := 118140960795 + 1542835 * 2 ^ 59
def prefixEnd_1542835 : Nat := 4983230072969 + 3 ^ 40 * 1542835 * 2
def baseEnd_1542835 : Nat := 88023991731064042740793

theorem tailTrace_1542835 : CollatzResearch.WordTrace tailWord_1542835 prefixEnd_1542835 88023991731064042740793 := by
  unfold tailWord_1542835
  simp only [CollatzResearch.WordTrace]
  refine ⟨56271815365579765085181959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37514543577053176723454639 56271815365579765085181959)
  ·
    refine ⟨84407723048369647627772939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56271815365579765085181959 84407723048369647627772939)
    ·
      refine ⟨126611584572554471441659409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84407723048369647627772939 126611584572554471441659409)
      ·
        refine ⟨94958688429415853581244557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126611584572554471441659409 94958688429415853581244557)
        ·
          refine ⟨35609508161030945092966709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94958688429415853581244557 35609508161030945092966709)
          ·
            refine ⟨3338391390096651102465629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35609508161030945092966709 3338391390096651102465629)
            ·
              refine ⟨1251896771286244163424611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3338391390096651102465629 1251896771286244163424611)
              ·
                refine ⟨1877845156929366245136917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1251896771286244163424611 1877845156929366245136917)
                ·
                  refine ⟨88023991731064042740793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1877845156929366245136917 88023991731064042740793)
                  ·
                    rfl

theorem cell23_1542835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 6].length) (baseStart_1542835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542835 prefixEnd_1542835 := by exact prefixLift 1542835
  have htrace : WordTrace (prefixWord ++ tailWord_1542835) baseStart_1542835 baseEnd_1542835 := by
    simpa [prefixWord, tailWord_1542835, baseEnd_1542835] using wordTrace_append hprefix tailTrace_1542835
  have hstable : (prefixWord ++ tailWord_1542835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542835).length < 2 ^ (prefixWord ++ tailWord_1542835).sum := by decide
  have hdescent : baseEnd_1542835 < baseStart_1542835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542872 : List Nat := [2, 1, 2, 2, 3, 3, 1, 2, 2, 3, 2]
def baseStart_1542872 : Nat := 118140960795 + 1542872 * 2 ^ 59
def prefixEnd_1542872 : Nat := 4983230072969 + 3 ^ 40 * 1542872 * 2
def baseEnd_1542872 : Nat := 792234924363792739904467

theorem tailTrace_1542872 : CollatzResearch.WordTrace tailWord_1542872 prefixEnd_1542872 792234924363792739904467 := by
  unfold tailWord_1542872
  simp only [CollatzResearch.WordTrace]
  refine ⟨28136582433222860202139435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37515443244297146936185913 28136582433222860202139435)
  ·
    refine ⟨42204873649834290303209153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28136582433222860202139435 42204873649834290303209153)
    ·
      refine ⟨31653655237375717727406865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42204873649834290303209153 31653655237375717727406865)
      ·
        refine ⟨23740241428031788295555149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31653655237375717727406865 23740241428031788295555149)
        ·
          refine ⟨8902590535511920610833181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23740241428031788295555149 8902590535511920610833181)
          ·
            refine ⟨3338471450816970229062443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8902590535511920610833181 3338471450816970229062443)
            ·
              refine ⟨5007707176225455343593665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3338471450816970229062443 5007707176225455343593665)
              ·
                refine ⟨3755780382169091507695249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5007707176225455343593665 3755780382169091507695249)
                ·
                  refine ⟨2816835286626818630771437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3755780382169091507695249 2816835286626818630771437)
                  ·
                    refine ⟨1056313232485056986539289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2816835286626818630771437 1056313232485056986539289)
                    ·
                      refine ⟨792234924363792739904467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1056313232485056986539289 792234924363792739904467)
                      ·
                        rfl

theorem cell23_1542872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 2, 3, 2].length) (baseStart_1542872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542872 prefixEnd_1542872 := by exact prefixLift 1542872
  have htrace : WordTrace (prefixWord ++ tailWord_1542872) baseStart_1542872 baseEnd_1542872 := by
    simpa [prefixWord, tailWord_1542872, baseEnd_1542872] using wordTrace_append hprefix tailTrace_1542872
  have hstable : (prefixWord ++ tailWord_1542872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542872).length < 2 ^ (prefixWord ++ tailWord_1542872).sum := by decide
  have hdescent : baseEnd_1542872 < baseStart_1542872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542908 : List Nat := [2, 2, 2, 1, 3, 2, 2, 9]
def baseStart_1542908 : Nat := 118140960795 + 1542908 * 2 ^ 59
def prefixEnd_1542908 : Nat := 4983230072969 + 3 ^ 40 * 1542908 * 2
def baseEnd_1542908 : Nat := 29342718876568688853863

theorem tailTrace_1542908 : CollatzResearch.WordTrace tailWord_1542908 prefixEnd_1542908 29342718876568688853863 := by
  unfold tailWord_1542908
  simp only [CollatzResearch.WordTrace]
  refine ⟨28137238947157649276294689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37516318596210199035059585 28137238947157649276294689)
  ·
    refine ⟨21102929210368236957221017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28137238947157649276294689 21102929210368236957221017)
    ·
      refine ⟨15827196907776177717915763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21102929210368236957221017 15827196907776177717915763)
      ·
        refine ⟨23740795361664266576873645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15827196907776177717915763 23740795361664266576873645)
        ·
          refine ⟨8902798260624099966327617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23740795361664266576873645 8902798260624099966327617)
          ·
            refine ⟨6677098695468074974745713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8902798260624099966327617 6677098695468074974745713)
            ·
              refine ⟨5007824021601056231059285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6677098695468074974745713 5007824021601056231059285)
              ·
                refine ⟨29342718876568688853863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5007824021601056231059285 29342718876568688853863)
                ·
                  rfl

theorem cell23_1542908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 9].length) (baseStart_1542908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542908 prefixEnd_1542908 := by exact prefixLift 1542908
  have htrace : WordTrace (prefixWord ++ tailWord_1542908) baseStart_1542908 baseEnd_1542908 := by
    simpa [prefixWord, tailWord_1542908, baseEnd_1542908] using wordTrace_append hprefix tailTrace_1542908
  have hstable : (prefixWord ++ tailWord_1542908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542908).length < 2 ^ (prefixWord ++ tailWord_1542908).sum := by decide
  have hdescent : baseEnd_1542908 < baseStart_1542908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542919 : List Nat := [1, 1, 4, 4, 1, 2, 3, 1, 1, 1, 4]
def baseStart_1542919 : Nat := 118140960795 + 1542919 * 2 ^ 59
def prefixEnd_1542919 : Nat := 4983230072969 + 3 ^ 40 * 1542919 * 2
def baseEnd_1542919 : Nat := 792259057954554056016751

theorem tailTrace_1542919 : CollatzResearch.WordTrace tailWord_1542919 prefixEnd_1542919 792259057954554056016751 := by
  unfold tailWord_1542919
  simp only [CollatzResearch.WordTrace]
  refine ⟨56274879097275447431239811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37516586064850298287493207 56274879097275447431239811)
  ·
    refine ⟨84412318645913171146859717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56274879097275447431239811 84412318645913171146859717)
    ·
      refine ⟨15827309746108719590036197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84412318645913171146859717 15827309746108719590036197)
      ·
        refine ⟨2967620577395384923131787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15827309746108719590036197 2967620577395384923131787)
        ·
          refine ⟨4451430866093077384697681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2967620577395384923131787 4451430866093077384697681)
          ·
            refine ⟨3338573149569808038523261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4451430866093077384697681 3338573149569808038523261)
            ·
              refine ⟨1251964931088678014446223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3338573149569808038523261 1251964931088678014446223)
              ·
                refine ⟨1877947396633017021669335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1251964931088678014446223 1877947396633017021669335)
                ·
                  refine ⟨2816921094949525532504003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1877947396633017021669335 2816921094949525532504003)
                  ·
                    refine ⟨4225381642424288298756005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2816921094949525532504003 4225381642424288298756005)
                    ·
                      refine ⟨792259057954554056016751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4225381642424288298756005 792259057954554056016751)
                      ·
                        rfl

theorem cell23_1542919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_1542919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542919 prefixEnd_1542919 := by exact prefixLift 1542919
  have htrace : WordTrace (prefixWord ++ tailWord_1542919) baseStart_1542919 baseEnd_1542919 := by
    simpa [prefixWord, tailWord_1542919, baseEnd_1542919] using wordTrace_append hprefix tailTrace_1542919
  have hstable : (prefixWord ++ tailWord_1542919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542919).length < 2 ^ (prefixWord ++ tailWord_1542919).sum := by decide
  have hdescent : baseEnd_1542919 < baseStart_1542919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542930 : List Nat := [3, 2, 4, 1, 2, 2, 2, 2, 1, 1, 3]
def baseStart_1542930 : Nat := 118140960795 + 1542930 * 2 ^ 59
def prefixEnd_1542930 : Nat := 4983230072969 + 3 ^ 40 * 1542930 * 2
def baseEnd_1542930 : Nat := 792264706241753512979201

theorem tailTrace_1542930 : CollatzResearch.WordTrace tailWord_1542930 prefixEnd_1542930 792264706241753512979201 := by
  unfold tailWord_1542930
  simp only [CollatzResearch.WordTrace]
  refine ⟨14068820075058899077472561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37516853533490397539926829 14068820075058899077472561)
  ·
    refine ⟨10551615056294174308104421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14068820075058899077472561 10551615056294174308104421)
    ·
      refine ⟨1978427823055157682769579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10551615056294174308104421 1978427823055157682769579)
      ·
        refine ⟨2967641734582736524154369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1978427823055157682769579 2967641734582736524154369)
        ·
          refine ⟨2225731300937052393115777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2967641734582736524154369 2225731300937052393115777)
          ·
            refine ⟨1669298475702789294836833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2225731300937052393115777 1669298475702789294836833)
            ·
              refine ⟨1251973856777091971127625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1669298475702789294836833 1251973856777091971127625)
              ·
                refine ⟨938980392582818978345719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1251973856777091971127625 938980392582818978345719)
                ·
                  refine ⟨1408470588874228467518579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 938980392582818978345719 1408470588874228467518579)
                  ·
                    refine ⟨2112705883311342701277869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1408470588874228467518579 2112705883311342701277869)
                    ·
                      refine ⟨792264706241753512979201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2112705883311342701277869 792264706241753512979201)
                      ·
                        rfl

theorem cell23_1542930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_1542930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542930 prefixEnd_1542930 := by exact prefixLift 1542930
  have htrace : WordTrace (prefixWord ++ tailWord_1542930) baseStart_1542930 baseEnd_1542930 := by
    simpa [prefixWord, tailWord_1542930, baseEnd_1542930] using wordTrace_append hprefix tailTrace_1542930
  have hstable : (prefixWord ++ tailWord_1542930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542930).length < 2 ^ (prefixWord ++ tailWord_1542930).sum := by decide
  have hdescent : baseEnd_1542930 < baseStart_1542930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542938 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 1, 9]
def baseStart_1542938 : Nat := 118140960795 + 1542938 * 2 ^ 59
def prefixEnd_1542938 : Nat := 4983230072969 + 3 ^ 40 * 1542938 * 2
def baseEnd_1542938 : Nat := 264089604695663160559721

theorem tailTrace_1542938 : CollatzResearch.WordTrace tailWord_1542938 prefixEnd_1542938 264089604695663160559721 := by
  unfold tailWord_1542938
  simp only [CollatzResearch.WordTrace]
  refine ⟨14068893021051653419045367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37517048056137742450787645 14068893021051653419045367)
  ·
    refine ⟨21103339531577480128568051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14068893021051653419045367 21103339531577480128568051)
    ·
      refine ⟨31655009297366220192852077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21103339531577480128568051 31655009297366220192852077)
      ·
        refine ⟨11870628486512332572319529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31655009297366220192852077 11870628486512332572319529)
        ·
          refine ⟨8902971364884249429239647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11870628486512332572319529 8902971364884249429239647)
          ·
            refine ⟨13354457047326374143859471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8902971364884249429239647 13354457047326374143859471)
            ·
              refine ⟨20031685570989561215789207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13354457047326374143859471 20031685570989561215789207)
              ·
                refine ⟨30047528356484341823683811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20031685570989561215789207 30047528356484341823683811)
                ·
                  refine ⟨45071292534726512735525717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30047528356484341823683811 45071292534726512735525717)
                  ·
                    refine ⟨264089604695663160559721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 45071292534726512735525717 264089604695663160559721)
                    ·
                      rfl

theorem cell23_1542938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 1, 9].length) (baseStart_1542938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542938 prefixEnd_1542938 := by exact prefixLift 1542938
  have htrace : WordTrace (prefixWord ++ tailWord_1542938) baseStart_1542938 baseEnd_1542938 := by
    simpa [prefixWord, tailWord_1542938, baseEnd_1542938] using wordTrace_append hprefix tailTrace_1542938
  have hstable : (prefixWord ++ tailWord_1542938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542938).length < 2 ^ (prefixWord ++ tailWord_1542938).sum := by decide
  have hdescent : baseEnd_1542938 < baseStart_1542938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542952 : List Nat := [2, 1, 5, 1, 1, 1, 4, 1, 1, 3, 3]
def baseStart_1542952 : Nat := 118140960795 + 1542952 * 2 ^ 59
def prefixEnd_1542952 : Nat := 4983230072969 + 3 ^ 40 * 1542952 * 2
def baseEnd_1542952 : Nat := 792276002816152426904099

theorem tailTrace_1542952 : CollatzResearch.WordTrace tailWord_1542952 prefixEnd_1542952 792276002816152426904099 := by
  unfold tailWord_1542952
  simp only [CollatzResearch.WordTrace]
  refine ⟨28138041353077947033595555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37517388470770596044794073 28138041353077947033595555)
  ·
    refine ⟨42207062029616920550393333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28138041353077947033595555 42207062029616920550393333)
    ·
      refine ⟨3956912065276586301599375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42207062029616920550393333 3956912065276586301599375)
      ·
        refine ⟨5935368097914879452399063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3956912065276586301599375 5935368097914879452399063)
        ·
          refine ⟨8903052146872319178598595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5935368097914879452399063 8903052146872319178598595)
          ·
            refine ⟨13354578220308478767897893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8903052146872319178598595 13354578220308478767897893)
            ·
              refine ⟨2503983416307839768980855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13354578220308478767897893 2503983416307839768980855)
              ·
                refine ⟨3755975124461759653471283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2503983416307839768980855 3755975124461759653471283)
                ·
                  refine ⟨5633962686692639480206925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3755975124461759653471283 5633962686692639480206925)
                  ·
                    refine ⟨2112736007509739805077597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5633962686692639480206925 2112736007509739805077597)
                    ·
                      refine ⟨792276002816152426904099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2112736007509739805077597 792276002816152426904099)
                      ·
                        rfl

theorem cell23_1542952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_1542952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542952 prefixEnd_1542952 := by exact prefixLift 1542952
  have htrace : WordTrace (prefixWord ++ tailWord_1542952) baseStart_1542952 baseEnd_1542952 := by
    simpa [prefixWord, tailWord_1542952, baseEnd_1542952] using wordTrace_append hprefix tailTrace_1542952
  have hstable : (prefixWord ++ tailWord_1542952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542952).length < 2 ^ (prefixWord ++ tailWord_1542952).sum := by decide
  have hdescent : baseEnd_1542952 < baseStart_1542952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542962 : List Nat := [3, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2]
def baseStart_1542962 : Nat := 118140960795 + 1542962 * 2 ^ 59
def prefixEnd_1542962 : Nat := 4983230072969 + 3 ^ 40 * 1542962 * 2
def baseEnd_1542962 : Nat := 792281137622697387779053

theorem tailTrace_1542962 : CollatzResearch.WordTrace tailWord_1542962 prefixEnd_1542962 792281137622697387779053 := by
  unfold tailWord_1542962
  simp only [CollatzResearch.WordTrace]
  refine ⟨14069111859029916443763785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37517631624079777183370093 14069111859029916443763785)
  ·
    refine ⟨10551833894272437332822839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14069111859029916443763785 10551833894272437332822839)
    ·
      refine ⟨15827750841408655999234259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10551833894272437332822839 15827750841408655999234259)
      ·
        refine ⟨23741626262112983998851389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15827750841408655999234259 23741626262112983998851389)
        ·
          refine ⟨8903109848292368999569271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23741626262112983998851389 8903109848292368999569271)
          ·
            refine ⟨13354664772438553499353907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8903109848292368999569271 13354664772438553499353907)
            ·
              refine ⟨20031997158657830249030861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13354664772438553499353907 20031997158657830249030861)
              ·
                refine ⟨7511998934496686343386573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20031997158657830249030861 7511998934496686343386573)
                ·
                  refine ⟨2816999600436257378769965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7511998934496686343386573 2816999600436257378769965)
                  ·
                    refine ⟨1056374850163596517038737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2816999600436257378769965 1056374850163596517038737)
                    ·
                      refine ⟨792281137622697387779053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1056374850163596517038737 792281137622697387779053)
                      ·
                        rfl

theorem cell23_1542962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2].length) (baseStart_1542962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542962 prefixEnd_1542962 := by exact prefixLift 1542962
  have htrace : WordTrace (prefixWord ++ tailWord_1542962) baseStart_1542962 baseEnd_1542962 := by
    simpa [prefixWord, tailWord_1542962, baseEnd_1542962] using wordTrace_append hprefix tailTrace_1542962
  have hstable : (prefixWord ++ tailWord_1542962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542962).length < 2 ^ (prefixWord ++ tailWord_1542962).sum := by decide
  have hdescent : baseEnd_1542962 < baseStart_1542962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542968 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 1, 8]
def baseStart_1542968 : Nat := 118140960795 + 1542968 * 2 ^ 59
def prefixEnd_1542968 : Nat := 4983230072969 + 3 ^ 40 * 1542968 * 2
def baseEnd_1542968 : Nat := 264094739502208121434675

theorem tailTrace_1542968 : CollatzResearch.WordTrace tailWord_1542968 prefixEnd_1542968 264094739502208121434675 := by
  unfold tailWord_1542968
  simp only [CollatzResearch.WordTrace]
  refine ⟨28138333137048964399886779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37517777516065285866515705 28138333137048964399886779)
  ·
    refine ⟨42207499705573446599830169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28138333137048964399886779 42207499705573446599830169)
    ·
      refine ⟨31655624779180084949872627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42207499705573446599830169 31655624779180084949872627)
      ·
        refine ⟨47483437168770127424808941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31655624779180084949872627 47483437168770127424808941)
        ·
          refine ⟨17806288938288797784303353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47483437168770127424808941 17806288938288797784303353)
          ·
            refine ⟨13354716703716598338227515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17806288938288797784303353 13354716703716598338227515)
            ·
              refine ⟨20032075055574897507341273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13354716703716598338227515 20032075055574897507341273)
              ·
                refine ⟨15024056291681173130505955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20032075055574897507341273 15024056291681173130505955)
                ·
                  refine ⟨22536084437521759695758933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15024056291681173130505955 22536084437521759695758933)
                  ·
                    refine ⟨264094739502208121434675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 22536084437521759695758933 264094739502208121434675)
                    ·
                      rfl

theorem cell23_1542968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 1, 8].length) (baseStart_1542968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542968 prefixEnd_1542968 := by exact prefixLift 1542968
  have htrace : WordTrace (prefixWord ++ tailWord_1542968) baseStart_1542968 baseEnd_1542968 := by
    simpa [prefixWord, tailWord_1542968, baseEnd_1542968] using wordTrace_append hprefix tailTrace_1542968
  have hstable : (prefixWord ++ tailWord_1542968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542968).length < 2 ^ (prefixWord ++ tailWord_1542968).sum := by decide
  have hdescent : baseEnd_1542968 < baseStart_1542968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542973 : List Nat := [1, 4, 1, 4, 3, 1, 2, 1, 1, 2, 3]
def baseStart_1542973 : Nat := 118140960795 + 1542973 * 2 ^ 59
def prefixEnd_1542973 : Nat := 4983230072969 + 3 ^ 40 * 1542973 * 2
def baseEnd_1542973 : Nat := 792286785909896844741503

theorem tailTrace_1542973 : CollatzResearch.WordTrace tailWord_1542973 prefixEnd_1542973 792286785909896844741503 := by
  unfold tailWord_1542973
  simp only [CollatzResearch.WordTrace]
  refine ⟨56276848639079814653705573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37517899092719876435803715 56276848639079814653705573)
  ·
    refine ⟨10551909119827465247569795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56276848639079814653705573 10551909119827465247569795)
    ·
      refine ⟨15827863679741197871354693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10551909119827465247569795 15827863679741197871354693)
      ·
        refine ⟨2967724439951474600879005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15827863679741197871354693 2967724439951474600879005)
        ·
          refine ⟨1112896664981802975329627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2967724439951474600879005 1112896664981802975329627)
          ·
            refine ⟨1669344997472704462994441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1112896664981802975329627 1669344997472704462994441)
            ·
              refine ⟨1252008748104528347245831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1669344997472704462994441 1252008748104528347245831)
              ·
                refine ⟨1878013122156792520868747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1252008748104528347245831 1878013122156792520868747)
                ·
                  refine ⟨2817019683235188781303121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1878013122156792520868747 2817019683235188781303121)
                  ·
                    refine ⟨2112764762426391585977341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2817019683235188781303121 2112764762426391585977341)
                    ·
                      refine ⟨792286785909896844741503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2112764762426391585977341 792286785909896844741503)
                      ·
                        rfl

theorem cell23_1542973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_1542973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1542973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1542973 prefixEnd_1542973 := by exact prefixLift 1542973
  have htrace : WordTrace (prefixWord ++ tailWord_1542973) baseStart_1542973 baseEnd_1542973 := by
    simpa [prefixWord, tailWord_1542973, baseEnd_1542973] using wordTrace_append hprefix tailTrace_1542973
  have hstable : (prefixWord ++ tailWord_1542973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542973).length < 2 ^ (prefixWord ++ tailWord_1542973).sum := by decide
  have hdescent : baseEnd_1542973 < baseStart_1542973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543015 : List Nat := [1, 1, 5, 1, 2, 2, 2, 2, 7]
def baseStart_1543015 : Nat := 118140960795 + 1543015 * 2 ^ 59
def prefixEnd_1543015 : Nat := 4983230072969 + 3 ^ 40 * 1543015 * 2
def baseEnd_1543015 : Nat := 88034261344153964490701

theorem tailTrace_1543015 : CollatzResearch.WordTrace tailWord_1543015 prefixEnd_1543015 88034261344153964490701 := by
  unfold tailWord_1543015
  simp only [CollatzResearch.WordTrace]
  refine ⟨56278380504927655826734499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37518920336618437217822999 56278380504927655826734499)
  ·
    refine ⟨84417570757391483740101749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56278380504927655826734499 84417570757391483740101749)
    ·
      refine ⟨7914147258505451600634539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84417570757391483740101749 7914147258505451600634539)
      ·
        refine ⟨11871220887758177400951809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7914147258505451600634539 11871220887758177400951809)
        ·
          refine ⟨8903415665818633050713857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11871220887758177400951809 8903415665818633050713857)
          ·
            refine ⟨6677561749363974788035393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8903415665818633050713857 6677561749363974788035393)
            ·
              refine ⟨5008171312022981091026545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6677561749363974788035393 5008171312022981091026545)
              ·
                refine ⟨3756128484017235818269909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5008171312022981091026545 3756128484017235818269909)
                ·
                  refine ⟨88034261344153964490701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3756128484017235818269909 88034261344153964490701)
                  ·
                    rfl

theorem cell23_1543015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 7].length) (baseStart_1543015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543015 prefixEnd_1543015 := by exact prefixLift 1543015
  have htrace : WordTrace (prefixWord ++ tailWord_1543015) baseStart_1543015 baseEnd_1543015 := by
    simpa [prefixWord, tailWord_1543015, baseEnd_1543015] using wordTrace_append hprefix tailTrace_1543015
  have hstable : (prefixWord ++ tailWord_1543015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543015).length < 2 ^ (prefixWord ++ tailWord_1543015).sum := by decide
  have hdescent : baseEnd_1543015 < baseStart_1543015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543045 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 4, 5]
def baseStart_1543045 : Nat := 118140960795 + 1543045 * 2 ^ 59
def prefixEnd_1543045 : Nat := 4983230072969 + 3 ^ 40 * 1543045 * 2
def baseEnd_1543045 : Nat := 264107918839006854347057

theorem tailTrace_1543045 : CollatzResearch.WordTrace tailWord_1543045 prefixEnd_1543045 264107918839006854347057 := by
  unfold tailWord_1543045
  simp only [CollatzResearch.WordTrace]
  refine ⟨56279474694818970950326589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37519649796545980633551059 56279474694818970950326589)
  ·
    refine ⟨21104803010557114106372471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56279474694818970950326589 21104803010557114106372471)
    ·
      refine ⟨31657204515835671159558707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21104803010557114106372471 31657204515835671159558707)
      ·
        refine ⟨47485806773753506739338061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31657204515835671159558707 47485806773753506739338061)
        ·
          refine ⟨17807177540157565027251773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47485806773753506739338061 17807177540157565027251773)
          ·
            refine ⟨6677691577559086885219415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17807177540157565027251773 6677691577559086885219415)
            ·
              refine ⟨10016537366338630327829123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6677691577559086885219415 10016537366338630327829123)
              ·
                refine ⟨15024806049507945491743685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10016537366338630327829123 15024806049507945491743685)
                ·
                  refine ⟨2817151134282739779701941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15024806049507945491743685 2817151134282739779701941)
                  ·
                    refine ⟨264107918839006854347057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2817151134282739779701941 264107918839006854347057)
                    ·
                      rfl

theorem cell23_1543045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 5].length) (baseStart_1543045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543045 prefixEnd_1543045 := by exact prefixLift 1543045
  have htrace : WordTrace (prefixWord ++ tailWord_1543045) baseStart_1543045 baseEnd_1543045 := by
    simpa [prefixWord, tailWord_1543045, baseEnd_1543045] using wordTrace_append hprefix tailTrace_1543045
  have hstable : (prefixWord ++ tailWord_1543045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543045).length < 2 ^ (prefixWord ++ tailWord_1543045).sum := by decide
  have hdescent : baseEnd_1543045 < baseStart_1543045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543049 : List Nat := [1, 2, 1, 1, 5, 3, 3, 2, 5]
def baseStart_1543049 : Nat := 118140960795 + 1543049 * 2 ^ 59
def prefixEnd_1543049 : Nat := 4983230072969 + 3 ^ 40 * 1543049 * 2
def baseEnd_1543049 : Nat := 88036201159959838599017

theorem tailTrace_1543049 : CollatzResearch.WordTrace tailWord_1543049 prefixEnd_1543049 88036201159959838599017 := by
  unfold tailWord_1543049
  simp only [CollatzResearch.WordTrace]
  refine ⟨56279620586804479633472201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37519747057869653088981467 56279620586804479633472201)
  ·
    refine ⟨42209715440103359725104151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56279620586804479633472201 42209715440103359725104151)
    ·
      refine ⟨63314573160155039587656227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42209715440103359725104151 63314573160155039587656227)
      ·
        refine ⟨94971859740232559381484341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63314573160155039587656227 94971859740232559381484341)
        ·
          refine ⟨8903611850646802442014157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94971859740232559381484341 8903611850646802442014157)
          ·
            refine ⟨3338854443992550915755309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8903611850646802442014157 3338854443992550915755309)
            ·
              refine ⟨1252070416497206593408241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3338854443992550915755309 1252070416497206593408241)
              ·
                refine ⟨939052812372904945056181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1252070416497206593408241 939052812372904945056181)
                ·
                  refine ⟨88036201159959838599017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 939052812372904945056181 88036201159959838599017)
                  ·
                    rfl

theorem cell23_1543049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 2, 5].length) (baseStart_1543049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543049 prefixEnd_1543049 := by exact prefixLift 1543049
  have htrace : WordTrace (prefixWord ++ tailWord_1543049) baseStart_1543049 baseEnd_1543049 := by
    simpa [prefixWord, tailWord_1543049, baseEnd_1543049] using wordTrace_append hprefix tailTrace_1543049
  have hstable : (prefixWord ++ tailWord_1543049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543049).length < 2 ^ (prefixWord ++ tailWord_1543049).sum := by decide
  have hdescent : baseEnd_1543049 < baseStart_1543049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543065 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 6, 1, 4]
def baseStart_1543065 : Nat := 118140960795 + 1543065 * 2 ^ 59
def prefixEnd_1543065 : Nat := 4983230072969 + 3 ^ 40 * 1543065 * 2
def baseEnd_1543065 : Nat := 792334026130110484791079

theorem tailTrace_1543065 : CollatzResearch.WordTrace tailWord_1543065 prefixEnd_1543065 792334026130110484791079 := by
  unfold tailWord_1543065
  simp only [CollatzResearch.WordTrace]
  refine ⟨56280204154746514366054649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37520136103164342910703099 56280204154746514366054649)
  ·
    refine ⟨42210153116059885774540987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56280204154746514366054649 42210153116059885774540987)
    ·
      refine ⟨63315229674089828661811481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42210153116059885774540987 63315229674089828661811481)
      ·
        refine ⟨47486422255567371496358611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63315229674089828661811481 47486422255567371496358611)
        ·
          refine ⟨71229633383351057244537917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47486422255567371496358611 71229633383351057244537917)
          ·
            refine ⟨26711112518756646466701719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71229633383351057244537917 26711112518756646466701719)
            ·
              refine ⟨40066668778134969700052579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26711112518756646466701719 40066668778134969700052579)
              ·
                refine ⟨60100003167202454550078869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40066668778134969700052579 60100003167202454550078869)
                ·
                  refine ⟨2817187648462615057034947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60100003167202454550078869 2817187648462615057034947)
                  ·
                    refine ⟨4225781472693922585552421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2817187648462615057034947 4225781472693922585552421)
                    ·
                      refine ⟨792334026130110484791079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4225781472693922585552421 792334026130110484791079)
                      ·
                        rfl

theorem cell23_1543065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_1543065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543065 prefixEnd_1543065 := by exact prefixLift 1543065
  have htrace : WordTrace (prefixWord ++ tailWord_1543065) baseStart_1543065 baseEnd_1543065 := by
    simpa [prefixWord, tailWord_1543065, baseEnd_1543065] using wordTrace_append hprefix tailTrace_1543065
  have hstable : (prefixWord ++ tailWord_1543065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543065).length < 2 ^ (prefixWord ++ tailWord_1543065).sum := by decide
  have hdescent : baseEnd_1543065 < baseStart_1543065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543079 : List Nat := [1, 1, 6, 1, 3, 1, 2, 1, 2, 5]
def baseStart_1543079 : Nat := 118140960795 + 1543079 * 2 ^ 59
def prefixEnd_1543079 : Nat := 4983230072969 + 3 ^ 40 * 1543079 * 2
def baseEnd_1543079 : Nat := 264113738286424476672005

theorem tailTrace_1543079 : CollatzResearch.WordTrace tailWord_1543079 prefixEnd_1543079 264113738286424476672005 := by
  unfold tailWord_1543079
  simp only [CollatzResearch.WordTrace]
  refine ⟨56280714776695794757064291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37520476517797196504709527 56280714776695794757064291)
  ·
    refine ⟨84421072165043692135596437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56280714776695794757064291 84421072165043692135596437)
    ·
      refine ⟨3957237757736423068856083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 84421072165043692135596437 3957237757736423068856083)
      ·
        refine ⟨5935856636604634603284125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3957237757736423068856083 5935856636604634603284125)
        ·
          refine ⟨2225946238726737976231547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5935856636604634603284125 2225946238726737976231547)
          ·
            refine ⟨3338919358090106964347321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2225946238726737976231547 3338919358090106964347321)
            ·
              refine ⟨2504189518567580223260491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3338919358090106964347321 2504189518567580223260491)
              ·
                refine ⟨3756284277851370334890737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2504189518567580223260491 3756284277851370334890737)
                ·
                  refine ⟨2817213208388527751168053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3756284277851370334890737 2817213208388527751168053)
                  ·
                    refine ⟨264113738286424476672005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2817213208388527751168053 264113738286424476672005)
                    ·
                      rfl

theorem cell23_1543079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_1543079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543079 prefixEnd_1543079 := by exact prefixLift 1543079
  have htrace : WordTrace (prefixWord ++ tailWord_1543079) baseStart_1543079 baseEnd_1543079 := by
    simpa [prefixWord, tailWord_1543079, baseEnd_1543079] using wordTrace_append hprefix tailTrace_1543079
  have hstable : (prefixWord ++ tailWord_1543079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543079).length < 2 ^ (prefixWord ++ tailWord_1543079).sum := by decide
  have hdescent : baseEnd_1543079 < baseStart_1543079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543110 : List Nat := [6, 1, 3, 1, 1, 1, 1, 1, 2, 3, 3]
def baseStart_1543110 : Nat := 118140960795 + 1543110 * 2 ^ 59
def prefixEnd_1543110 : Nat := 4983230072969 + 3 ^ 40 * 1543110 * 2
def baseEnd_1543110 : Nat := 792357132759562808728373

theorem tailTrace_1543110 : CollatzResearch.WordTrace tailWord_1543110 prefixEnd_1543110 792357132759562808728373 := by
  unfold tailWord_1543110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1758807669986983970357587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37521230293055658034295189 1758807669986983970357587)
  ·
    refine ⟨2638211504980475955536381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1758807669986983970357587 2638211504980475955536381)
    ·
      refine ⟨989329314367678483326143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2638211504980475955536381 989329314367678483326143)
      ·
        refine ⟨1483993971551517724989215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 989329314367678483326143 1483993971551517724989215)
        ·
          refine ⟨2225990957327276587483823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1483993971551517724989215 2225990957327276587483823)
          ·
            refine ⟨3338986435990914881225735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2225990957327276587483823 3338986435990914881225735)
            ·
              refine ⟨5008479653986372321838603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3338986435990914881225735 5008479653986372321838603)
              ·
                refine ⟨7512719480979558482757905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5008479653986372321838603 7512719480979558482757905)
                ·
                  refine ⟨5634539610734668862068429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7512719480979558482757905 5634539610734668862068429)
                  ·
                    refine ⟨2112952354025500823275661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5634539610734668862068429 2112952354025500823275661)
                    ·
                      refine ⟨792357132759562808728373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2112952354025500823275661 792357132759562808728373)
                      ·
                        rfl

theorem cell23_1543110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_1543110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543110 prefixEnd_1543110 := by exact prefixLift 1543110
  have htrace : WordTrace (prefixWord ++ tailWord_1543110) baseStart_1543110 baseEnd_1543110 := by
    simpa [prefixWord, tailWord_1543110, baseEnd_1543110] using wordTrace_append hprefix tailTrace_1543110
  have hstable : (prefixWord ++ tailWord_1543110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543110).length < 2 ^ (prefixWord ++ tailWord_1543110).sum := by decide
  have hdescent : baseEnd_1543110 < baseStart_1543110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543126 : List Nat := [5, 2, 1, 1, 2, 2, 1, 2, 3, 4]
def baseStart_1543126 : Nat := 118140960795 + 1543126 * 2 ^ 59
def prefixEnd_1543126 : Nat := 4983230072969 + 3 ^ 40 * 1543126 * 2
def baseEnd_1543126 : Nat := 264121782816678248709433

theorem tailTrace_1543126 : CollatzResearch.WordTrace tailWord_1543126 prefixEnd_1543126 264121782816678248709433 := by
  unfold tailWord_1543126
  simp only [CollatzResearch.WordTrace]
  refine ⟨3517651812970345111501577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37521619338350347856016821 3517651812970345111501577)
  ·
    refine ⟨2638238859727758833626183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3517651812970345111501577 2638238859727758833626183)
    ·
      refine ⟨3957358289591638250439275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2638238859727758833626183 3957358289591638250439275)
      ·
        refine ⟨5936037434387457375658913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3957358289591638250439275 5936037434387457375658913)
        ·
          refine ⟨4452028075790593031744185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5936037434387457375658913 4452028075790593031744185)
          ·
            refine ⟨3339021056842944773808139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4452028075790593031744185 3339021056842944773808139)
            ·
              refine ⟨5008531585264417160712209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3339021056842944773808139 5008531585264417160712209)
              ·
                refine ⟨3756398688948312870534157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5008531585264417160712209 3756398688948312870534157)
                ·
                  refine ⟨1408649508355617326450309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3756398688948312870534157 1408649508355617326450309)
                  ·
                    refine ⟨264121782816678248709433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1408649508355617326450309 264121782816678248709433)
                    ·
                      rfl

theorem cell23_1543126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_1543126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543126 prefixEnd_1543126 := by exact prefixLift 1543126
  have htrace : WordTrace (prefixWord ++ tailWord_1543126) baseStart_1543126 baseEnd_1543126 := by
    simpa [prefixWord, tailWord_1543126, baseEnd_1543126] using wordTrace_append hprefix tailTrace_1543126
  have hstable : (prefixWord ++ tailWord_1543126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543126).length < 2 ^ (prefixWord ++ tailWord_1543126).sum := by decide
  have hdescent : baseEnd_1543126 < baseStart_1543126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543189 : List Nat := [1, 3, 2, 1, 4, 1, 1, 4, 1, 1, 4]
def baseStart_1543189 : Nat := 118140960795 + 1543189 * 2 ^ 59
def prefixEnd_1543189 : Nat := 4983230072969 + 3 ^ 40 * 1543189 * 2
def baseEnd_1543189 : Nat := 792397697731267999640509

theorem tailTrace_1543189 : CollatzResearch.WordTrace tailWord_1543189 prefixEnd_1543189 792397697731267999640509 := by
  unfold tailWord_1543189
  simp only [CollatzResearch.WordTrace]
  refine ⟨56284726806297283543568621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37523151204198189029045747 56284726806297283543568621)
  ·
    refine ⟨21106772552361481328838233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56284726806297283543568621 21106772552361481328838233)
    ·
      refine ⟨15830079414271110996628675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21106772552361481328838233 15830079414271110996628675)
      ·
        refine ⟨23745119121406666494943013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15830079414271110996628675 23745119121406666494943013)
        ·
          refine ⟨4452209835263749967801815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23745119121406666494943013 4452209835263749967801815)
          ·
            refine ⟨6678314752895624951702723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4452209835263749967801815 6678314752895624951702723)
            ·
              refine ⟨10017472129343437427554085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6678314752895624951702723 10017472129343437427554085)
              ·
                refine ⟨1878276024251894517666391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10017472129343437427554085 1878276024251894517666391)
                ·
                  refine ⟨2817414036377841776499587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1878276024251894517666391 2817414036377841776499587)
                  ·
                    refine ⟨4226121054566762664749381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2817414036377841776499587 4226121054566762664749381)
                    ·
                      refine ⟨792397697731267999640509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4226121054566762664749381 792397697731267999640509)
                      ·
                        rfl

theorem cell23_1543189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_1543189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543189 prefixEnd_1543189 := by exact prefixLift 1543189
  have htrace : WordTrace (prefixWord ++ tailWord_1543189) baseStart_1543189 baseEnd_1543189 := by
    simpa [prefixWord, tailWord_1543189, baseEnd_1543189] using wordTrace_append hprefix tailTrace_1543189
  have hstable : (prefixWord ++ tailWord_1543189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543189).length < 2 ^ (prefixWord ++ tailWord_1543189).sum := by decide
  have hdescent : baseEnd_1543189 < baseStart_1543189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543252 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 1, 4, 5]
def baseStart_1543252 : Nat := 118140960795 + 1543252 * 2 ^ 59
def prefixEnd_1543252 : Nat := 4983230072969 + 3 ^ 40 * 1543252 * 2
def baseEnd_1543252 : Nat := 792430047012501253152719

theorem tailTrace_1543252 : CollatzResearch.WordTrace tailWord_1543252 prefixEnd_1543252 792430047012501253152719 := by
  unfold tailWord_1543252
  simp only [CollatzResearch.WordTrace]
  refine ⟨28143512302534522651556005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37524683070046030202074673 28143512302534522651556005)
  ·
    refine ⟨5276908556725222997166751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28143512302534522651556005 5276908556725222997166751)
    ·
      refine ⟨7915362835087834495750127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5276908556725222997166751 7915362835087834495750127)
      ·
        refine ⟨11873044252631751743625191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7915362835087834495750127 11873044252631751743625191)
        ·
          refine ⟨17809566378947627615437787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11873044252631751743625191 17809566378947627615437787)
          ·
            refine ⟨26714349568421441423156681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17809566378947627615437787 26714349568421441423156681)
            ·
              refine ⟨20035762176316081067367511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26714349568421441423156681 20035762176316081067367511)
              ·
                refine ⟨30053643264474121601051267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20035762176316081067367511 30053643264474121601051267)
                ·
                  refine ⟨45080464896711182401576901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30053643264474121601051267 45080464896711182401576901)
                  ·
                    refine ⟨8452587168133346700295669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45080464896711182401576901 8452587168133346700295669)
                    ·
                      refine ⟨792430047012501253152719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8452587168133346700295669 792430047012501253152719)
                      ·
                        rfl

theorem cell23_1543252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_1543252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543252 prefixEnd_1543252 := by exact prefixLift 1543252
  have htrace : WordTrace (prefixWord ++ tailWord_1543252) baseStart_1543252 baseEnd_1543252 := by
    simpa [prefixWord, tailWord_1543252, baseEnd_1543252] using wordTrace_append hprefix tailTrace_1543252
  have hstable : (prefixWord ++ tailWord_1543252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543252).length < 2 ^ (prefixWord ++ tailWord_1543252).sum := by decide
  have hdescent : baseEnd_1543252 < baseStart_1543252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543279 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 3, 4, 2]
def baseStart_1543279 : Nat := 118140960795 + 1543279 * 2 ^ 59
def prefixEnd_1543279 : Nat := 4983230072969 + 3 ^ 40 * 1543279 * 2
def baseEnd_1543279 : Nat := 792443910990172647515095

theorem tailTrace_1543279 : CollatzResearch.WordTrace tailWord_1543279 prefixEnd_1543279 792443910990172647515095 := by
  unfold tailWord_1543279
  simp only [CollatzResearch.WordTrace]
  refine ⟨56288009375971228914344891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37525339583980819276229927 56288009375971228914344891)
  ·
    refine ⟨84432014063956843371517337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56288009375971228914344891 84432014063956843371517337)
    ·
      refine ⟨63324010547967632528638003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84432014063956843371517337 63324010547967632528638003)
      ·
        refine ⟨94986015821951448792957005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63324010547967632528638003 94986015821951448792957005)
        ·
          refine ⟨35619755933231793297358877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94986015821951448792957005 35619755933231793297358877)
          ·
            refine ⟨13357408474961922486509579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35619755933231793297358877 13357408474961922486509579)
            ·
              refine ⟨20036112712442883729764369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13357408474961922486509579 20036112712442883729764369)
              ·
                refine ⟨15027084534332162797323277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20036112712442883729764369 15027084534332162797323277)
                ·
                  refine ⟨5635156700374561048996229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15027084534332162797323277 5635156700374561048996229)
                  ·
                    refine ⟨1056591881320230196686793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5635156700374561048996229 1056591881320230196686793)
                    ·
                      refine ⟨792443910990172647515095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1056591881320230196686793 792443910990172647515095)
                      ·
                        rfl

theorem cell23_1543279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 4, 2].length) (baseStart_1543279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543279 prefixEnd_1543279 := by exact prefixLift 1543279
  have htrace : WordTrace (prefixWord ++ tailWord_1543279) baseStart_1543279 baseEnd_1543279 := by
    simpa [prefixWord, tailWord_1543279, baseEnd_1543279] using wordTrace_append hprefix tailTrace_1543279
  have hstable : (prefixWord ++ tailWord_1543279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543279).length < 2 ^ (prefixWord ++ tailWord_1543279).sum := by decide
  have hdescent : baseEnd_1543279 < baseStart_1543279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543289 : List Nat := [1, 2, 1, 3, 5, 1, 1, 1, 2, 6]
def baseStart_1543289 : Nat := 118140960795 + 1543289 * 2 ^ 59
def prefixEnd_1543289 : Nat := 4983230072969 + 3 ^ 40 * 1543289 * 2
def baseEnd_1543289 : Nat := 264149681932239202796683

theorem tailTrace_1543289 : CollatzResearch.WordTrace tailWord_1543289 prefixEnd_1543289 264149681932239202796683 := by
  unfold tailWord_1543289
  simp only [CollatzResearch.WordTrace]
  refine ⟨56288374105935000622208921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37525582737290000414805947 56288374105935000622208921)
  ·
    refine ⟨42216280579451250466656691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56288374105935000622208921 42216280579451250466656691)
    ·
      refine ⟨63324420869176875699985037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42216280579451250466656691 63324420869176875699985037)
      ·
        refine ⟨23746657825941328387494389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63324420869176875699985037 23746657825941328387494389)
        ·
          refine ⟨2226249171181999536327599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23746657825941328387494389 2226249171181999536327599)
          ·
            refine ⟨3339373756772999304491399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2226249171181999536327599 3339373756772999304491399)
            ·
              refine ⟨5009060635159498956737099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3339373756772999304491399 5009060635159498956737099)
              ·
                refine ⟨7513590952739248435105649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5009060635159498956737099 7513590952739248435105649)
                ·
                  refine ⟨5635193214554436326329237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7513590952739248435105649 5635193214554436326329237)
                  ·
                    refine ⟨264149681932239202796683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5635193214554436326329237 264149681932239202796683)
                    ·
                      rfl

theorem cell23_1543289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 6].length) (baseStart_1543289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543289 prefixEnd_1543289 := by exact prefixLift 1543289
  have htrace : WordTrace (prefixWord ++ tailWord_1543289) baseStart_1543289 baseEnd_1543289 := by
    simpa [prefixWord, tailWord_1543289, baseEnd_1543289] using wordTrace_append hprefix tailTrace_1543289
  have hstable : (prefixWord ++ tailWord_1543289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543289).length < 2 ^ (prefixWord ++ tailWord_1543289).sum := by decide
  have hdescent : baseEnd_1543289 < baseStart_1543289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543326 : List Nat := [4, 3, 1, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_1543326 : Nat := 118140960795 + 1543326 * 2 ^ 59
def prefixEnd_1543326 : Nat := 4983230072969 + 3 ^ 40 * 1543326 * 2
def baseEnd_1543326 : Nat := 792468044580933963627379

theorem tailTrace_1543326 : CollatzResearch.WordTrace tailWord_1543326 prefixEnd_1543326 792468044580933963627379 := by
  unfold tailWord_1543326
  simp only [CollatzResearch.WordTrace]
  refine ⟨7036215450850119492663229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37526482404533970627537221 7036215450850119492663229)
  ·
    refine ⟨2638580794068794809748711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7036215450850119492663229 2638580794068794809748711)
    ·
      refine ⟨3957871191103192214623067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2638580794068794809748711 3957871191103192214623067)
      ·
        refine ⟨5936806786654788321934601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3957871191103192214623067 5936806786654788321934601)
        ·
          refine ⟨4452605089991091241450951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5936806786654788321934601 4452605089991091241450951)
          ·
            refine ⟨6678907634986636862176427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4452605089991091241450951 6678907634986636862176427)
            ·
              refine ⟨10018361452479955293264641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6678907634986636862176427 10018361452479955293264641)
              ·
                refine ⟨7513771089359966469948481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10018361452479955293264641 7513771089359966469948481)
                ·
                  refine ⟨5635328317019974852461361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7513771089359966469948481 5635328317019974852461361)
                  ·
                    refine ⟨4226496237764981139346021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5635328317019974852461361 4226496237764981139346021)
                    ·
                      refine ⟨792468044580933963627379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4226496237764981139346021 792468044580933963627379)
                      ·
                        rfl

theorem cell23_1543326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_1543326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543326 prefixEnd_1543326 := by exact prefixLift 1543326
  have htrace : WordTrace (prefixWord ++ tailWord_1543326) baseStart_1543326 baseEnd_1543326 := by
    simpa [prefixWord, tailWord_1543326, baseEnd_1543326] using wordTrace_append hprefix tailTrace_1543326
  have hstable : (prefixWord ++ tailWord_1543326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543326).length < 2 ^ (prefixWord ++ tailWord_1543326).sum := by decide
  have hdescent : baseEnd_1543326 < baseStart_1543326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543329 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 4, 3, 3]
def baseStart_1543329 : Nat := 118140960795 + 1543329 * 2 ^ 59
def prefixEnd_1543329 : Nat := 4983230072969 + 3 ^ 40 * 1543329 * 2
def baseEnd_1543329 : Nat := 792469585022897451889865

theorem tailTrace_1543329 : CollatzResearch.WordTrace tailWord_1543329 prefixEnd_1543329 792469585022897451889865 := by
  unfold tailWord_1543329
  simp only [CollatzResearch.WordTrace]
  refine ⟨56289833025790087453665041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37526555350526724969110027 56289833025790087453665041)
  ·
    refine ⟨42217374769342565590248781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56289833025790087453665041 42217374769342565590248781)
    ·
      refine ⟨15831515538503462096343293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42217374769342565590248781 15831515538503462096343293)
      ·
        refine ⟨5936818326938798286128735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15831515538503462096343293 5936818326938798286128735)
        ·
          refine ⟨8905227490408197429193103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5936818326938798286128735 8905227490408197429193103)
          ·
            refine ⟨13357841235612296143789655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8905227490408197429193103 13357841235612296143789655)
            ·
              refine ⟨20036761853418444215684483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13357841235612296143789655 20036761853418444215684483)
              ·
                refine ⟨30055142780127666323526725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20036761853418444215684483 30055142780127666323526725)
                ·
                  refine ⟨5635339271273937435661261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30055142780127666323526725 5635339271273937435661261)
                  ·
                    refine ⟨2113252226727726538372973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5635339271273937435661261 2113252226727726538372973)
                    ·
                      refine ⟨792469585022897451889865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2113252226727726538372973 792469585022897451889865)
                      ·
                        rfl

theorem cell23_1543329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_1543329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543329 prefixEnd_1543329 := by exact prefixLift 1543329
  have htrace : WordTrace (prefixWord ++ tailWord_1543329) baseStart_1543329 baseEnd_1543329 := by
    simpa [prefixWord, tailWord_1543329, baseEnd_1543329] using wordTrace_append hprefix tailTrace_1543329
  have hstable : (prefixWord ++ tailWord_1543329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543329).length < 2 ^ (prefixWord ++ tailWord_1543329).sum := by decide
  have hdescent : baseEnd_1543329 < baseStart_1543329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543330 : List Nat := [3, 3, 1, 3, 2, 1, 1, 1, 4, 2, 2]
def baseStart_1543330 : Nat := 118140960795 + 1543330 * 2 ^ 59
def prefixEnd_1543330 : Nat := 4983230072969 + 3 ^ 40 * 1543330 * 2
def baseEnd_1543330 : Nat := 792470098503551947977361

theorem tailTrace_1543330 : CollatzResearch.WordTrace tailWord_1543330 prefixEnd_1543330 792470098503551947977361 := by
  unfold tailWord_1543330
  simp only [CollatzResearch.WordTrace]
  refine ⟨14072467374696616156112861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37526579665857643082967629 14072467374696616156112861)
  ·
    refine ⟨5277175265511231058542323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14072467374696616156112861 5277175265511231058542323)
    ·
      refine ⟨7915762898266846587813485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5277175265511231058542323 7915762898266846587813485)
      ·
        refine ⟨2968411086850067470430057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7915762898266846587813485 2968411086850067470430057)
        ·
          refine ⟨2226308315137550602822543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2968411086850067470430057 2226308315137550602822543)
          ·
            refine ⟨3339462472706325904233815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2226308315137550602822543 3339462472706325904233815)
            ·
              refine ⟨5009193709059488856350723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3339462472706325904233815 5009193709059488856350723)
              ·
                refine ⟨7513790563589233284526085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5009193709059488856350723 7513790563589233284526085)
                ·
                  refine ⟨1408835730672981240848641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7513790563589233284526085 1408835730672981240848641)
                  ·
                    refine ⟨1056626798004735930636481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1408835730672981240848641 1056626798004735930636481)
                    ·
                      refine ⟨792470098503551947977361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1056626798004735930636481 792470098503551947977361)
                      ·
                        rfl

theorem cell23_1543330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_1543330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543330 prefixEnd_1543330 := by exact prefixLift 1543330
  have htrace : WordTrace (prefixWord ++ tailWord_1543330) baseStart_1543330 baseEnd_1543330 := by
    simpa [prefixWord, tailWord_1543330, baseEnd_1543330] using wordTrace_append hprefix tailTrace_1543330
  have hstable : (prefixWord ++ tailWord_1543330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543330).length < 2 ^ (prefixWord ++ tailWord_1543330).sum := by decide
  have hdescent : baseEnd_1543330 < baseStart_1543330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543396 : List Nat := [2, 3, 1, 1, 1, 2, 5, 1, 3, 4]
def baseStart_1543396 : Nat := 118140960795 + 1543396 * 2 ^ 59
def prefixEnd_1543396 : Nat := 4983230072969 + 3 ^ 40 * 1543396 * 2
def baseEnd_1543396 : Nat := 264167996075582896584019

theorem tailTrace_1543396 : CollatzResearch.WordTrace tailWord_1543396 prefixEnd_1543396 264167996075582896584019 := by
  unfold tailWord_1543396
  simp only [CollatzResearch.WordTrace]
  refine ⟨28146138358273678948177021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37528184477698238597569361 28146138358273678948177021)
  ·
    refine ⟨10554801884352629605566383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28146138358273678948177021 10554801884352629605566383)
    ·
      refine ⟨15832202826528944408349575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10554801884352629605566383 15832202826528944408349575)
      ·
        refine ⟨23748304239793416612524363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15832202826528944408349575 23748304239793416612524363)
        ·
          refine ⟨35622456359690124918786545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23748304239793416612524363 35622456359690124918786545)
          ·
            refine ⟨26716842269767593689089909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35622456359690124918786545 26716842269767593689089909)
            ·
              refine ⟨2504703962790711908352179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26716842269767593689089909 2504703962790711908352179)
              ·
                refine ⟨3757055944186067862528269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2504703962790711908352179 3757055944186067862528269)
                ·
                  refine ⟨1408895979069775448448101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3757055944186067862528269 1408895979069775448448101)
                  ·
                    refine ⟨264167996075582896584019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1408895979069775448448101 264167996075582896584019)
                    ·
                      rfl

theorem cell23_1543396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_1543396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543396 prefixEnd_1543396 := by exact prefixLift 1543396
  have htrace : WordTrace (prefixWord ++ tailWord_1543396) baseStart_1543396 baseEnd_1543396 := by
    simpa [prefixWord, tailWord_1543396, baseEnd_1543396] using wordTrace_append hprefix tailTrace_1543396
  have hstable : (prefixWord ++ tailWord_1543396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543396).length < 2 ^ (prefixWord ++ tailWord_1543396).sum := by decide
  have hdescent : baseEnd_1543396 < baseStart_1543396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543486 : List Nat := [4, 2, 1, 2, 1, 1, 1, 4, 1, 6]
def baseStart_1543486 : Nat := 118140960795 + 1543486 * 2 ^ 59
def prefixEnd_1543486 : Nat := 4983230072969 + 3 ^ 40 * 1543486 * 2
def baseEnd_1543486 : Nat := 264183400495217779208881

theorem tailTrace_1543486 : CollatzResearch.WordTrace tailWord_1543486 prefixEnd_1543486 264183400495217779208881 := by
  unfold tailWord_1543486
  simp only [CollatzResearch.WordTrace]
  refine ⟨7036944910777662908391289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37530372857480868844753541 7036944910777662908391289)
  ·
    refine ⟨5277708683083247181293467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7036944910777662908391289 5277708683083247181293467)
    ·
      refine ⟨7916563024624870771940201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5277708683083247181293467 7916563024624870771940201)
      ·
        refine ⟨5937422268468653078955151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7916563024624870771940201 5937422268468653078955151)
        ·
          refine ⟨8906133402702979618432727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5937422268468653078955151 8906133402702979618432727)
          ·
            refine ⟨13359200104054469427649091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8906133402702979618432727 13359200104054469427649091)
            ·
              refine ⟨20038800156081704141473637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13359200104054469427649091 20038800156081704141473637)
              ·
                refine ⟨3757275029265319526526307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20038800156081704141473637 3757275029265319526526307)
                ·
                  refine ⟨5635912543897979289789461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3757275029265319526526307 5635912543897979289789461)
                  ·
                    refine ⟨264183400495217779208881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5635912543897979289789461 264183400495217779208881)
                    ·
                      rfl

theorem cell23_1543486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_1543486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543486 prefixEnd_1543486 := by exact prefixLift 1543486
  have htrace : WordTrace (prefixWord ++ tailWord_1543486) baseStart_1543486 baseEnd_1543486 := by
    simpa [prefixWord, tailWord_1543486, baseEnd_1543486] using wordTrace_append hprefix tailTrace_1543486
  have hstable : (prefixWord ++ tailWord_1543486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543486).length < 2 ^ (prefixWord ++ tailWord_1543486).sum := by decide
  have hdescent : baseEnd_1543486 < baseStart_1543486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543494 : List Nat := [6, 1, 1, 3, 2, 1, 1, 2, 6]
def baseStart_1543494 : Nat := 118140960795 + 1543494 * 2 ^ 59
def prefixEnd_1543494 : Nat := 4983230072969 + 3 ^ 40 * 1543494 * 2
def baseEnd_1543494 : Nat := 88061589925654367369623

theorem tailTrace_1543494 : CollatzResearch.WordTrace tailWord_1543494 prefixEnd_1543494 88061589925654367369623 := by
  unfold tailWord_1543494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1759245345943510019794423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37530567380128213755614357 1759245345943510019794423)
  ·
    refine ⟨2638868018915265029691635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1759245345943510019794423 2638868018915265029691635)
    ·
      refine ⟨3958302028372897544537453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2638868018915265029691635 3958302028372897544537453)
      ·
        refine ⟨1484363260639836579201545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3958302028372897544537453 1484363260639836579201545)
        ·
          refine ⟨1113272445479877434401159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1484363260639836579201545 1113272445479877434401159)
          ·
            refine ⟨1669908668219816151601739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1113272445479877434401159 1669908668219816151601739)
            ·
              refine ⟨2504863002329724227402609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1669908668219816151601739 2504863002329724227402609)
              ·
                refine ⟨1878647251747293170551957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2504863002329724227402609 1878647251747293170551957)
                ·
                  refine ⟨88061589925654367369623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1878647251747293170551957 88061589925654367369623)
                  ·
                    rfl

theorem cell23_1543494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_1543494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543494 prefixEnd_1543494 := by exact prefixLift 1543494
  have htrace : WordTrace (prefixWord ++ tailWord_1543494) baseStart_1543494 baseEnd_1543494 := by
    simpa [prefixWord, tailWord_1543494, baseEnd_1543494] using wordTrace_append hprefix tailTrace_1543494
  have hstable : (prefixWord ++ tailWord_1543494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543494).length < 2 ^ (prefixWord ++ tailWord_1543494).sum := by decide
  have hdescent : baseEnd_1543494 < baseStart_1543494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543520 : List Nat := [2, 1, 1, 3, 4, 2, 3, 1, 2, 4]
def baseStart_1543520 : Nat := 118140960795 + 1543520 * 2 ^ 59
def prefixEnd_1543520 : Nat := 4983230072969 + 3 ^ 40 * 1543520 * 2
def baseEnd_1543520 : Nat := 264189219942635401533829

theorem tailTrace_1543520 : CollatzResearch.WordTrace tailWord_1543520 prefixEnd_1543520 264189219942635401533829 := by
  unfold tailWord_1543520
  simp only [CollatzResearch.WordTrace]
  refine ⟨28148399684049063536934007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37531199578732084715912009 28148399684049063536934007)
  ·
    refine ⟨42222599526073595305401011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28148399684049063536934007 42222599526073595305401011)
    ·
      refine ⟨63333899289110392958101517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42222599526073595305401011 63333899289110392958101517)
      ·
        refine ⟨23750212233416397359288069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63333899289110392958101517 23750212233416397359288069)
        ·
          refine ⟨4453164793765574504866513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23750212233416397359288069 4453164793765574504866513)
          ·
            refine ⟨3339873595324180878649885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4453164793765574504866513 3339873595324180878649885)
            ·
              refine ⟨1252452598246567829493707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3339873595324180878649885 1252452598246567829493707)
              ·
                refine ⟨1878678897369851744240561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1252452598246567829493707 1878678897369851744240561)
                ·
                  refine ⟨1409009173027388808180421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1878678897369851744240561 1409009173027388808180421)
                  ·
                    refine ⟨264189219942635401533829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1409009173027388808180421 264189219942635401533829)
                    ·
                      rfl

theorem cell23_1543520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 2, 4].length) (baseStart_1543520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543520 prefixEnd_1543520 := by exact prefixLift 1543520
  have htrace : WordTrace (prefixWord ++ tailWord_1543520) baseStart_1543520 baseEnd_1543520 := by
    simpa [prefixWord, tailWord_1543520, baseEnd_1543520] using wordTrace_append hprefix tailTrace_1543520
  have hstable : (prefixWord ++ tailWord_1543520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543520).length < 2 ^ (prefixWord ++ tailWord_1543520).sum := by decide
  have hdescent : baseEnd_1543520 < baseStart_1543520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543523 : List Nat := [1, 1, 1, 5, 2, 4, 1, 1, 1, 2, 4]
def baseStart_1543523 : Nat := 118140960795 + 1543523 * 2 ^ 59
def prefixEnd_1543523 : Nat := 4983230072969 + 3 ^ 40 * 1543523 * 2
def baseEnd_1543523 : Nat := 792569200269869692863973

theorem tailTrace_1543523 : CollatzResearch.WordTrace tailWord_1543523 prefixEnd_1543523 792569200269869692863973 := by
  unfold tailWord_1543523
  simp only [CollatzResearch.WordTrace]
  refine ⟨56296908787087258586227223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37531272524724839057484815 56296908787087258586227223)
  ·
    refine ⟨84445363180630887879340835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56296908787087258586227223 84445363180630887879340835)
    ·
      refine ⟨126668044770946331819011253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84445363180630887879340835 126668044770946331819011253)
      ·
        refine ⟨11875129197276218608032305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126668044770946331819011253 11875129197276218608032305)
        ·
          refine ⟨8906346897957163956024229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11875129197276218608032305 8906346897957163956024229)
          ·
            refine ⟨1669940043366968241754543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8906346897957163956024229 1669940043366968241754543)
            ·
              refine ⟨2504910065050452362631815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1669940043366968241754543 2504910065050452362631815)
              ·
                refine ⟨3757365097575678543947723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2504910065050452362631815 3757365097575678543947723)
                ·
                  refine ⟨5636047646363517815921585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3757365097575678543947723 5636047646363517815921585)
                  ·
                    refine ⟨4227035734772638361941189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5636047646363517815921585 4227035734772638361941189)
                    ·
                      refine ⟨792569200269869692863973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4227035734772638361941189 792569200269869692863973)
                      ·
                        rfl

theorem cell23_1543523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_1543523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543523 prefixEnd_1543523 := by exact prefixLift 1543523
  have htrace : WordTrace (prefixWord ++ tailWord_1543523) baseStart_1543523 baseEnd_1543523 := by
    simpa [prefixWord, tailWord_1543523, baseEnd_1543523] using wordTrace_append hprefix tailTrace_1543523
  have hstable : (prefixWord ++ tailWord_1543523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543523).length < 2 ^ (prefixWord ++ tailWord_1543523).sum := by decide
  have hdescent : baseEnd_1543523 < baseStart_1543523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543533 : List Nat := [1, 5, 1, 1, 1, 5, 2, 7]
def baseStart_1543533 : Nat := 118140960795 + 1543533 * 2 ^ 59
def prefixEnd_1543533 : Nat := 4983230072969 + 3 ^ 40 * 1543533 * 2
def baseEnd_1543533 : Nat := 29354605002830172360701

theorem tailTrace_1543533 : CollatzResearch.WordTrace tailWord_1543533 prefixEnd_1543533 29354605002830172360701 := by
  unfold tailWord_1543533
  simp only [CollatzResearch.WordTrace]
  refine ⟨56297273517051030294091253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37531515678034020196060835 56297273517051030294091253)
  ·
    refine ⟨5277869392223534090071055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56297273517051030294091253 5277869392223534090071055)
    ·
      refine ⟨7916804088335301135106583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5277869392223534090071055 7916804088335301135106583)
      ·
        refine ⟨11875206132502951702659875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7916804088335301135106583 11875206132502951702659875)
        ·
          refine ⟨17812809198754427553989813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11875206132502951702659875 17812809198754427553989813)
          ·
            refine ⟨1669950862383227583186545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17812809198754427553989813 1669950862383227583186545)
            ·
              refine ⟨1252463146787420687389909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1669950862383227583186545 1252463146787420687389909)
              ·
                refine ⟨29354605002830172360701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1252463146787420687389909 29354605002830172360701)
                ·
                  rfl

theorem cell23_1543533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 7].length) (baseStart_1543533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543533 prefixEnd_1543533 := by exact prefixLift 1543533
  have htrace : WordTrace (prefixWord ++ tailWord_1543533) baseStart_1543533 baseEnd_1543533 := by
    simpa [prefixWord, tailWord_1543533, baseEnd_1543533] using wordTrace_append hprefix tailTrace_1543533
  have hstable : (prefixWord ++ tailWord_1543533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543533).length < 2 ^ (prefixWord ++ tailWord_1543533).sum := by decide
  have hdescent : baseEnd_1543533 < baseStart_1543533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543550 : List Nat := [4, 2, 3, 2, 1, 2, 9]
def baseStart_1543550 : Nat := 118140960795 + 1543550 * 2 ^ 59
def prefixEnd_1543550 : Nat := 4983230072969 + 3 ^ 40 * 1543550 * 2
def baseEnd_1543550 : Nat := 9784976101821494904029

theorem tailTrace_1543550 : CollatzResearch.WordTrace tailWord_1543550 prefixEnd_1543550 9784976101821494904029 := by
  unfold tailWord_1543550
  simp only [CollatzResearch.WordTrace]
  refine ⟨7037236694748680274682513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37531929038659628131640069 7037236694748680274682513)
  ·
    refine ⟨5277927521061510206011885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7037236694748680274682513 5277927521061510206011885)
    ·
      refine ⟨1979222820398066327254457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5277927521061510206011885 1979222820398066327254457)
      ·
        refine ⟨1484417115298549745440843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1979222820398066327254457 1484417115298549745440843)
        ·
          refine ⟨2226625672947824618161265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1484417115298549745440843 2226625672947824618161265)
          ·
            refine ⟨1669969254710868463620949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2226625672947824618161265 1669969254710868463620949)
            ·
              refine ⟨9784976101821494904029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1669969254710868463620949 9784976101821494904029)
              ·
                rfl

theorem cell23_1543550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 9].length) (baseStart_1543550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543550 prefixEnd_1543550 := by exact prefixLift 1543550
  have htrace : WordTrace (prefixWord ++ tailWord_1543550) baseStart_1543550 baseEnd_1543550 := by
    simpa [prefixWord, tailWord_1543550, baseEnd_1543550] using wordTrace_append hprefix tailTrace_1543550
  have hstable : (prefixWord ++ tailWord_1543550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543550).length < 2 ^ (prefixWord ++ tailWord_1543550).sum := by decide
  have hdescent : baseEnd_1543550 < baseStart_1543550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543577 : List Nat := [1, 2, 1, 2, 1, 7, 2, 1, 2, 1, 3]
def baseStart_1543577 : Nat := 118140960795 + 1543577 * 2 ^ 59
def prefixEnd_1543577 : Nat := 4983230072969 + 3 ^ 40 * 1543577 * 2
def baseEnd_1543577 : Nat := 792596928225212481588725

theorem tailTrace_1543577 : CollatzResearch.WordTrace tailWord_1543577 prefixEnd_1543577 792596928225212481588725 := by
  unfold tailWord_1543577
  simp only [CollatzResearch.WordTrace]
  refine ⟨56298878328891625808692985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37532585552594417205795323 56298878328891625808692985)
  ·
    refine ⟨42224158746668719356519739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56298878328891625808692985 42224158746668719356519739)
    ·
      refine ⟨63336238120003079034779609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42224158746668719356519739 63336238120003079034779609)
      ·
        refine ⟨47502178590002309276084707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63336238120003079034779609 47502178590002309276084707)
        ·
          refine ⟨71253267885003463914127061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47502178590002309276084707 71253267885003463914127061)
          ·
            refine ⟨1669998466054768685487353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 71253267885003463914127061 1669998466054768685487353)
            ·
              refine ⟨1252498849541076514115515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1669998466054768685487353 1252498849541076514115515)
              ·
                refine ⟨1878748274311614771173273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1252498849541076514115515 1878748274311614771173273)
                ·
                  refine ⟨1409061205733711078379955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1878748274311614771173273 1409061205733711078379955)
                  ·
                    refine ⟨2113591808600566617569933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1409061205733711078379955 2113591808600566617569933)
                    ·
                      refine ⟨792596928225212481588725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2113591808600566617569933 792596928225212481588725)
                      ·
                        rfl

theorem cell23_1543577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 2, 1, 3].length) (baseStart_1543577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543577 prefixEnd_1543577 := by exact prefixLift 1543577
  have htrace : WordTrace (prefixWord ++ tailWord_1543577) baseStart_1543577 baseEnd_1543577 := by
    simpa [prefixWord, tailWord_1543577, baseEnd_1543577] using wordTrace_append hprefix tailTrace_1543577
  have hstable : (prefixWord ++ tailWord_1543577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543577).length < 2 ^ (prefixWord ++ tailWord_1543577).sum := by decide
  have hdescent : baseEnd_1543577 < baseStart_1543577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543623 : List Nat := [1, 1, 4, 1, 1, 3, 3, 4, 5]
def baseStart_1543623 : Nat := 118140960795 + 1543623 * 2 ^ 59
def prefixEnd_1543623 : Nat := 4983230072969 + 3 ^ 40 * 1543623 * 2
def baseEnd_1543623 : Nat := 88068949815035477957057

theorem tailTrace_1543623 : CollatzResearch.WordTrace tailWord_1543623 prefixEnd_1543623 88068949815035477957057 := by
  unfold tailWord_1543623
  simp only [CollatzResearch.WordTrace]
  refine ⟨56300556086724975664867523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37533704057816650443245015 56300556086724975664867523)
  ·
    refine ⟨84450834130087463497301285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56300556086724975664867523 84450834130087463497301285)
    ·
      refine ⟨15834531399391399405743991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84450834130087463497301285 15834531399391399405743991)
      ·
        refine ⟨23751797099087099108615987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15834531399391399405743991 23751797099087099108615987)
        ·
          refine ⟨35627695648630648662923981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23751797099087099108615987 35627695648630648662923981)
          ·
            refine ⟨13360385868236493248596493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35627695648630648662923981 13360385868236493248596493)
            ·
              refine ⟨5010144700588684968223685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13360385868236493248596493 5010144700588684968223685)
              ·
                refine ⟨939402131360378431541941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5010144700588684968223685 939402131360378431541941)
                ·
                  refine ⟨88068949815035477957057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 939402131360378431541941 88068949815035477957057)
                  ·
                    rfl

theorem cell23_1543623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 4, 5].length) (baseStart_1543623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543623 prefixEnd_1543623 := by exact prefixLift 1543623
  have htrace : WordTrace (prefixWord ++ tailWord_1543623) baseStart_1543623 baseEnd_1543623 := by
    simpa [prefixWord, tailWord_1543623, baseEnd_1543623] using wordTrace_append hprefix tailTrace_1543623
  have hstable : (prefixWord ++ tailWord_1543623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543623).length < 2 ^ (prefixWord ++ tailWord_1543623).sum := by decide
  have hdescent : baseEnd_1543623 < baseStart_1543623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543653 : List Nat := [1, 3, 1, 5, 1, 2, 1, 1, 1, 7]
def baseStart_1543653 : Nat := 118140960795 + 1543653 * 2 ^ 59
def prefixEnd_1543653 : Nat := 4983230072969 + 3 ^ 40 * 1543653 * 2
def baseEnd_1543653 : Nat := 264211984251651394746125

theorem tailTrace_1543653 : CollatzResearch.WordTrace tailWord_1543653 prefixEnd_1543653 264211984251651394746125 := by
  unfold tailWord_1543653
  simp only [CollatzResearch.WordTrace]
  refine ⟨56301650276616290788459613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37534433517744193858973075 56301650276616290788459613)
  ·
    refine ⟨21113118853731109045672355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56301650276616290788459613 21113118853731109045672355)
    ·
      refine ⟨31669678280596663568508533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21113118853731109045672355 31669678280596663568508533)
      ·
        refine ⟨2969032338805937209547675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31669678280596663568508533 2969032338805937209547675)
        ·
          refine ⟨4453548508208905814321513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2969032338805937209547675 4453548508208905814321513)
          ·
            refine ⟨3340161381156679360741135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4453548508208905814321513 3340161381156679360741135)
            ·
              refine ⟨5010242071735019041111703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3340161381156679360741135 5010242071735019041111703)
              ·
                refine ⟨7515363107602528561667555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5010242071735019041111703 7515363107602528561667555)
                ·
                  refine ⟨11273044661403792842501333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7515363107602528561667555 11273044661403792842501333)
                  ·
                    refine ⟨264211984251651394746125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11273044661403792842501333 264211984251651394746125)
                    ·
                      rfl

theorem cell23_1543653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 7].length) (baseStart_1543653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543653 prefixEnd_1543653 := by exact prefixLift 1543653
  have htrace : WordTrace (prefixWord ++ tailWord_1543653) baseStart_1543653 baseEnd_1543653 := by
    simpa [prefixWord, tailWord_1543653, baseEnd_1543653] using wordTrace_append hprefix tailTrace_1543653
  have hstable : (prefixWord ++ tailWord_1543653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543653).length < 2 ^ (prefixWord ++ tailWord_1543653).sum := by decide
  have hdescent : baseEnd_1543653 < baseStart_1543653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543676 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 2, 3, 5]
def baseStart_1543676 : Nat := 118140960795 + 1543676 * 2 ^ 59
def prefixEnd_1543676 : Nat := 4983230072969 + 3 ^ 40 * 1543676 * 2
def baseEnd_1543676 : Nat := 792647762810007594250769

theorem tailTrace_1543676 : CollatzResearch.WordTrace tailWord_1543676 prefixEnd_1543676 792647762810007594250769 := by
  unfold tailWord_1543676
  simp only [CollatzResearch.WordTrace]
  refine ⟨28151244577766482858273441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37534992770355310477697921 28151244577766482858273441)
  ·
    refine ⟨21113433433324862143705081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28151244577766482858273441 21113433433324862143705081)
    ·
      refine ⟨15835075074993646607778811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21113433433324862143705081 15835075074993646607778811)
      ·
        refine ⟨23752612612490469911668217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15835075074993646607778811 23752612612490469911668217)
        ·
          refine ⟨17814459459367852433751163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23752612612490469911668217 17814459459367852433751163)
          ·
            refine ⟨26721689189051778650626745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17814459459367852433751163 26721689189051778650626745)
            ·
              refine ⟨20041266891788833987970059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26721689189051778650626745 20041266891788833987970059)
              ·
                refine ⟨30061900337683250981955089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20041266891788833987970059 30061900337683250981955089)
                ·
                  refine ⟨22546425253262438236466317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30061900337683250981955089 22546425253262438236466317)
                  ·
                    refine ⟨8454909469973414338674869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22546425253262438236466317 8454909469973414338674869)
                    ·
                      refine ⟨792647762810007594250769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8454909469973414338674869 792647762810007594250769)
                      ·
                        rfl

theorem cell23_1543676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_1543676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543676 prefixEnd_1543676 := by exact prefixLift 1543676
  have htrace : WordTrace (prefixWord ++ tailWord_1543676) baseStart_1543676 baseEnd_1543676 := by
    simpa [prefixWord, tailWord_1543676, baseEnd_1543676] using wordTrace_append hprefix tailTrace_1543676
  have hstable : (prefixWord ++ tailWord_1543676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543676).length < 2 ^ (prefixWord ++ tailWord_1543676).sum := by decide
  have hdescent : baseEnd_1543676 < baseStart_1543676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543690 : List Nat := [3, 1, 2, 2, 2, 2, 2, 1, 2, 4, 2]
def baseStart_1543690 : Nat := 118140960795 + 1543690 * 2 ^ 59
def prefixEnd_1543690 : Nat := 4983230072969 + 3 ^ 40 * 1543690 * 2
def baseEnd_1543690 : Nat := 792654951539170539475705

theorem tailTrace_1543690 : CollatzResearch.WordTrace tailWord_1543690 prefixEnd_1543690 792654951539170539475705 := by
  unfold tailWord_1543690
  simp only [CollatzResearch.WordTrace]
  refine ⟨14075749944370561526889131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37535333184988164071704349 14075749944370561526889131)
  ·
    refine ⟨21113624916555842290333697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14075749944370561526889131 21113624916555842290333697)
    ·
      refine ⟨15835218687416881717750273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21113624916555842290333697 15835218687416881717750273)
      ·
        refine ⟨11876414015562661288312705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15835218687416881717750273 11876414015562661288312705)
        ·
          refine ⟨8907310511671995966234529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11876414015562661288312705 8907310511671995966234529)
          ·
            refine ⟨6680482883753996974675897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8907310511671995966234529 6680482883753996974675897)
            ·
              refine ⟨5010362162815497731006923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6680482883753996974675897 5010362162815497731006923)
              ·
                refine ⟨7515543244223246596510385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5010362162815497731006923 7515543244223246596510385)
                ·
                  refine ⟨5636657433167434947382789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7515543244223246596510385 5636657433167434947382789)
                  ·
                    refine ⟨1056873268718894052634273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5636657433167434947382789 1056873268718894052634273)
                    ·
                      refine ⟨792654951539170539475705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1056873268718894052634273 792654951539170539475705)
                      ·
                        rfl

theorem cell23_1543690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_1543690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543690 prefixEnd_1543690 := by exact prefixLift 1543690
  have htrace : WordTrace (prefixWord ++ tailWord_1543690) baseStart_1543690 baseEnd_1543690 := by
    simpa [prefixWord, tailWord_1543690, baseEnd_1543690] using wordTrace_append hprefix tailTrace_1543690
  have hstable : (prefixWord ++ tailWord_1543690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543690).length < 2 ^ (prefixWord ++ tailWord_1543690).sum := by decide
  have hdescent : baseEnd_1543690 < baseStart_1543690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543734 : List Nat := [5, 1, 2, 1, 3, 2, 1, 1, 3, 4]
def baseStart_1543734 : Nat := 118140960795 + 1543734 * 2 ^ 59
def prefixEnd_1543734 : Nat := 4983230072969 + 3 ^ 40 * 1543734 * 2
def baseEnd_1543734 : Nat := 264225848229322789108501

theorem tailTrace_1543734 : CollatzResearch.WordTrace tailWord_1543734 prefixEnd_1543734 264225848229322789108501 := by
  unfold tailWord_1543734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3519037786832677601384891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37536403059548561081438837 3519037786832677601384891)
  ·
    refine ⟨5278556680249016402077337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3519037786832677601384891 5278556680249016402077337)
    ·
      refine ⟨3958917510186762301558003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5278556680249016402077337 3958917510186762301558003)
      ·
        refine ⟨5938376265280143452337005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3958917510186762301558003 5938376265280143452337005)
        ·
          refine ⟨2226891099480053794626377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5938376265280143452337005 2226891099480053794626377)
          ·
            refine ⟨1670168324610040345969783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2226891099480053794626377 1670168324610040345969783)
            ·
              refine ⟨2505252486915060518954675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1670168324610040345969783 2505252486915060518954675)
              ·
                refine ⟨3757878730372590778432013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2505252486915060518954675 3757878730372590778432013)
                ·
                  refine ⟨1409204523889721541912005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3757878730372590778432013 1409204523889721541912005)
                  ·
                    refine ⟨264225848229322789108501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1409204523889721541912005 264225848229322789108501)
                    ·
                      rfl

theorem cell23_1543734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_1543734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543734 prefixEnd_1543734 := by exact prefixLift 1543734
  have htrace : WordTrace (prefixWord ++ tailWord_1543734) baseStart_1543734 baseEnd_1543734 := by
    simpa [prefixWord, tailWord_1543734, baseEnd_1543734] using wordTrace_append hprefix tailTrace_1543734
  have hstable : (prefixWord ++ tailWord_1543734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543734).length < 2 ^ (prefixWord ++ tailWord_1543734).sum := by decide
  have hdescent : baseEnd_1543734 < baseStart_1543734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543767 : List Nat := [1, 1, 3, 2, 2, 4, 2, 1, 2, 3, 2]
def baseStart_1543767 : Nat := 118140960795 + 1543767 * 2 ^ 59
def prefixEnd_1543767 : Nat := 4983230072969 + 3 ^ 40 * 1543767 * 2
def baseEnd_1543767 : Nat := 792694489549566738212851

theorem tailTrace_1543767 : CollatzResearch.WordTrace tailWord_1543767 prefixEnd_1543767 792694489549566738212851 := by
  unfold tailWord_1543767
  simp only [CollatzResearch.WordTrace]
  refine ⟨56305808198203288258109555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37537205465468858838739703 56305808198203288258109555)
  ·
    refine ⟨84458712297304932387164333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56305808198203288258109555 84458712297304932387164333)
    ·
      refine ⟨31672017111489349645186625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84458712297304932387164333 31672017111489349645186625)
      ·
        refine ⟨23754012833617012233889969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31672017111489349645186625 23754012833617012233889969)
        ·
          refine ⟨17815509625212759175417477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23754012833617012233889969 17815509625212759175417477)
          ·
            refine ⟨3340408054727392345390777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17815509625212759175417477 3340408054727392345390777)
            ·
              refine ⟨2505306041045544259043083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3340408054727392345390777 2505306041045544259043083)
              ·
                refine ⟨3757959061568316388564625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2505306041045544259043083 3757959061568316388564625)
                ·
                  refine ⟨2818469296176237291423469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3757959061568316388564625 2818469296176237291423469)
                  ·
                    refine ⟨1056925986066088984283801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2818469296176237291423469 1056925986066088984283801)
                    ·
                      refine ⟨792694489549566738212851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1056925986066088984283801 792694489549566738212851)
                      ·
                        rfl

theorem cell23_1543767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 3, 2].length) (baseStart_1543767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543767 prefixEnd_1543767 := by exact prefixLift 1543767
  have htrace : WordTrace (prefixWord ++ tailWord_1543767) baseStart_1543767 baseEnd_1543767 := by
    simpa [prefixWord, tailWord_1543767, baseEnd_1543767] using wordTrace_append hprefix tailTrace_1543767
  have hstable : (prefixWord ++ tailWord_1543767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543767).length < 2 ^ (prefixWord ++ tailWord_1543767).sum := by decide
  have hdescent : baseEnd_1543767 < baseStart_1543767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543831 : List Nat := [1, 1, 3, 3, 2, 3, 2, 3, 1, 2, 2]
def baseStart_1543831 : Nat := 118140960795 + 1543831 * 2 ^ 59
def prefixEnd_1543831 : Nat := 4983230072969 + 3 ^ 40 * 1543831 * 2
def baseEnd_1543831 : Nat := 792727352311454487812557

theorem tailTrace_1543831 : CollatzResearch.WordTrace tailWord_1543831 prefixEnd_1543831 792727352311454487812557 := by
  unfold tailWord_1543831
  simp only [CollatzResearch.WordTrace]
  refine ⟨56308142469971427188439347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37538761646647618125626231 56308142469971427188439347)
  ·
    refine ⟨84462213704957140782659021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56308142469971427188439347 84462213704957140782659021)
    ·
      refine ⟨31673330139358927793497133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84462213704957140782659021 31673330139358927793497133)
      ·
        refine ⟨11877498802259597922561425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31673330139358927793497133 11877498802259597922561425)
        ·
          refine ⟨8908124101694698441921069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11877498802259597922561425 8908124101694698441921069)
          ·
            refine ⟨3340546538135511915720401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8908124101694698441921069 3340546538135511915720401)
            ·
              refine ⟨2505409903601633936790301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3340546538135511915720401 2505409903601633936790301)
              ·
                refine ⟨939528713850612726296363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2505409903601633936790301 939528713850612726296363)
                ·
                  refine ⟨1409293070775919089444545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 939528713850612726296363 1409293070775919089444545)
                  ·
                    refine ⟨1056969803081939317083409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1409293070775919089444545 1056969803081939317083409)
                    ·
                      refine ⟨792727352311454487812557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1056969803081939317083409 792727352311454487812557)
                      ·
                        rfl

theorem cell23_1543831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_1543831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543831 prefixEnd_1543831 := by exact prefixLift 1543831
  have htrace : WordTrace (prefixWord ++ tailWord_1543831) baseStart_1543831 baseEnd_1543831 := by
    simpa [prefixWord, tailWord_1543831, baseEnd_1543831] using wordTrace_append hprefix tailTrace_1543831
  have hstable : (prefixWord ++ tailWord_1543831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543831).length < 2 ^ (prefixWord ++ tailWord_1543831).sum := by decide
  have hdescent : baseEnd_1543831 < baseStart_1543831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543883 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 4]
def baseStart_1543883 : Nat := 118140960795 + 1543883 * 2 ^ 59
def prefixEnd_1543883 : Nat := 4983230072969 + 3 ^ 40 * 1543883 * 2
def baseEnd_1543883 : Nat := 792754053305488284362317

theorem tailTrace_1543883 : CollatzResearch.WordTrace tailWord_1543883 prefixEnd_1543883 792754053305488284362317 := by
  unfold tailWord_1543883
  simp only [CollatzResearch.WordTrace]
  refine ⟨56310039065783040069332303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37540026043855360046221535 56310039065783040069332303)
  ·
    refine ⟨84465058598674560103998455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56310039065783040069332303 84465058598674560103998455)
    ·
      refine ⟨126697587898011840155997683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84465058598674560103998455 126697587898011840155997683)
      ·
        refine ⟨190046381847017760233996525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126697587898011840155997683 190046381847017760233996525)
        ·
          refine ⟨71267393192631660087748697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190046381847017760233996525 71267393192631660087748697)
          ·
            refine ⟨53450544894473745065811523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71267393192631660087748697 53450544894473745065811523)
            ·
              refine ⟨80175817341710617598717285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53450544894473745065811523 80175817341710617598717285)
              ·
                refine ⟨15032965751570740799759491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80175817341710617598717285 15032965751570740799759491)
                ·
                  refine ⟨22549448627356111199639237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15032965751570740799759491 22549448627356111199639237)
                  ·
                    refine ⟨4228021617629270849932357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22549448627356111199639237 4228021617629270849932357)
                    ·
                      refine ⟨792754053305488284362317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4228021617629270849932357 792754053305488284362317)
                      ·
                        rfl

theorem cell23_1543883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 4].length) (baseStart_1543883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543883 prefixEnd_1543883 := by exact prefixLift 1543883
  have htrace : WordTrace (prefixWord ++ tailWord_1543883) baseStart_1543883 baseEnd_1543883 := by
    simpa [prefixWord, tailWord_1543883, baseEnd_1543883] using wordTrace_append hprefix tailTrace_1543883
  have hstable : (prefixWord ++ tailWord_1543883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543883).length < 2 ^ (prefixWord ++ tailWord_1543883).sum := by decide
  have hdescent : baseEnd_1543883 < baseStart_1543883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543890 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 1, 3, 5]
def baseStart_1543890 : Nat := 118140960795 + 1543890 * 2 ^ 59
def prefixEnd_1543890 : Nat := 4983230072969 + 3 ^ 40 * 1543890 * 2
def baseEnd_1543890 : Nat := 792757647670069756974785

theorem tailTrace_1543890 : CollatzResearch.WordTrace tailWord_1543890 prefixEnd_1543890 792757647670069756974785 := by
  unfold tailWord_1543890
  simp only [CollatzResearch.WordTrace]
  refine ⟨14077573594189420066209281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37540196251171786843224749 14077573594189420066209281)
  ·
    refine ⟨10558180195642065049656961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14077573594189420066209281 10558180195642065049656961)
    ·
      refine ⟨7918635146731548787242721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10558180195642065049656961 7918635146731548787242721)
      ·
        refine ⟨5938976360048661590432041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7918635146731548787242721 5938976360048661590432041)
        ·
          refine ⟨4454232270036496192824031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5938976360048661590432041 4454232270036496192824031)
          ·
            refine ⟨6681348405054744289236047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4454232270036496192824031 6681348405054744289236047)
            ·
              refine ⟨10022022607582116433854071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6681348405054744289236047 10022022607582116433854071)
              ·
                refine ⟨15033033911373174650781107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10022022607582116433854071 15033033911373174650781107)
                ·
                  refine ⟨22549550867059761976171661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15033033911373174650781107 22549550867059761976171661)
                  ·
                    refine ⟨8456081575147410741064373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22549550867059761976171661 8456081575147410741064373)
                    ·
                      refine ⟨792757647670069756974785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8456081575147410741064373 792757647670069756974785)
                      ·
                        rfl

theorem cell23_1543890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_1543890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543890 prefixEnd_1543890 := by exact prefixLift 1543890
  have htrace : WordTrace (prefixWord ++ tailWord_1543890) baseStart_1543890 baseEnd_1543890 := by
    simpa [prefixWord, tailWord_1543890, baseEnd_1543890] using wordTrace_append hprefix tailTrace_1543890
  have hstable : (prefixWord ++ tailWord_1543890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543890).length < 2 ^ (prefixWord ++ tailWord_1543890).sum := by decide
  have hdescent : baseEnd_1543890 < baseStart_1543890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543903 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 7]
def baseStart_1543903 : Nat := 118140960795 + 1543903 * 2 ^ 59
def prefixEnd_1543903 : Nat := 4983230072969 + 3 ^ 40 * 1543903 * 2
def baseEnd_1543903 : Nat := 792764322918578206112225

theorem tailTrace_1543903 : CollatzResearch.WordTrace tailWord_1543903 prefixEnd_1543903 792764322918578206112225 := by
  unfold tailWord_1543903
  simp only [CollatzResearch.WordTrace]
  refine ⟨56310768525710583485060363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37540512350473722323373575 56310768525710583485060363)
  ·
    refine ⟨84466152788565875227590545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56310768525710583485060363 84466152788565875227590545)
    ·
      refine ⟨63349614591424406420692909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84466152788565875227590545 63349614591424406420692909)
      ·
        refine ⟨23756105471784152407759841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63349614591424406420692909 23756105471784152407759841)
        ·
          refine ⟨17817079103838114305819881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23756105471784152407759841 17817079103838114305819881)
          ·
            refine ⟨13362809327878585729364911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17817079103838114305819881 13362809327878585729364911)
            ·
              refine ⟨20044213991817878594047367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13362809327878585729364911 20044213991817878594047367)
              ·
                refine ⟨30066320987726817891071051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20044213991817878594047367 30066320987726817891071051)
                ·
                  refine ⟨45099481481590226836606577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30066320987726817891071051 45099481481590226836606577)
                  ·
                    refine ⟨33824611111192670127454933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45099481481590226836606577 33824611111192670127454933)
                    ·
                      refine ⟨792764322918578206112225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 33824611111192670127454933 792764322918578206112225)
                      ·
                        rfl

theorem cell23_1543903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_1543903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543903 prefixEnd_1543903 := by exact prefixLift 1543903
  have htrace : WordTrace (prefixWord ++ tailWord_1543903) baseStart_1543903 baseEnd_1543903 := by
    simpa [prefixWord, tailWord_1543903, baseEnd_1543903] using wordTrace_append hprefix tailTrace_1543903
  have hstable : (prefixWord ++ tailWord_1543903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543903).length < 2 ^ (prefixWord ++ tailWord_1543903).sum := by decide
  have hdescent : baseEnd_1543903 < baseStart_1543903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543921 : List Nat := [1, 2, 2, 2, 2, 3, 4, 1, 2, 2, 2]
def baseStart_1543921 : Nat := 118140960795 + 1543921 * 2 ^ 59
def prefixEnd_1543921 : Nat := 4983230072969 + 3 ^ 40 * 1543921 * 2
def baseEnd_1543921 : Nat := 792773565570359135687143

theorem tailTrace_1543921 : CollatzResearch.WordTrace tailWord_1543921 prefixEnd_1543921 792773565570359135687143 := by
  unfold tailWord_1543921
  simp only [CollatzResearch.WordTrace]
  refine ⟨56311425039645372559215617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37540950026430248372810411 56311425039645372559215617)
  ·
    refine ⟨42233568779734029419411713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56311425039645372559215617 42233568779734029419411713)
    ·
      refine ⟨31675176584800522064558785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42233568779734029419411713 31675176584800522064558785)
      ·
        refine ⟨23756382438600391548419089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31675176584800522064558785 23756382438600391548419089)
        ·
          refine ⟨17817286828950293661314317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23756382438600391548419089 17817286828950293661314317)
          ·
            refine ⟨6681482560856360122992869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17817286828950293661314317 6681482560856360122992869)
            ·
              refine ⟨1252777980160567523061163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6681482560856360122992869 1252777980160567523061163)
              ·
                refine ⟨1879166970240851284591745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1252777980160567523061163 1879166970240851284591745)
                ·
                  refine ⟨1409375227680638463443809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1879166970240851284591745 1409375227680638463443809)
                  ·
                    refine ⟨1057031420760478847582857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1409375227680638463443809 1057031420760478847582857)
                    ·
                      refine ⟨792773565570359135687143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1057031420760478847582857 792773565570359135687143)
                      ·
                        rfl

theorem cell23_1543921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 2, 2, 2].length) (baseStart_1543921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543921 prefixEnd_1543921 := by exact prefixLift 1543921
  have htrace : WordTrace (prefixWord ++ tailWord_1543921) baseStart_1543921 baseEnd_1543921 := by
    simpa [prefixWord, tailWord_1543921, baseEnd_1543921] using wordTrace_append hprefix tailTrace_1543921
  have hstable : (prefixWord ++ tailWord_1543921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543921).length < 2 ^ (prefixWord ++ tailWord_1543921).sum := by decide
  have hdescent : baseEnd_1543921 < baseStart_1543921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543923 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 3, 7]
def baseStart_1543923 : Nat := 118140960795 + 1543923 * 2 ^ 59
def prefixEnd_1543923 : Nat := 4983230072969 + 3 ^ 40 * 1543923 * 2
def baseEnd_1543923 : Nat := 264258197510556042620711

theorem tailTrace_1543923 : CollatzResearch.WordTrace tailWord_1543923 prefixEnd_1543923 264258197510556042620711 := by
  unfold tailWord_1543923
  simp only [CollatzResearch.WordTrace]
  refine ⟨56311497985638126900788423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37540998657092084600525615 56311497985638126900788423)
  ·
    refine ⟨84467246978457190351182635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56311497985638126900788423 84467246978457190351182635)
    ·
      refine ⟨126700870467685785526773953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84467246978457190351182635 126700870467685785526773953)
      ·
        refine ⟨95025652850764339145080465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126700870467685785526773953 95025652850764339145080465)
        ·
          refine ⟨71269239638073254358810349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95025652850764339145080465 71269239638073254358810349)
          ·
            refine ⟨26725964864277470384553881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71269239638073254358810349 26725964864277470384553881)
            ·
              refine ⟨20044473648208102788415411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26725964864277470384553881 20044473648208102788415411)
              ·
                refine ⟨30066710472312154182623117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20044473648208102788415411 30066710472312154182623117)
                ·
                  refine ⟨11275016427117057818483669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30066710472312154182623117 11275016427117057818483669)
                  ·
                    refine ⟨264258197510556042620711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11275016427117057818483669 264258197510556042620711)
                    ·
                      rfl

theorem cell23_1543923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 7].length) (baseStart_1543923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543923 prefixEnd_1543923 := by exact prefixLift 1543923
  have htrace : WordTrace (prefixWord ++ tailWord_1543923) baseStart_1543923 baseEnd_1543923 := by
    simpa [prefixWord, tailWord_1543923, baseEnd_1543923] using wordTrace_append hprefix tailTrace_1543923
  have hstable : (prefixWord ++ tailWord_1543923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543923).length < 2 ^ (prefixWord ++ tailWord_1543923).sum := by decide
  have hdescent : baseEnd_1543923 < baseStart_1543923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543924 : List Nat := [2, 6, 1, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_1543924 : Nat := 118140960795 + 1543924 * 2 ^ 59
def prefixEnd_1543924 : Nat := 4983230072969 + 3 ^ 40 * 1543924 * 2
def baseEnd_1543924 : Nat := 792775106012322623949629

theorem tailTrace_1543924 : CollatzResearch.WordTrace tailWord_1543924 prefixEnd_1543924 792775106012322623949629 := by
  unfold tailWord_1543924
  simp only [CollatzResearch.WordTrace]
  refine ⟨28155767229317252035787413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37541022972423002714383217 28155767229317252035787413)
  ·
    refine ⟨1319801588874246189177535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28155767229317252035787413 1319801588874246189177535)
    ·
      refine ⟨1979702383311369283766303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1319801588874246189177535 1979702383311369283766303)
      ·
        refine ⟨2969553574967053925649455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1979702383311369283766303 2969553574967053925649455)
        ·
          refine ⟨4454330362450580888474183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2969553574967053925649455 4454330362450580888474183)
          ·
            refine ⟨6681495543675871332711275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4454330362450580888474183 6681495543675871332711275)
            ·
              refine ⟨10022243315513806999066913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6681495543675871332711275 10022243315513806999066913)
              ·
                refine ⟨7516682486635355249300185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10022243315513806999066913 7516682486635355249300185)
                ·
                  refine ⟨5637511864976516436975139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7516682486635355249300185 5637511864976516436975139)
                  ·
                    refine ⟨8456267797464774655462709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5637511864976516436975139 8456267797464774655462709)
                    ·
                      refine ⟨792775106012322623949629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8456267797464774655462709 792775106012322623949629)
                      ·
                        rfl

theorem cell23_1543924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_1543924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543924 prefixEnd_1543924 := by exact prefixLift 1543924
  have htrace : WordTrace (prefixWord ++ tailWord_1543924) baseStart_1543924 baseEnd_1543924 := by
    simpa [prefixWord, tailWord_1543924, baseEnd_1543924] using wordTrace_append hprefix tailTrace_1543924
  have hstable : (prefixWord ++ tailWord_1543924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543924).length < 2 ^ (prefixWord ++ tailWord_1543924).sum := by decide
  have hdescent : baseEnd_1543924 < baseStart_1543924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543950 : List Nat := [4, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5]
def baseStart_1543950 : Nat := 118140960795 + 1543950 * 2 ^ 59
def prefixEnd_1543950 : Nat := 4983230072969 + 3 ^ 40 * 1543950 * 2
def baseEnd_1543950 : Nat := 792788456509339522224509

theorem tailTrace_1543950 : CollatzResearch.WordTrace tailWord_1543950 prefixEnd_1543950 792788456509339522224509 := by
  unfold tailWord_1543950
  simp only [CollatzResearch.WordTrace]
  refine ⟨7039060344567538814002663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37541655171026873674680869 7039060344567538814002663)
  ·
    refine ⟨10558590516851308221003995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7039060344567538814002663 10558590516851308221003995)
    ·
      refine ⟨15837885775276962331505993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10558590516851308221003995 15837885775276962331505993)
      ·
        refine ⟨11878414331457721748629495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15837885775276962331505993 11878414331457721748629495)
        ·
          refine ⟨17817621497186582622944243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11878414331457721748629495 17817621497186582622944243)
          ·
            refine ⟨26726432245779873934416365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17817621497186582622944243 26726432245779873934416365)
            ·
              refine ⟨10022412092167452725406137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26726432245779873934416365 10022412092167452725406137)
              ·
                refine ⟨7516809069125589544054603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10022412092167452725406137 7516809069125589544054603)
                ·
                  refine ⟨11275213603688384316081905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7516809069125589544054603 11275213603688384316081905)
                  ·
                    refine ⟨8456410202766288237061429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11275213603688384316081905 8456410202766288237061429)
                    ·
                      refine ⟨792788456509339522224509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8456410202766288237061429 792788456509339522224509)
                      ·
                        rfl

theorem cell23_1543950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_1543950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543950 prefixEnd_1543950 := by exact prefixLift 1543950
  have htrace : WordTrace (prefixWord ++ tailWord_1543950) baseStart_1543950 baseEnd_1543950 := by
    simpa [prefixWord, tailWord_1543950, baseEnd_1543950] using wordTrace_append hprefix tailTrace_1543950
  have hstable : (prefixWord ++ tailWord_1543950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543950).length < 2 ^ (prefixWord ++ tailWord_1543950).sum := by decide
  have hdescent : baseEnd_1543950 < baseStart_1543950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543994 : List Nat := [3, 1, 1, 1, 5, 3, 1, 1, 2, 1, 4]
def baseStart_1543994 : Nat := 118140960795 + 1543994 * 2 ^ 59
def prefixEnd_1543994 : Nat := 4983230072969 + 3 ^ 40 * 1543994 * 2
def baseEnd_1543994 : Nat := 792811049658137350074307

theorem tailTrace_1543994 : CollatzResearch.WordTrace tailWord_1543994 prefixEnd_1543994 792811049658137350074307 := by
  unfold tailWord_1543994
  simp only [CollatzResearch.WordTrace]
  refine ⟨14078521892095226506655759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37542725045587270684415357 14078521892095226506655759)
  ·
    refine ⟨21117782838142839759983639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14078521892095226506655759 21117782838142839759983639)
    ·
      refine ⟨31676674257214259639975459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21117782838142839759983639 31676674257214259639975459)
      ·
        refine ⟨47515011385821389459963189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31676674257214259639975459 47515011385821389459963189)
        ·
          refine ⟨4454532317420755261871549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47515011385821389459963189 4454532317420755261871549)
          ·
            refine ⟨1670449619032783223201831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4454532317420755261871549 1670449619032783223201831)
            ·
              refine ⟨2505674428549174834802747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1670449619032783223201831 2505674428549174834802747)
              ·
                refine ⟨3758511642823762252204121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2505674428549174834802747 3758511642823762252204121)
                ·
                  refine ⟨2818883732117821689153091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3758511642823762252204121 2818883732117821689153091)
                  ·
                    refine ⟨4228325598176732533729637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2818883732117821689153091 4228325598176732533729637)
                    ·
                      refine ⟨792811049658137350074307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4228325598176732533729637 792811049658137350074307)
                      ·
                        rfl

theorem cell23_1543994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 2, 1, 4].length) (baseStart_1543994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1543994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1543994 prefixEnd_1543994 := by exact prefixLift 1543994
  have htrace : WordTrace (prefixWord ++ tailWord_1543994) baseStart_1543994 baseEnd_1543994 := by
    simpa [prefixWord, tailWord_1543994, baseEnd_1543994] using wordTrace_append hprefix tailTrace_1543994
  have hstable : (prefixWord ++ tailWord_1543994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543994).length < 2 ^ (prefixWord ++ tailWord_1543994).sum := by decide
  have hdescent : baseEnd_1543994 < baseStart_1543994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544017 : List Nat := [1, 2, 2, 1, 5, 1, 3, 2, 6]
def baseStart_1544017 : Nat := 118140960795 + 1544017 * 2 ^ 59
def prefixEnd_1544017 : Nat := 4983230072969 + 3 ^ 40 * 1544017 * 2
def baseEnd_1544017 : Nat := 88091428857021195565189

theorem tailTrace_1544017 : CollatzResearch.WordTrace tailWord_1544017 prefixEnd_1544017 88091428857021195565189 := by
  unfold tailWord_1544017
  simp only [CollatzResearch.WordTrace]
  refine ⟨56314926447297580954710305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37543284298198387303140203 56314926447297580954710305)
  ·
    refine ⟨42236194835473185716032729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56314926447297580954710305 42236194835473185716032729)
    ·
      refine ⟨31677146126604889287024547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42236194835473185716032729 31677146126604889287024547)
      ·
        refine ⟨47515719189907333930536821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31677146126604889287024547 47515719189907333930536821)
        ·
          refine ⟨4454598674053812555987827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47515719189907333930536821 4454598674053812555987827)
          ·
            refine ⟨6681898011080718833981741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4454598674053812555987827 6681898011080718833981741)
            ·
              refine ⟨2505711754155269562743153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6681898011080718833981741 2505711754155269562743153)
              ·
                refine ⟨1879283815616452172057365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2505711754155269562743153 1879283815616452172057365)
                ·
                  refine ⟨88091428857021195565189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1879283815616452172057365 88091428857021195565189)
                  ·
                    rfl

theorem cell23_1544017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 6].length) (baseStart_1544017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544017 prefixEnd_1544017 := by exact prefixLift 1544017
  have htrace : WordTrace (prefixWord ++ tailWord_1544017) baseStart_1544017 baseEnd_1544017 := by
    simpa [prefixWord, tailWord_1544017, baseEnd_1544017] using wordTrace_append hprefix tailTrace_1544017
  have hstable : (prefixWord ++ tailWord_1544017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544017).length < 2 ^ (prefixWord ++ tailWord_1544017).sum := by decide
  have hdescent : baseEnd_1544017 < baseStart_1544017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544044 : List Nat := [2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 3]
def baseStart_1544044 : Nat := 118140960795 + 1544044 * 2 ^ 59
def prefixEnd_1544044 : Nat := 4983230072969 + 3 ^ 40 * 1544044 * 2
def baseEnd_1544044 : Nat := 792836723690862154449077

theorem tailTrace_1544044 : CollatzResearch.WordTrace tailWord_1544044 prefixEnd_1544044 792836723690862154449077 := by
  unfold tailWord_1544044
  simp only [CollatzResearch.WordTrace]
  refine ⟨28157955609099882282971593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37543940812133176377295457 28157955609099882282971593)
  ·
    refine ⟨21118466706824911712228695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28157955609099882282971593 21118466706824911712228695)
    ·
      refine ⟨31677700060237367568343043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21118466706824911712228695 31677700060237367568343043)
      ·
        refine ⟨47516550090356051352514565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31677700060237367568343043 47516550090356051352514565)
        ·
          refine ⟨8909353141941759628596481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47516550090356051352514565 8909353141941759628596481)
          ·
            refine ⟨6682014856456319721447361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8909353141941759628596481 6682014856456319721447361)
            ·
              refine ⟨5011511142342239791085521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6682014856456319721447361 5011511142342239791085521)
              ·
                refine ⟨3758633356756679843314141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5011511142342239791085521 3758633356756679843314141)
                ·
                  refine ⟨1409487508783754941242803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3758633356756679843314141 1409487508783754941242803)
                  ·
                    refine ⟨2114231263175632411864205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1409487508783754941242803 2114231263175632411864205)
                    ·
                      refine ⟨792836723690862154449077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2114231263175632411864205 792836723690862154449077)
                      ·
                        rfl

theorem cell23_1544044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 3].length) (baseStart_1544044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544044 prefixEnd_1544044 := by exact prefixLift 1544044
  have htrace : WordTrace (prefixWord ++ tailWord_1544044) baseStart_1544044 baseEnd_1544044 := by
    simpa [prefixWord, tailWord_1544044, baseEnd_1544044] using wordTrace_append hprefix tailTrace_1544044
  have hstable : (prefixWord ++ tailWord_1544044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544044).length < 2 ^ (prefixWord ++ tailWord_1544044).sum := by decide
  have hdescent : baseEnd_1544044 < baseStart_1544044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544071 : List Nat := [1, 1, 4, 2, 4, 1, 1, 2, 2, 3, 2]
def baseStart_1544071 : Nat := 118140960795 + 1544071 * 2 ^ 59
def prefixEnd_1544071 : Nat := 4983230072969 + 3 ^ 40 * 1544071 * 2
def baseEnd_1544071 : Nat := 792850587668533548811453

theorem tailTrace_1544071 : CollatzResearch.WordTrace tailWord_1544071 prefixEnd_1544071 792850587668533548811453 := by
  unfold tailWord_1544071
  simp only [CollatzResearch.WordTrace]
  refine ⟨56316895989101948177176067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37544597326067965451450711 56316895989101948177176067)
  ·
    refine ⟨84475343983652922265764101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56316895989101948177176067 84475343983652922265764101)
    ·
      refine ⟨15839126996934922924830769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84475343983652922265764101 15839126996934922924830769)
      ·
        refine ⟨11879345247701192193623077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15839126996934922924830769 11879345247701192193623077)
        ·
          refine ⟨2227377233943973536304327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11879345247701192193623077 2227377233943973536304327)
          ·
            refine ⟨3341065850915960304456491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2227377233943973536304327 3341065850915960304456491)
            ·
              refine ⟨5011598776373940456684737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3341065850915960304456491 5011598776373940456684737)
              ·
                refine ⟨3758699082280455342513553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5011598776373940456684737 3758699082280455342513553)
                ·
                  refine ⟨2819024311710341506885165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3758699082280455342513553 2819024311710341506885165)
                  ·
                    refine ⟨1057134116891378065081937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2819024311710341506885165 1057134116891378065081937)
                    ·
                      refine ⟨792850587668533548811453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1057134116891378065081937 792850587668533548811453)
                      ·
                        rfl

theorem cell23_1544071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_1544071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544071 prefixEnd_1544071 := by exact prefixLift 1544071
  have htrace : WordTrace (prefixWord ++ tailWord_1544071) baseStart_1544071 baseEnd_1544071 := by
    simpa [prefixWord, tailWord_1544071, baseEnd_1544071] using wordTrace_append hprefix tailTrace_1544071
  have hstable : (prefixWord ++ tailWord_1544071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544071).length < 2 ^ (prefixWord ++ tailWord_1544071).sum := by decide
  have hdescent : baseEnd_1544071 < baseStart_1544071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544080 : List Nat := [2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 6]
def baseStart_1544080 : Nat := 118140960795 + 1544080 * 2 ^ 59
def prefixEnd_1544080 : Nat := 4983230072969 + 3 ^ 40 * 1544080 * 2
def baseEnd_1544080 : Nat := 792855208994424013598911

theorem tailTrace_1544080 : CollatzResearch.WordTrace tailWord_1544080 prefixEnd_1544080 792855208994424013598911 := by
  unfold tailWord_1544080
  simp only [CollatzResearch.WordTrace]
  refine ⟨28158612123034671357126847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37544816164046228476169129 28158612123034671357126847)
  ·
    refine ⟨42237918184552007035690271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28158612123034671357126847 42237918184552007035690271)
    ·
      refine ⟨63356877276828010553535407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42237918184552007035690271 63356877276828010553535407)
      ·
        refine ⟨95035315915242015830303111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63356877276828010553535407 95035315915242015830303111)
        ·
          refine ⟨142552973872863023745454667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95035315915242015830303111 142552973872863023745454667)
          ·
            refine ⟨213829460809294535618182001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142552973872863023745454667 213829460809294535618182001)
            ·
              refine ⟨160372095606970901713636501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213829460809294535618182001 160372095606970901713636501)
              ·
                refine ⟨7517441981576761017826711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 160372095606970901713636501 7517441981576761017826711)
                ·
                  refine ⟨11276162972365141526740067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7517441981576761017826711 11276162972365141526740067)
                  ·
                    refine ⟨16914244458547712290110101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11276162972365141526740067 16914244458547712290110101)
                    ·
                      refine ⟨792855208994424013598911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16914244458547712290110101 792855208994424013598911)
                      ·
                        rfl

theorem cell23_1544080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 6].length) (baseStart_1544080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544080 prefixEnd_1544080 := by exact prefixLift 1544080
  have htrace : WordTrace (prefixWord ++ tailWord_1544080) baseStart_1544080 baseEnd_1544080 := by
    simpa [prefixWord, tailWord_1544080, baseEnd_1544080] using wordTrace_append hprefix tailTrace_1544080
  have hstable : (prefixWord ++ tailWord_1544080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544080).length < 2 ^ (prefixWord ++ tailWord_1544080).sum := by decide
  have hdescent : baseEnd_1544080 < baseStart_1544080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544087 : List Nat := [1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 5]
def baseStart_1544087 : Nat := 118140960795 + 1544087 * 2 ^ 59
def prefixEnd_1544087 : Nat := 4983230072969 + 3 ^ 40 * 1544087 * 2
def baseEnd_1544087 : Nat := 792858803359005486211379

theorem tailTrace_1544087 : CollatzResearch.WordTrace tailWord_1544087 prefixEnd_1544087 792858803359005486211379 := by
  unfold tailWord_1544087
  simp only [CollatzResearch.WordTrace]
  refine ⟨56317479557043982909758515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37544986371362655273172343 56317479557043982909758515)
  ·
    refine ⟨84476219335565974364637773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56317479557043982909758515 84476219335565974364637773)
    ·
      refine ⟨31678582250837240386739165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84476219335565974364637773 31678582250837240386739165)
      ·
        refine ⟨11879468344063965145027187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31678582250837240386739165 11879468344063965145027187)
        ·
          refine ⟨17819202516095947717540781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11879468344063965145027187 17819202516095947717540781)
          ·
            refine ⟨6682200943535980394077793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17819202516095947717540781 6682200943535980394077793)
            ·
              refine ⟨5011650707651985295558345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6682200943535980394077793 5011650707651985295558345)
              ·
                refine ⟨3758738030738988971668759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5011650707651985295558345 3758738030738988971668759)
                ·
                  refine ⟨5638107046108483457503139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3758738030738988971668759 5638107046108483457503139)
                  ·
                    refine ⟨8457160569162725186254709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5638107046108483457503139 8457160569162725186254709)
                    ·
                      refine ⟨792858803359005486211379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8457160569162725186254709 792858803359005486211379)
                      ·
                        rfl

theorem cell23_1544087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_1544087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544087 prefixEnd_1544087 := by exact prefixLift 1544087
  have htrace : WordTrace (prefixWord ++ tailWord_1544087) baseStart_1544087 baseEnd_1544087 := by
    simpa [prefixWord, tailWord_1544087, baseEnd_1544087] using wordTrace_append hprefix tailTrace_1544087
  have hstable : (prefixWord ++ tailWord_1544087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544087).length < 2 ^ (prefixWord ++ tailWord_1544087).sum := by decide
  have hdescent : baseEnd_1544087 < baseStart_1544087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544098 : List Nat := [3, 3, 1, 2, 4, 1, 1, 2, 1, 5]
def baseStart_1544098 : Nat := 118140960795 + 1544098 * 2 ^ 59
def prefixEnd_1544098 : Nat := 4983230072969 + 3 ^ 40 * 1544098 * 2
def baseEnd_1544098 : Nat := 264288150548734981057943

theorem tailTrace_1544098 : CollatzResearch.WordTrace tailWord_1544098 prefixEnd_1544098 264288150548734981057943 := by
  unfold tailWord_1544098
  simp only [CollatzResearch.WordTrace]
  refine ⟨14079470190001032947102237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37545253840002754525605965 14079470190001032947102237)
  ·
    refine ⟨5279801321250387355163339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14079470190001032947102237 5279801321250387355163339)
    ·
      refine ⟨7919701981875581032745009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5279801321250387355163339 7919701981875581032745009)
      ·
        refine ⟨5939776486406685774558757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7919701981875581032745009 5939776486406685774558757)
        ·
          refine ⟨1113708091201253582729767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5939776486406685774558757 1113708091201253582729767)
          ·
            refine ⟨1670562136801880374094651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1113708091201253582729767 1670562136801880374094651)
            ·
              refine ⟨2505843205202820561141977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1670562136801880374094651 2505843205202820561141977)
              ·
                refine ⟨1879382403902115420856483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2505843205202820561141977 1879382403902115420856483)
                ·
                  refine ⟨2819073605853173131284725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1879382403902115420856483 2819073605853173131284725)
                  ·
                    refine ⟨264288150548734981057943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2819073605853173131284725 264288150548734981057943)
                    ·
                      rfl

theorem cell23_1544098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_1544098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544098 prefixEnd_1544098 := by exact prefixLift 1544098
  have htrace : WordTrace (prefixWord ++ tailWord_1544098) baseStart_1544098 baseEnd_1544098 := by
    simpa [prefixWord, tailWord_1544098, baseEnd_1544098] using wordTrace_append hprefix tailTrace_1544098
  have hstable : (prefixWord ++ tailWord_1544098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544098).length < 2 ^ (prefixWord ++ tailWord_1544098).sum := by decide
  have hdescent : baseEnd_1544098 < baseStart_1544098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544121 : List Nat := [1, 2, 1, 4, 2, 1, 5, 1, 1, 2, 3]
def baseStart_1544121 : Nat := 118140960795 + 1544121 * 2 ^ 59
def prefixEnd_1544121 : Nat := 4983230072969 + 3 ^ 40 * 1544121 * 2
def baseEnd_1544121 : Nat := 792876261701258353186223

theorem tailTrace_1544121 : CollatzResearch.WordTrace tailWord_1544121 prefixEnd_1544121 792876261701258353186223 := by
  unfold tailWord_1544121
  simp only [CollatzResearch.WordTrace]
  refine ⟨56318719638920806716496217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37545813092613871144330811 56318719638920806716496217)
  ·
    refine ⟨42239039729190605037372163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56318719638920806716496217 42239039729190605037372163)
    ·
      refine ⟨63358559593785907556058245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42239039729190605037372163 63358559593785907556058245)
      ·
        refine ⟨11879729923834857666760921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63358559593785907556058245 11879729923834857666760921)
        ·
          refine ⟨8909797442876143250070691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11879729923834857666760921 8909797442876143250070691)
          ·
            refine ⟨13364696164314214875106037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8909797442876143250070691 13364696164314214875106037)
            ·
              refine ⟨1252940265404457644541191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13364696164314214875106037 1252940265404457644541191)
              ·
                refine ⟨1879410398106686466811787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1252940265404457644541191 1879410398106686466811787)
                ·
                  refine ⟨2819115597160029700217681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1879410398106686466811787 2819115597160029700217681)
                  ·
                    refine ⟨2114336697870022275163261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2819115597160029700217681 2114336697870022275163261)
                    ·
                      refine ⟨792876261701258353186223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2114336697870022275163261 792876261701258353186223)
                      ·
                        rfl

theorem cell23_1544121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_1544121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544121 prefixEnd_1544121 := by exact prefixLift 1544121
  have htrace : WordTrace (prefixWord ++ tailWord_1544121) baseStart_1544121 baseEnd_1544121 := by
    simpa [prefixWord, tailWord_1544121, baseEnd_1544121] using wordTrace_append hprefix tailTrace_1544121
  have hstable : (prefixWord ++ tailWord_1544121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544121).length < 2 ^ (prefixWord ++ tailWord_1544121).sum := by decide
  have hdescent : baseEnd_1544121 < baseStart_1544121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544124 : List Nat := [2, 2, 2, 5, 2, 10]
def baseStart_1544124 : Nat := 118140960795 + 1544124 * 2 ^ 59
def prefixEnd_1544124 : Nat := 4983230072969 + 3 ^ 40 * 1544124 * 2
def baseEnd_1544124 : Nat := 3262871613758114573863

theorem tailTrace_1544124 : CollatzResearch.WordTrace tailWord_1544124 prefixEnd_1544124 3262871613758114573863 := by
  unfold tailWord_1544124
  simp only [CollatzResearch.WordTrace]
  refine ⟨28159414528954969114427713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37545886038606625485903617 28159414528954969114427713)
  ·
    refine ⟨21119560896716226835820785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28159414528954969114427713 21119560896716226835820785)
    ·
      refine ⟨15839670672537170126865589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21119560896716226835820785 15839670672537170126865589)
      ·
        refine ⟨1484969125550359699393649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15839670672537170126865589 1484969125550359699393649)
        ·
          refine ⟨1113726844162769774545237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1484969125550359699393649 1113726844162769774545237)
          ·
            refine ⟨3262871613758114573863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1113726844162769774545237 3262871613758114573863)
            ·
              rfl

theorem cell23_1544124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 10].length) (baseStart_1544124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544124 prefixEnd_1544124 := by exact prefixLift 1544124
  have htrace : WordTrace (prefixWord ++ tailWord_1544124) baseStart_1544124 baseEnd_1544124 := by
    simpa [prefixWord, tailWord_1544124, baseEnd_1544124] using wordTrace_append hprefix tailTrace_1544124
  have hstable : (prefixWord ++ tailWord_1544124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544124).length < 2 ^ (prefixWord ++ tailWord_1544124).sum := by decide
  have hdescent : baseEnd_1544124 < baseStart_1544124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544144 : List Nat := [2, 1, 1, 1, 1, 2, 5, 2, 3, 3, 2]
def baseStart_1544144 : Nat := 118140960795 + 1544144 * 2 ^ 59
def prefixEnd_1544144 : Nat := 4983230072969 + 3 ^ 40 * 1544144 * 2
def baseEnd_1544144 : Nat := 792888071756311763198617

theorem tailTrace_1544144 : CollatzResearch.WordTrace tailWord_1544144 prefixEnd_1544144 792888071756311763198617 := by
  unfold tailWord_1544144
  simp only [CollatzResearch.WordTrace]
  refine ⟨28159779258918740822291743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37546372345224987763055657 28159779258918740822291743)
  ·
    refine ⟨42239668888378111233437615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28159779258918740822291743 42239668888378111233437615)
    ·
      refine ⟨63359503332567166850156423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42239668888378111233437615 63359503332567166850156423)
      ·
        refine ⟨95039254998850750275234635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63359503332567166850156423 95039254998850750275234635)
        ·
          refine ⟨142558882498276125412851953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95039254998850750275234635 142558882498276125412851953)
          ·
            refine ⟨106919161873707094059638965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142558882498276125412851953 106919161873707094059638965)
            ·
              refine ⟨10023671425660040068091153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106919161873707094059638965 10023671425660040068091153)
              ·
                refine ⟨7517753569245030051068365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10023671425660040068091153 7517753569245030051068365)
                ·
                  refine ⟨2819157588466886269150637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7517753569245030051068365 2819157588466886269150637)
                  ·
                    refine ⟨1057184095675082350931489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2819157588466886269150637 1057184095675082350931489)
                    ·
                      refine ⟨792888071756311763198617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1057184095675082350931489 792888071756311763198617)
                      ·
                        rfl

theorem cell23_1544144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 3, 3, 2].length) (baseStart_1544144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544144 prefixEnd_1544144 := by exact prefixLift 1544144
  have htrace : WordTrace (prefixWord ++ tailWord_1544144) baseStart_1544144 baseEnd_1544144 := by
    simpa [prefixWord, tailWord_1544144, baseEnd_1544144] using wordTrace_append hprefix tailTrace_1544144
  have hstable : (prefixWord ++ tailWord_1544144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544144).length < 2 ^ (prefixWord ++ tailWord_1544144).sum := by decide
  have hdescent : baseEnd_1544144 < baseStart_1544144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544187 : List Nat := [1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 4]
def baseStart_1544187 : Nat := 118140960795 + 1544187 * 2 ^ 59
def prefixEnd_1544187 : Nat := 4983230072969 + 3 ^ 40 * 1544187 * 2
def baseEnd_1544187 : Nat := 792910151424455094960919

theorem tailTrace_1544187 : CollatzResearch.WordTrace tailWord_1544187 prefixEnd_1544187 792910151424455094960919 := by
  unfold tailWord_1544187
  simp only [CollatzResearch.WordTrace]
  refine ⟨56321126856681699988398815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37547417904454466658932543 56321126856681699988398815)
  ·
    refine ⟨84481690285022549982598223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56321126856681699988398815 84481690285022549982598223)
    ·
      refine ⟨126722535427533824973897335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84481690285022549982598223 126722535427533824973897335)
      ·
        refine ⟨190083803141300737460846003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126722535427533824973897335 190083803141300737460846003)
        ·
          refine ⟨285125704711951106191269005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190083803141300737460846003 285125704711951106191269005)
          ·
            refine ⟨106922139266981664821725877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285125704711951106191269005 106922139266981664821725877)
            ·
              refine ⟨10023950556279531077036801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106922139266981664821725877 10023950556279531077036801)
              ·
                refine ⟨7517962917209648307777601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10023950556279531077036801 7517962917209648307777601)
                ·
                  refine ⟨5638472187907236230833201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7517962917209648307777601 5638472187907236230833201)
                  ·
                    refine ⟨4228854140930427173124901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5638472187907236230833201 4228854140930427173124901)
                    ·
                      refine ⟨792910151424455094960919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4228854140930427173124901 792910151424455094960919)
                      ·
                        rfl

theorem cell23_1544187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 4].length) (baseStart_1544187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544187 prefixEnd_1544187 := by exact prefixLift 1544187
  have htrace : WordTrace (prefixWord ++ tailWord_1544187) baseStart_1544187 baseEnd_1544187 := by
    simpa [prefixWord, tailWord_1544187, baseEnd_1544187] using wordTrace_append hprefix tailTrace_1544187
  have hstable : (prefixWord ++ tailWord_1544187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544187).length < 2 ^ (prefixWord ++ tailWord_1544187).sum := by decide
  have hdescent : baseEnd_1544187 < baseStart_1544187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544197 : List Nat := [1, 3, 1, 1, 2, 4, 1, 3, 7]
def baseStart_1544197 : Nat := 118140960795 + 1544197 * 2 ^ 59
def prefixEnd_1544197 : Nat := 4983230072969 + 3 ^ 40 * 1544197 * 2
def baseEnd_1544197 : Nat := 88101698470111117315097

theorem tailTrace_1544197 : CollatzResearch.WordTrace tailWord_1544197 prefixEnd_1544197 88101698470111117315097 := by
  unfold tailWord_1544197
  simp only [CollatzResearch.WordTrace]
  refine ⟨56321491586645471696262845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37547661057763647797508563 56321491586645471696262845)
  ·
    refine ⟨21120559344992051886098567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56321491586645471696262845 21120559344992051886098567)
    ·
      refine ⟨31680839017488077829147851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21120559344992051886098567 31680839017488077829147851)
      ·
        refine ⟨47521258526232116743721777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31680839017488077829147851 47521258526232116743721777)
        ·
          refine ⟨35640943894674087557791333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47521258526232116743721777 35640943894674087557791333)
          ·
            refine ⟨6682676980251391417085875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35640943894674087557791333 6682676980251391417085875)
            ·
              refine ⟨10024015470377087125628813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6682676980251391417085875 10024015470377087125628813)
              ·
                refine ⟨3759005801391407672110805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10024015470377087125628813 3759005801391407672110805)
                ·
                  refine ⟨88101698470111117315097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3759005801391407672110805 88101698470111117315097)
                  ·
                    rfl

theorem cell23_1544197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 7].length) (baseStart_1544197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544197 prefixEnd_1544197 := by exact prefixLift 1544197
  have htrace : WordTrace (prefixWord ++ tailWord_1544197) baseStart_1544197 baseEnd_1544197 := by
    simpa [prefixWord, tailWord_1544197, baseEnd_1544197] using wordTrace_append hprefix tailTrace_1544197
  have hstable : (prefixWord ++ tailWord_1544197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544197).length < 2 ^ (prefixWord ++ tailWord_1544197).sum := by decide
  have hdescent : baseEnd_1544197 < baseStart_1544197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544212 : List Nat := [2, 4, 3, 2, 1, 1, 2, 2, 1, 3, 2]
def baseStart_1544212 : Nat := 118140960795 + 1544212 * 2 ^ 59
def prefixEnd_1544212 : Nat := 4983230072969 + 3 ^ 40 * 1544212 * 2
def baseEnd_1544212 : Nat := 792922988440817497148305

theorem tailTrace_1544212 : CollatzResearch.WordTrace tailWord_1544212 prefixEnd_1544212 792922988440817497148305 := by
  unfold tailWord_1544212
  simp only [CollatzResearch.WordTrace]
  refine ⟨28161019340795564629029445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37548025787727419505372593 28161019340795564629029445)
  ·
    refine ⟨5280191126399168367943021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28161019340795564629029445 5280191126399168367943021)
    ·
      refine ⟨1980071672399688137978633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5280191126399168367943021 1980071672399688137978633)
      ·
        refine ⟨1485053754299766103483975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1980071672399688137978633 1485053754299766103483975)
        ·
          refine ⟨2227580631449649155225963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1485053754299766103483975 2227580631449649155225963)
          ·
            refine ⟨3341370947174473732838945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2227580631449649155225963 3341370947174473732838945)
            ·
              refine ⟨2506028210380855299629209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3341370947174473732838945 2506028210380855299629209)
              ·
                refine ⟨1879521157785641474721907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2506028210380855299629209 1879521157785641474721907)
                ·
                  refine ⟨2819281736678462212082861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1879521157785641474721907 2819281736678462212082861)
                  ·
                    refine ⟨1057230651254423329531073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2819281736678462212082861 1057230651254423329531073)
                    ·
                      refine ⟨792922988440817497148305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1057230651254423329531073 792922988440817497148305)
                      ·
                        rfl

theorem cell23_1544212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_1544212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544212 prefixEnd_1544212 := by exact prefixLift 1544212
  have htrace : WordTrace (prefixWord ++ tailWord_1544212) baseStart_1544212 baseEnd_1544212 := by
    simpa [prefixWord, tailWord_1544212, baseEnd_1544212] using wordTrace_append hprefix tailTrace_1544212
  have hstable : (prefixWord ++ tailWord_1544212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544212).length < 2 ^ (prefixWord ++ tailWord_1544212).sum := by decide
  have hdescent : baseEnd_1544212 < baseStart_1544212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544227 : List Nat := [1, 1, 1, 4, 3, 1, 1, 3, 1, 7]
def baseStart_1544227 : Nat := 118140960795 + 1544227 * 2 ^ 59
def prefixEnd_1544227 : Nat := 4983230072969 + 3 ^ 40 * 1544227 * 2
def baseEnd_1544227 : Nat := 264310230216878312820245

theorem tailTrace_1544227 : CollatzResearch.WordTrace tailWord_1544227 prefixEnd_1544227 264310230216878312820245 := by
  unfold tailWord_1544227
  simp only [CollatzResearch.WordTrace]
  refine ⟨56322585776536786819854935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37548390517691191213236623 56322585776536786819854935)
  ·
    refine ⟨84483878664805180229782403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56322585776536786819854935 84483878664805180229782403)
    ·
      refine ⟨126725817997207770344673605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84483878664805180229782403 126725817997207770344673605)
      ·
        refine ⟨23761090874476456939626301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126725817997207770344673605 23761090874476456939626301)
        ·
          refine ⟨8910409077928671352359863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23761090874476456939626301 8910409077928671352359863)
          ·
            refine ⟨13365613616893007028539795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8910409077928671352359863 13365613616893007028539795)
            ·
              refine ⟨20048420425339510542809693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13365613616893007028539795 20048420425339510542809693)
              ·
                refine ⟨7518157659502316453553635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20048420425339510542809693 7518157659502316453553635)
                ·
                  refine ⟨11277236489253474680330453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7518157659502316453553635 11277236489253474680330453)
                  ·
                    refine ⟨264310230216878312820245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11277236489253474680330453 264310230216878312820245)
                    ·
                      rfl

theorem cell23_1544227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 7].length) (baseStart_1544227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544227 prefixEnd_1544227 := by exact prefixLift 1544227
  have htrace : WordTrace (prefixWord ++ tailWord_1544227) baseStart_1544227 baseEnd_1544227 := by
    simpa [prefixWord, tailWord_1544227, baseEnd_1544227] using wordTrace_append hprefix tailTrace_1544227
  have hstable : (prefixWord ++ tailWord_1544227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544227).length < 2 ^ (prefixWord ++ tailWord_1544227).sum := by decide
  have hdescent : baseEnd_1544227 < baseStart_1544227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544248 : List Nat := [2, 1, 2, 1, 6, 1, 3, 2, 5]
def baseStart_1544248 : Nat := 118140960795 + 1544248 * 2 ^ 59
def prefixEnd_1544248 : Nat := 4983230072969 + 3 ^ 40 * 1544248 * 2
def baseEnd_1544248 : Nat := 88104608193819928477571

theorem tailTrace_1544248 : CollatzResearch.WordTrace tailWord_1544248 prefixEnd_1544248 88104608193819928477571 := by
  unfold tailWord_1544248
  simp only [CollatzResearch.WordTrace]
  refine ⟨28161675854730353703184699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37548901139640471604246265 28161675854730353703184699)
  ·
    refine ⟨42242513782095530554777049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28161675854730353703184699 42242513782095530554777049)
    ·
      refine ⟨31681885336571647916082787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42242513782095530554777049 31681885336571647916082787)
      ·
        refine ⟨47522828004857471874124181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31681885336571647916082787 47522828004857471874124181)
        ·
          refine ⟨2227632562727693994099571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47522828004857471874124181 2227632562727693994099571)
          ·
            refine ⟨3341448844091540991149357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2227632562727693994099571 3341448844091540991149357)
            ·
              refine ⟨1253043316534327871681009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3341448844091540991149357 1253043316534327871681009)
              ·
                refine ⟨939782487400745903760757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1253043316534327871681009 939782487400745903760757)
                ·
                  refine ⟨88104608193819928477571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 939782487400745903760757 88104608193819928477571)
                  ·
                    rfl

theorem cell23_1544248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 2, 5].length) (baseStart_1544248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544248 prefixEnd_1544248 := by exact prefixLift 1544248
  have htrace : WordTrace (prefixWord ++ tailWord_1544248) baseStart_1544248 baseEnd_1544248 := by
    simpa [prefixWord, tailWord_1544248, baseEnd_1544248] using wordTrace_append hprefix tailTrace_1544248
  have hstable : (prefixWord ++ tailWord_1544248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544248).length < 2 ^ (prefixWord ++ tailWord_1544248).sum := by decide
  have hdescent : baseEnd_1544248 < baseStart_1544248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544278 : List Nat := [5, 2, 2, 1, 1, 1, 1, 3, 2, 5]
def baseStart_1544278 : Nat := 118140960795 + 1544278 * 2 ^ 59
def prefixEnd_1544278 : Nat := 4983230072969 + 3 ^ 40 * 1544278 * 2
def baseEnd_1544278 : Nat := 264318959388004746307667

theorem tailTrace_1544278 : CollatzResearch.WordTrace tailWord_1544278 prefixEnd_1544278 264318959388004746307667 := by
  unfold tailWord_1544278
  simp only [CollatzResearch.WordTrace]
  refine ⟨3520277868709501408122593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37549630599568015019974325 3520277868709501408122593)
  ·
    refine ⟨2640208401532126056091945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3520277868709501408122593 2640208401532126056091945)
    ·
      refine ⟨1980156301149094542068959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2640208401532126056091945 1980156301149094542068959)
      ·
        refine ⟨2970234451723641813103439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1980156301149094542068959 2970234451723641813103439)
        ·
          refine ⟨4455351677585462719655159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2970234451723641813103439 4455351677585462719655159)
          ·
            refine ⟨6683027516378194079482739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4455351677585462719655159 6683027516378194079482739)
            ·
              refine ⟨10024541274567291119224109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6683027516378194079482739 10024541274567291119224109)
              ·
                refine ⟨3759202977962734169709041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10024541274567291119224109 3759202977962734169709041)
                ·
                  refine ⟨2819402233472050627281781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3759202977962734169709041 2819402233472050627281781)
                  ·
                    refine ⟨264318959388004746307667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2819402233472050627281781 264318959388004746307667)
                    ·
                      rfl

theorem cell23_1544278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_1544278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544278 prefixEnd_1544278 := by exact prefixLift 1544278
  have htrace : WordTrace (prefixWord ++ tailWord_1544278) baseStart_1544278 baseEnd_1544278 := by
    simpa [prefixWord, tailWord_1544278, baseEnd_1544278] using wordTrace_append hprefix tailTrace_1544278
  have hstable : (prefixWord ++ tailWord_1544278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544278).length < 2 ^ (prefixWord ++ tailWord_1544278).sum := by decide
  have hdescent : baseEnd_1544278 < baseStart_1544278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544287 : List Nat := [1, 1, 2, 3, 1, 1, 2, 4, 8]
def baseStart_1544287 : Nat := 118140960795 + 1544287 * 2 ^ 59
def prefixEnd_1544287 : Nat := 4983230072969 + 3 ^ 40 * 1544287 * 2
def baseEnd_1544287 : Nat := 88106833276656078190051

theorem tailTrace_1544287 : CollatzResearch.WordTrace tailWord_1544287 prefixEnd_1544287 88106833276656078190051 := by
  unfold tailWord_1544287
  simp only [CollatzResearch.WordTrace]
  refine ⟨56324774156319417067039115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37549849437546278044692743 56324774156319417067039115)
  ·
    refine ⟨84487161234479125600558673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56324774156319417067039115 84487161234479125600558673)
    ·
      refine ⟨63365370925859344200419005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84487161234479125600558673 63365370925859344200419005)
      ·
        refine ⟨23762014097197254075157127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63365370925859344200419005 23762014097197254075157127)
        ·
          refine ⟨35643021145795881112735691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23762014097197254075157127 35643021145795881112735691)
          ·
            refine ⟨53464531718693821669103537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35643021145795881112735691 53464531718693821669103537)
            ·
              refine ⟨40098398789020366251827653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53464531718693821669103537 40098398789020366251827653)
              ·
                refine ⟨7518449772941318672217685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40098398789020366251827653 7518449772941318672217685)
                ·
                  refine ⟨88106833276656078190051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7518449772941318672217685 88106833276656078190051)
                  ·
                    rfl

theorem cell23_1544287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 8].length) (baseStart_1544287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1544287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1544287 prefixEnd_1544287 := by exact prefixLift 1544287
  have htrace : WordTrace (prefixWord ++ tailWord_1544287) baseStart_1544287 baseEnd_1544287 := by
    simpa [prefixWord, tailWord_1544287, baseEnd_1544287] using wordTrace_append hprefix tailTrace_1544287
  have hstable : (prefixWord ++ tailWord_1544287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544287).length < 2 ^ (prefixWord ++ tailWord_1544287).sum := by decide
  have hdescent : baseEnd_1544287 < baseStart_1544287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
