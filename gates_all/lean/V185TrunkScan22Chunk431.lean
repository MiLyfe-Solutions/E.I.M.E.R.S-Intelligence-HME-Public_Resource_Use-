import V185TrunkScan22Chunk430

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3843339 : List Nat := [1, 1, 1, 1, 5, 3, 4, 6]
def baseStart_3843339 : Nat := 118140960795 + 3843339 * 2 ^ 59
def prefixEnd_3843339 : Nat := 4983230072969 + 3 ^ 40 * 3843339 * 2
def baseEnd_3843339 : Nat := 146183720382995826087949

theorem tailTrace_3843339 : CollatzResearch.WordTrace tailWord_3843339 prefixEnd_3843339 146183720382995826087949 := by
  unfold tailWord_3843339
  simp only [CollatzResearch.WordTrace]
  refine ⟨140178089423246667888429071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93452059615497778592286047 140178089423246667888429071)
  ·
    refine ⟨210267134134870001832643607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140178089423246667888429071 210267134134870001832643607)
    ·
      refine ⟨315400701202305002748965411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210267134134870001832643607 315400701202305002748965411)
      ·
        refine ⟨473101051803457504123448117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315400701202305002748965411 473101051803457504123448117)
        ·
          refine ⟨44353223606574141011573261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 473101051803457504123448117 44353223606574141011573261)
          ·
            refine ⟨16632458852465302879339973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44353223606574141011573261 16632458852465302879339973)
            ·
              refine ⟨3118586034837244289876245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16632458852465302879339973 3118586034837244289876245)
              ·
                refine ⟨146183720382995826087949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3118586034837244289876245 146183720382995826087949)
                ·
                  rfl

theorem cell22_3843339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 6].length) (baseStart_3843339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843339 prefixEnd_3843339 := by exact prefixLift 3843339
  have htrace : WordTrace (prefixWord ++ tailWord_3843339) baseStart_3843339 baseEnd_3843339 := by
    simpa [prefixWord, tailWord_3843339, baseEnd_3843339] using wordTrace_append hprefix tailTrace_3843339
  have hstable : (prefixWord ++ tailWord_3843339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843339).length < 2 ^ (prefixWord ++ tailWord_3843339).sum := by decide
  have hdescent : baseEnd_3843339 < baseStart_3843339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843429 : List Nat := [1, 3, 1, 3, 1, 2, 2, 3, 6]
def baseStart_3843429 : Nat := 118140960795 + 3843429 * 2 ^ 59
def prefixEnd_3843429 : Nat := 4983230072969 + 3 ^ 40 * 3843429 * 2
def baseEnd_3843429 : Nat := 438561430762077400013755

theorem tailTrace_3843429 : CollatzResearch.WordTrace tailWord_3843429 prefixEnd_3843429 438561430762077400013755 := by
  unfold tailWord_3843429
  simp only [CollatzResearch.WordTrace]
  refine ⟨140181371992920613259205341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93454247995280408839470227 140181371992920613259205341)
  ·
    refine ⟨52568014497345229972202003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140181371992920613259205341 52568014497345229972202003)
    ·
      refine ⟨78852021746017844958303005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52568014497345229972202003 78852021746017844958303005)
      ·
        refine ⟨29569508154756691859363627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78852021746017844958303005 29569508154756691859363627)
        ·
          refine ⟨44354262232135037789045441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29569508154756691859363627 44354262232135037789045441)
          ·
            refine ⟨33265696674101278341784081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44354262232135037789045441 33265696674101278341784081)
            ·
              refine ⟨24949272505575958756338061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33265696674101278341784081 24949272505575958756338061)
              ·
                refine ⟨9355977189590984533626773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24949272505575958756338061 9355977189590984533626773)
                ·
                  refine ⟨438561430762077400013755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9355977189590984533626773 438561430762077400013755)
                  ·
                    rfl

theorem cell22_3843429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 6].length) (baseStart_3843429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843429 prefixEnd_3843429 := by exact prefixLift 3843429
  have htrace : WordTrace (prefixWord ++ tailWord_3843429) baseStart_3843429 baseEnd_3843429 := by
    simpa [prefixWord, tailWord_3843429, baseEnd_3843429] using wordTrace_append hprefix tailTrace_3843429
  have hstable : (prefixWord ++ tailWord_3843429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843429).length < 2 ^ (prefixWord ++ tailWord_3843429).sum := by decide
  have hdescent : baseEnd_3843429 < baseStart_3843429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843463 : List Nat := [1, 1, 4, 2, 2, 3, 2, 3, 4]
def baseStart_3843463 : Nat := 118140960795 + 3843463 * 2 ^ 59
def prefixEnd_3843463 : Nat := 4983230072969 + 3 ^ 40 * 3843463 * 2
def baseEnd_3843463 : Nat := 438565310393689148230387

theorem tailTrace_3843463 : CollatzResearch.WordTrace tailWord_3843463 prefixEnd_3843463 438565310393689148230387 := by
  unfold tailWord_3843463
  simp only [CollatzResearch.WordTrace]
  refine ⟨140182612074797437065943043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93455074716531624710628695 140182612074797437065943043)
  ·
    refine ⟨210273918112196155598914565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140182612074797437065943043 210273918112196155598914565)
    ·
      refine ⟨39426359646036779174796481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210273918112196155598914565 39426359646036779174796481)
      ·
        refine ⟨29569769734527584381097361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39426359646036779174796481 29569769734527584381097361)
        ·
          refine ⟨22177327300895688285823021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29569769734527584381097361 22177327300895688285823021)
          ·
            refine ⟨8316497737835883107183633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22177327300895688285823021 8316497737835883107183633)
            ·
              refine ⟨6237373303376912330387725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8316497737835883107183633 6237373303376912330387725)
              ·
                refine ⟨2339014988766342123895397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6237373303376912330387725 2339014988766342123895397)
                ·
                  refine ⟨438565310393689148230387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2339014988766342123895397 438565310393689148230387)
                  ·
                    rfl

theorem cell22_3843463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 3, 4].length) (baseStart_3843463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843463 prefixEnd_3843463 := by exact prefixLift 3843463
  have htrace : WordTrace (prefixWord ++ tailWord_3843463) baseStart_3843463 baseEnd_3843463 := by
    simpa [prefixWord, tailWord_3843463, baseEnd_3843463] using wordTrace_append hprefix tailTrace_3843463
  have hstable : (prefixWord ++ tailWord_3843463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843463).length < 2 ^ (prefixWord ++ tailWord_3843463).sum := by decide
  have hdescent : baseEnd_3843463 < baseStart_3843463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843465 : List Nat := [1, 2, 1, 1, 7, 2, 2, 1, 1, 4]
def baseStart_3843465 : Nat := 118140960795 + 3843465 * 2 ^ 59
def prefixEnd_3843465 : Nat := 4983230072969 + 3 ^ 40 * 3843465 * 2
def baseEnd_3843465 : Nat := 1315696615821940106141155

theorem tailTrace_3843465 : CollatzResearch.WordTrace tailWord_3843465 prefixEnd_3843465 1315696615821940106141155 := by
  unfold tailWord_3843465
  simp only [CollatzResearch.WordTrace]
  refine ⟨140182685020790191407515849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93455123347193460938343899 140182685020790191407515849)
  ·
    refine ⟨105137013765592643555636887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140182685020790191407515849 105137013765592643555636887)
    ·
      refine ⟨157705520648388965333455331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105137013765592643555636887 157705520648388965333455331)
      ·
        refine ⟨236558280972583448000182997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157705520648388965333455331 236558280972583448000182997)
        ·
          refine ⟨5544334710294924562504289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 236558280972583448000182997 5544334710294924562504289)
          ·
            refine ⟨4158251032721193421878217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5544334710294924562504289 4158251032721193421878217)
            ·
              refine ⟨3118688274540895066408663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4158251032721193421878217 3118688274540895066408663)
              ·
                refine ⟨4678032411811342599612995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3118688274540895066408663 4678032411811342599612995)
                ·
                  refine ⟨7017048617717013899419493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4678032411811342599612995 7017048617717013899419493)
                  ·
                    refine ⟨1315696615821940106141155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7017048617717013899419493 1315696615821940106141155)
                    ·
                      rfl

theorem cell22_3843465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 1, 4].length) (baseStart_3843465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843465 prefixEnd_3843465 := by exact prefixLift 3843465
  have htrace : WordTrace (prefixWord ++ tailWord_3843465) baseStart_3843465 baseEnd_3843465 := by
    simpa [prefixWord, tailWord_3843465, baseEnd_3843465] using wordTrace_append hprefix tailTrace_3843465
  have hstable : (prefixWord ++ tailWord_3843465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843465).length < 2 ^ (prefixWord ++ tailWord_3843465).sum := by decide
  have hdescent : baseEnd_3843465 < baseStart_3843465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843495 : List Nat := [1, 1, 6, 1, 1, 1, 5, 1, 2, 3]
def baseStart_3843495 : Nat := 118140960795 + 3843495 * 2 ^ 59
def prefixEnd_3843495 : Nat := 4983230072969 + 3 ^ 40 * 3843495 * 2
def baseEnd_3843495 : Nat := 1315706885435030027891063

theorem tailTrace_3843495 : CollatzResearch.WordTrace tailWord_3843495 prefixEnd_3843495 1315706885435030027891063 := by
  unfold tailWord_3843495
  simp only [CollatzResearch.WordTrace]
  refine ⟨140183779210681506531107939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93455852807121004354071959 140183779210681506531107939)
  ·
    refine ⟨210275668816022259796661909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140183779210681506531107939 210275668816022259796661909)
    ·
      refine ⟨9856671975751043427968527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 210275668816022259796661909 9856671975751043427968527)
      ·
        refine ⟨14785007963626565141952791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9856671975751043427968527 14785007963626565141952791)
        ·
          refine ⟨22177511945439847712929187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14785007963626565141952791 22177511945439847712929187)
          ·
            refine ⟨33266267918159771569393781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22177511945439847712929187 33266267918159771569393781)
            ·
              refine ⟨3118712617327478584630667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33266267918159771569393781 3118712617327478584630667)
              ·
                refine ⟨4678068925991217876946001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3118712617327478584630667 4678068925991217876946001)
                ·
                  refine ⟨3508551694493413407709501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4678068925991217876946001 3508551694493413407709501)
                  ·
                    refine ⟨1315706885435030027891063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3508551694493413407709501 1315706885435030027891063)
                    ·
                      rfl

theorem cell22_3843495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_3843495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843495 prefixEnd_3843495 := by exact prefixLift 3843495
  have htrace : WordTrace (prefixWord ++ tailWord_3843495) baseStart_3843495 baseEnd_3843495 := by
    simpa [prefixWord, tailWord_3843495, baseEnd_3843495] using wordTrace_append hprefix tailTrace_3843495
  have hstable : (prefixWord ++ tailWord_3843495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843495).length < 2 ^ (prefixWord ++ tailWord_3843495).sum := by decide
  have hdescent : baseEnd_3843495 < baseStart_3843495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843506 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 5, 3]
def baseStart_3843506 : Nat := 118140960795 + 3843506 * 2 ^ 59
def prefixEnd_3843506 : Nat := 4983230072969 + 3 ^ 40 * 3843506 * 2
def baseEnd_3843506 : Nat := 1315710650959829665866029

theorem tailTrace_3843506 : CollatzResearch.WordTrace tailWord_3843506 prefixEnd_3843506 1315710650959829665866029 := by
  unfold tailWord_3843506
  simp only [CollatzResearch.WordTrace]
  refine ⟨35046045103410413852439593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93456120275761103606505581 35046045103410413852439593)
  ·
    refine ⟨26284533827557810389329695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35046045103410413852439593 26284533827557810389329695)
    ·
      refine ⟨39426800741336715583994543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26284533827557810389329695 39426800741336715583994543)
      ·
        refine ⟨59140201112005073375991815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39426800741336715583994543 59140201112005073375991815)
        ·
          refine ⟨88710301668007610063987723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59140201112005073375991815 88710301668007610063987723)
          ·
            refine ⟨133065452502011415095981585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88710301668007610063987723 133065452502011415095981585)
            ·
              refine ⟨99799089376508561321986189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133065452502011415095981585 99799089376508561321986189)
              ·
                refine ⟨37424658516190710495744821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99799089376508561321986189 37424658516190710495744821)
                ·
                  refine ⟨3508561735892879108976077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37424658516190710495744821 3508561735892879108976077)
                  ·
                    refine ⟨1315710650959829665866029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3508561735892879108976077 1315710650959829665866029)
                    ·
                      rfl

theorem cell22_3843506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_3843506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843506 prefixEnd_3843506 := by exact prefixLift 3843506
  have htrace : WordTrace (prefixWord ++ tailWord_3843506) baseStart_3843506 baseEnd_3843506 := by
    simpa [prefixWord, tailWord_3843506, baseEnd_3843506] using wordTrace_append hprefix tailTrace_3843506
  have hstable : (prefixWord ++ tailWord_3843506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843506).length < 2 ^ (prefixWord ++ tailWord_3843506).sum := by decide
  have hdescent : baseEnd_3843506 < baseStart_3843506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843553 : List Nat := [1, 2, 3, 1, 2, 3, 4, 1, 5]
def baseStart_3843553 : Nat := 118140960795 + 3843553 * 2 ^ 59
def prefixEnd_3843553 : Nat := 4983230072969 + 3 ^ 40 * 3843553 * 2
def baseEnd_3843553 : Nat := 438575580006779069980295

theorem tailTrace_3843553 : CollatzResearch.WordTrace tailWord_3843553 prefixEnd_3843553 438575580006779069980295 := by
  unfold tailWord_3843553
  simp only [CollatzResearch.WordTrace]
  refine ⟨140185894644471382436719313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93457263096314254957812875 140185894644471382436719313)
  ·
    refine ⟨105139420983353536827539485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140185894644471382436719313 105139420983353536827539485)
    ·
      refine ⟨39427282868757576310327307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105139420983353536827539485 39427282868757576310327307)
      ·
        refine ⟨59140924303136364465490961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39427282868757576310327307 59140924303136364465490961)
        ·
          refine ⟨44355693227352273349118221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59140924303136364465490961 44355693227352273349118221)
          ·
            refine ⟨16633384960257102505919333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44355693227352273349118221 16633384960257102505919333)
            ·
              refine ⟨3118759680048206719859875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16633384960257102505919333 3118759680048206719859875)
              ·
                refine ⟨4678139520072310079789813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3118759680048206719859875 4678139520072310079789813)
                ·
                  refine ⟨438575580006779069980295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4678139520072310079789813 438575580006779069980295)
                  ·
                    rfl

theorem cell22_3843553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 5].length) (baseStart_3843553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843553 prefixEnd_3843553 := by exact prefixLift 3843553
  have htrace : WordTrace (prefixWord ++ tailWord_3843553) baseStart_3843553 baseEnd_3843553 := by
    simpa [prefixWord, tailWord_3843553, baseEnd_3843553] using wordTrace_append hprefix tailTrace_3843553
  have hstable : (prefixWord ++ tailWord_3843553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843553).length < 2 ^ (prefixWord ++ tailWord_3843553).sum := by decide
  have hdescent : baseEnd_3843553 < baseStart_3843553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843613 : List Nat := [1, 4, 2, 2, 1, 1, 4, 1, 1, 5]
def baseStart_3843613 : Nat := 118140960795 + 3843613 * 2 ^ 59
def prefixEnd_3843613 : Nat := 4983230072969 + 3 ^ 40 * 3843613 * 2
def baseEnd_3843613 : Nat := 1315747279246517053440701

theorem tailTrace_3843613 : CollatzResearch.WordTrace tailWord_3843613 prefixEnd_3843613 1315747279246517053440701 := by
  unfold tailWord_3843613
  simp only [CollatzResearch.WordTrace]
  refine ⟨140188083024254012683903493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93458722016169341789268995 140188083024254012683903493)
  ·
    refine ⟨26285265567047627378231905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140188083024254012683903493 26285265567047627378231905)
    ·
      refine ⟨19713949175285720533673929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26285265567047627378231905 19713949175285720533673929)
      ·
        refine ⟨14785461881464290400255447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19713949175285720533673929 14785461881464290400255447)
        ·
          refine ⟨22178192822196435600383171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14785461881464290400255447 22178192822196435600383171)
          ·
            refine ⟨33267289233294653400574757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22178192822196435600383171 33267289233294653400574757)
            ·
              refine ⟨6237616731242747512607767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33267289233294653400574757 6237616731242747512607767)
              ·
                refine ⟨9356425096864121268911651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6237616731242747512607767 9356425096864121268911651)
                ·
                  refine ⟨14034637645296181903367477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9356425096864121268911651 14034637645296181903367477)
                  ·
                    refine ⟨1315747279246517053440701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14034637645296181903367477 1315747279246517053440701)
                    ·
                      rfl

theorem cell22_3843613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_3843613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843613 prefixEnd_3843613 := by exact prefixLift 3843613
  have htrace : WordTrace (prefixWord ++ tailWord_3843613) baseStart_3843613 baseEnd_3843613 := by
    simpa [prefixWord, tailWord_3843613, baseEnd_3843613] using wordTrace_append hprefix tailTrace_3843613
  have hstable : (prefixWord ++ tailWord_3843613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843613).length < 2 ^ (prefixWord ++ tailWord_3843613).sum := by decide
  have hdescent : baseEnd_3843613 < baseStart_3843613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843688 : List Nat := [2, 1, 4, 3, 1, 1, 1, 2, 7]
def baseStart_3843688 : Nat := 118140960795 + 3843688 * 2 ^ 59
def prefixEnd_3843688 : Nat := 4983230072969 + 3 ^ 40 * 3843688 * 2
def baseEnd_3843688 : Nat := 438590984426413952605157

theorem tailTrace_3843688 : CollatzResearch.WordTrace tailWord_3843688 prefixEnd_3843688 438590984426413952605157 := by
  unfold tailWord_3843688
  simp only [CollatzResearch.WordTrace]
  refine ⟨70095409249491150246441859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93460545665988200328589145 70095409249491150246441859)
  ·
    refine ⟨105143113874236725369662789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70095409249491150246441859 105143113874236725369662789)
    ·
      refine ⟨19714333851419386006811773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105143113874236725369662789 19714333851419386006811773)
      ·
        refine ⟨7392875194282269752554415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19714333851419386006811773 7392875194282269752554415)
        ·
          refine ⟨11089312791423404628831623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7392875194282269752554415 11089312791423404628831623)
          ·
            refine ⟨16633969187135106943247435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11089312791423404628831623 16633969187135106943247435)
            ·
              refine ⟨24950953780702660414871153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16633969187135106943247435 24950953780702660414871153)
              ·
                refine ⟨18713215335526995311153365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24950953780702660414871153 18713215335526995311153365)
                ·
                  refine ⟨438590984426413952605157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18713215335526995311153365 438590984426413952605157)
                  ·
                    rfl

theorem cell22_3843688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 7].length) (baseStart_3843688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843688 prefixEnd_3843688 := by exact prefixLift 3843688
  have htrace : WordTrace (prefixWord ++ tailWord_3843688) baseStart_3843688 baseEnd_3843688 := by
    simpa [prefixWord, tailWord_3843688, baseEnd_3843688] using wordTrace_append hprefix tailTrace_3843688
  have hstable : (prefixWord ++ tailWord_3843688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843688).length < 2 ^ (prefixWord ++ tailWord_3843688).sum := by decide
  have hdescent : baseEnd_3843688 < baseStart_3843688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843709 : List Nat := [1, 4, 1, 1, 4, 2, 3, 2, 1, 3]
def baseStart_3843709 : Nat := 118140960795 + 3843709 * 2 ^ 59
def prefixEnd_3843709 : Nat := 4983230072969 + 3 ^ 40 * 3843709 * 2
def baseEnd_3843709 : Nat := 1315780142008404803040407

theorem tailTrace_3843709 : CollatzResearch.WordTrace tailWord_3843709 prefixEnd_3843709 1315780142008404803040407 := by
  unfold tailWord_3843709
  simp only [CollatzResearch.WordTrace]
  refine ⟨140191584431906221079398181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93461056287937480719598787 140191584431906221079398181)
  ·
    refine ⟨26285922080982416452387159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140191584431906221079398181 26285922080982416452387159)
    ·
      refine ⟨39428883121473624678580739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26285922080982416452387159 39428883121473624678580739)
      ·
        refine ⟨59143324682210437017871109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39428883121473624678580739 59143324682210437017871109)
        ·
          refine ⟨11089373377914456940850833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59143324682210437017871109 11089373377914456940850833)
          ·
            refine ⟨8317030033435842705638125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11089373377914456940850833 8317030033435842705638125)
            ·
              refine ⟨3118886262538441014614297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8317030033435842705638125 3118886262538441014614297)
              ·
                refine ⟨2339164696903830760960723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3118886262538441014614297 2339164696903830760960723)
                ·
                  refine ⟨3508747045355746141441085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2339164696903830760960723 3508747045355746141441085)
                  ·
                    refine ⟨1315780142008404803040407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3508747045355746141441085 1315780142008404803040407)
                    ·
                      rfl

theorem cell22_3843709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_3843709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843709 prefixEnd_3843709 := by exact prefixLift 3843709
  have htrace : WordTrace (prefixWord ++ tailWord_3843709) baseStart_3843709 baseEnd_3843709 := by
    simpa [prefixWord, tailWord_3843709, baseEnd_3843709] using wordTrace_append hprefix tailTrace_3843709
  have hstable : (prefixWord ++ tailWord_3843709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843709).length < 2 ^ (prefixWord ++ tailWord_3843709).sum := by decide
  have hdescent : baseEnd_3843709 < baseStart_3843709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843722 : List Nat := [3, 1, 2, 3, 2, 3, 2, 1, 5]
def baseStart_3843722 : Nat := 118140960795 + 3843722 * 2 ^ 59
def prefixEnd_3843722 : Nat := 4983230072969 + 3 ^ 40 * 3843722 * 2
def baseEnd_3843722 : Nat := 438594864058025700821789

theorem tailTrace_3843722 : CollatzResearch.WordTrace tailWord_3843722 prefixEnd_3843722 438594864058025700821789 := by
  unfold tailWord_3843722
  simp only [CollatzResearch.WordTrace]
  refine ⟨35048014645214781074905355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93461372387239416199747613 35048014645214781074905355)
  ·
    refine ⟨52572021967822171612358033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35048014645214781074905355 52572021967822171612358033)
    ·
      refine ⟨39429016475866628709268525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52572021967822171612358033 39429016475866628709268525)
      ·
        refine ⟨14785881178449985765975697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39429016475866628709268525 14785881178449985765975697)
        ·
          refine ⟨11089410883837489324481773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14785881178449985765975697 11089410883837489324481773)
          ·
            refine ⟨4158529081439058496680665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11089410883837489324481773 4158529081439058496680665)
            ·
              refine ⟨3118896811079293872510499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4158529081439058496680665 3118896811079293872510499)
              ·
                refine ⟨4678345216618940808765749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3118896811079293872510499 4678345216618940808765749)
                ·
                  refine ⟨438594864058025700821789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4678345216618940808765749 438594864058025700821789)
                  ·
                    rfl

theorem cell22_3843722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 5].length) (baseStart_3843722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843722 prefixEnd_3843722 := by exact prefixLift 3843722
  have htrace : WordTrace (prefixWord ++ tailWord_3843722) baseStart_3843722 baseEnd_3843722 := by
    simpa [prefixWord, tailWord_3843722, baseEnd_3843722] using wordTrace_append hprefix tailTrace_3843722
  have hstable : (prefixWord ++ tailWord_3843722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843722).length < 2 ^ (prefixWord ++ tailWord_3843722).sum := by decide
  have hdescent : baseEnd_3843722 < baseStart_3843722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843735 : List Nat := [1, 1, 3, 3, 2, 2, 3, 2, 1, 4]
def baseStart_3843735 : Nat := 118140960795 + 3843735 * 2 ^ 59
def prefixEnd_3843735 : Nat := 4983230072969 + 3 ^ 40 * 3843735 * 2
def baseEnd_3843735 : Nat := 1315789042339749401890327

theorem tailTrace_3843735 : CollatzResearch.WordTrace tailWord_3843735 prefixEnd_3843735 1315789042339749401890327 := by
  unfold tailWord_3843735
  simp only [CollatzResearch.WordTrace]
  refine ⟨140192532729812027519844659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93461688486541351679896439 140192532729812027519844659)
  ·
    refine ⟨210288799094718041279766989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140192532729812027519844659 210288799094718041279766989)
    ·
      refine ⟨78858299660519265479912621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210288799094718041279766989 78858299660519265479912621)
      ·
        refine ⟨29571862372694724554967233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78858299660519265479912621 29571862372694724554967233)
        ·
          refine ⟨22178896779521043416225425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29571862372694724554967233 22178896779521043416225425)
          ·
            refine ⟨16634172584640782562169069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22178896779521043416225425 16634172584640782562169069)
            ·
              refine ⟨6237814719240293460813401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16634172584640782562169069 6237814719240293460813401)
              ·
                refine ⟨4678361039430220095610051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6237814719240293460813401 4678361039430220095610051)
                ·
                  refine ⟨7017541559145330143415077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4678361039430220095610051 7017541559145330143415077)
                  ·
                    refine ⟨1315789042339749401890327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7017541559145330143415077 1315789042339749401890327)
                    ·
                      rfl

theorem cell22_3843735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_3843735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843735 prefixEnd_3843735 := by exact prefixLift 3843735
  have htrace : WordTrace (prefixWord ++ tailWord_3843735) baseStart_3843735 baseEnd_3843735 := by
    simpa [prefixWord, tailWord_3843735, baseEnd_3843735] using wordTrace_append hprefix tailTrace_3843735
  have hstable : (prefixWord ++ tailWord_3843735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843735).length < 2 ^ (prefixWord ++ tailWord_3843735).sum := by decide
  have hdescent : baseEnd_3843735 < baseStart_3843735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843748 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 3, 5]
def baseStart_3843748 : Nat := 118140960795 + 3843748 * 2 ^ 59
def prefixEnd_3843748 : Nat := 4983230072969 + 3 ^ 40 * 3843748 * 2
def baseEnd_3843748 : Nat := 1315793492505421701315287

theorem tailTrace_3843748 : CollatzResearch.WordTrace tailWord_3843748 prefixEnd_3843748 1315793492505421701315287 := by
  unfold tailWord_3843748
  simp only [CollatzResearch.WordTrace]
  refine ⟨70096503439382465370033949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93462004585843287160045265 70096503439382465370033949)
  ·
    refine ⟨26286188789768424513762731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70096503439382465370033949 26286188789768424513762731)
    ·
      refine ⟨39429283184652636770644097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26286188789768424513762731 39429283184652636770644097)
      ·
        refine ⟨29571962388489477577983073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39429283184652636770644097 29571962388489477577983073)
        ·
          refine ⟨22178971791367108183487305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29571962388489477577983073 22178971791367108183487305)
          ·
            refine ⟨16634228843525331137615479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22178971791367108183487305 16634228843525331137615479)
            ·
              refine ⟨24951343265287996706423219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16634228843525331137615479 24951343265287996706423219)
              ·
                refine ⟨37427014897931995059634829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24951343265287996706423219 37427014897931995059634829)
                ·
                  refine ⟨14035130586724498147363061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37427014897931995059634829 14035130586724498147363061)
                  ·
                    refine ⟨1315793492505421701315287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14035130586724498147363061 1315793492505421701315287)
                    ·
                      rfl

theorem cell22_3843748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_3843748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843748 prefixEnd_3843748 := by exact prefixLift 3843748
  have htrace : WordTrace (prefixWord ++ tailWord_3843748) baseStart_3843748 baseEnd_3843748 := by
    simpa [prefixWord, tailWord_3843748, baseEnd_3843748] using wordTrace_append hprefix tailTrace_3843748
  have hstable : (prefixWord ++ tailWord_3843748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843748).length < 2 ^ (prefixWord ++ tailWord_3843748).sum := by decide
  have hdescent : baseEnd_3843748 < baseStart_3843748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843761 : List Nat := [1, 2, 2, 17]
def baseStart_3843761 : Nat := 118140960795 + 3843761 * 2 ^ 59
def prefixEnd_3843761 : Nat := 4983230072969 + 3 ^ 40 * 3843761 * 2
def baseEnd_3843761 : Nat := 1804935449480238684143

theorem tailTrace_3843761 : CollatzResearch.WordTrace tailWord_3843761 prefixEnd_3843761 1804935449480238684143 := by
  unfold tailWord_3843761
  simp only [CollatzResearch.WordTrace]
  refine ⟨140193481027717833960291137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93462320685145222640194091 140193481027717833960291137)
  ·
    refine ⟨105145110770788375470218353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140193481027717833960291137 105145110770788375470218353)
    ·
      refine ⟨78858833078091281602663765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105145110770788375470218353 78858833078091281602663765)
      ·
        refine ⟨1804935449480238684143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 17 78858833078091281602663765 1804935449480238684143)
        ·
          rfl

theorem cell22_3843761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 17].length) (baseStart_3843761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843761 prefixEnd_3843761 := by exact prefixLift 3843761
  have htrace : WordTrace (prefixWord ++ tailWord_3843761) baseStart_3843761 baseEnd_3843761 := by
    simpa [prefixWord, tailWord_3843761, baseEnd_3843761] using wordTrace_append hprefix tailTrace_3843761
  have hstable : (prefixWord ++ tailWord_3843761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843761).length < 2 ^ (prefixWord ++ tailWord_3843761).sum := by decide
  have hdescent : baseEnd_3843761 < baseStart_3843761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843763 : List Nat := [1, 1, 1, 2, 3, 3, 1, 4, 2, 4]
def baseStart_3843763 : Nat := 118140960795 + 3843763 * 2 ^ 59
def prefixEnd_3843763 : Nat := 4983230072969 + 3 ^ 40 * 3843763 * 2
def baseEnd_3843763 : Nat := 1315798627311966662190241

theorem tailTrace_3843763 : CollatzResearch.WordTrace tailWord_3843763 prefixEnd_3843763 1315798627311966662190241 := by
  unfold tailWord_3843763
  simp only [CollatzResearch.WordTrace]
  refine ⟨140193553973710588301863943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93462369315807058867909295 140193553973710588301863943)
  ·
    refine ⟨210290330960565882452795915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140193553973710588301863943 210290330960565882452795915)
    ·
      refine ⟨315435496440848823679193873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210290330960565882452795915 315435496440848823679193873)
      ·
        refine ⟨236576622330636617759395405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315435496440848823679193873 236576622330636617759395405)
        ·
          refine ⟨88716233373988731659773277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236576622330636617759395405 88716233373988731659773277)
          ·
            refine ⟨33268587515245774372414979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88716233373988731659773277 33268587515245774372414979)
            ·
              refine ⟨49902881272868661558622469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33268587515245774372414979 49902881272868661558622469)
              ·
                refine ⟨9356790238662874042241713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49902881272868661558622469 9356790238662874042241713)
                ·
                  refine ⟨7017592678997155531681285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9356790238662874042241713 7017592678997155531681285)
                  ·
                    refine ⟨1315798627311966662190241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7017592678997155531681285 1315798627311966662190241)
                    ·
                      rfl

theorem cell22_3843763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 4].length) (baseStart_3843763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843763 prefixEnd_3843763 := by exact prefixLift 3843763
  have htrace : WordTrace (prefixWord ++ tailWord_3843763) baseStart_3843763 baseEnd_3843763 := by
    simpa [prefixWord, tailWord_3843763, baseEnd_3843763] using wordTrace_append hprefix tailTrace_3843763
  have hstable : (prefixWord ++ tailWord_3843763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843763).length < 2 ^ (prefixWord ++ tailWord_3843763).sum := by decide
  have hdescent : baseEnd_3843763 < baseStart_3843763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843767 : List Nat := [1, 1, 3, 1, 5, 1, 4, 2, 4]
def baseStart_3843767 : Nat := 118140960795 + 3843767 * 2 ^ 59
def prefixEnd_3843767 : Nat := 4983230072969 + 3 ^ 40 * 3843767 * 2
def baseEnd_3843767 : Nat := 438599998864570661696743

theorem tailTrace_3843767 : CollatzResearch.WordTrace tailWord_3843767 prefixEnd_3843767 438599998864570661696743 := by
  unfold tailWord_3843767
  simp only [CollatzResearch.WordTrace]
  refine ⟨140193699865696096985009555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93462466577130731323339703 140193699865696096985009555)
  ·
    refine ⟨210290549798544145477514333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140193699865696096985009555 210290549798544145477514333)
    ·
      refine ⟨78858956174454054554067875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210290549798544145477514333 78858956174454054554067875)
      ·
        refine ⟨118288434261681081831101813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78858956174454054554067875 118288434261681081831101813)
        ·
          refine ⟨11089540712032601421665795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118288434261681081831101813 11089540712032601421665795)
          ·
            refine ⟨16634311068048902132498693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11089540712032601421665795 16634311068048902132498693)
            ·
              refine ⟨3118933325259169149843505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16634311068048902132498693 3118933325259169149843505)
              ·
                refine ⟨2339199993944376862382629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3118933325259169149843505 2339199993944376862382629)
                ·
                  refine ⟨438599998864570661696743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2339199993944376862382629 438599998864570661696743)
                  ·
                    rfl

theorem cell22_3843767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 2, 4].length) (baseStart_3843767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843767 prefixEnd_3843767 := by exact prefixLift 3843767
  have htrace : WordTrace (prefixWord ++ tailWord_3843767) baseStart_3843767 baseEnd_3843767 := by
    simpa [prefixWord, tailWord_3843767, baseEnd_3843767] using wordTrace_append hprefix tailTrace_3843767
  have hstable : (prefixWord ++ tailWord_3843767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843767).length < 2 ^ (prefixWord ++ tailWord_3843767).sum := by decide
  have hdescent : baseEnd_3843767 < baseStart_3843767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843823 : List Nat := [1, 1, 2, 1, 5, 1, 3, 1, 7]
def baseStart_3843823 : Nat := 118140960795 + 3843823 * 2 ^ 59
def prefixEnd_3843823 : Nat := 4983230072969 + 3 ^ 40 * 3843823 * 2
def baseEnd_3843823 : Nat := 438606388846048835230019

theorem tailTrace_3843823 : CollatzResearch.WordTrace tailWord_3843823 prefixEnd_3843823 438606388846048835230019 := by
  unfold tailWord_3843823
  simp only [CollatzResearch.WordTrace]
  refine ⟨140195742353493218549048123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93463828235662145699365415 140195742353493218549048123)
  ·
    refine ⟨210293613530239827823572185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140195742353493218549048123 210293613530239827823572185)
    ·
      refine ⟨157720210147679870867679139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210293613530239827823572185 157720210147679870867679139)
      ·
        refine ⟨236580315221519806301518709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157720210147679870867679139 236580315221519806301518709)
        ·
          refine ⟨22179404552017481840767379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 236580315221519806301518709 22179404552017481840767379)
          ·
            refine ⟨33269106828026222761151069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22179404552017481840767379 33269106828026222761151069)
            ·
              refine ⟨12475915060509833535431651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33269106828026222761151069 12475915060509833535431651)
              ·
                refine ⟨18713872590764750303147477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12475915060509833535431651 18713872590764750303147477)
                ·
                  refine ⟨438606388846048835230019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18713872590764750303147477 438606388846048835230019)
                  ·
                    rfl

theorem cell22_3843823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 7].length) (baseStart_3843823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843823 prefixEnd_3843823 := by exact prefixLift 3843823
  have htrace : WordTrace (prefixWord ++ tailWord_3843823) baseStart_3843823 baseEnd_3843823 := by
    simpa [prefixWord, tailWord_3843823, baseEnd_3843823] using wordTrace_append hprefix tailTrace_3843823
  have hstable : (prefixWord ++ tailWord_3843823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843823).length < 2 ^ (prefixWord ++ tailWord_3843823).sum := by decide
  have hdescent : baseEnd_3843823 < baseStart_3843823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843827 : List Nat := [1, 1, 1, 2, 2, 3, 4, 4, 1, 3]
def baseStart_3843827 : Nat := 118140960795 + 3843827 * 2 ^ 59
def prefixEnd_3843827 : Nat := 4983230072969 + 3 ^ 40 * 3843827 * 2
def baseEnd_3843827 : Nat := 1315820535819891828590045

theorem tailTrace_3843827 : CollatzResearch.WordTrace tailWord_3843827 prefixEnd_3843827 1315820535819891828590045 := by
  unfold tailWord_3843827
  simp only [CollatzResearch.WordTrace]
  refine ⟨140195888245478727232193735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93463925496985818154795823 140195888245478727232193735)
  ·
    refine ⟨210293832368218090848290603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140195888245478727232193735 210293832368218090848290603)
    ·
      refine ⟨315440748552327136272435905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210293832368218090848290603 315440748552327136272435905)
      ·
        refine ⟨236580561414245352204326929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315440748552327136272435905 236580561414245352204326929)
        ·
          refine ⟨177435421060684014153245197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236580561414245352204326929 177435421060684014153245197)
          ·
            refine ⟨66538282897756505307466949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177435421060684014153245197 66538282897756505307466949)
            ·
              refine ⟨12475928043329344745150053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66538282897756505307466949 12475928043329344745150053)
              ·
                refine ⟨2339236508124252139715635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12475928043329344745150053 2339236508124252139715635)
                ·
                  refine ⟨3508854762186378209573453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2339236508124252139715635 3508854762186378209573453)
                  ·
                    refine ⟨1315820535819891828590045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3508854762186378209573453 1315820535819891828590045)
                    ·
                      rfl

theorem cell22_3843827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4, 1, 3].length) (baseStart_3843827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843827 prefixEnd_3843827 := by exact prefixLift 3843827
  have htrace : WordTrace (prefixWord ++ tailWord_3843827) baseStart_3843827 baseEnd_3843827 := by
    simpa [prefixWord, tailWord_3843827, baseEnd_3843827] using wordTrace_append hprefix tailTrace_3843827
  have hstable : (prefixWord ++ tailWord_3843827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843827).length < 2 ^ (prefixWord ++ tailWord_3843827).sum := by decide
  have hdescent : baseEnd_3843827 < baseStart_3843827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843913 : List Nat := [1, 2, 1, 1, 2, 4, 1, 10]
def baseStart_3843913 : Nat := 118140960795 + 3843913 * 2 ^ 59
def prefixEnd_3843913 : Nat := 4983230072969 + 3 ^ 40 * 3843913 * 2
def baseEnd_3843913 : Nat := 146205552819712918993309

theorem tailTrace_3843913 : CollatzResearch.WordTrace tailWord_3843913 prefixEnd_3843913 146205552819712918993309 := by
  unfold tailWord_3843913
  simp only [CollatzResearch.WordTrace]
  refine ⟨140199024923167163919824393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93466016615444775946549595 140199024923167163919824393)
  ·
    refine ⟨105149268692375372939868295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140199024923167163919824393 105149268692375372939868295)
    ·
      refine ⟨157723903038563059409802443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105149268692375372939868295 157723903038563059409802443)
      ·
        refine ⟨236585854557844589114703665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157723903038563059409802443 236585854557844589114703665)
        ·
          refine ⟨177439390918383441836027749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236585854557844589114703665 177439390918383441836027749)
          ·
            refine ⟨33269885797196895344255203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177439390918383441836027749 33269885797196895344255203)
            ·
              refine ⟨49904828695795343016382805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33269885797196895344255203 49904828695795343016382805)
              ·
                refine ⟨146205552819712918993309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49904828695795343016382805 146205552819712918993309)
                ·
                  rfl

theorem cell22_3843913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 10].length) (baseStart_3843913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843913 prefixEnd_3843913 := by exact prefixLift 3843913
  have htrace : WordTrace (prefixWord ++ tailWord_3843913) baseStart_3843913 baseEnd_3843913 := by
    simpa [prefixWord, tailWord_3843913, baseEnd_3843913] using wordTrace_append hprefix tailTrace_3843913
  have hstable : (prefixWord ++ tailWord_3843913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843913).length < 2 ^ (prefixWord ++ tailWord_3843913).sum := by decide
  have hdescent : baseEnd_3843913 < baseStart_3843913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843917 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_3843917 : Nat := 118140960795 + 3843917 * 2 ^ 59
def prefixEnd_3843917 : Nat := 4983230072969 + 3 ^ 40 * 3843917 * 2
def baseEnd_3843917 : Nat := 1315851344659161593839769

theorem tailTrace_3843917 : CollatzResearch.WordTrace tailWord_3843917 prefixEnd_3843917 1315851344659161593839769 := by
  unfold tailWord_3843917
  simp only [CollatzResearch.WordTrace]
  refine ⟨140199170815152672602970005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93466113876768448401980003 140199170815152672602970005)
  ·
    refine ⟨6571836131960281528264219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 140199170815152672602970005 6571836131960281528264219)
    ·
      refine ⟨9857754197940422292396329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6571836131960281528264219 9857754197940422292396329)
      ·
        refine ⟨7393315648455316719297247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9857754197940422292396329 7393315648455316719297247)
        ·
          refine ⟨11089973472682975078945871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7393315648455316719297247 11089973472682975078945871)
          ·
            refine ⟨16634960209024462618418807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11089973472682975078945871 16634960209024462618418807)
            ·
              refine ⟨24952440313536693927628211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16634960209024462618418807 24952440313536693927628211)
              ·
                refine ⟨37428660470305040891442317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24952440313536693927628211 37428660470305040891442317)
                ·
                  refine ⟨14035747676364390334290869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37428660470305040891442317 14035747676364390334290869)
                  ·
                    refine ⟨1315851344659161593839769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14035747676364390334290869 1315851344659161593839769)
                    ·
                      rfl

theorem cell22_3843917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_3843917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843917 prefixEnd_3843917 := by exact prefixLift 3843917
  have htrace : WordTrace (prefixWord ++ tailWord_3843917) baseStart_3843917 baseEnd_3843917 := by
    simpa [prefixWord, tailWord_3843917, baseEnd_3843917] using wordTrace_append hprefix tailTrace_3843917
  have hstable : (prefixWord ++ tailWord_3843917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843917).length < 2 ^ (prefixWord ++ tailWord_3843917).sum := by decide
  have hdescent : baseEnd_3843917 < baseStart_3843917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843945 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 7, 3]
def baseStart_3843945 : Nat := 118140960795 + 3843945 * 2 ^ 59
def prefixEnd_3843945 : Nat := 4983230072969 + 3 ^ 40 * 3843945 * 2
def baseEnd_3843945 : Nat := 1315860929631378854139683

theorem tailTrace_3843945 : CollatzResearch.WordTrace tailWord_3843945 prefixEnd_3843945 1315860929631378854139683 := by
  unfold tailWord_3843945
  simp only [CollatzResearch.WordTrace]
  refine ⟨140200192059051233384989289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93466794706034155589992859 140200192059051233384989289)
  ·
    refine ⟨105150144044288425038741967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140200192059051233384989289 105150144044288425038741967)
    ·
      refine ⟨157725216066432637558112951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105150144044288425038741967 157725216066432637558112951)
      ·
        refine ⟨236587824099648956337169427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157725216066432637558112951 236587824099648956337169427)
        ·
          refine ⟨354881736149473434505754141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236587824099648956337169427 354881736149473434505754141)
          ·
            refine ⟨133080651056052537939657803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 354881736149473434505754141 133080651056052537939657803)
            ·
              refine ⟨199620976584078806909486705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133080651056052537939657803 199620976584078806909486705)
              ·
                refine ⟨149715732438059105182115029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199620976584078806909486705 149715732438059105182115029)
                ·
                  refine ⟨3508962479017010277705821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 149715732438059105182115029 3508962479017010277705821)
                  ·
                    refine ⟨1315860929631378854139683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3508962479017010277705821 1315860929631378854139683)
                    ·
                      rfl

theorem cell22_3843945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 7, 3].length) (baseStart_3843945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843945 prefixEnd_3843945 := by exact prefixLift 3843945
  have htrace : WordTrace (prefixWord ++ tailWord_3843945) baseStart_3843945 baseEnd_3843945 := by
    simpa [prefixWord, tailWord_3843945, baseEnd_3843945] using wordTrace_append hprefix tailTrace_3843945
  have hstable : (prefixWord ++ tailWord_3843945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843945).length < 2 ^ (prefixWord ++ tailWord_3843945).sum := by decide
  have hdescent : baseEnd_3843945 < baseStart_3843945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843966 : List Nat := [4, 2, 3, 1, 1, 3, 1, 1, 2, 4]
def baseStart_3843966 : Nat := 118140960795 + 3843966 * 2 ^ 59
def prefixEnd_3843966 : Nat := 4983230072969 + 3 ^ 40 * 3843966 * 2
def baseEnd_3843966 : Nat := 1315868118360541799364619

theorem tailTrace_3843966 : CollatzResearch.WordTrace tailWord_3843966 prefixEnd_3843966 1315868118360541799364619 := by
  unfold tailWord_3843966
  simp only [CollatzResearch.WordTrace]
  refine ⟨17525119748996894246437969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93467305327983435981002501 17525119748996894246437969)
  ·
    refine ⟨13143839811747670684828477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17525119748996894246437969 13143839811747670684828477)
    ·
      refine ⟨4928939929405376506810679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13143839811747670684828477 4928939929405376506810679)
      ·
        refine ⟨7393409894108064760216019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4928939929405376506810679 7393409894108064760216019)
        ·
          refine ⟨11090114841162097140324029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7393409894108064760216019 11090114841162097140324029)
          ·
            refine ⟨4158793065435786427621511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11090114841162097140324029 4158793065435786427621511)
            ·
              refine ⟨6238189598153679641432267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4158793065435786427621511 6238189598153679641432267)
              ·
                refine ⟨9357284397230519462148401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6238189598153679641432267 9357284397230519462148401)
                ·
                  refine ⟨7017963297922889596611301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9357284397230519462148401 7017963297922889596611301)
                  ·
                    refine ⟨1315868118360541799364619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7017963297922889596611301 1315868118360541799364619)
                    ·
                      rfl

theorem cell22_3843966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_3843966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843966 prefixEnd_3843966 := by exact prefixLift 3843966
  have htrace : WordTrace (prefixWord ++ tailWord_3843966) baseStart_3843966 baseEnd_3843966 := by
    simpa [prefixWord, tailWord_3843966, baseEnd_3843966] using wordTrace_append hprefix tailTrace_3843966
  have hstable : (prefixWord ++ tailWord_3843966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843966).length < 2 ^ (prefixWord ++ tailWord_3843966).sum := by decide
  have hdescent : baseEnd_3843966 < baseStart_3843966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843996 : List Nat := [2, 2, 3, 3, 1, 1, 2, 4, 1, 3]
def baseStart_3843996 : Nat := 118140960795 + 3843996 * 2 ^ 59
def prefixEnd_3843996 : Nat := 4983230072969 + 3 ^ 40 * 3843996 * 2
def baseEnd_3843996 : Nat := 1315878387973631721114527

theorem tailTrace_3843996 : CollatzResearch.WordTrace tailWord_3843996 prefixEnd_3843996 1315878387973631721114527 := by
  unfold tailWord_3843996
  simp only [CollatzResearch.WordTrace]
  refine ⟨70101026090933234547547921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93468034787910979396730561 70101026090933234547547921)
  ·
    refine ⟨52575769568199925910660941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70101026090933234547547921 52575769568199925910660941)
    ·
      refine ⟨19715913588074972216497853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52575769568199925910660941 19715913588074972216497853)
      ·
        refine ⟨7393467595528114581186695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19715913588074972216497853 7393467595528114581186695)
        ·
          refine ⟨11090201393292171871780043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7393467595528114581186695 11090201393292171871780043)
          ·
            refine ⟨16635302089938257807670065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11090201393292171871780043 16635302089938257807670065)
            ·
              refine ⟨12476476567453693355752549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16635302089938257807670065 12476476567453693355752549)
              ·
                refine ⟨2339339356397567504203603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12476476567453693355752549 2339339356397567504203603)
                ·
                  refine ⟨3509009034596351256305405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2339339356397567504203603 3509009034596351256305405)
                  ·
                    refine ⟨1315878387973631721114527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3509009034596351256305405 1315878387973631721114527)
                    ·
                      rfl

theorem cell22_3843996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_3843996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3843996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3843996 prefixEnd_3843996 := by exact prefixLift 3843996
  have htrace : WordTrace (prefixWord ++ tailWord_3843996) baseStart_3843996 baseEnd_3843996 := by
    simpa [prefixWord, tailWord_3843996, baseEnd_3843996] using wordTrace_append hprefix tailTrace_3843996
  have hstable : (prefixWord ++ tailWord_3843996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843996).length < 2 ^ (prefixWord ++ tailWord_3843996).sum := by decide
  have hdescent : baseEnd_3843996 < baseStart_3843996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844005 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 5, 4]
def baseStart_3844005 : Nat := 118140960795 + 3844005 * 2 ^ 59
def prefixEnd_3844005 : Nat := 4983230072969 + 3 ^ 40 * 3844005 * 2
def baseEnd_3844005 : Nat := 1315881468857558697639499

theorem tailTrace_3844005 : CollatzResearch.WordTrace tailWord_3844005 prefixEnd_3844005 1315881468857558697639499 := by
  unfold tailWord_3844005
  simp only [CollatzResearch.WordTrace]
  refine ⟨140202380438833863632173469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93468253625889242421448979 140202380438833863632173469)
  ·
    refine ⟨52575892664562698862065051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140202380438833863632173469 52575892664562698862065051)
    ·
      refine ⟨78863838996844048293097577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52575892664562698862065051 78863838996844048293097577)
      ·
        refine ⟨59147879247633036219823183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78863838996844048293097577 59147879247633036219823183)
        ·
          refine ⟨88721818871449554329734775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59147879247633036219823183 88721818871449554329734775)
          ·
            refine ⟨133082728307174331494602163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88721818871449554329734775 133082728307174331494602163)
            ·
              refine ⟨199624092460761497241903245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133082728307174331494602163 199624092460761497241903245)
              ·
                refine ⟨74859034672785561465713717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199624092460761497241903245 74859034672785561465713717)
                ·
                  refine ⟨7018034500573646387410661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74859034672785561465713717 7018034500573646387410661)
                  ·
                    refine ⟨1315881468857558697639499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7018034500573646387410661 1315881468857558697639499)
                    ·
                      rfl

theorem cell22_3844005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_3844005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844005 prefixEnd_3844005 := by exact prefixLift 3844005
  have htrace : WordTrace (prefixWord ++ tailWord_3844005) baseStart_3844005 baseEnd_3844005 := by
    simpa [prefixWord, tailWord_3844005, baseEnd_3844005] using wordTrace_append hprefix tailTrace_3844005
  have hstable : (prefixWord ++ tailWord_3844005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844005).length < 2 ^ (prefixWord ++ tailWord_3844005).sum := by decide
  have hdescent : baseEnd_3844005 < baseStart_3844005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844007 : List Nat := [1, 1, 6, 1, 2, 1, 2, 1, 2, 5]
def baseStart_3844007 : Nat := 118140960795 + 3844007 * 2 ^ 59
def prefixEnd_3844007 : Nat := 4983230072969 + 3 ^ 40 * 3844007 * 2
def baseEnd_3844007 : Nat := 1315882153498431359089493

theorem tailTrace_3844007 : CollatzResearch.WordTrace tailWord_3844007 prefixEnd_3844007 1315882153498431359089493 := by
  unfold tailWord_3844007
  simp only [CollatzResearch.WordTrace]
  refine ⟨140202453384826617973746275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93468302256551078649164183 140202453384826617973746275)
  ·
    refine ⟨210303680077239926960619413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140202453384826617973746275 210303680077239926960619413)
    ·
      refine ⟨9857985003620621576279035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 210303680077239926960619413 9857985003620621576279035)
      ·
        refine ⟨14786977505430932364418553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9857985003620621576279035 14786977505430932364418553)
        ·
          refine ⟨11090233129073199273313915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14786977505430932364418553 11090233129073199273313915)
          ·
            refine ⟨16635349693609798909970873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11090233129073199273313915 16635349693609798909970873)
            ·
              refine ⟨12476512270207349182478155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16635349693609798909970873 12476512270207349182478155)
              ·
                refine ⟨18714768405311023773717233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12476512270207349182478155 18714768405311023773717233)
                ·
                  refine ⟨14036076303983267830287925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18714768405311023773717233 14036076303983267830287925)
                  ·
                    refine ⟨1315882153498431359089493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14036076303983267830287925 1315882153498431359089493)
                    ·
                      rfl

theorem cell22_3844007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_3844007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844007 prefixEnd_3844007 := by exact prefixLift 3844007
  have htrace : WordTrace (prefixWord ++ tailWord_3844007) baseStart_3844007 baseEnd_3844007 := by
    simpa [prefixWord, tailWord_3844007, baseEnd_3844007] using wordTrace_append hprefix tailTrace_3844007
  have hstable : (prefixWord ++ tailWord_3844007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844007).length < 2 ^ (prefixWord ++ tailWord_3844007).sum := by decide
  have hdescent : baseEnd_3844007 < baseStart_3844007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844037 : List Nat := [1, 3, 1, 1, 1, 1, 1, 9, 4]
def baseStart_3844037 : Nat := 118140960795 + 3844037 * 2 ^ 59
def prefixEnd_3844037 : Nat := 4983230072969 + 3 ^ 40 * 3844037 * 2
def baseEnd_3844037 : Nat := 438630807703840426946467

theorem tailTrace_3844037 : CollatzResearch.WordTrace tailWord_3844037 prefixEnd_3844037 438630807703840426946467 := by
  unfold tailWord_3844037
  simp only [CollatzResearch.WordTrace]
  refine ⟨140203547574717933097338365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93469031716478622064892243 140203547574717933097338365)
  ·
    refine ⟨52576330340519224911501887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140203547574717933097338365 52576330340519224911501887)
    ·
      refine ⟨78864495510778837367252831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52576330340519224911501887 78864495510778837367252831)
      ·
        refine ⟨118296743266168256050879247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78864495510778837367252831 118296743266168256050879247)
        ·
          refine ⟨177445114899252384076318871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118296743266168256050879247 177445114899252384076318871)
          ·
            refine ⟨266167672348878576114478307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177445114899252384076318871 266167672348878576114478307)
            ·
              refine ⟨399251508523317864171717461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266167672348878576114478307 399251508523317864171717461)
              ·
                refine ⟨2339364307753815610381157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 399251508523317864171717461 2339364307753815610381157)
                ·
                  refine ⟨438630807703840426946467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2339364307753815610381157 438630807703840426946467)
                  ·
                    rfl

theorem cell22_3844037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 9, 4].length) (baseStart_3844037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844037 prefixEnd_3844037 := by exact prefixLift 3844037
  have htrace : WordTrace (prefixWord ++ tailWord_3844037) baseStart_3844037 baseEnd_3844037 := by
    simpa [prefixWord, tailWord_3844037, baseEnd_3844037] using wordTrace_append hprefix tailTrace_3844037
  have hstable : (prefixWord ++ tailWord_3844037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844037).length < 2 ^ (prefixWord ++ tailWord_3844037).sum := by decide
  have hdescent : baseEnd_3844037 < baseStart_3844037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844060 : List Nat := [2, 2, 6, 1, 1, 2, 2, 1, 5]
def baseStart_3844060 : Nat := 118140960795 + 3844060 * 2 ^ 59
def prefixEnd_3844060 : Nat := 4983230072969 + 3 ^ 40 * 3844060 * 2
def baseEnd_3844060 : Nat := 438633432160518962504777

theorem tailTrace_3844060 : CollatzResearch.WordTrace tailWord_3844060 prefixEnd_3844060 438633432160518962504777 := by
  unfold tailWord_3844060
  simp only [CollatzResearch.WordTrace]
  refine ⟨70102193226817304012712817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93469590969089738683617089 70102193226817304012712817)
  ·
    refine ⟨52576644920112978009534613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70102193226817304012712817 52576644920112978009534613)
    ·
      refine ⟨2464530230630295844196935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52576644920112978009534613 2464530230630295844196935)
      ·
        refine ⟨3696795345945443766295403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2464530230630295844196935 3696795345945443766295403)
        ·
          refine ⟨5545193018918165649443105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3696795345945443766295403 5545193018918165649443105)
          ·
            refine ⟨4158894764188624237082329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5545193018918165649443105 4158894764188624237082329)
            ·
              refine ⟨3119171073141468177811747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4158894764188624237082329 3119171073141468177811747)
              ·
                refine ⟨4678756609712202266717621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3119171073141468177811747 4678756609712202266717621)
                ·
                  refine ⟨438633432160518962504777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4678756609712202266717621 438633432160518962504777)
                  ·
                    rfl

theorem cell22_3844060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 5].length) (baseStart_3844060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844060 prefixEnd_3844060 := by exact prefixLift 3844060
  have htrace : WordTrace (prefixWord ++ tailWord_3844060) baseStart_3844060 baseEnd_3844060 := by
    simpa [prefixWord, tailWord_3844060, baseEnd_3844060] using wordTrace_append hprefix tailTrace_3844060
  have hstable : (prefixWord ++ tailWord_3844060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844060).length < 2 ^ (prefixWord ++ tailWord_3844060).sum := by decide
  have hdescent : baseEnd_3844060 < baseStart_3844060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844065 : List Nat := [1, 2, 3, 1, 2, 1, 3, 9]
def baseStart_3844065 : Nat := 118140960795 + 3844065 * 2 ^ 59
def prefixEnd_3844065 : Nat := 4983230072969 + 3 ^ 40 * 3844065 * 2
def baseEnd_3844065 : Nat := 146211334231526504571035

theorem tailTrace_3844065 : CollatzResearch.WordTrace tailWord_3844065 prefixEnd_3844065 146211334231526504571035 := by
  unfold tailWord_3844065
  simp only [CollatzResearch.WordTrace]
  refine ⟨140204568818616493879357649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93469712545744329252905099 140204568818616493879357649)
  ·
    refine ⟨105153426613962370409518237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140204568818616493879357649 105153426613962370409518237)
    ·
      refine ⟨39432534980235888903569339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105153426613962370409518237 39432534980235888903569339)
      ·
        refine ⟨59148802470353833355354009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39432534980235888903569339 59148802470353833355354009)
        ·
          refine ⟨44361601852765375016515507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59148802470353833355354009 44361601852765375016515507)
          ·
            refine ⟨66542402779148062524773261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44361601852765375016515507 66542402779148062524773261)
            ·
              refine ⟨24953401042180523446789973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66542402779148062524773261 24953401042180523446789973)
              ·
                refine ⟨146211334231526504571035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24953401042180523446789973 146211334231526504571035)
                ·
                  rfl

theorem cell22_3844065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 9].length) (baseStart_3844065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844065 prefixEnd_3844065 := by exact prefixLift 3844065
  have htrace : WordTrace (prefixWord ++ tailWord_3844065) baseStart_3844065 baseEnd_3844065 := by
    simpa [prefixWord, tailWord_3844065, baseEnd_3844065] using wordTrace_append hprefix tailTrace_3844065
  have hstable : (prefixWord ++ tailWord_3844065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844065).length < 2 ^ (prefixWord ++ tailWord_3844065).sum := by decide
  have hdescent : baseEnd_3844065 < baseStart_3844065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844080 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 2, 7]
def baseStart_3844080 : Nat := 118140960795 + 3844080 * 2 ^ 59
def prefixEnd_3844080 : Nat := 4983230072969 + 3 ^ 40 * 3844080 * 2
def baseEnd_3844080 : Nat := 1315907142890283502014269

theorem tailTrace_3844080 : CollatzResearch.WordTrace tailWord_3844080 prefixEnd_3844080 1315907142890283502014269 := by
  unfold tailWord_3844080
  simp only [CollatzResearch.WordTrace]
  refine ⟨70102557956781075720576847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93470077275708100960769129 70102557956781075720576847)
  ·
    refine ⟨105153836935171613580865271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70102557956781075720576847 105153836935171613580865271)
    ·
      refine ⟨157730755402757420371297907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105153836935171613580865271 157730755402757420371297907)
      ·
        refine ⟨236596133104136130556946861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157730755402757420371297907 236596133104136130556946861)
        ·
          refine ⟨88723549914051048958855073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236596133104136130556946861 88723549914051048958855073)
          ·
            refine ⟨66542662435538286719141305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88723549914051048958855073 66542662435538286719141305)
            ·
              refine ⟨49906996826653715039355979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66542662435538286719141305 49906996826653715039355979)
              ·
                refine ⟨74860495239980572559033969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49906996826653715039355979 74860495239980572559033969)
                ·
                  refine ⟨56145371429985429419275477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74860495239980572559033969 56145371429985429419275477)
                  ·
                    refine ⟨1315907142890283502014269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56145371429985429419275477 1315907142890283502014269)
                    ·
                      rfl

theorem cell22_3844080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 7].length) (baseStart_3844080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844080 prefixEnd_3844080 := by exact prefixLift 3844080
  have htrace : WordTrace (prefixWord ++ tailWord_3844080) baseStart_3844080 baseEnd_3844080 := by
    simpa [prefixWord, tailWord_3844080, baseEnd_3844080] using wordTrace_append hprefix tailTrace_3844080
  have hstable : (prefixWord ++ tailWord_3844080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844080).length < 2 ^ (prefixWord ++ tailWord_3844080).sum := by decide
  have hdescent : baseEnd_3844080 < baseStart_3844080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844095 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 4, 6]
def baseStart_3844095 : Nat := 118140960795 + 3844095 * 2 ^ 59
def prefixEnd_3844095 : Nat := 4983230072969 + 3 ^ 40 * 3844095 * 2
def baseEnd_3844095 : Nat := 1315912277696828462889223

theorem tailTrace_3844095 : CollatzResearch.WordTrace tailWord_3844095 prefixEnd_3844095 1315912277696828462889223 := by
  unfold tailWord_3844095
  simp only [CollatzResearch.WordTrace]
  refine ⟨140205663008507809002949739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93470442005671872668633159 140205663008507809002949739)
  ·
    refine ⟨210308494512761713504424609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140205663008507809002949739 210308494512761713504424609)
    ·
      refine ⟨157731370884571285128318457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210308494512761713504424609 157731370884571285128318457)
      ·
        refine ⟨118298528163428463846238843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157731370884571285128318457 118298528163428463846238843)
        ·
          refine ⟨177447792245142695769358265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118298528163428463846238843 177447792245142695769358265)
          ·
            refine ⟨133085844183857021827018699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177447792245142695769358265 133085844183857021827018699)
            ·
              refine ⟨199628766275785532740528049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133085844183857021827018699 199628766275785532740528049)
              ·
                refine ⟨149721574706839149555396037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199628766275785532740528049 149721574706839149555396037)
                ·
                  refine ⟨28072795257532340541636757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149721574706839149555396037 28072795257532340541636757)
                  ·
                    refine ⟨1315912277696828462889223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28072795257532340541636757 1315912277696828462889223)
                    ·
                      rfl

theorem cell22_3844095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 6].length) (baseStart_3844095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844095 prefixEnd_3844095 := by exact prefixLift 3844095
  have htrace : WordTrace (prefixWord ++ tailWord_3844095) baseStart_3844095 baseEnd_3844095 := by
    simpa [prefixWord, tailWord_3844095, baseEnd_3844095] using wordTrace_append hprefix tailTrace_3844095
  have hstable : (prefixWord ++ tailWord_3844095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844095).length < 2 ^ (prefixWord ++ tailWord_3844095).sum := by decide
  have hdescent : baseEnd_3844095 < baseStart_3844095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844127 : List Nat := [1, 1, 2, 4, 1, 2, 1, 5, 5]
def baseStart_3844127 : Nat := 118140960795 + 3844127 * 2 ^ 59
def prefixEnd_3844127 : Nat := 4983230072969 + 3 ^ 40 * 3844127 * 2
def baseEnd_3844127 : Nat := 438641077316930348696375

theorem tailTrace_3844127 : CollatzResearch.WordTrace tailWord_3844127 prefixEnd_3844127 438641077316930348696375 := by
  unfold tailWord_3844127
  simp only [CollatzResearch.WordTrace]
  refine ⟨140206830144391878468114635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93471220096261252312076423 140206830144391878468114635)
  ·
    refine ⟨210310245216587817702171953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140206830144391878468114635 210310245216587817702171953)
    ·
      refine ⟨157732683912440863276628965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210310245216587817702171953 157732683912440863276628965)
      ·
        refine ⟨29574878233582661864367931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157732683912440863276628965 29574878233582661864367931)
        ·
          refine ⟨44362317350373992796551897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29574878233582661864367931 44362317350373992796551897)
          ·
            refine ⟨33271738012780494597413923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44362317350373992796551897 33271738012780494597413923)
            ·
              refine ⟨49907607019170741896120885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33271738012780494597413923 49907607019170741896120885)
              ·
                refine ⟨4678838158047257052761333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49907607019170741896120885 4678838158047257052761333)
                ·
                  refine ⟨438641077316930348696375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4678838158047257052761333 438641077316930348696375)
                  ·
                    rfl

theorem cell22_3844127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 5].length) (baseStart_3844127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844127 prefixEnd_3844127 := by exact prefixLift 3844127
  have htrace : WordTrace (prefixWord ++ tailWord_3844127) baseStart_3844127 baseEnd_3844127 := by
    simpa [prefixWord, tailWord_3844127, baseEnd_3844127] using wordTrace_append hprefix tailTrace_3844127
  have hstable : (prefixWord ++ tailWord_3844127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844127).length < 2 ^ (prefixWord ++ tailWord_3844127).sum := by decide
  have hdescent : baseEnd_3844127 < baseStart_3844127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844161 : List Nat := [1, 2, 5, 1, 2, 3, 1, 2, 5]
def baseStart_3844161 : Nat := 118140960795 + 3844161 * 2 ^ 59
def prefixEnd_3844161 : Nat := 4983230072969 + 3 ^ 40 * 3844161 * 2
def baseEnd_3844161 : Nat := 438644956948542096913007

theorem tailTrace_3844161 : CollatzResearch.WordTrace tailWord_3844161 prefixEnd_3844161 438644956948542096913007 := by
  unfold tailWord_3844161
  simp only [CollatzResearch.WordTrace]
  refine ⟨140208070226268702274852337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93472046817512468183234891 140208070226268702274852337)
  ·
    refine ⟨105156052669701526706139253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140208070226268702274852337 105156052669701526706139253)
    ·
      refine ⟨9858379937784518128700555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105156052669701526706139253 9858379937784518128700555)
      ·
        refine ⟨14787569906676777193050833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9858379937784518128700555 14787569906676777193050833)
        ·
          refine ⟨11090677430007582894788125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14787569906676777193050833 11090677430007582894788125)
          ·
            refine ⟨4159004036252843585545547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11090677430007582894788125 4159004036252843585545547)
            ·
              refine ⟨6238506054379265378318321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4159004036252843585545547 6238506054379265378318321)
              ·
                refine ⟨4678879540784449033738741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6238506054379265378318321 4678879540784449033738741)
                ·
                  refine ⟨438644956948542096913007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4678879540784449033738741 438644956948542096913007)
                  ·
                    rfl

theorem cell22_3844161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 5].length) (baseStart_3844161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844161 prefixEnd_3844161 := by exact prefixLift 3844161
  have htrace : WordTrace (prefixWord ++ tailWord_3844161) baseStart_3844161 baseEnd_3844161 := by
    simpa [prefixWord, tailWord_3844161, baseEnd_3844161] using wordTrace_append hprefix tailTrace_3844161
  have hstable : (prefixWord ++ tailWord_3844161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844161).length < 2 ^ (prefixWord ++ tailWord_3844161).sum := by decide
  have hdescent : baseEnd_3844161 < baseStart_3844161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844172 : List Nat := [2, 2, 1, 3, 1, 1, 3, 3, 6]
def baseStart_3844172 : Nat := 118140960795 + 3844172 * 2 ^ 59
def prefixEnd_3844172 : Nat := 4983230072969 + 3 ^ 40 * 3844172 * 2
def baseEnd_3844172 : Nat := 438646212123475309571329

theorem tailTrace_3844172 : CollatzResearch.WordTrace tailWord_3844172 prefixEnd_3844172 438646212123475309571329 := by
  unfold tailWord_3844172
  simp only [CollatzResearch.WordTrace]
  refine ⟨70104235714614425576751385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93472314286152567435668513 70104235714614425576751385)
  ·
    refine ⟨52578176785960819182563539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70104235714614425576751385 52578176785960819182563539)
    ·
      refine ⟨78867265178941228773845309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52578176785960819182563539 78867265178941228773845309)
      ·
        refine ⟨29575224442102960790191991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78867265178941228773845309 29575224442102960790191991)
        ·
          refine ⟨44362836663154441185287987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29575224442102960790191991 44362836663154441185287987)
          ·
            refine ⟨66544254994731661777931981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44362836663154441185287987 66544254994731661777931981)
            ·
              refine ⟨24954095623024373166724493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66544254994731661777931981 24954095623024373166724493)
              ·
                refine ⟨9357785858634139937521685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24954095623024373166724493 9357785858634139937521685)
                ·
                  refine ⟨438646212123475309571329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9357785858634139937521685 438646212123475309571329)
                  ·
                    rfl

theorem cell22_3844172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 6].length) (baseStart_3844172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844172 prefixEnd_3844172 := by exact prefixLift 3844172
  have htrace : WordTrace (prefixWord ++ tailWord_3844172) baseStart_3844172 baseEnd_3844172 := by
    simpa [prefixWord, tailWord_3844172, baseEnd_3844172] using wordTrace_append hprefix tailTrace_3844172
  have hstable : (prefixWord ++ tailWord_3844172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844172).length < 2 ^ (prefixWord ++ tailWord_3844172).sum := by decide
  have hdescent : baseEnd_3844172 < baseStart_3844172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844204 : List Nat := [2, 2, 1, 1, 3, 3, 1, 2, 4, 3]
def baseStart_3844204 : Nat := 118140960795 + 3844204 * 2 ^ 59
def prefixEnd_3844204 : Nat := 4983230072969 + 3 ^ 40 * 3844204 * 2
def baseEnd_3844204 : Nat := 1315949590624388511913889

theorem tailTrace_3844204 : CollatzResearch.WordTrace tailWord_3844204 prefixEnd_3844204 1315949590624388511913889 := by
  unfold tailWord_3844204
  simp only [CollatzResearch.WordTrace]
  refine ⟨70104819282556460309333833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93473092376741947079111777 70104819282556460309333833)
  ·
    refine ⟨52578614461917345232000375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70104819282556460309333833 52578614461917345232000375)
    ·
      refine ⟨78867921692876017848000563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52578614461917345232000375 78867921692876017848000563)
      ·
        refine ⟨118301882539314026772000845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78867921692876017848000563 118301882539314026772000845)
        ·
          refine ⟨44363205952242760039500317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118301882539314026772000845 44363205952242760039500317)
          ·
            refine ⟨16636202232091035014812619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44363205952242760039500317 16636202232091035014812619)
            ·
              refine ⟨24954303348136552522218929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16636202232091035014812619 24954303348136552522218929)
              ·
                refine ⟨18715727511102414391664197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24954303348136552522218929 18715727511102414391664197)
                ·
                  refine ⟨3509198908331702698437037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18715727511102414391664197 3509198908331702698437037)
                  ·
                    refine ⟨1315949590624388511913889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3509198908331702698437037 1315949590624388511913889)
                    ·
                      rfl

theorem cell22_3844204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 3].length) (baseStart_3844204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844204 prefixEnd_3844204 := by exact prefixLift 3844204
  have htrace : WordTrace (prefixWord ++ tailWord_3844204) baseStart_3844204 baseEnd_3844204 := by
    simpa [prefixWord, tailWord_3844204, baseEnd_3844204] using wordTrace_append hprefix tailTrace_3844204
  have hstable : (prefixWord ++ tailWord_3844204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844204).length < 2 ^ (prefixWord ++ tailWord_3844204).sum := by decide
  have hdescent : baseEnd_3844204 < baseStart_3844204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844217 : List Nat := [1, 2, 1, 3, 4, 1, 10]
def baseStart_3844217 : Nat := 118140960795 + 3844217 * 2 ^ 59
def prefixEnd_3844217 : Nat := 4983230072969 + 3 ^ 40 * 3844217 * 2
def baseEnd_3844217 : Nat := 48739038547780030049587

theorem tailTrace_3844217 : CollatzResearch.WordTrace tailWord_3844217 prefixEnd_3844217 48739038547780030049587 := by
  unfold tailWord_3844217
  simp only [CollatzResearch.WordTrace]
  refine ⟨140210112714065823838890905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93473408476043882559260603 140210112714065823838890905)
  ·
    refine ⟨105157584535549367879168179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140210112714065823838890905 105157584535549367879168179)
    ·
      refine ⟨157736376803324051818752269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105157584535549367879168179 157736376803324051818752269)
      ·
        refine ⟨59151141301246519432032101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157736376803324051818752269 59151141301246519432032101)
        ·
          refine ⟨11090838993983722393506019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59151141301246519432032101 11090838993983722393506019)
          ·
            refine ⟨16636258490975583590259029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11090838993983722393506019 16636258490975583590259029)
            ·
              refine ⟨48739038547780030049587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16636258490975583590259029 48739038547780030049587)
              ·
                rfl

theorem cell22_3844217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 10].length) (baseStart_3844217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844217 prefixEnd_3844217 := by exact prefixLift 3844217
  have htrace : WordTrace (prefixWord ++ tailWord_3844217) baseStart_3844217 baseEnd_3844217 := by
    simpa [prefixWord, tailWord_3844217, baseEnd_3844217] using wordTrace_append hprefix tailTrace_3844217
  have hstable : (prefixWord ++ tailWord_3844217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844217).length < 2 ^ (prefixWord ++ tailWord_3844217).sum := by decide
  have hdescent : baseEnd_3844217 < baseStart_3844217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844234 : List Nat := [3, 1, 2, 3, 1, 3, 2, 7]
def baseStart_3844234 : Nat := 118140960795 + 3844234 * 2 ^ 59
def prefixEnd_3844234 : Nat := 4983230072969 + 3 ^ 40 * 3844234 * 2
def baseEnd_3844234 : Nat := 146217762248608714851533

theorem tailTrace_3844234 : CollatzResearch.WordTrace tailWord_3844234 prefixEnd_3844234 146217762248608714851533 := by
  unfold tailWord_3844234
  simp only [CollatzResearch.WordTrace]
  refine ⟨35052683188751058935564939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93473821836669490494839837 35052683188751058935564939)
  ·
    refine ⟨52579024783126588403347409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35052683188751058935564939 52579024783126588403347409)
    ·
      refine ⟨39434268587344941302510557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52579024783126588403347409 39434268587344941302510557)
      ·
        refine ⟨14787850720254352988441459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39434268587344941302510557 14787850720254352988441459)
        ·
          refine ⟨22181776080381529482662189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14787850720254352988441459 22181776080381529482662189)
          ·
            refine ⟨8318166030143073555998321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22181776080381529482662189 8318166030143073555998321)
            ·
              refine ⟨6238624522607305166998741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8318166030143073555998321 6238624522607305166998741)
              ·
                refine ⟨146217762248608714851533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6238624522607305166998741 146217762248608714851533)
                ·
                  rfl

theorem cell22_3844234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 7].length) (baseStart_3844234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844234 prefixEnd_3844234 := by exact prefixLift 3844234
  have htrace : WordTrace (prefixWord ++ tailWord_3844234) baseStart_3844234 baseEnd_3844234 := by
    simpa [prefixWord, tailWord_3844234, baseEnd_3844234] using wordTrace_append hprefix tailTrace_3844234
  have hstable : (prefixWord ++ tailWord_3844234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844234).length < 2 ^ (prefixWord ++ tailWord_3844234).sum := by decide
  have hdescent : baseEnd_3844234 < baseStart_3844234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844238 : List Nat := [4, 1, 1, 3, 3, 1, 1, 3, 2, 3]
def baseStart_3844238 : Nat := 118140960795 + 3844238 * 2 ^ 59
def prefixEnd_3844238 : Nat := 4983230072969 + 3 ^ 40 * 3844238 * 2
def baseEnd_3844238 : Nat := 1315961229519223756563785

theorem tailTrace_3844238 : CollatzResearch.WordTrace tailWord_3844238 prefixEnd_3844238 1315961229519223756563785 := by
  unfold tailWord_3844238
  simp only [CollatzResearch.WordTrace]
  refine ⟨17526359830873718053175671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93473919097993162950270245 17526359830873718053175671)
  ·
    refine ⟨26289539746310577079763507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17526359830873718053175671 26289539746310577079763507)
    ·
      refine ⟨39434309619465865619645261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26289539746310577079763507 39434309619465865619645261)
      ·
        refine ⟨14787866107299699607366973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39434309619465865619645261 14787866107299699607366973)
        ·
          refine ⟨5545449790237387352762615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14787866107299699607366973 5545449790237387352762615)
          ·
            refine ⟨8318174685356081029143923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5545449790237387352762615 8318174685356081029143923)
            ·
              refine ⟨12477262028034121543715885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8318174685356081029143923 12477262028034121543715885)
              ·
                refine ⟨4678973260512795578893457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12477262028034121543715885 4678973260512795578893457)
                ·
                  refine ⟨3509229945384596684170093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4678973260512795578893457 3509229945384596684170093)
                  ·
                    refine ⟨1315961229519223756563785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3509229945384596684170093 1315961229519223756563785)
                    ·
                      rfl

theorem cell22_3844238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_3844238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844238 prefixEnd_3844238 := by exact prefixLift 3844238
  have htrace : WordTrace (prefixWord ++ tailWord_3844238) baseStart_3844238 baseEnd_3844238 := by
    simpa [prefixWord, tailWord_3844238, baseEnd_3844238] using wordTrace_append hprefix tailTrace_3844238
  have hstable : (prefixWord ++ tailWord_3844238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844238).length < 2 ^ (prefixWord ++ tailWord_3844238).sum := by decide
  have hdescent : baseEnd_3844238 < baseStart_3844238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844249 : List Nat := [1, 2, 1, 2, 1, 2, 1, 6, 3, 3]
def baseStart_3844249 : Nat := 118140960795 + 3844249 * 2 ^ 59
def prefixEnd_3844249 : Nat := 4983230072969 + 3 ^ 40 * 3844249 * 2
def baseEnd_3844249 : Nat := 1315964995044023394538751

theorem tailTrace_3844249 : CollatzResearch.WordTrace tailWord_3844249 prefixEnd_3844249 1315964995044023394538751 := by
  unfold tailWord_3844249
  simp only [CollatzResearch.WordTrace]
  refine ⟨140211279849949893304055801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93474186566633262202703867 140211279849949893304055801)
  ·
    refine ⟨105158459887462419978041851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140211279849949893304055801 105158459887462419978041851)
    ·
      refine ⟨157737689831193629967062777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105158459887462419978041851 157737689831193629967062777)
      ·
        refine ⟨118303267373395222475297083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157737689831193629967062777 118303267373395222475297083)
        ·
          refine ⟨177454901060092833712945625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118303267373395222475297083 177454901060092833712945625)
          ·
            refine ⟨133091175795069625284709219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177454901060092833712945625 133091175795069625284709219)
            ·
              refine ⟨199636763692604437927063829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133091175795069625284709219 199636763692604437927063829)
              ·
                refine ⟨9357973298090833027831117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 199636763692604437927063829 9357973298090833027831117)
                ·
                  refine ⟨3509239986784062385436669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9357973298090833027831117 3509239986784062385436669)
                  ·
                    refine ⟨1315964995044023394538751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3509239986784062385436669 1315964995044023394538751)
                    ·
                      rfl

theorem cell22_3844249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 3, 3].length) (baseStart_3844249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844249 prefixEnd_3844249 := by exact prefixLift 3844249
  have htrace : WordTrace (prefixWord ++ tailWord_3844249) baseStart_3844249 baseEnd_3844249 := by
    simpa [prefixWord, tailWord_3844249, baseEnd_3844249] using wordTrace_append hprefix tailTrace_3844249
  have hstable : (prefixWord ++ tailWord_3844249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844249).length < 2 ^ (prefixWord ++ tailWord_3844249).sum := by decide
  have hdescent : baseEnd_3844249 < baseStart_3844249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844279 : List Nat := [1, 1, 3, 1, 4, 2, 1, 4, 5]
def baseStart_3844279 : Nat := 118140960795 + 3844279 * 2 ^ 59
def prefixEnd_3844279 : Nat := 4983230072969 + 3 ^ 40 * 3844279 * 2
def baseEnd_3844279 : Nat := 438658421552371105429553

theorem tailTrace_3844279 : CollatzResearch.WordTrace tailWord_3844279 prefixEnd_3844279 438658421552371105429553 := by
  unfold tailWord_3844279
  simp only [CollatzResearch.WordTrace]
  refine ⟨140212374039841208427647891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93474916026560805618431927 140212374039841208427647891)
  ·
    refine ⟨210318561059761812641471837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140212374039841208427647891 210318561059761812641471837)
    ·
      refine ⟨78869460397410679740551939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210318561059761812641471837 78869460397410679740551939)
      ·
        refine ⟨118304190596116019610827909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78869460397410679740551939 118304190596116019610827909)
        ·
          refine ⟨22182035736771753677030233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118304190596116019610827909 22182035736771753677030233)
          ·
            refine ⟨16636526802578815257772675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22182035736771753677030233 16636526802578815257772675)
            ·
              refine ⟨24954790203868222886659013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16636526802578815257772675 24954790203868222886659013)
              ·
                refine ⟨4679023163225291791248565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24954790203868222886659013 4679023163225291791248565)
                ·
                  refine ⟨438658421552371105429553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4679023163225291791248565 438658421552371105429553)
                  ·
                    rfl

theorem cell22_3844279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 5].length) (baseStart_3844279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844279 prefixEnd_3844279 := by exact prefixLift 3844279
  have htrace : WordTrace (prefixWord ++ tailWord_3844279) baseStart_3844279 baseEnd_3844279 := by
    simpa [prefixWord, tailWord_3844279, baseEnd_3844279] using wordTrace_append hprefix tailTrace_3844279
  have hstable : (prefixWord ++ tailWord_3844279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844279).length < 2 ^ (prefixWord ++ tailWord_3844279).sum := by decide
  have hdescent : baseEnd_3844279 < baseStart_3844279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844369 : List Nat := [1, 2, 2, 1, 1, 6, 1, 8]
def baseStart_3844369 : Nat := 118140960795 + 3844369 * 2 ^ 59
def prefixEnd_3844369 : Nat := 4983230072969 + 3 ^ 40 * 3844369 * 2
def baseEnd_3844369 : Nat := 146222897055153675726487

theorem tailTrace_3844369 : CollatzResearch.WordTrace tailWord_3844369 prefixEnd_3844369 146222897055153675726487 := by
  unfold tailWord_3844369
  simp only [CollatzResearch.WordTrace]
  refine ⟨140215656609515153798424161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93477104406343435865616107 140215656609515153798424161)
  ·
    refine ⟨105161742457136365348818121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140215656609515153798424161 105161742457136365348818121)
    ·
      refine ⟨78871306842852274011613591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105161742457136365348818121 78871306842852274011613591)
      ·
        refine ⟨118306960264278411017420387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78871306842852274011613591 118306960264278411017420387)
        ·
          refine ⟨177460440396417616526130581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118306960264278411017420387 177460440396417616526130581)
          ·
            refine ⟨8318458143582075774662371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 177460440396417616526130581 8318458143582075774662371)
            ·
              refine ⟨12477687215373113661993557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8318458143582075774662371 12477687215373113661993557)
              ·
                refine ⟨146222897055153675726487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12477687215373113661993557 146222897055153675726487)
                ·
                  rfl

theorem cell22_3844369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 8].length) (baseStart_3844369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844369 prefixEnd_3844369 := by exact prefixLift 3844369
  have htrace : WordTrace (prefixWord ++ tailWord_3844369) baseStart_3844369 baseEnd_3844369 := by
    simpa [prefixWord, tailWord_3844369, baseEnd_3844369] using wordTrace_append hprefix tailTrace_3844369
  have hstable : (prefixWord ++ tailWord_3844369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844369).length < 2 ^ (prefixWord ++ tailWord_3844369).sum := by decide
  have hdescent : baseEnd_3844369 < baseStart_3844369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844386 : List Nat := [3, 3, 1, 1, 3, 3, 8]
def baseStart_3844386 : Nat := 118140960795 + 3844386 * 2 ^ 59
def prefixEnd_3844386 : Nat := 4983230072969 + 3 ^ 40 * 3844386 * 2
def baseEnd_3844386 : Nat := 48741181220140766809753

theorem tailTrace_3844386 : CollatzResearch.WordTrace tailWord_3844386 prefixEnd_3844386 48741181220140766809753 := by
  unfold tailWord_3844386
  simp only [CollatzResearch.WordTrace]
  refine ⟨35054069162613391425448253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93477517766969043801195341 35054069162613391425448253)
  ·
    refine ⟨13145275935980021784543095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35054069162613391425448253 13145275935980021784543095)
    ·
      refine ⟨19717913903970032676814643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13145275935980021784543095 19717913903970032676814643)
      ·
        refine ⟨29576870855955049015221965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19717913903970032676814643 29576870855955049015221965)
        ·
          refine ⟨11091326570983143380708237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29576870855955049015221965 11091326570983143380708237)
          ·
            refine ⟨4159247464118678767765589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11091326570983143380708237 4159247464118678767765589)
            ·
              refine ⟨48741181220140766809753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4159247464118678767765589 48741181220140766809753)
              ·
                rfl

theorem cell22_3844386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 8].length) (baseStart_3844386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844386 prefixEnd_3844386 := by exact prefixLift 3844386
  have htrace : WordTrace (prefixWord ++ tailWord_3844386) baseStart_3844386 baseEnd_3844386 := by
    simpa [prefixWord, tailWord_3844386, baseEnd_3844386] using wordTrace_append hprefix tailTrace_3844386
  have hstable : (prefixWord ++ tailWord_3844386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844386).length < 2 ^ (prefixWord ++ tailWord_3844386).sum := by decide
  have hdescent : baseEnd_3844386 < baseStart_3844386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844448 : List Nat := [2, 1, 1, 3, 5, 1, 2, 2, 5]
def baseStart_3844448 : Nat := 118140960795 + 3844448 * 2 ^ 59
def prefixEnd_3844448 : Nat := 4983230072969 + 3 ^ 40 * 3844448 * 2
def baseEnd_3844448 : Nat := 438677705603617736271047

theorem tailTrace_3844448 : CollatzResearch.WordTrace tailWord_3844448 prefixEnd_3844448 438677705603617736271047 := by
  unfold tailWord_3844448
  simp only [CollatzResearch.WordTrace]
  refine ⟨70109268988114475145274999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93479025317485966860366665 70109268988114475145274999)
  ·
    refine ⟨105163903482171712717912499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70109268988114475145274999 105163903482171712717912499)
    ·
      refine ⟨157745855223257569076868749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105163903482171712717912499 157745855223257569076868749)
      ·
        refine ⟨59154695708721588403825781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157745855223257569076868749 59154695708721588403825781)
        ·
          refine ⟨5545752722692648912858667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59154695708721588403825781 5545752722692648912858667)
          ·
            refine ⟨8318629084038973369288001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5545752722692648912858667 8318629084038973369288001)
            ·
              refine ⟨6238971813029230026966001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8318629084038973369288001 6238971813029230026966001)
              ·
                refine ⟨4679228859771922520224501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6238971813029230026966001 4679228859771922520224501)
                ·
                  refine ⟨438677705603617736271047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4679228859771922520224501 438677705603617736271047)
                  ·
                    rfl

theorem cell22_3844448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 5].length) (baseStart_3844448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844448 prefixEnd_3844448 := by exact prefixLift 3844448
  have htrace : WordTrace (prefixWord ++ tailWord_3844448) baseStart_3844448 baseEnd_3844448 := by
    simpa [prefixWord, tailWord_3844448, baseEnd_3844448] using wordTrace_append hprefix tailTrace_3844448
  have hstable : (prefixWord ++ tailWord_3844448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844448).length < 2 ^ (prefixWord ++ tailWord_3844448).sum := by decide
  have hdescent : baseEnd_3844448 < baseStart_3844448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844461 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 5, 4]
def baseStart_3844461 : Nat := 118140960795 + 3844461 * 2 ^ 59
def prefixEnd_3844461 : Nat := 4983230072969 + 3 ^ 40 * 3844461 * 2
def baseEnd_3844461 : Nat := 1316037566976525508238101

theorem tailTrace_3844461 : CollatzResearch.WordTrace tailWord_3844461 prefixEnd_3844461 1316037566976525508238101 := by
  unfold tailWord_3844461
  simp only [CollatzResearch.WordTrace]
  refine ⟨140219012125181853510773237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93479341416787902340515491 140219012125181853510773237)
  ·
    refine ⟨13145532386735798766634991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140219012125181853510773237 13145532386735798766634991)
    ·
      refine ⟨19718298580103698149952487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13145532386735798766634991 19718298580103698149952487)
      ·
        refine ⟨29577447870155547224928731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19718298580103698149952487 29577447870155547224928731)
        ·
          refine ⟨44366171805233320837393097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29577447870155547224928731 44366171805233320837393097)
          ·
            refine ⟨33274628853924990628044823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44366171805233320837393097 33274628853924990628044823)
            ·
              refine ⟨49911943280887485942067235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33274628853924990628044823 49911943280887485942067235)
              ·
                refine ⟨74867914921331228913100853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49911943280887485942067235 74867914921331228913100853)
                ·
                  refine ⟨7018867023874802710603205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74867914921331228913100853 7018867023874802710603205)
                  ·
                    refine ⟨1316037566976525508238101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7018867023874802710603205 1316037566976525508238101)
                    ·
                      rfl

theorem cell22_3844461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_3844461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844461 prefixEnd_3844461 := by exact prefixLift 3844461
  have htrace : WordTrace (prefixWord ++ tailWord_3844461) baseStart_3844461 baseEnd_3844461 := by
    simpa [prefixWord, tailWord_3844461, baseEnd_3844461] using wordTrace_append hprefix tailTrace_3844461
  have hstable : (prefixWord ++ tailWord_3844461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844461).length < 2 ^ (prefixWord ++ tailWord_3844461).sum := by decide
  have hdescent : baseEnd_3844461 < baseStart_3844461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844491 : List Nat := [1, 1, 1, 1, 4, 4, 2, 2, 1, 5]
def baseStart_3844491 : Nat := 118140960795 + 3844491 * 2 ^ 59
def prefixEnd_3844491 : Nat := 4983230072969 + 3 ^ 40 * 3844491 * 2
def baseEnd_3844491 : Nat := 1316047836589615429988009

theorem tailTrace_3844491 : CollatzResearch.WordTrace tailWord_3844491 prefixEnd_3844491 1316047836589615429988009 := by
  unfold tailWord_3844491
  simp only [CollatzResearch.WordTrace]
  refine ⟨140220106315073168634365327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93480070876715445756243551 140220106315073168634365327)
  ·
    refine ⟨210330159472609752951547991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140220106315073168634365327 210330159472609752951547991)
    ·
      refine ⟨315495239208914629427321987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210330159472609752951547991 315495239208914629427321987)
      ·
        refine ⟨473242858813371944140982981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315495239208914629427321987 473242858813371944140982981)
        ·
          refine ⟨88733036027507239526434309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 473242858813371944140982981 88733036027507239526434309)
          ·
            refine ⟨16637444255157607411206433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88733036027507239526434309 16637444255157607411206433)
            ·
              refine ⟨12478083191368205558404825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16637444255157607411206433 12478083191368205558404825)
              ·
                refine ⟨9358562393526154168803619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12478083191368205558404825 9358562393526154168803619)
                ·
                  refine ⟨14037843590289231253205429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9358562393526154168803619 14037843590289231253205429)
                  ·
                    refine ⟨1316047836589615429988009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14037843590289231253205429 1316047836589615429988009)
                    ·
                      rfl

theorem cell22_3844491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 5].length) (baseStart_3844491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844491 prefixEnd_3844491 := by exact prefixLift 3844491
  have htrace : WordTrace (prefixWord ++ tailWord_3844491) baseStart_3844491 baseEnd_3844491 := by
    simpa [prefixWord, tailWord_3844491, baseEnd_3844491] using wordTrace_append hprefix tailTrace_3844491
  have hstable : (prefixWord ++ tailWord_3844491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844491).length < 2 ^ (prefixWord ++ tailWord_3844491).sum := by decide
  have hdescent : baseEnd_3844491 < baseStart_3844491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844510 : List Nat := [4, 3, 1, 2, 1, 2, 2, 1, 6]
def baseStart_3844510 : Nat := 118140960795 + 3844510 * 2 ^ 59
def prefixEnd_3844510 : Nat := 4983230072969 + 3 ^ 40 * 3844510 * 2
def baseEnd_3844510 : Nat := 438684780225968571254317

theorem tailTrace_3844510 : CollatzResearch.WordTrace tailWord_3844510 prefixEnd_3844510 438684780225968571254317 := by
  unfold tailWord_3844510
  simp only [CollatzResearch.WordTrace]
  refine ⟨17527599912750541859913373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93480532868002889919537989 17527599912750541859913373)
  ·
    refine ⟨6572849967281453197467515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17527599912750541859913373 6572849967281453197467515)
    ·
      refine ⟨9859274950922179796201273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6572849967281453197467515 9859274950922179796201273)
      ·
        refine ⟨7394456213191634847150955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9859274950922179796201273 7394456213191634847150955)
        ·
          refine ⟨11091684319787452270726433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7394456213191634847150955 11091684319787452270726433)
          ·
            refine ⟨8318763239840589203044825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11091684319787452270726433 8318763239840589203044825)
            ·
              refine ⟨6239072429880441902283619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8318763239840589203044825 6239072429880441902283619)
              ·
                refine ⟨9358608644820662853425429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6239072429880441902283619 9358608644820662853425429)
                ·
                  refine ⟨438684780225968571254317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9358608644820662853425429 438684780225968571254317)
                  ·
                    rfl

theorem cell22_3844510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_3844510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844510 prefixEnd_3844510 := by exact prefixLift 3844510
  have htrace : WordTrace (prefixWord ++ tailWord_3844510) baseStart_3844510 baseEnd_3844510 := by
    simpa [prefixWord, tailWord_3844510, baseEnd_3844510] using wordTrace_append hprefix tailTrace_3844510
  have hstable : (prefixWord ++ tailWord_3844510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844510).length < 2 ^ (prefixWord ++ tailWord_3844510).sum := by decide
  have hdescent : baseEnd_3844510 < baseStart_3844510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844583 : List Nat := [1, 1, 5, 2, 1, 1, 3, 3, 5]
def baseStart_3844583 : Nat := 118140960795 + 3844583 * 2 ^ 59
def prefixEnd_3844583 : Nat := 4983230072969 + 3 ^ 40 * 3844583 * 2
def baseEnd_3844583 : Nat := 438693110023252618895909

theorem tailTrace_3844583 : CollatzResearch.WordTrace tailWord_3844583 prefixEnd_3844583 438693110023252618895909 := by
  unfold tailWord_3844583
  simp only [CollatzResearch.WordTrace]
  refine ⟨140223461830739868346714403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93482307887159912231142935 140223461830739868346714403)
  ·
    refine ⟨210335192746109802520071605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140223461830739868346714403 210335192746109802520071605)
    ·
      refine ⟨19718924319947793986256713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 210335192746109802520071605 19718924319947793986256713)
      ·
        refine ⟨14789193239960845489692535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19718924319947793986256713 14789193239960845489692535)
        ·
          refine ⟨22183789859941268234538803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14789193239960845489692535 22183789859941268234538803)
          ·
            refine ⟨33275684789911902351808205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22183789859941268234538803 33275684789911902351808205)
            ·
              refine ⟨12478381796216963381928077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33275684789911902351808205 12478381796216963381928077)
              ·
                refine ⟨4679393173581361268223029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12478381796216963381928077 4679393173581361268223029)
                ·
                  refine ⟨438693110023252618895909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4679393173581361268223029 438693110023252618895909)
                  ·
                    rfl

theorem cell22_3844583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 5].length) (baseStart_3844583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844583 prefixEnd_3844583 := by exact prefixLift 3844583
  have htrace : WordTrace (prefixWord ++ tailWord_3844583) baseStart_3844583 baseEnd_3844583 := by
    simpa [prefixWord, tailWord_3844583, baseEnd_3844583] using wordTrace_append hprefix tailTrace_3844583
  have hstable : (prefixWord ++ tailWord_3844583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844583).length < 2 ^ (prefixWord ++ tailWord_3844583).sum := by decide
  have hdescent : baseEnd_3844583 < baseStart_3844583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844613 : List Nat := [1, 3, 1, 1, 2, 2, 2, 5, 1, 4]
def baseStart_3844613 : Nat := 118140960795 + 3844613 * 2 ^ 59
def prefixEnd_3844613 : Nat := 4983230072969 + 3 ^ 40 * 3844613 * 2
def baseEnd_3844613 : Nat := 1316089599682847778437635

theorem tailTrace_3844613 : CollatzResearch.WordTrace tailWord_3844613 prefixEnd_3844613 1316089599682847778437635 := by
  unfold tailWord_3844613
  simp only [CollatzResearch.WordTrace]
  refine ⟨140224556020631183470306493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93483037347087455646870995 140224556020631183470306493)
  ·
    refine ⟨52584208507736693801364935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140224556020631183470306493 52584208507736693801364935)
    ·
      refine ⟨78876312761605040702047403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52584208507736693801364935 78876312761605040702047403)
      ·
        refine ⟨118314469142407561053071105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78876312761605040702047403 118314469142407561053071105)
        ·
          refine ⟨88735851856805670789803329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118314469142407561053071105 88735851856805670789803329)
          ·
            refine ⟨66551888892604253092352497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88735851856805670789803329 66551888892604253092352497)
            ·
              refine ⟨49913916669453189819264373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66551888892604253092352497 49913916669453189819264373)
              ·
                refine ⟨4679429687761236545556035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49913916669453189819264373 4679429687761236545556035)
                ·
                  refine ⟨7019144531641854818334053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4679429687761236545556035 7019144531641854818334053)
                  ·
                    refine ⟨1316089599682847778437635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7019144531641854818334053 1316089599682847778437635)
                    ·
                      rfl

theorem cell22_3844613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_3844613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844613 prefixEnd_3844613 := by exact prefixLift 3844613
  have htrace : WordTrace (prefixWord ++ tailWord_3844613) baseStart_3844613 baseEnd_3844613 := by
    simpa [prefixWord, tailWord_3844613, baseEnd_3844613] using wordTrace_append hprefix tailTrace_3844613
  have hstable : (prefixWord ++ tailWord_3844613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844613).length < 2 ^ (prefixWord ++ tailWord_3844613).sum := by decide
  have hdescent : baseEnd_3844613 < baseStart_3844613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844621 : List Nat := [1, 7, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_3844621 : Nat := 118140960795 + 3844621 * 2 ^ 59
def prefixEnd_3844621 : Nat := 4983230072969 + 3 ^ 40 * 3844621 * 2
def baseEnd_3844621 : Nat := 1316092338246338424237611

theorem tailTrace_3844621 : CollatzResearch.WordTrace tailWord_3844621 prefixEnd_3844621 1316092338246338424237611 := by
  unfold tailWord_3844621
  simp only [CollatzResearch.WordTrace]
  refine ⟨140224847804602200836597717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93483231869734800557731811 140224847804602200836597717)
  ·
    refine ⟨3286519870420364082107759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 140224847804602200836597717 3286519870420364082107759)
    ·
      refine ⟨4929779805630546123161639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3286519870420364082107759 4929779805630546123161639)
      ·
        refine ⟨7394669708445819184742459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4929779805630546123161639 7394669708445819184742459)
        ·
          refine ⟨11092004562668728777113689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7394669708445819184742459 11092004562668728777113689)
          ·
            refine ⟨8319003422001546582835267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11092004562668728777113689 8319003422001546582835267)
            ·
              refine ⟨12478505133002319874252901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8319003422001546582835267 12478505133002319874252901)
              ·
                refine ⟨2339719712437934976422419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12478505133002319874252901 2339719712437934976422419)
                ·
                  refine ⟨3509579568656902464633629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2339719712437934976422419 3509579568656902464633629)
                  ·
                    refine ⟨1316092338246338424237611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3509579568656902464633629 1316092338246338424237611)
                    ·
                      rfl

theorem cell22_3844621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_3844621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844621 prefixEnd_3844621 := by exact prefixLift 3844621
  have htrace : WordTrace (prefixWord ++ tailWord_3844621) baseStart_3844621 baseEnd_3844621 := by
    simpa [prefixWord, tailWord_3844621, baseEnd_3844621] using wordTrace_append hprefix tailTrace_3844621
  have hstable : (prefixWord ++ tailWord_3844621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844621).length < 2 ^ (prefixWord ++ tailWord_3844621).sum := by decide
  have hdescent : baseEnd_3844621 < baseStart_3844621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844643 : List Nat := [1, 1, 1, 4, 4, 1, 1, 3, 1, 5]
def baseStart_3844643 : Nat := 118140960795 + 3844643 * 2 ^ 59
def prefixEnd_3844643 : Nat := 4983230072969 + 3 ^ 40 * 3844643 * 2
def baseEnd_3844643 : Nat := 1316099869295937700187543

theorem tailTrace_3844643 : CollatzResearch.WordTrace tailWord_3844643 prefixEnd_3844643 1316099869295937700187543 := by
  unfold tailWord_3844643
  simp only [CollatzResearch.WordTrace]
  refine ⟨140225650210522498593898583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93483766807014999062599055 140225650210522498593898583)
  ·
    refine ⟨210338475315783747890847875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140225650210522498593898583 210338475315783747890847875)
    ·
      refine ⟨315507712973675621836271813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210338475315783747890847875 315507712973675621836271813)
      ·
        refine ⟨59157696182564179094300965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 315507712973675621836271813 59157696182564179094300965)
        ·
          refine ⟨11092068034230783580181431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59157696182564179094300965 11092068034230783580181431)
          ·
            refine ⟨16638102051346175370272147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11092068034230783580181431 16638102051346175370272147)
            ·
              refine ⟨24957153077019263055408221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16638102051346175370272147 24957153077019263055408221)
              ·
                refine ⟨9358932403882223645778083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24957153077019263055408221 9358932403882223645778083)
                ·
                  refine ⟨14038398605823335468667125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9358932403882223645778083 14038398605823335468667125)
                  ·
                    refine ⟨1316099869295937700187543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14038398605823335468667125 1316099869295937700187543)
                    ·
                      rfl

theorem cell22_3844643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 5].length) (baseStart_3844643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844643 prefixEnd_3844643 := by exact prefixLift 3844643
  have htrace : WordTrace (prefixWord ++ tailWord_3844643) baseStart_3844643 baseEnd_3844643 := by
    simpa [prefixWord, tailWord_3844643, baseEnd_3844643] using wordTrace_append hprefix tailTrace_3844643
  have hstable : (prefixWord ++ tailWord_3844643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844643).length < 2 ^ (prefixWord ++ tailWord_3844643).sum := by decide
  have hdescent : baseEnd_3844643 < baseStart_3844643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844656 : List Nat := [2, 1, 1, 1, 2, 3, 2, 10]
def baseStart_3844656 : Nat := 118140960795 + 3844656 * 2 ^ 59
def prefixEnd_3844656 : Nat := 4983230072969 + 3 ^ 40 * 3844656 * 2
def baseEnd_3844656 : Nat := 146233813273512222179167

theorem tailTrace_3844656 : CollatzResearch.WordTrace tailWord_3844656 prefixEnd_3844656 146233813273512222179167 := by
  unfold tailWord_3844656
  simp only [CollatzResearch.WordTrace]
  refine ⟨70113062179737700907060911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93484082906316934542747881 70113062179737700907060911)
  ·
    refine ⟨105169593269606551360591367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70113062179737700907060911 105169593269606551360591367)
    ·
      refine ⟨157754389904409827040887051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105169593269606551360591367 157754389904409827040887051)
      ·
        refine ⟨236631584856614740561330577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157754389904409827040887051 236631584856614740561330577)
        ·
          refine ⟨177473688642461055420997933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236631584856614740561330577 177473688642461055420997933)
          ·
            refine ⟨66552633240922895782874225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177473688642461055420997933 66552633240922895782874225)
            ·
              refine ⟨49914474930692171837155669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66552633240922895782874225 49914474930692171837155669)
              ·
                refine ⟨146233813273512222179167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49914474930692171837155669 146233813273512222179167)
                ·
                  rfl

theorem cell22_3844656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 10].length) (baseStart_3844656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844656 prefixEnd_3844656 := by exact prefixLift 3844656
  have htrace : WordTrace (prefixWord ++ tailWord_3844656) baseStart_3844656 baseEnd_3844656 := by
    simpa [prefixWord, tailWord_3844656, baseEnd_3844656] using wordTrace_append hprefix tailTrace_3844656
  have hstable : (prefixWord ++ tailWord_3844656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844656).length < 2 ^ (prefixWord ++ tailWord_3844656).sum := by decide
  have hdescent : baseEnd_3844656 < baseStart_3844656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844662 : List Nat := [5, 1, 2, 1, 2, 1, 1, 5, 4]
def baseStart_3844662 : Nat := 118140960795 + 3844662 * 2 ^ 59
def prefixEnd_3844662 : Nat := 4983230072969 + 3 ^ 40 * 3844662 * 2
def baseEnd_3844662 : Nat := 438702124461409327987495

theorem tailTrace_3844662 : CollatzResearch.WordTrace tailWord_3844662 prefixEnd_3844662 438702124461409327987495 := by
  unfold tailWord_3844662
  simp only [CollatzResearch.WordTrace]
  refine ⟨8764146449840854052427515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93484228798302443225893493 8764146449840854052427515)
  ·
    refine ⟨13146219674761281078641273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8764146449840854052427515 13146219674761281078641273)
    ·
      refine ⟨9859664756070960808980955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13146219674761281078641273 9859664756070960808980955)
      ·
        refine ⟨14789497134106441213471433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9859664756070960808980955 14789497134106441213471433)
        ·
          refine ⟨11092122850579830910103575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14789497134106441213471433 11092122850579830910103575)
          ·
            refine ⟨16638184275869746365155363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11092122850579830910103575 16638184275869746365155363)
            ·
              refine ⟨24957276413804619547733045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16638184275869746365155363 24957276413804619547733045)
              ·
                refine ⟨2339744663794183082599973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24957276413804619547733045 2339744663794183082599973)
                ·
                  refine ⟨438702124461409327987495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2339744663794183082599973 438702124461409327987495)
                  ·
                    rfl

theorem cell22_3844662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_3844662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844662 prefixEnd_3844662 := by exact prefixLift 3844662
  have htrace : WordTrace (prefixWord ++ tailWord_3844662) baseStart_3844662 baseEnd_3844662 := by
    simpa [prefixWord, tailWord_3844662, baseEnd_3844662] using wordTrace_append hprefix tailTrace_3844662
  have hstable : (prefixWord ++ tailWord_3844662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844662).length < 2 ^ (prefixWord ++ tailWord_3844662).sum := by decide
  have hdescent : baseEnd_3844662 < baseStart_3844662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844673 : List Nat := [1, 2, 5, 1, 1, 3, 9]
def baseStart_3844673 : Nat := 118140960795 + 3844673 * 2 ^ 59
def prefixEnd_3844673 : Nat := 4983230072969 + 3 ^ 40 * 3844673 * 2
def baseEnd_3844673 : Nat := 48744819959593615627313

theorem tailTrace_3844673 : CollatzResearch.WordTrace tailWord_3844673 prefixEnd_3844673 48744819959593615627313 := by
  unfold tailWord_3844673
  simp only [CollatzResearch.WordTrace]
  refine ⟨140226744400413813717490673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93484496266942542478327115 140226744400413813717490673)
  ·
    refine ⟨105170058300310360288118005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140226744400413813717490673 105170058300310360288118005)
    ·
      refine ⟨9859692965654096277011063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105170058300310360288118005 9859692965654096277011063)
      ·
        refine ⟨14789539448481144415516595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9859692965654096277011063 14789539448481144415516595)
        ·
          refine ⟨22184309172721716623274893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14789539448481144415516595 22184309172721716623274893)
          ·
            refine ⟨8319115939770643733728085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22184309172721716623274893 8319115939770643733728085)
            ·
              refine ⟨48744819959593615627313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8319115939770643733728085 48744819959593615627313)
              ·
                rfl

theorem cell22_3844673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 9].length) (baseStart_3844673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844673 prefixEnd_3844673 := by exact prefixLift 3844673
  have htrace : WordTrace (prefixWord ++ tailWord_3844673) baseStart_3844673 baseEnd_3844673 := by
    simpa [prefixWord, tailWord_3844673, baseEnd_3844673] using wordTrace_append hprefix tailTrace_3844673
  have hstable : (prefixWord ++ tailWord_3844673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844673).length < 2 ^ (prefixWord ++ tailWord_3844673).sum := by decide
  have hdescent : baseEnd_3844673 < baseStart_3844673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844677 : List Nat := [1, 3, 1, 1, 1, 7, 1, 2, 2, 3]
def baseStart_3844677 : Nat := 118140960795 + 3844677 * 2 ^ 59
def prefixEnd_3844677 : Nat := 4983230072969 + 3 ^ 40 * 3844677 * 2
def baseEnd_3844677 : Nat := 1316111508190772944837439

theorem tailTrace_3844677 : CollatzResearch.WordTrace tailWord_3844677 prefixEnd_3844677 1316111508190772944837439 := by
  unfold tailWord_3844677
  simp only [CollatzResearch.WordTrace]
  refine ⟨140226890292399322400636285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93484593528266214933757523 140226890292399322400636285)
  ·
    refine ⟨52585083859649745900238607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140226890292399322400636285 52585083859649745900238607)
    ·
      refine ⟨78877625789474618850357911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52585083859649745900238607 78877625789474618850357911)
      ·
        refine ⟨118316438684211928275536867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78877625789474618850357911 118316438684211928275536867)
        ·
          refine ⟨177474658026317892413305301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118316438684211928275536867 177474658026317892413305301)
          ·
            refine ⟨4159562297491825603436843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 177474658026317892413305301 4159562297491825603436843)
            ·
              refine ⟨6239343446237738405155265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4159562297491825603436843 6239343446237738405155265)
              ·
                refine ⟨4679507584678303803866449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6239343446237738405155265 4679507584678303803866449)
                ·
                  refine ⟨3509630688508727852899837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4679507584678303803866449 3509630688508727852899837)
                  ·
                    refine ⟨1316111508190772944837439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3509630688508727852899837 1316111508190772944837439)
                    ·
                      rfl

theorem cell22_3844677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 2, 3].length) (baseStart_3844677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844677 prefixEnd_3844677 := by exact prefixLift 3844677
  have htrace : WordTrace (prefixWord ++ tailWord_3844677) baseStart_3844677 baseEnd_3844677 := by
    simpa [prefixWord, tailWord_3844677, baseEnd_3844677] using wordTrace_append hprefix tailTrace_3844677
  have hstable : (prefixWord ++ tailWord_3844677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844677).length < 2 ^ (prefixWord ++ tailWord_3844677).sum := by decide
  have hdescent : baseEnd_3844677 < baseStart_3844677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844705 : List Nat := [1, 2, 3, 1, 1, 4, 2, 2, 3, 3]
def baseStart_3844705 : Nat := 118140960795 + 3844705 * 2 ^ 59
def prefixEnd_3844705 : Nat := 4983230072969 + 3 ^ 40 * 3844705 * 2
def baseEnd_3844705 : Nat := 1316121093162990205137353

theorem tailTrace_3844705 : CollatzResearch.WordTrace tailWord_3844705 prefixEnd_3844705 1316121093162990205137353 := by
  unfold tailWord_3844705
  simp only [CollatzResearch.WordTrace]
  refine ⟨140227911536297883182655569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93485274357531922121770379 140227911536297883182655569)
  ·
    refine ⟨105170933652223412386991677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140227911536297883182655569 105170933652223412386991677)
    ·
      refine ⟨39439100119583779645121879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105170933652223412386991677 39439100119583779645121879)
      ·
        refine ⟨59158650179375669467682819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39439100119583779645121879 59158650179375669467682819)
        ·
          refine ⟨88737975269063504201524229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59158650179375669467682819 88737975269063504201524229)
          ·
            refine ⟨16638370362949407037785793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88737975269063504201524229 16638370362949407037785793)
            ·
              refine ⟨12478777772212055278339345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16638370362949407037785793 12478777772212055278339345)
              ·
                refine ⟨9359083329159041458754509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12478777772212055278339345 9359083329159041458754509)
                ·
                  refine ⟨3509656248434640547032941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9359083329159041458754509 3509656248434640547032941)
                  ·
                    refine ⟨1316121093162990205137353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3509656248434640547032941 1316121093162990205137353)
                    ·
                      rfl

theorem cell22_3844705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_3844705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844705 prefixEnd_3844705 := by exact prefixLift 3844705
  have htrace : WordTrace (prefixWord ++ tailWord_3844705) baseStart_3844705 baseEnd_3844705 := by
    simpa [prefixWord, tailWord_3844705, baseEnd_3844705] using wordTrace_append hprefix tailTrace_3844705
  have hstable : (prefixWord ++ tailWord_3844705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844705).length < 2 ^ (prefixWord ++ tailWord_3844705).sum := by decide
  have hdescent : baseEnd_3844705 < baseStart_3844705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844790 : List Nat := [5, 1, 3, 1, 2, 2, 2, 2, 1, 3]
def baseStart_3844790 : Nat := 118140960795 + 3844790 * 2 ^ 59
def prefixEnd_3844790 : Nat := 4983230072969 + 3 ^ 40 * 3844790 * 2
def baseEnd_3844790 : Nat := 1316150190400078316762093

theorem tailTrace_3844790 : CollatzResearch.WordTrace tailWord_3844790 prefixEnd_3844790 1316150190400078316762093 := by
  unfold tailWord_3844790
  simp only [CollatzResearch.WordTrace]
  refine ⟨8764438233811871418718739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93487341160659961799666549 8764438233811871418718739)
  ·
    refine ⟨13146657350717807128078109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8764438233811871418718739 13146657350717807128078109)
    ·
      refine ⟨4929996506519177673029291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13146657350717807128078109 4929996506519177673029291)
      ·
        refine ⟨7394994759778766509543937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4929996506519177673029291 7394994759778766509543937)
        ·
          refine ⟨5546246069834074882157953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7394994759778766509543937 5546246069834074882157953)
          ·
            refine ⟨4159684552375556161618465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5546246069834074882157953 4159684552375556161618465)
            ·
              refine ⟨3119763414281667121213849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4159684552375556161618465 3119763414281667121213849)
              ·
                refine ⟨2339822560711250340910387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3119763414281667121213849 2339822560711250340910387)
                ·
                  refine ⟨3509733841066875511365581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2339822560711250340910387 3509733841066875511365581)
                  ·
                    refine ⟨1316150190400078316762093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3509733841066875511365581 1316150190400078316762093)
                    ·
                      rfl

theorem cell22_3844790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_3844790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844790 prefixEnd_3844790 := by exact prefixLift 3844790
  have htrace : WordTrace (prefixWord ++ tailWord_3844790) baseStart_3844790 baseEnd_3844790 := by
    simpa [prefixWord, tailWord_3844790, baseEnd_3844790] using wordTrace_append hprefix tailTrace_3844790
  have hstable : (prefixWord ++ tailWord_3844790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844790).length < 2 ^ (prefixWord ++ tailWord_3844790).sum := by decide
  have hdescent : baseEnd_3844790 < baseStart_3844790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844793 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 3, 6]
def baseStart_3844793 : Nat := 118140960795 + 3844793 * 2 ^ 59
def prefixEnd_3844793 : Nat := 4983230072969 + 3 ^ 40 * 3844793 * 2
def baseEnd_3844793 : Nat := 1316151217361387308937083

theorem tailTrace_3844793 : CollatzResearch.WordTrace tailWord_3844793 prefixEnd_3844793 1316151217361387308937083 := by
  unfold tailWord_3844793
  simp only [CollatzResearch.WordTrace]
  refine ⟨140231121159979074211859033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93487414106652716141239355 140231121159979074211859033)
  ·
    refine ⟨105173340869984305658894275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140231121159979074211859033 105173340869984305658894275)
    ·
      refine ⟨157760011304976458488341413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105173340869984305658894275 157760011304976458488341413)
      ·
        refine ⟨29580002119683085966564015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157760011304976458488341413 29580002119683085966564015)
        ·
          refine ⟨44370003179524628949846023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29580002119683085966564015 44370003179524628949846023)
          ·
            refine ⟨66555004769286943424769035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44370003179524628949846023 66555004769286943424769035)
            ·
              refine ⟨99832507153930415137153553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66555004769286943424769035 99832507153930415137153553)
              ·
                refine ⟨74874380365447811352865165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99832507153930415137153553 74874380365447811352865165)
                ·
                  refine ⟨28077892637042929257324437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74874380365447811352865165 28077892637042929257324437)
                  ·
                    refine ⟨1316151217361387308937083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28077892637042929257324437 1316151217361387308937083)
                    ·
                      rfl

theorem cell22_3844793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 6].length) (baseStart_3844793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844793 prefixEnd_3844793 := by exact prefixLift 3844793
  have htrace : WordTrace (prefixWord ++ tailWord_3844793) baseStart_3844793 baseEnd_3844793 := by
    simpa [prefixWord, tailWord_3844793, baseEnd_3844793] using wordTrace_append hprefix tailTrace_3844793
  have hstable : (prefixWord ++ tailWord_3844793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844793).length < 2 ^ (prefixWord ++ tailWord_3844793).sum := by decide
  have hdescent : baseEnd_3844793 < baseStart_3844793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844797 : List Nat := [1, 4, 1, 2, 1, 4, 1, 4, 4]
def baseStart_3844797 : Nat := 118140960795 + 3844797 * 2 ^ 59
def prefixEnd_3844797 : Nat := 4983230072969 + 3 ^ 40 * 3844797 * 2
def baseEnd_3844797 : Nat := 438717528881044210612357

theorem tailTrace_3844797 : CollatzResearch.WordTrace tailWord_3844797 prefixEnd_3844797 438717528881044210612357 := by
  unfold tailWord_3844797
  simp only [CollatzResearch.WordTrace]
  refine ⟨140231267051964582895004645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93487511367976388596669763 140231267051964582895004645)
  ·
    refine ⟨26293362572243359292813371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140231267051964582895004645 26293362572243359292813371)
    ·
      refine ⟨39440043858365038939220057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26293362572243359292813371 39440043858365038939220057)
      ·
        refine ⟨29580032893773779204415043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39440043858365038939220057 29580032893773779204415043)
        ·
          refine ⟨44370049340660668806622565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29580032893773779204415043 44370049340660668806622565)
          ·
            refine ⟨8319384251373875401241731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44370049340660668806622565 8319384251373875401241731)
            ·
              refine ⟨12479076377060813101862597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8319384251373875401241731 12479076377060813101862597)
              ·
                refine ⟨2339826820698902456599237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12479076377060813101862597 2339826820698902456599237)
                ·
                  refine ⟨438717528881044210612357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2339826820698902456599237 438717528881044210612357)
                  ·
                    rfl

theorem cell22_3844797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_3844797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844797 prefixEnd_3844797 := by exact prefixLift 3844797
  have htrace : WordTrace (prefixWord ++ tailWord_3844797) baseStart_3844797 baseEnd_3844797 := by
    simpa [prefixWord, tailWord_3844797, baseEnd_3844797] using wordTrace_append hprefix tailTrace_3844797
  have hstable : (prefixWord ++ tailWord_3844797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844797).length < 2 ^ (prefixWord ++ tailWord_3844797).sum := by decide
  have hdescent : baseEnd_3844797 < baseStart_3844797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844812 : List Nat := [2, 2, 1, 5, 1, 2, 2, 1, 1, 5]
def baseStart_3844812 : Nat := 118140960795 + 3844812 * 2 ^ 59
def prefixEnd_3844812 : Nat := 4983230072969 + 3 ^ 40 * 3844812 * 2
def baseEnd_3844812 : Nat := 1316157721449677592712025

theorem tailTrace_3844812 : CollatzResearch.WordTrace tailWord_3844812 prefixEnd_3844812 1316157721449677592712025 := by
  unfold tailWord_3844812
  simp only [CollatzResearch.WordTrace]
  refine ⟨70115907073455120228400345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93487876097940160304533793 70115907073455120228400345)
  ·
    refine ⟨52586930305091340171300259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70115907073455120228400345 52586930305091340171300259)
    ·
      refine ⟨78880395457637010256950389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52586930305091340171300259 78880395457637010256950389)
      ·
        refine ⟨7395037074153469711589099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78880395457637010256950389 7395037074153469711589099)
        ·
          refine ⟨11092555611230204567383649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7395037074153469711589099 11092555611230204567383649)
          ·
            refine ⟨8319416708422653425537737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11092555611230204567383649 8319416708422653425537737)
            ·
              refine ⟨6239562531316990069153303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8319416708422653425537737 6239562531316990069153303)
              ·
                refine ⟨9359343796975485103729955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6239562531316990069153303 9359343796975485103729955)
                ·
                  refine ⟨14039015695463227655594933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9359343796975485103729955 14039015695463227655594933)
                  ·
                    refine ⟨1316157721449677592712025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14039015695463227655594933 1316157721449677592712025)
                    ·
                      rfl

theorem cell22_3844812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_3844812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844812 prefixEnd_3844812 := by exact prefixLift 3844812
  have htrace : WordTrace (prefixWord ++ tailWord_3844812) baseStart_3844812 baseEnd_3844812 := by
    simpa [prefixWord, tailWord_3844812, baseEnd_3844812] using wordTrace_append hprefix tailTrace_3844812
  have hstable : (prefixWord ++ tailWord_3844812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844812).length < 2 ^ (prefixWord ++ tailWord_3844812).sum := by decide
  have hdescent : baseEnd_3844812 < baseStart_3844812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844825 : List Nat := [1, 2, 1, 2, 3, 2, 5, 6]
def baseStart_3844825 : Nat := 118140960795 + 3844825 * 2 ^ 59
def prefixEnd_3844825 : Nat := 4983230072969 + 3 ^ 40 * 3844825 * 2
def baseEnd_3844825 : Nat := 146240241290594432459665

theorem tailTrace_3844825 : CollatzResearch.WordTrace tailWord_3844825 prefixEnd_3844825 146240241290594432459665 := by
  unfold tailWord_3844825
  simp only [CollatzResearch.WordTrace]
  refine ⟨140232288295863143677023929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93488192197242095784682619 140232288295863143677023929)
  ·
    refine ⟨105174216221897357757767947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140232288295863143677023929 105174216221897357757767947)
    ·
      refine ⟨157761324332846036636651921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105174216221897357757767947 157761324332846036636651921)
      ·
        refine ⟨118320993249634527477488941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157761324332846036636651921 118320993249634527477488941)
        ·
          refine ⟨44370372468612947804058353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118320993249634527477488941 44370372468612947804058353)
          ·
            refine ⟨33277779351459710853043765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44370372468612947804058353 33277779351459710853043765)
            ·
              refine ⟨3119791814199347892472853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33277779351459710853043765 3119791814199347892472853)
              ·
                refine ⟨146240241290594432459665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3119791814199347892472853 146240241290594432459665)
                ·
                  rfl

theorem cell22_3844825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 6].length) (baseStart_3844825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844825 prefixEnd_3844825 := by exact prefixLift 3844825
  have htrace : WordTrace (prefixWord ++ tailWord_3844825) baseStart_3844825 baseEnd_3844825 := by
    simpa [prefixWord, tailWord_3844825, baseEnd_3844825] using wordTrace_append hprefix tailTrace_3844825
  have hstable : (prefixWord ++ tailWord_3844825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844825).length < 2 ^ (prefixWord ++ tailWord_3844825).sum := by decide
  have hdescent : baseEnd_3844825 < baseStart_3844825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844964 : List Nat := [2, 3, 1, 1, 4, 1, 1, 4, 2, 3]
def baseStart_3844964 : Nat := 118140960795 + 3844964 * 2 ^ 59
def prefixEnd_3844964 : Nat := 4983230072969 + 3 ^ 40 * 3844964 * 2
def baseEnd_3844964 : Nat := 1316209754155999862911559

theorem tailTrace_3844964 : CollatzResearch.WordTrace tailWord_3844964 prefixEnd_3844964 1316209754155999862911559 := by
  unfold tailWord_3844964
  simp only [CollatzResearch.WordTrace]
  refine ⟨70118679021179785208166973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93491572028239713610889297 70118679021179785208166973)
  ·
    refine ⟨26294504632942419453062615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70118679021179785208166973 26294504632942419453062615)
    ·
      refine ⟨39441756949413629179593923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26294504632942419453062615 39441756949413629179593923)
      ·
        refine ⟨59162635424120443769390885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39441756949413629179593923 59162635424120443769390885)
        ·
          refine ⟨11092994142022583206760791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59162635424120443769390885 11092994142022583206760791)
          ·
            refine ⟨16639491213033874810141187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11092994142022583206760791 16639491213033874810141187)
            ·
              refine ⟨24959236819550812215211781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16639491213033874810141187 24959236819550812215211781)
              ·
                refine ⟨4679856903665777290352209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24959236819550812215211781 4679856903665777290352209)
                ·
                  refine ⟨3509892677749332967764157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4679856903665777290352209 3509892677749332967764157)
                  ·
                    refine ⟨1316209754155999862911559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3509892677749332967764157 1316209754155999862911559)
                    ·
                      rfl

theorem cell22_3844964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_3844964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844964 prefixEnd_3844964 := by exact prefixLift 3844964
  have htrace : WordTrace (prefixWord ++ tailWord_3844964) baseStart_3844964 baseEnd_3844964 := by
    simpa [prefixWord, tailWord_3844964, baseEnd_3844964] using wordTrace_append hprefix tailTrace_3844964
  have hstable : (prefixWord ++ tailWord_3844964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844964).length < 2 ^ (prefixWord ++ tailWord_3844964).sum := by decide
  have hdescent : baseEnd_3844964 < baseStart_3844964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844977 : List Nat := [1, 2, 2, 2, 1, 6, 1, 7]
def baseStart_3844977 : Nat := 118140960795 + 3844977 * 2 ^ 59
def prefixEnd_3844977 : Nat := 4983230072969 + 3 ^ 40 * 3844977 * 2
def baseEnd_3844977 : Nat := 146246022702408018037391

theorem tailTrace_3844977 : CollatzResearch.WordTrace tailWord_3844977 prefixEnd_3844977 146246022702408018037391 := by
  unfold tailWord_3844977
  simp only [CollatzResearch.WordTrace]
  refine ⟨140237832191312473636557185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93491888127541649091038123 140237832191312473636557185)
  ·
    refine ⟨105178374143484355227417889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140237832191312473636557185 105178374143484355227417889)
    ·
      refine ⟨78883780607613266420563417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105178374143484355227417889 78883780607613266420563417)
      ·
        refine ⟨59162835455709949815422563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78883780607613266420563417 59162835455709949815422563)
        ·
          refine ⟨88744253183564924723133845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59162835455709949815422563 88744253183564924723133845)
          ·
            refine ⟨4159886867979605846396899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 88744253183564924723133845 4159886867979605846396899)
            ·
              refine ⟨6239830301969408769595349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4159886867979605846396899 6239830301969408769595349)
              ·
                refine ⟨146246022702408018037391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6239830301969408769595349 146246022702408018037391)
                ·
                  rfl

theorem cell22_3844977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 7].length) (baseStart_3844977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3844977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3844977 prefixEnd_3844977 := by exact prefixLift 3844977
  have htrace : WordTrace (prefixWord ++ tailWord_3844977) baseStart_3844977 baseEnd_3844977 := by
    simpa [prefixWord, tailWord_3844977, baseEnd_3844977] using wordTrace_append hprefix tailTrace_3844977
  have hstable : (prefixWord ++ tailWord_3844977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844977).length < 2 ^ (prefixWord ++ tailWord_3844977).sum := by decide
  have hdescent : baseEnd_3844977 < baseStart_3844977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845026 : List Nat := [3, 3, 1, 2, 2, 2, 2, 1, 3, 3]
def baseStart_3845026 : Nat := 118140960795 + 3845026 * 2 ^ 59
def prefixEnd_3845026 : Nat := 4983230072969 + 3 ^ 40 * 3845026 * 2
def baseEnd_3845026 : Nat := 1316230978023052367861369

theorem tailTrace_3845026 : CollatzResearch.WordTrace tailWord_3845026 prefixEnd_3845026 1316230978023052367861369 := by
  unfold tailWord_3845026
  simp only [CollatzResearch.WordTrace]
  refine ⟨35059904842033738751272733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93493079578756636670060621 35059904842033738751272733)
  ·
    refine ⟨13147464315762652031727275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35059904842033738751272733 13147464315762652031727275)
    ·
      refine ⟨19721196473643978047590913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13147464315762652031727275 19721196473643978047590913)
      ·
        refine ⟨14790897355232983535693185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19721196473643978047590913 14790897355232983535693185)
        ·
          refine ⟨11093173016424737651769889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14790897355232983535693185 11093173016424737651769889)
          ·
            refine ⟨8319879762318553238827417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11093173016424737651769889 8319879762318553238827417)
            ·
              refine ⟨6239909821738914929120563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8319879762318553238827417 6239909821738914929120563)
              ·
                refine ⟨9359864732608372393680845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6239909821738914929120563 9359864732608372393680845)
                ·
                  refine ⟨3509949274728139647630317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9359864732608372393680845 3509949274728139647630317)
                  ·
                    refine ⟨1316230978023052367861369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3509949274728139647630317 1316230978023052367861369)
                    ·
                      rfl

theorem cell22_3845026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_3845026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845026 prefixEnd_3845026 := by exact prefixLift 3845026
  have htrace : WordTrace (prefixWord ++ tailWord_3845026) baseStart_3845026 baseEnd_3845026 := by
    simpa [prefixWord, tailWord_3845026, baseEnd_3845026] using wordTrace_append hprefix tailTrace_3845026
  have hstable : (prefixWord ++ tailWord_3845026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845026).length < 2 ^ (prefixWord ++ tailWord_3845026).sum := by decide
  have hdescent : baseEnd_3845026 < baseStart_3845026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845191 : List Nat := [1, 1, 4, 1, 3, 4, 1, 2, 5]
def baseStart_3845191 : Nat := 118140960795 + 3845191 * 2 ^ 59
def prefixEnd_3845191 : Nat := 4983230072969 + 3 ^ 40 * 3845191 * 2
def baseEnd_3845191 : Nat := 438762486965015645828621

theorem tailTrace_3845191 : CollatzResearch.WordTrace tailWord_3845191 prefixEnd_3845191 438762486965015645828621 := by
  unfold tailWord_3845191
  simp only [CollatzResearch.WordTrace]
  refine ⟨140245637412537188184847427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93497091608358125456564951 140245637412537188184847427)
  ·
    refine ⟨210368456118805782277271141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140245637412537188184847427 210368456118805782277271141)
    ·
      refine ⟨39444085522276084176988339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210368456118805782277271141 39444085522276084176988339)
      ·
        refine ⟨59166128283414126265482509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39444085522276084176988339 59166128283414126265482509)
        ·
          refine ⟨22187298106280297349555941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59166128283414126265482509 22187298106280297349555941)
          ·
            refine ⟨4160118394927555753041739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22187298106280297349555941 4160118394927555753041739)
            ·
              refine ⟨6240177592391333629562609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4160118394927555753041739 6240177592391333629562609)
              ·
                refine ⟨4680133194293500222171957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6240177592391333629562609 4680133194293500222171957)
                ·
                  refine ⟨438762486965015645828621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4680133194293500222171957 438762486965015645828621)
                  ·
                    rfl

theorem cell22_3845191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 5].length) (baseStart_3845191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845191 prefixEnd_3845191 := by exact prefixLift 3845191
  have htrace : WordTrace (prefixWord ++ tailWord_3845191) baseStart_3845191 baseEnd_3845191 := by
    simpa [prefixWord, tailWord_3845191, baseEnd_3845191] using wordTrace_append hprefix tailTrace_3845191
  have hstable : (prefixWord ++ tailWord_3845191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845191).length < 2 ^ (prefixWord ++ tailWord_3845191).sum := by decide
  have hdescent : baseEnd_3845191 < baseStart_3845191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845204 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 5, 4]
def baseStart_3845204 : Nat := 118140960795 + 3845204 * 2 ^ 59
def prefixEnd_3845204 : Nat := 4983230072969 + 3 ^ 40 * 3845204 * 2
def baseEnd_3845204 : Nat := 1316291911060719236910823

theorem tailTrace_3845204 : CollatzResearch.WordTrace tailWord_3845204 prefixEnd_3845204 1316291911060719236910823 := by
  unfold tailWord_3845204
  simp only [CollatzResearch.WordTrace]
  refine ⟨70123055780745045702535333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93497407707660060936713777 70123055780745045702535333)
  ·
    refine ⟨13148072958889696069225375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70123055780745045702535333 13148072958889696069225375)
    ·
      refine ⟨19722109438334544103838063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13148072958889696069225375 19722109438334544103838063)
      ·
        refine ⟨29583164157501816155757095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19722109438334544103838063 29583164157501816155757095)
        ·
          refine ⟨44374746236252724233635643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29583164157501816155757095 44374746236252724233635643)
          ·
            refine ⟨66562119354379086350453465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44374746236252724233635643 66562119354379086350453465)
            ·
              refine ⟨49921589515784314762840099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66562119354379086350453465 49921589515784314762840099)
              ·
                refine ⟨74882384273676472144260149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49921589515784314762840099 74882384273676472144260149)
                ·
                  refine ⟨7020223525657169263524389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74882384273676472144260149 7020223525657169263524389)
                  ·
                    refine ⟨1316291911060719236910823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7020223525657169263524389 1316291911060719236910823)
                    ·
                      rfl

theorem cell22_3845204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_3845204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845204 prefixEnd_3845204 := by exact prefixLift 3845204
  have htrace : WordTrace (prefixWord ++ tailWord_3845204) baseStart_3845204 baseEnd_3845204 := by
    simpa [prefixWord, tailWord_3845204, baseEnd_3845204] using wordTrace_append hprefix tailTrace_3845204
  have hstable : (prefixWord ++ tailWord_3845204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845204).length < 2 ^ (prefixWord ++ tailWord_3845204).sum := by decide
  have hdescent : baseEnd_3845204 < baseStart_3845204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845221 : List Nat := [1, 3, 1, 3, 2, 1, 4, 2, 1, 4]
def baseStart_3845221 : Nat := 118140960795 + 3845221 * 2 ^ 59
def prefixEnd_3845221 : Nat := 4983230072969 + 3 ^ 40 * 3845221 * 2
def baseEnd_3845221 : Nat := 1316297730508136859235771

theorem tailTrace_3845221 : CollatzResearch.WordTrace tailWord_3845221 prefixEnd_3845221 1316297730508136859235771 := by
  unfold tailWord_3845221
  simp only [CollatzResearch.WordTrace]
  refine ⟨140246731602428503308439517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93497821068285668872293011 140246731602428503308439517)
  ·
    refine ⟨52592524350910688740664819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140246731602428503308439517 52592524350910688740664819)
    ·
      refine ⟨78888786526366033110997229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52592524350910688740664819 78888786526366033110997229)
      ·
        refine ⟨29583294947387262416623961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78888786526366033110997229 29583294947387262416623961)
        ·
          refine ⟨22187471210540446812467971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29583294947387262416623961 22187471210540446812467971)
          ·
            refine ⟨33281206815810670218701957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22187471210540446812467971 33281206815810670218701957)
            ·
              refine ⟨6240226277964500666006617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33281206815810670218701957 6240226277964500666006617)
              ·
                refine ⟨4680169708473375499504963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6240226277964500666006617 4680169708473375499504963)
                ·
                  refine ⟨7020254562710063249257445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4680169708473375499504963 7020254562710063249257445)
                  ·
                    refine ⟨1316297730508136859235771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7020254562710063249257445 1316297730508136859235771)
                    ·
                      rfl

theorem cell22_3845221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_3845221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845221 prefixEnd_3845221 := by exact prefixLift 3845221
  have htrace : WordTrace (prefixWord ++ tailWord_3845221) baseStart_3845221 baseEnd_3845221 := by
    simpa [prefixWord, tailWord_3845221, baseEnd_3845221] using wordTrace_append hprefix tailTrace_3845221
  have hstable : (prefixWord ++ tailWord_3845221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845221).length < 2 ^ (prefixWord ++ tailWord_3845221).sum := by decide
  have hdescent : baseEnd_3845221 < baseStart_3845221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845234 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 3, 5]
def baseStart_3845234 : Nat := 118140960795 + 3845234 * 2 ^ 59
def prefixEnd_3845234 : Nat := 4983230072969 + 3 ^ 40 * 3845234 * 2
def baseEnd_3845234 : Nat := 1316302180673809158660731

theorem tailTrace_3845234 : CollatzResearch.WordTrace tailWord_3845234 prefixEnd_3845234 1316302180673809158660731 := by
  unfold tailWord_3845234
  simp only [CollatzResearch.WordTrace]
  refine ⟨35061801437845351632165689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93498137167587604352441837 35061801437845351632165689)
  ·
    refine ⟨26296351078384013724124267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35061801437845351632165689 26296351078384013724124267)
    ·
      refine ⟨39444526617576020586186401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26296351078384013724124267 39444526617576020586186401)
      ·
        refine ⟨29583394963182015439639801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39444526617576020586186401 29583394963182015439639801)
        ·
          refine ⟨22187546222386511579729851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29583394963182015439639801 22187546222386511579729851)
          ·
            refine ⟨33281319333579767369594777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22187546222386511579729851 33281319333579767369594777)
            ·
              refine ⟨24960989500184825527196083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33281319333579767369594777 24960989500184825527196083)
              ·
                refine ⟨37441484250277238290794125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24960989500184825527196083 37441484250277238290794125)
                ·
                  refine ⟨14040556593853964359047797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37441484250277238290794125 14040556593853964359047797)
                  ·
                    refine ⟨1316302180673809158660731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14040556593853964359047797 1316302180673809158660731)
                    ·
                      rfl

theorem cell22_3845234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_3845234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845234 prefixEnd_3845234 := by exact prefixLift 3845234
  have htrace : WordTrace (prefixWord ++ tailWord_3845234) baseStart_3845234 baseEnd_3845234 := by
    simpa [prefixWord, tailWord_3845234, baseEnd_3845234] using wordTrace_append hprefix tailTrace_3845234
  have hstable : (prefixWord ++ tailWord_3845234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845234).length < 2 ^ (prefixWord ++ tailWord_3845234).sum := by decide
  have hdescent : baseEnd_3845234 < baseStart_3845234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845246 : List Nat := [4, 2, 4, 1, 1, 1, 3, 2, 1, 3]
def baseStart_3845246 : Nat := 118140960795 + 3845246 * 2 ^ 59
def prefixEnd_3845246 : Nat := 4983230072969 + 3 ^ 40 * 3845246 * 2
def baseEnd_3845246 : Nat := 1316306288519045127360695

theorem tailTrace_3845246 : CollatzResearch.WordTrace tailWord_3845246 prefixEnd_3845246 1316306288519045127360695 := by
  unfold tailWord_3845246
  simp only [CollatzResearch.WordTrace]
  refine ⟨17530955428417241572262449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93498428951558621718733061 17530955428417241572262449)
  ·
    refine ⟨13148216571312931179196837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17530955428417241572262449 13148216571312931179196837)
    ·
      refine ⟨2465290607121174596099407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13148216571312931179196837 2465290607121174596099407)
      ·
        refine ⟨3697935910681761894149111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2465290607121174596099407 3697935910681761894149111)
        ·
          refine ⟨5546903866022642841223667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3697935910681761894149111 5546903866022642841223667)
          ·
            refine ⟨8320355799033964261835501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5546903866022642841223667 8320355799033964261835501)
            ·
              refine ⟨3120133424637736598188313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8320355799033964261835501 3120133424637736598188313)
              ·
                refine ⟨2340100068478302448641235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3120133424637736598188313 2340100068478302448641235)
                ·
                  refine ⟨3510150102717453672961853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2340100068478302448641235 3510150102717453672961853)
                  ·
                    refine ⟨1316306288519045127360695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3510150102717453672961853 1316306288519045127360695)
                    ·
                      rfl

theorem cell22_3845246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_3845246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845246 prefixEnd_3845246 := by exact prefixLift 3845246
  have htrace : WordTrace (prefixWord ++ tailWord_3845246) baseStart_3845246 baseEnd_3845246 := by
    simpa [prefixWord, tailWord_3845246, baseEnd_3845246] using wordTrace_append hprefix tailTrace_3845246
  have hstable : (prefixWord ++ tailWord_3845246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845246).length < 2 ^ (prefixWord ++ tailWord_3845246).sum := by decide
  have hdescent : baseEnd_3845246 < baseStart_3845246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845251 : List Nat := [1, 1, 1, 3, 3, 2, 2, 4, 2, 3]
def baseStart_3845251 : Nat := 118140960795 + 3845251 * 2 ^ 59
def prefixEnd_3845251 : Nat := 4983230072969 + 3 ^ 40 * 3845251 * 2
def baseEnd_3845251 : Nat := 1316308000121226780985679

theorem tailTrace_3845251 : CollatzResearch.WordTrace tailWord_3845251 prefixEnd_3845251 1316308000121226780985679 := by
  unfold tailWord_3845251
  simp only [CollatzResearch.WordTrace]
  refine ⟨140247825792319818432031607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93498550528213212288021071 140247825792319818432031607)
  ·
    refine ⟨210371738688479727648047411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140247825792319818432031607 210371738688479727648047411)
    ·
      refine ⟨315557608032719591472071117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210371738688479727648047411 315557608032719591472071117)
      ·
        refine ⟨118334103012269846802026669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315557608032719591472071117 118334103012269846802026669)
        ·
          refine ⟨44375288629601192550760001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118334103012269846802026669 44375288629601192550760001)
          ·
            refine ⟨33281466472200894413070001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44375288629601192550760001 33281466472200894413070001)
            ·
              refine ⟨24961099854150670809802501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33281466472200894413070001 24961099854150670809802501)
              ·
                refine ⟨4680206222653250776837969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24961099854150670809802501 4680206222653250776837969)
                ·
                  refine ⟨3510154666989938082628477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4680206222653250776837969 3510154666989938082628477)
                  ·
                    refine ⟨1316308000121226780985679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3510154666989938082628477 1316308000121226780985679)
                    ·
                      rfl

theorem cell22_3845251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 2, 3].length) (baseStart_3845251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845251 prefixEnd_3845251 := by exact prefixLift 3845251
  have htrace : WordTrace (prefixWord ++ tailWord_3845251) baseStart_3845251 baseEnd_3845251 := by
    simpa [prefixWord, tailWord_3845251, baseEnd_3845251] using wordTrace_append hprefix tailTrace_3845251
  have hstable : (prefixWord ++ tailWord_3845251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845251).length < 2 ^ (prefixWord ++ tailWord_3845251).sum := by decide
  have hdescent : baseEnd_3845251 < baseStart_3845251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845253 : List Nat := [1, 3, 1, 1, 7, 1, 1, 1, 6]
def baseStart_3845253 : Nat := 118140960795 + 3845253 * 2 ^ 59
def prefixEnd_3845253 : Nat := 4983230072969 + 3 ^ 40 * 3845253 * 2
def baseEnd_3845253 : Nat := 438769561587366480811891

theorem tailTrace_3845253 : CollatzResearch.WordTrace tailWord_3845253 prefixEnd_3845253 438769561587366480811891 := by
  unfold tailWord_3845253
  simp only [CollatzResearch.WordTrace]
  refine ⟨140247898738312572773604413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93498599158875048515736275 140247898738312572773604413)
  ·
    refine ⟨52592962026867214790101655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140247898738312572773604413 52592962026867214790101655)
    ·
      refine ⟨78889443040300822185152483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52592962026867214790101655 78889443040300822185152483)
      ·
        refine ⟨118334164560451233277728725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78889443040300822185152483 118334164560451233277728725)
        ·
          refine ⟨2773456981885575779946767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 118334164560451233277728725 2773456981885575779946767)
          ·
            refine ⟨4160185472828363669920151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2773456981885575779946767 4160185472828363669920151)
            ·
              refine ⟨6240278209242545504880227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4160185472828363669920151 6240278209242545504880227)
              ·
                refine ⟨9360417313863818257320341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6240278209242545504880227 9360417313863818257320341)
                ·
                  refine ⟨438769561587366480811891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9360417313863818257320341 438769561587366480811891)
                  ·
                    rfl

theorem cell22_3845253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 6].length) (baseStart_3845253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845253 prefixEnd_3845253 := by exact prefixLift 3845253
  have htrace : WordTrace (prefixWord ++ tailWord_3845253) baseStart_3845253 baseEnd_3845253 := by
    simpa [prefixWord, tailWord_3845253, baseEnd_3845253] using wordTrace_append hprefix tailTrace_3845253
  have hstable : (prefixWord ++ tailWord_3845253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845253).length < 2 ^ (prefixWord ++ tailWord_3845253).sum := by decide
  have hdescent : baseEnd_3845253 < baseStart_3845253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845309 : List Nat := [1, 4, 1, 2, 1, 1, 2, 3, 7]
def baseStart_3845309 : Nat := 118140960795 + 3845309 * 2 ^ 59
def prefixEnd_3845309 : Nat := 4983230072969 + 3 ^ 40 * 3845309 * 2
def baseEnd_3845309 : Nat := 438775951568844654345167

theorem tailTrace_3845309 : CollatzResearch.WordTrace tailWord_3845309 prefixEnd_3845309 438775951568844654345167 := by
  unfold tailWord_3845309
  simp only [CollatzResearch.WordTrace]
  refine ⟨140249941226109694337642981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93499960817406462891761987 140249941226109694337642981)
  ·
    refine ⟨26296863979895567688308059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140249941226109694337642981 26296863979895567688308059)
    ·
      refine ⟨39445295969843351532462089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26296863979895567688308059 39445295969843351532462089)
      ·
        refine ⟨29583971977382513649346567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39445295969843351532462089 29583971977382513649346567)
        ·
          refine ⟨44375957966073770474019851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29583971977382513649346567 44375957966073770474019851)
          ·
            refine ⟨66563936949110655711029777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44375957966073770474019851 66563936949110655711029777)
            ·
              refine ⟨49922952711832991783272333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66563936949110655711029777 49922952711832991783272333)
              ·
                refine ⟨18721107266937371918727125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49922952711832991783272333 18721107266937371918727125)
                ·
                  refine ⟨438775951568844654345167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18721107266937371918727125 438775951568844654345167)
                  ·
                    rfl

theorem cell22_3845309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_3845309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845309 prefixEnd_3845309 := by exact prefixLift 3845309
  have htrace : WordTrace (prefixWord ++ tailWord_3845309) baseStart_3845309 baseEnd_3845309 := by
    simpa [prefixWord, tailWord_3845309, baseEnd_3845309] using wordTrace_append hprefix tailTrace_3845309
  have hstable : (prefixWord ++ tailWord_3845309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845309).length < 2 ^ (prefixWord ++ tailWord_3845309).sum := by decide
  have hdescent : baseEnd_3845309 < baseStart_3845309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845339 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 7, 4]
def baseStart_3845339 : Nat := 118140960795 + 3845339 * 2 ^ 59
def prefixEnd_3845339 : Nat := 4983230072969 + 3 ^ 40 * 3845339 * 2
def baseEnd_3845339 : Nat := 1316338124319623884785409

theorem tailTrace_3845339 : CollatzResearch.WordTrace tailWord_3845339 prefixEnd_3845339 1316338124319623884785409 := by
  unfold tailWord_3845339
  simp only [CollatzResearch.WordTrace]
  refine ⟨140251035416001009461235071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93500690277334006307490047 140251035416001009461235071)
  ·
    refine ⟨210376553124001514191852607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140251035416001009461235071 210376553124001514191852607)
    ·
      refine ⟨315564829686002271287778911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210376553124001514191852607 315564829686002271287778911)
      ·
        refine ⟨473347244529003406931668367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315564829686002271287778911 473347244529003406931668367)
        ·
          refine ⟨710020866793505110397502551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473347244529003406931668367 710020866793505110397502551)
          ·
            refine ⟨1065031300190257665596253827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710020866793505110397502551 1065031300190257665596253827)
            ·
              refine ⟨1597546950285386498394380741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1065031300190257665596253827 1597546950285386498394380741)
              ·
                refine ⟨299540053178509968448946389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1597546950285386498394380741 299540053178509968448946389)
                ·
                  refine ⟨7020469996371327385522181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 299540053178509968448946389 7020469996371327385522181)
                  ·
                    refine ⟨1316338124319623884785409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7020469996371327385522181 1316338124319623884785409)
                    ·
                      rfl

theorem cell22_3845339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 4].length) (baseStart_3845339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845339 prefixEnd_3845339 := by exact prefixLift 3845339
  have htrace : WordTrace (prefixWord ++ tailWord_3845339) baseStart_3845339 baseEnd_3845339 := by
    simpa [prefixWord, tailWord_3845339, baseEnd_3845339] using wordTrace_append hprefix tailTrace_3845339
  have hstable : (prefixWord ++ tailWord_3845339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845339).length < 2 ^ (prefixWord ++ tailWord_3845339).sum := by decide
  have hdescent : baseEnd_3845339 < baseStart_3845339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845364 : List Nat := [2, 6, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_3845364 : Nat := 118140960795 + 3845364 * 2 ^ 59
def prefixEnd_3845364 : Nat := 4983230072969 + 3 ^ 40 * 3845364 * 2
def baseEnd_3845364 : Nat := 1316346682330532152910333

theorem tailTrace_3845364 : CollatzResearch.WordTrace tailWord_3845364 prefixEnd_3845364 1316346682330532152910333 := by
  unfold tailWord_3845364
  simp only [CollatzResearch.WordTrace]
  refine ⟨70125973620455219365447573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93501298160606959153930097 70125973620455219365447573)
  ·
    refine ⟨3287155013458838407755355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70125973620455219365447573 3287155013458838407755355)
    ·
      refine ⟨4930732520188257611633033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3287155013458838407755355 4930732520188257611633033)
      ·
        refine ⟨3698049390141193208724775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4930732520188257611633033 3698049390141193208724775)
        ·
          refine ⟨5547074085211789813087163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3698049390141193208724775 5547074085211789813087163)
          ·
            refine ⟨8320611127817684719630745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5547074085211789813087163 8320611127817684719630745)
            ·
              refine ⟨6240458345863263539723059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8320611127817684719630745 6240458345863263539723059)
              ·
                refine ⟨9360687518794895309584589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6240458345863263539723059 9360687518794895309584589)
                ·
                  refine ⟨3510257819548085741094221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9360687518794895309584589 3510257819548085741094221)
                  ·
                    refine ⟨1316346682330532152910333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3510257819548085741094221 1316346682330532152910333)
                    ·
                      rfl

theorem cell22_3845364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_3845364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845364 prefixEnd_3845364 := by exact prefixLift 3845364
  have htrace : WordTrace (prefixWord ++ tailWord_3845364) baseStart_3845364 baseEnd_3845364 := by
    simpa [prefixWord, tailWord_3845364, baseEnd_3845364] using wordTrace_append hprefix tailTrace_3845364
  have hstable : (prefixWord ++ tailWord_3845364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845364).length < 2 ^ (prefixWord ++ tailWord_3845364).sum := by decide
  have hdescent : baseEnd_3845364 < baseStart_3845364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845405 : List Nat := [1, 4, 2, 3, 1, 1, 3, 3, 4]
def baseStart_3845405 : Nat := 118140960795 + 3845405 * 2 ^ 59
def prefixEnd_3845405 : Nat := 4983230072969 + 3 ^ 40 * 3845405 * 2
def baseEnd_3845405 : Nat := 438786905822807237545069

theorem tailTrace_3845405 : CollatzResearch.WordTrace tailWord_3845405 prefixEnd_3845405 438786905822807237545069 := by
  unfold tailWord_3845405
  simp only [CollatzResearch.WordTrace]
  refine ⟨140253442633761902733137669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93502295089174601822091779 140253442633761902733137669)
  ·
    refine ⟨26297520493830356762463313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140253442633761902733137669 26297520493830356762463313)
    ·
      refine ⟨19723140370372767571847485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26297520493830356762463313 19723140370372767571847485)
      ·
        refine ⟨7396177638889787839442807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19723140370372767571847485 7396177638889787839442807)
        ·
          refine ⟨11094266458334681759164211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7396177638889787839442807 11094266458334681759164211)
          ·
            refine ⟨16641399687502022638746317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11094266458334681759164211 16641399687502022638746317)
            ·
              refine ⟨6240524882813258489529869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16641399687502022638746317 6240524882813258489529869)
              ·
                refine ⟨2340196831054971933573701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6240524882813258489529869 2340196831054971933573701)
                ·
                  refine ⟨438786905822807237545069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2340196831054971933573701 438786905822807237545069)
                  ·
                    rfl

theorem cell22_3845405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_3845405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845405 prefixEnd_3845405 := by exact prefixLift 3845405
  have htrace : WordTrace (prefixWord ++ tailWord_3845405) baseStart_3845405 baseEnd_3845405 := by
    simpa [prefixWord, tailWord_3845405, baseEnd_3845405] using wordTrace_append hprefix tailTrace_3845405
  have hstable : (prefixWord ++ tailWord_3845405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845405).length < 2 ^ (prefixWord ++ tailWord_3845405).sum := by decide
  have hdescent : baseEnd_3845405 < baseStart_3845405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845416 : List Nat := [2, 1, 5, 1, 2, 1, 10]
def baseStart_3845416 : Nat := 118140960795 + 3845416 * 2 ^ 59
def prefixEnd_3845416 : Nat := 4983230072969 + 3 ^ 40 * 3845416 * 2
def baseEnd_3845416 : Nat := 48754240110860050022599

theorem tailTrace_3845416 : CollatzResearch.WordTrace tailWord_3845416 prefixEnd_3845416 48754240110860050022599 := by
  unfold tailWord_3845416
  simp only [CollatzResearch.WordTrace]
  refine ⟨70126921918361025805894051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93502562557814701074525401 70126921918361025805894051)
  ·
    refine ⟨105190382877541538708841077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70126921918361025805894051 105190382877541538708841077)
    ·
      refine ⟨9861598394769519253953851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105190382877541538708841077 9861598394769519253953851)
      ·
        refine ⟨14792397592154278880930777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9861598394769519253953851 14792397592154278880930777)
        ·
          refine ⟨11094298194115709160698083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14792397592154278880930777 11094298194115709160698083)
          ·
            refine ⟨16641447291173563741047125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11094298194115709160698083 16641447291173563741047125)
            ·
              refine ⟨48754240110860050022599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16641447291173563741047125 48754240110860050022599)
              ·
                rfl

theorem cell22_3845416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 10].length) (baseStart_3845416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845416 prefixEnd_3845416 := by exact prefixLift 3845416
  have htrace : WordTrace (prefixWord ++ tailWord_3845416) baseStart_3845416 baseEnd_3845416 := by
    simpa [prefixWord, tailWord_3845416, baseEnd_3845416] using wordTrace_append hprefix tailTrace_3845416
  have hstable : (prefixWord ++ tailWord_3845416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845416).length < 2 ^ (prefixWord ++ tailWord_3845416).sum := by decide
  have hdescent : baseEnd_3845416 < baseStart_3845416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845418 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 4, 4]
def baseStart_3845418 : Nat := 118140960795 + 3845418 * 2 ^ 59
def prefixEnd_3845418 : Nat := 4983230072969 + 3 ^ 40 * 3845418 * 2
def baseEnd_3845418 : Nat := 1316365167634094012060167

theorem tailTrace_3845418 : CollatzResearch.WordTrace tailWord_3845418 prefixEnd_3845418 1316365167634094012060167 := by
  unfold tailWord_3845418
  simp only [CollatzResearch.WordTrace]
  refine ⟨35063479195678701488340227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93502611188476537302240605 35063479195678701488340227)
  ·
    refine ⟨52595218793518052232510341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35063479195678701488340227 52595218793518052232510341)
    ·
      refine ⟨9861603523784634793595689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52595218793518052232510341 9861603523784634793595689)
      ·
        refine ⟨7396202642838476095196767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9861603523784634793595689 7396202642838476095196767)
        ·
          refine ⟨11094303964257714142795151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7396202642838476095196767 11094303964257714142795151)
          ·
            refine ⟨16641455946386571214192727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11094303964257714142795151 16641455946386571214192727)
            ·
              refine ⟨24962183919579856821289091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16641455946386571214192727 24962183919579856821289091)
              ·
                refine ⟨37443275879369785231933637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24962183919579856821289091 37443275879369785231933637)
                ·
                  refine ⟨7020614227381834730987557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37443275879369785231933637 7020614227381834730987557)
                  ·
                    refine ⟨1316365167634094012060167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7020614227381834730987557 1316365167634094012060167)
                    ·
                      rfl

theorem cell22_3845418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_3845418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845418 prefixEnd_3845418 := by exact prefixLift 3845418
  have htrace : WordTrace (prefixWord ++ tailWord_3845418) baseStart_3845418 baseEnd_3845418 := by
    simpa [prefixWord, tailWord_3845418, baseEnd_3845418] using wordTrace_append hprefix tailTrace_3845418
  have hstable : (prefixWord ++ tailWord_3845418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845418).length < 2 ^ (prefixWord ++ tailWord_3845418).sum := by decide
  have hdescent : baseEnd_3845418 < baseStart_3845418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845433 : List Nat := [1, 2, 1, 6, 2, 1, 2, 7]
def baseStart_3845433 : Nat := 118140960795 + 3845433 * 2 ^ 59
def prefixEnd_3845433 : Nat := 4983230072969 + 3 ^ 40 * 3845433 * 2
def baseEnd_3845433 : Nat := 146263366937848774770569

theorem tailTrace_3845433 : CollatzResearch.WordTrace tailWord_3845433 prefixEnd_3845433 146263366937848774770569 := by
  unfold tailWord_3845433
  simp only [CollatzResearch.WordTrace]
  refine ⟨140254463877660463515156953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93502975918440309010104635 140254463877660463515156953)
  ·
    refine ⟨105190847908245347636367715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140254463877660463515156953 105190847908245347636367715)
    ·
      refine ⟨157786271862368021454551573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105190847908245347636367715 157786271862368021454551573)
      ·
        refine ⟨7396231493548501005682105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 157786271862368021454551573 7396231493548501005682105)
        ·
          refine ⟨5547173620161375754261579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7396231493548501005682105 5547173620161375754261579)
          ·
            refine ⟨8320760430242063631392369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5547173620161375754261579 8320760430242063631392369)
            ·
              refine ⟨6240570322681547723544277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8320760430242063631392369 6240570322681547723544277)
              ·
                refine ⟨146263366937848774770569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6240570322681547723544277 146263366937848774770569)
                ·
                  rfl

theorem cell22_3845433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 7].length) (baseStart_3845433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845433 prefixEnd_3845433 := by exact prefixLift 3845433
  have htrace : WordTrace (prefixWord ++ tailWord_3845433) baseStart_3845433 baseEnd_3845433 := by
    simpa [prefixWord, tailWord_3845433, baseEnd_3845433] using wordTrace_append hprefix tailTrace_3845433
  have hstable : (prefixWord ++ tailWord_3845433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845433).length < 2 ^ (prefixWord ++ tailWord_3845433).sum := by decide
  have hdescent : baseEnd_3845433 < baseStart_3845433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845437 : List Nat := [1, 4, 1, 5, 1, 1, 1, 3, 2, 3]
def baseStart_3845437 : Nat := 118140960795 + 3845437 * 2 ^ 59
def prefixEnd_3845437 : Nat := 4983230072969 + 3 ^ 40 * 3845437 * 2
def baseEnd_3845437 : Nat := 1316371671722384295835109

theorem tailTrace_3845437 : CollatzResearch.WordTrace tailWord_3845437 prefixEnd_3845437 1316371671722384295835109 := by
  unfold tailWord_3845437
  simp only [CollatzResearch.WordTrace]
  refine ⟨140254609769645972198302565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93503073179763981465535043 140254609769645972198302565)
  ·
    refine ⟨26297739331808619787181731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140254609769645972198302565 26297739331808619787181731)
    ·
      refine ⟨39446608997712929680772597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26297739331808619787181731 39446608997712929680772597)
      ·
        refine ⟨3698119593535587157572431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39446608997712929680772597 3698119593535587157572431)
        ·
          refine ⟨5547179390303380736358647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3698119593535587157572431 5547179390303380736358647)
          ·
            refine ⟨8320769085455071104537971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5547179390303380736358647 8320769085455071104537971)
            ·
              refine ⟨12481153628182606656806957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8320769085455071104537971 12481153628182606656806957)
              ·
                refine ⟨4680432610568477496302609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12481153628182606656806957 4680432610568477496302609)
                ·
                  refine ⟨3510324457926358122226957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4680432610568477496302609 3510324457926358122226957)
                  ·
                    refine ⟨1316371671722384295835109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3510324457926358122226957 1316371671722384295835109)
                    ·
                      rfl

theorem cell22_3845437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_3845437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845437 prefixEnd_3845437 := by exact prefixLift 3845437
  have htrace : WordTrace (prefixWord ++ tailWord_3845437) baseStart_3845437 baseEnd_3845437 := by
    simpa [prefixWord, tailWord_3845437, baseEnd_3845437] using wordTrace_append hprefix tailTrace_3845437
  have hstable : (prefixWord ++ tailWord_3845437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845437).length < 2 ^ (prefixWord ++ tailWord_3845437).sum := by decide
  have hdescent : baseEnd_3845437 < baseStart_3845437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845508 : List Nat := [2, 3, 2, 1, 1, 3, 2, 1, 3, 4]
def baseStart_3845508 : Nat := 118140960795 + 3845508 * 2 ^ 59
def prefixEnd_3845508 : Nat := 4983230072969 + 3 ^ 40 * 3845508 * 2
def baseEnd_3845508 : Nat := 1316395976473363777309891

theorem tailTrace_3845508 : CollatzResearch.WordTrace tailWord_3845508 prefixEnd_3845508 1316395976473363777309891 := by
  unfold tailWord_3845508
  simp only [CollatzResearch.WordTrace]
  refine ⟨70128599676194375662068589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93504799568259167549424785 70128599676194375662068589)
  ·
    refine ⟨26298224878572890873275721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70128599676194375662068589 26298224878572890873275721)
    ·
      refine ⟨19723668658929668154956791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26298224878572890873275721 19723668658929668154956791)
      ·
        refine ⟨29585502988394502232435187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19723668658929668154956791 29585502988394502232435187)
        ·
          refine ⟨44378254482591753348652781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29585502988394502232435187 44378254482591753348652781)
          ·
            refine ⟨16641845430971907505744793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44378254482591753348652781 16641845430971907505744793)
            ·
              refine ⟨12481384073228930629308595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16641845430971907505744793 12481384073228930629308595)
              ·
                refine ⟨18722076109843395943962893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12481384073228930629308595 18722076109843395943962893)
                ·
                  refine ⟨7020778541191273478986085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18722076109843395943962893 7020778541191273478986085)
                  ·
                    refine ⟨1316395976473363777309891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7020778541191273478986085 1316395976473363777309891)
                    ·
                      rfl

theorem cell22_3845508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_3845508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845508 prefixEnd_3845508 := by exact prefixLift 3845508
  have htrace : WordTrace (prefixWord ++ tailWord_3845508) baseStart_3845508 baseEnd_3845508 := by
    simpa [prefixWord, tailWord_3845508, baseEnd_3845508] using wordTrace_append hprefix tailTrace_3845508
  have hstable : (prefixWord ++ tailWord_3845508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845508).length < 2 ^ (prefixWord ++ tailWord_3845508).sum := by decide
  have hdescent : baseEnd_3845508 < baseStart_3845508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845525 : List Nat := [1, 3, 2, 1, 1, 2, 6, 1, 1, 4]
def baseStart_3845525 : Nat := 118140960795 + 3845525 * 2 ^ 59
def prefixEnd_3845525 : Nat := 4983230072969 + 3 ^ 40 * 3845525 * 2
def baseEnd_3845525 : Nat := 1316401795920781399634839

theorem tailTrace_3845525 : CollatzResearch.WordTrace tailWord_3845525 prefixEnd_3845525 1316401795920781399634839 := by
  unfold tailWord_3845525
  simp only [CollatzResearch.WordTrace]
  refine ⟨140257819393327163227506029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93505212928884775485004019 140257819393327163227506029)
  ·
    refine ⟨52596682272497686210314761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140257819393327163227506029 52596682272497686210314761)
    ·
      refine ⟨39447511704373264657736071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52596682272497686210314761 39447511704373264657736071)
      ·
        refine ⟨59171267556559896986604107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39447511704373264657736071 59171267556559896986604107)
        ·
          refine ⟨88756901334839845479906161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59171267556559896986604107 88756901334839845479906161)
          ·
            refine ⟨66567676001129884109929621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88756901334839845479906161 66567676001129884109929621)
            ·
              refine ⟨3120359812552963317652951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66567676001129884109929621 3120359812552963317652951)
              ·
                refine ⟨4680539718829444976479427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3120359812552963317652951 4680539718829444976479427)
                ·
                  refine ⟨7020809578244167464719141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4680539718829444976479427 7020809578244167464719141)
                  ·
                    refine ⟨1316401795920781399634839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7020809578244167464719141 1316401795920781399634839)
                    ·
                      rfl

theorem cell22_3845525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_3845525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845525 prefixEnd_3845525 := by exact prefixLift 3845525
  have htrace : WordTrace (prefixWord ++ tailWord_3845525) baseStart_3845525 baseEnd_3845525 := by
    simpa [prefixWord, tailWord_3845525, baseEnd_3845525] using wordTrace_append hprefix tailTrace_3845525
  have hstable : (prefixWord ++ tailWord_3845525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845525).length < 2 ^ (prefixWord ++ tailWord_3845525).sum := by decide
  have hdescent : baseEnd_3845525 < baseStart_3845525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845568 : List Nat := [2, 1, 1, 2, 3, 1, 6, 6]
def baseStart_3845568 : Nat := 118140960795 + 3845568 * 2 ^ 59
def prefixEnd_3845568 : Nat := 4983230072969 + 3 ^ 40 * 3845568 * 2
def baseEnd_3845568 : Nat := 146268501744393735645523

theorem tailTrace_3845568 : CollatzResearch.WordTrace tailWord_3845568 prefixEnd_3845568 146268501744393735645523 := by
  unfold tailWord_3845568
  simp only [CollatzResearch.WordTrace]
  refine ⟨70129693866085690785660679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93506258488114254380880905 70129693866085690785660679)
  ·
    refine ⟨105194540799128536178491019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70129693866085690785660679 105194540799128536178491019)
    ·
      refine ⟨157791811198692804267736529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105194540799128536178491019 157791811198692804267736529)
      ·
        refine ⟨118343858399019603200802397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157791811198692804267736529 118343858399019603200802397)
        ·
          refine ⟨44378946899632351200300899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118343858399019603200802397 44378946899632351200300899)
          ·
            refine ⟨66568420349448526800451349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44378946899632351200300899 66568420349448526800451349)
            ·
              refine ⟨3120394703880399693771157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66568420349448526800451349 3120394703880399693771157)
              ·
                refine ⟨146268501744393735645523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3120394703880399693771157 146268501744393735645523)
                ·
                  rfl

theorem cell22_3845568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 6].length) (baseStart_3845568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845568 prefixEnd_3845568 := by exact prefixLift 3845568
  have htrace : WordTrace (prefixWord ++ tailWord_3845568) baseStart_3845568 baseEnd_3845568 := by
    simpa [prefixWord, tailWord_3845568, baseEnd_3845568] using wordTrace_append hprefix tailTrace_3845568
  have hstable : (prefixWord ++ tailWord_3845568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845568).length < 2 ^ (prefixWord ++ tailWord_3845568).sum := by decide
  have hdescent : baseEnd_3845568 < baseStart_3845568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845583 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 5, 3]
def baseStart_3845583 : Nat := 118140960795 + 3845583 * 2 ^ 59
def prefixEnd_3845583 : Nat := 4983230072969 + 3 ^ 40 * 3845583 * 2
def baseEnd_3845583 : Nat := 1316421650506088581684661

theorem tailTrace_3845583 : CollatzResearch.WordTrace tailWord_3845583 prefixEnd_3845583 1316421650506088581684661 := by
  unfold tailWord_3845583
  simp only [CollatzResearch.WordTrace]
  refine ⟨140259934827117039133117403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93506623218078026088744935 140259934827117039133117403)
  ·
    refine ⟨210389902240675558699676105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140259934827117039133117403 210389902240675558699676105)
    ·
      refine ⟨157792426680506669024757079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210389902240675558699676105 157792426680506669024757079)
      ·
        refine ⟨236688640020760003537135619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157792426680506669024757079 236688640020760003537135619)
        ·
          refine ⟨355032960031140005305703429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236688640020760003537135619 355032960031140005305703429)
          ·
            refine ⟨66568680005838750994819393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 355032960031140005305703429 66568680005838750994819393)
            ·
              refine ⟨49926510004379063246114545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66568680005838750994819393 49926510004379063246114545)
              ·
                refine ⟨37444882503284297434585909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49926510004379063246114545 37444882503284297434585909)
                ·
                  refine ⟨3510457734682902884492429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37444882503284297434585909 3510457734682902884492429)
                  ·
                    refine ⟨1316421650506088581684661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3510457734682902884492429 1316421650506088581684661)
                    ·
                      rfl

theorem cell22_3845583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 5, 3].length) (baseStart_3845583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845583 prefixEnd_3845583 := by exact prefixLift 3845583
  have htrace : WordTrace (prefixWord ++ tailWord_3845583) baseStart_3845583 baseEnd_3845583 := by
    simpa [prefixWord, tailWord_3845583, baseEnd_3845583] using wordTrace_append hprefix tailTrace_3845583
  have hstable : (prefixWord ++ tailWord_3845583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845583).length < 2 ^ (prefixWord ++ tailWord_3845583).sum := by decide
  have hdescent : baseEnd_3845583 < baseStart_3845583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845658 : List Nat := [3, 1, 1, 3, 1, 1, 1, 5, 6]
def baseStart_3845658 : Nat := 118140960795 + 3845658 * 2 ^ 59
def prefixEnd_3845658 : Nat := 4983230072969 + 3 ^ 40 * 3845658 * 2
def baseEnd_3845658 : Nat := 438815774846271128686477

theorem tailTrace_3845658 : CollatzResearch.WordTrace tailWord_3845658 prefixEnd_3845658 438815774846271128686477 := by
  unfold tailWord_3845658
  simp only [CollatzResearch.WordTrace]
  refine ⟨35065667575461331735524407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93508446867896884628065085 35065667575461331735524407)
  ·
    refine ⟨52598501363191997603286611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35065667575461331735524407 52598501363191997603286611)
    ·
      refine ⟨78897752044787996404929917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52598501363191997603286611 78897752044787996404929917)
      ·
        refine ⟨29586657016795498651848719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78897752044787996404929917 29586657016795498651848719)
        ·
          refine ⟨44379985525193247977773079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29586657016795498651848719 44379985525193247977773079)
          ·
            refine ⟨66569978287789871966659619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44379985525193247977773079 66569978287789871966659619)
            ·
              refine ⟨99854967431684807949989429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66569978287789871966659619 99854967431684807949989429)
              ·
                refine ⟨9361403196720450745311509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99854967431684807949989429 9361403196720450745311509)
                ·
                  refine ⟨438815774846271128686477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9361403196720450745311509 438815774846271128686477)
                  ·
                    rfl

theorem cell22_3845658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 6].length) (baseStart_3845658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845658 prefixEnd_3845658 := by exact prefixLift 3845658
  have htrace : WordTrace (prefixWord ++ tailWord_3845658) baseStart_3845658 baseEnd_3845658 := by
    simpa [prefixWord, tailWord_3845658, baseEnd_3845658] using wordTrace_append hprefix tailTrace_3845658
  have hstable : (prefixWord ++ tailWord_3845658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845658).length < 2 ^ (prefixWord ++ tailWord_3845658).sum := by decide
  have hdescent : baseEnd_3845658 < baseStart_3845658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845690 : List Nat := [3, 1, 1, 1, 3, 2, 2, 2, 4, 3]
def baseStart_3845690 : Nat := 118140960795 + 3845690 * 2 ^ 59
def prefixEnd_3845690 : Nat := 4983230072969 + 3 ^ 40 * 3845690 * 2
def baseEnd_3845690 : Nat := 1316458278792775969259333

theorem tailTrace_3845690 : CollatzResearch.WordTrace tailWord_3845690 prefixEnd_3845690 1316458278792775969259333 := by
  unfold tailWord_3845690
  simp only [CollatzResearch.WordTrace]
  refine ⟨35065959359432349101815631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93509224958486264271508349 35065959359432349101815631)
  ·
    refine ⟨52598939039148523652723447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35065959359432349101815631 52598939039148523652723447)
    ·
      refine ⟨78898408558722785479085171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52598939039148523652723447 78898408558722785479085171)
      ·
        refine ⟨118347612838084178218627757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78898408558722785479085171 118347612838084178218627757)
        ·
          refine ⟨44380354814281566831985409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118347612838084178218627757 44380354814281566831985409)
          ·
            refine ⟨33285266110711175123989057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44380354814281566831985409 33285266110711175123989057)
            ·
              refine ⟨24963949583033381342991793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33285266110711175123989057 24963949583033381342991793)
              ·
                refine ⟨18722962187275036007243845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24963949583033381342991793 18722962187275036007243845)
                ·
                  refine ⟨3510555410114069251358221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18722962187275036007243845 3510555410114069251358221)
                  ·
                    refine ⟨1316458278792775969259333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3510555410114069251358221 1316458278792775969259333)
                    ·
                      rfl

theorem cell22_3845690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 4, 3].length) (baseStart_3845690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845690 prefixEnd_3845690 := by exact prefixLift 3845690
  have htrace : WordTrace (prefixWord ++ tailWord_3845690) baseStart_3845690 baseEnd_3845690 := by
    simpa [prefixWord, tailWord_3845690, baseEnd_3845690] using wordTrace_append hprefix tailTrace_3845690
  have hstable : (prefixWord ++ tailWord_3845690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845690).length < 2 ^ (prefixWord ++ tailWord_3845690).sum := by decide
  have hdescent : baseEnd_3845690 < baseStart_3845690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845765 : List Nat := [1, 3, 1, 1, 4, 1, 2, 4, 5]
def baseStart_3845765 : Nat := 118140960795 + 3845765 * 2 ^ 59
def prefixEnd_3845765 : Nat := 4983230072969 + 3 ^ 40 * 3845765 * 2
def baseEnd_3845765 : Nat := 438827984275166924544701

theorem tailTrace_3845765 : CollatzResearch.WordTrace tailWord_3845765 prefixEnd_3845765 438827984275166924544701 := by
  unfold tailWord_3845765
  simp only [CollatzResearch.WordTrace]
  refine ⟨140266572912457684216242749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93511048608305122810828499 140266572912457684216242749)
  ·
    refine ⟨52599964842171631581091031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140266572912457684216242749 52599964842171631581091031)
    ·
      refine ⟨78899947263257447371636547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52599964842171631581091031 78899947263257447371636547)
      ·
        refine ⟨118349920894886171057454821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78899947263257447371636547 118349920894886171057454821)
        ·
          refine ⟨22190610167791157073272779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118349920894886171057454821 22190610167791157073272779)
          ·
            refine ⟨33285915251686735609909169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22190610167791157073272779 33285915251686735609909169)
            ·
              refine ⟨24964436438765051707431877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33285915251686735609909169 24964436438765051707431877)
              ·
                refine ⟨4680831832268447195143477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24964436438765051707431877 4680831832268447195143477)
                ·
                  refine ⟨438827984275166924544701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4680831832268447195143477 438827984275166924544701)
                  ·
                    rfl

theorem cell22_3845765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 5].length) (baseStart_3845765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845765 prefixEnd_3845765 := by exact prefixLift 3845765
  have htrace : WordTrace (prefixWord ++ tailWord_3845765) baseStart_3845765 baseEnd_3845765 := by
    simpa [prefixWord, tailWord_3845765, baseEnd_3845765] using wordTrace_append hprefix tailTrace_3845765
  have hstable : (prefixWord ++ tailWord_3845765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845765).length < 2 ^ (prefixWord ++ tailWord_3845765).sum := by decide
  have hdescent : baseEnd_3845765 < baseStart_3845765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845795 : List Nat := [1, 1, 1, 4, 1, 1, 5, 1, 3, 4]
def baseStart_3845795 : Nat := 118140960795 + 3845795 * 2 ^ 59
def prefixEnd_3845795 : Nat := 4983230072969 + 3 ^ 40 * 3845795 * 2
def baseEnd_3845795 : Nat := 1316494222438590695384011

theorem tailTrace_3845795 : CollatzResearch.WordTrace tailWord_3845795 prefixEnd_3845795 1316494222438590695384011 := by
  unfold tailWord_3845795
  simp only [CollatzResearch.WordTrace]
  refine ⟨140267667102348999339834839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93511778068232666226556559 140267667102348999339834839)
  ·
    refine ⟨210401500653523499009752259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140267667102348999339834839 210401500653523499009752259)
    ·
      refine ⟨315602250980285248514628389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210401500653523499009752259 315602250980285248514628389)
      ·
        refine ⟨59175422058803484096492823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 315602250980285248514628389 59175422058803484096492823)
        ·
          refine ⟨88763133088205226144739235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59175422058803484096492823 88763133088205226144739235)
          ·
            refine ⟨133144699632307839217108853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88763133088205226144739235 133144699632307839217108853)
            ·
              refine ⟨12482315590528859926603955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133144699632307839217108853 12482315590528859926603955)
              ·
                refine ⟨18723473385793289889905933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12482315590528859926603955 18723473385793289889905933)
                ·
                  refine ⟨7021302519672483708714725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18723473385793289889905933 7021302519672483708714725)
                  ·
                    refine ⟨1316494222438590695384011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7021302519672483708714725 1316494222438590695384011)
                    ·
                      rfl

theorem cell22_3845795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 4].length) (baseStart_3845795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845795 prefixEnd_3845795 := by exact prefixLift 3845795
  have htrace : WordTrace (prefixWord ++ tailWord_3845795) baseStart_3845795 baseEnd_3845795 := by
    simpa [prefixWord, tailWord_3845795, baseEnd_3845795] using wordTrace_append hprefix tailTrace_3845795
  have hstable : (prefixWord ++ tailWord_3845795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845795).length < 2 ^ (prefixWord ++ tailWord_3845795).sum := by decide
  have hdescent : baseEnd_3845795 < baseStart_3845795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845842 : List Nat := [3, 2, 2, 2, 2, 1, 1, 3, 1, 5]
def baseStart_3845842 : Nat := 118140960795 + 3845842 * 2 ^ 59
def prefixEnd_3845842 : Nat := 4983230072969 + 3 ^ 40 * 3845842 * 2
def baseEnd_3845842 : Nat := 1316510311499098239458867

theorem tailTrace_3845842 : CollatzResearch.WordTrace tailWord_3845842 prefixEnd_3845842 1316510311499098239458867 := by
  unfold tailWord_3845842
  simp only [CollatzResearch.WordTrace]
  refine ⟨35067345333294681591698945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93512920888785817577863853 35067345333294681591698945)
  ·
    refine ⟨26300508999971011193774209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35067345333294681591698945 26300508999971011193774209)
    ·
      refine ⟨19725381749978258395330657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26300508999971011193774209 19725381749978258395330657)
      ·
        refine ⟨14794036312483693796497993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19725381749978258395330657 14794036312483693796497993)
        ·
          refine ⟨11095527234362770347373495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14794036312483693796497993 11095527234362770347373495)
          ·
            refine ⟨16643290851544155521060243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11095527234362770347373495 16643290851544155521060243)
            ·
              refine ⟨24964936277316233281590365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16643290851544155521060243 24964936277316233281590365)
              ·
                refine ⟨9361851103993587480596387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24964936277316233281590365 9361851103993587480596387)
                ·
                  refine ⟨14042776655990381220894581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9361851103993587480596387 14042776655990381220894581)
                  ·
                    refine ⟨1316510311499098239458867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14042776655990381220894581 1316510311499098239458867)
                    ·
                      rfl

theorem cell22_3845842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_3845842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845842 prefixEnd_3845842 := by exact prefixLift 3845842
  have htrace : WordTrace (prefixWord ++ tailWord_3845842) baseStart_3845842 baseEnd_3845842 := by
    simpa [prefixWord, tailWord_3845842, baseEnd_3845842] using wordTrace_append hprefix tailTrace_3845842
  have hstable : (prefixWord ++ tailWord_3845842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845842).length < 2 ^ (prefixWord ++ tailWord_3845842).sum := by decide
  have hdescent : baseEnd_3845842 < baseStart_3845842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845857 : List Nat := [1, 2, 3, 1, 5, 1, 1, 1, 1, 6]
def baseStart_3845857 : Nat := 118140960795 + 3845857 * 2 ^ 59
def prefixEnd_3845857 : Nat := 4983230072969 + 3 ^ 40 * 3845857 * 2
def baseEnd_3845857 : Nat := 1316515446305643200333821

theorem tailTrace_3845857 : CollatzResearch.WordTrace tailWord_3845857 prefixEnd_3845857 1316515446305643200333821 := by
  unfold tailWord_3845857
  simp only [CollatzResearch.WordTrace]
  refine ⟨140269928428124383928591825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93513285618749589285727883 140269928428124383928591825)
  ·
    refine ⟨105202446321093287946443869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140269928428124383928591825 105202446321093287946443869)
    ·
      refine ⟨39450917370409982979916451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105202446321093287946443869 39450917370409982979916451)
      ·
        refine ⟨59176376055614974469874677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39450917370409982979916451 59176376055614974469874677)
        ·
          refine ⟨5547785255213903856550751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59176376055614974469874677 5547785255213903856550751)
          ·
            refine ⟨8321677882820855784826127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5547785255213903856550751 8321677882820855784826127)
            ·
              refine ⟨12482516824231283677239191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8321677882820855784826127 12482516824231283677239191)
              ·
                refine ⟨18723775236346925515858787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12482516824231283677239191 18723775236346925515858787)
                ·
                  refine ⟨28085662854520388273788181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18723775236346925515858787 28085662854520388273788181)
                  ·
                    refine ⟨1316515446305643200333821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28085662854520388273788181 1316515446305643200333821)
                    ·
                      rfl

theorem cell22_3845857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_3845857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845857 prefixEnd_3845857 := by exact prefixLift 3845857
  have htrace : WordTrace (prefixWord ++ tailWord_3845857) baseStart_3845857 baseEnd_3845857 := by
    simpa [prefixWord, tailWord_3845857, baseEnd_3845857] using wordTrace_append hprefix tailTrace_3845857
  have hstable : (prefixWord ++ tailWord_3845857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845857).length < 2 ^ (prefixWord ++ tailWord_3845857).sum := by decide
  have hdescent : baseEnd_3845857 < baseStart_3845857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845863 : List Nat := [1, 1, 5, 4, 1, 2, 2, 1, 1, 4]
def baseStart_3845863 : Nat := 118140960795 + 3845863 * 2 ^ 59
def prefixEnd_3845863 : Nat := 4983230072969 + 3 ^ 40 * 3845863 * 2
def baseEnd_3845863 : Nat := 1316517500228261184683803

theorem tailTrace_3845863 : CollatzResearch.WordTrace tailWord_3845863 prefixEnd_3845863 1316517500228261184683803 := by
  unfold tailWord_3845863
  simp only [CollatzResearch.WordTrace]
  refine ⟨140270147266102646953310243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93513431510735097968873495 140270147266102646953310243)
  ·
    refine ⟨210405220899153970429965365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140270147266102646953310243 210405220899153970429965365)
    ·
      refine ⟨19725489459295684727809253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 210405220899153970429965365 19725489459295684727809253)
      ·
        refine ⟨3698529273617940886464235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19725489459295684727809253 3698529273617940886464235)
        ·
          refine ⟨5547793910426911329696353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3698529273617940886464235 5547793910426911329696353)
          ·
            refine ⟨4160845432820183497272265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5547793910426911329696353 4160845432820183497272265)
            ·
              refine ⟨3120634074615137622954199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4160845432820183497272265 3120634074615137622954199)
              ·
                refine ⟨4680951111922706434431299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3120634074615137622954199 4680951111922706434431299)
                ·
                  refine ⟨7021426667884059651646949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4680951111922706434431299 7021426667884059651646949)
                  ·
                    refine ⟨1316517500228261184683803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7021426667884059651646949 1316517500228261184683803)
                    ·
                      rfl

theorem cell22_3845863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_3845863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845863 prefixEnd_3845863 := by exact prefixLift 3845863
  have htrace : WordTrace (prefixWord ++ tailWord_3845863) baseStart_3845863 baseEnd_3845863 := by
    simpa [prefixWord, tailWord_3845863, baseEnd_3845863] using wordTrace_append hprefix tailTrace_3845863
  have hstable : (prefixWord ++ tailWord_3845863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845863).length < 2 ^ (prefixWord ++ tailWord_3845863).sum := by decide
  have hdescent : baseEnd_3845863 < baseStart_3845863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845885 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 2, 6]
def baseStart_3845885 : Nat := 118140960795 + 3845885 * 2 ^ 59
def prefixEnd_3845885 : Nat := 4983230072969 + 3 ^ 40 * 3845885 * 2
def baseEnd_3845885 : Nat := 1316525031277860460633735

theorem tailTrace_3845885 : CollatzResearch.WordTrace tailWord_3845885 prefixEnd_3845885 1316525031277860460633735 := by
  unfold tailWord_3845885
  simp only [CollatzResearch.WordTrace]
  refine ⟨140270949672022944710611109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93513966448015296473740739 140270949672022944710611109)
  ·
    refine ⟨26300803063504302133239583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140270949672022944710611109 26300803063504302133239583)
    ·
      refine ⟨39451204595256453199859375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26300803063504302133239583 39451204595256453199859375)
      ·
        refine ⟨59176806892884679799789063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39451204595256453199859375 59176806892884679799789063)
        ·
          refine ⟨88765210339327019699683595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59176806892884679799789063 88765210339327019699683595)
          ·
            refine ⟨133147815508990529549525393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88765210339327019699683595 133147815508990529549525393)
            ·
              refine ⟨99860861631742897162144045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133147815508990529549525393 99860861631742897162144045)
              ·
                refine ⟨37447823111903586435804017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99860861631742897162144045 37447823111903586435804017)
                ·
                  refine ⟨28085867333927689826853013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37447823111903586435804017 28085867333927689826853013)
                  ·
                    refine ⟨1316525031277860460633735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28085867333927689826853013 1316525031277860460633735)
                    ·
                      rfl

theorem cell22_3845885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_3845885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845885 prefixEnd_3845885 := by exact prefixLift 3845885
  have htrace : WordTrace (prefixWord ++ tailWord_3845885) baseStart_3845885 baseEnd_3845885 := by
    simpa [prefixWord, tailWord_3845885, baseEnd_3845885] using wordTrace_append hprefix tailTrace_3845885
  have hstable : (prefixWord ++ tailWord_3845885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845885).length < 2 ^ (prefixWord ++ tailWord_3845885).sum := by decide
  have hdescent : baseEnd_3845885 < baseStart_3845885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845887 : List Nat := [1, 1, 2, 2, 1, 3, 3, 3, 3, 3]
def baseStart_3845887 : Nat := 118140960795 + 3845887 * 2 ^ 59
def prefixEnd_3845887 : Nat := 4983230072969 + 3 ^ 40 * 3845887 * 2
def baseEnd_3845887 : Nat := 1316525715918733122083729

theorem tailTrace_3845887 : CollatzResearch.WordTrace tailWord_3845887 prefixEnd_3845887 1316525715918733122083729 := by
  unfold tailWord_3845887
  simp only [CollatzResearch.WordTrace]
  refine ⟨140271022618015699052183915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93514015078677132701455943 140271022618015699052183915)
  ·
    refine ⟨210406533927023548578275873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140271022618015699052183915 210406533927023548578275873)
    ·
      refine ⟨157804900445267661433706905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210406533927023548578275873 157804900445267661433706905)
      ·
        refine ⟨118353675333950746075280179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157804900445267661433706905 118353675333950746075280179)
        ·
          refine ⟨177530513000926119112920269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118353675333950746075280179 177530513000926119112920269)
          ·
            refine ⟨66573942375347294667345101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177530513000926119112920269 66573942375347294667345101)
            ·
              refine ⟨24965228390755235500254413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66573942375347294667345101 24965228390755235500254413)
              ·
                refine ⟨9361960646533213312595405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24965228390755235500254413 9361960646533213312595405)
                ·
                  refine ⟨3510735242449954992223277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9361960646533213312595405 3510735242449954992223277)
                  ·
                    refine ⟨1316525715918733122083729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3510735242449954992223277 1316525715918733122083729)
                    ·
                      rfl

theorem cell22_3845887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 3, 3].length) (baseStart_3845887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845887 prefixEnd_3845887 := by exact prefixLift 3845887
  have htrace : WordTrace (prefixWord ++ tailWord_3845887) baseStart_3845887 baseEnd_3845887 := by
    simpa [prefixWord, tailWord_3845887, baseEnd_3845887] using wordTrace_append hprefix tailTrace_3845887
  have hstable : (prefixWord ++ tailWord_3845887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845887).length < 2 ^ (prefixWord ++ tailWord_3845887).sum := by decide
  have hdescent : baseEnd_3845887 < baseStart_3845887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845906 : List Nat := [3, 2, 4, 1, 1, 3, 2, 6]
def baseStart_3845906 : Nat := 118140960795 + 3845906 * 2 ^ 59
def prefixEnd_3845906 : Nat := 4983230072969 + 3 ^ 40 * 3845906 * 2
def baseEnd_3845906 : Nat := 146281357778558156206519

theorem tailTrace_3845906 : CollatzResearch.WordTrace tailWord_3845906 prefixEnd_3845906 146281357778558156206519 := by
  unfold tailWord_3845906
  simp only [CollatzResearch.WordTrace]
  refine ⟨35067928901236716324281393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93514477069964576864750381 35067928901236716324281393)
  ·
    refine ⟨26300946675927537243211045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35067928901236716324281393 26300946675927537243211045)
    ·
      refine ⟨4931427501736413233102071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26300946675927537243211045 4931427501736413233102071)
      ·
        refine ⟨7397141252604619849653107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4931427501736413233102071 7397141252604619849653107)
        ·
          refine ⟨11095711878906929774479661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7397141252604619849653107 11095711878906929774479661)
          ·
            refine ⟨4160891954590098665429873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11095711878906929774479661 4160891954590098665429873)
            ·
              refine ⟨3120668965942573999072405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4160891954590098665429873 3120668965942573999072405)
              ·
                refine ⟨146281357778558156206519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3120668965942573999072405 146281357778558156206519)
                ·
                  rfl

theorem cell22_3845906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 6].length) (baseStart_3845906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845906 prefixEnd_3845906 := by exact prefixLift 3845906
  have htrace : WordTrace (prefixWord ++ tailWord_3845906) baseStart_3845906 baseEnd_3845906 := by
    simpa [prefixWord, tailWord_3845906, baseEnd_3845906] using wordTrace_append hprefix tailTrace_3845906
  have hstable : (prefixWord ++ tailWord_3845906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845906).length < 2 ^ (prefixWord ++ tailWord_3845906).sum := by decide
  have hdescent : baseEnd_3845906 < baseStart_3845906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845921 : List Nat := [1, 2, 3, 2, 1, 3, 3, 3, 1, 3]
def baseStart_3845921 : Nat := 118140960795 + 3845921 * 2 ^ 59
def prefixEnd_3845921 : Nat := 4983230072969 + 3 ^ 40 * 3845921 * 2
def baseEnd_3845921 : Nat := 1316537354813568366733625

theorem tailTrace_3845921 : CollatzResearch.WordTrace tailWord_3845921 prefixEnd_3845921 1316537354813568366733625 := by
  unfold tailWord_3845921
  simp only [CollatzResearch.WordTrace]
  refine ⟨140272262699892522858921617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93514841799928348572614411 140272262699892522858921617)
  ·
    refine ⟨105204197024919392144191213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140272262699892522858921617 105204197024919392144191213)
    ·
      refine ⟨39451573884344772054071705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105204197024919392144191213 39451573884344772054071705)
      ·
        refine ⟨29588680413258579040553779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39451573884344772054071705 29588680413258579040553779)
        ·
          refine ⟨44383020619887868560830669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29588680413258579040553779 44383020619887868560830669)
          ·
            refine ⟨16643632732457950710311501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44383020619887868560830669 16643632732457950710311501)
            ·
              refine ⟨6241362274671731516366813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16643632732457950710311501 6241362274671731516366813)
              ·
                refine ⟨2340510853001899318637555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6241362274671731516366813 2340510853001899318637555)
                ·
                  refine ⟨3510766279502848977956333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2340510853001899318637555 3510766279502848977956333)
                  ·
                    refine ⟨1316537354813568366733625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3510766279502848977956333 1316537354813568366733625)
                    ·
                      rfl

theorem cell22_3845921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_3845921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845921 prefixEnd_3845921 := by exact prefixLift 3845921
  have htrace : WordTrace (prefixWord ++ tailWord_3845921) baseStart_3845921 baseEnd_3845921 := by
    simpa [prefixWord, tailWord_3845921, baseEnd_3845921] using wordTrace_append hprefix tailTrace_3845921
  have hstable : (prefixWord ++ tailWord_3845921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845921).length < 2 ^ (prefixWord ++ tailWord_3845921).sum := by decide
  have hdescent : baseEnd_3845921 < baseStart_3845921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845938 : List Nat := [3, 2, 1, 1, 3, 3, 3, 2, 1, 3]
def baseStart_3845938 : Nat := 118140960795 + 3845938 * 2 ^ 59
def prefixEnd_3845938 : Nat := 4983230072969 + 3 ^ 40 * 3845938 * 2
def baseEnd_3845938 : Nat := 1316543174260985989058573

theorem tailTrace_3845938 : CollatzResearch.WordTrace tailWord_3845938 prefixEnd_3845938 1316543174260985989058573 := by
  unfold tailWord_3845938
  simp only [CollatzResearch.WordTrace]
  refine ⟨35068220685207733690572617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93515255160553956508193645 35068220685207733690572617)
  ·
    refine ⟨26301165513905800267929463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35068220685207733690572617 26301165513905800267929463)
    ·
      refine ⟨39451748270858700401894195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26301165513905800267929463 39451748270858700401894195)
      ·
        refine ⟨59177622406288050602841293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39451748270858700401894195 59177622406288050602841293)
        ·
          refine ⟨22191608402358018976065485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59177622406288050602841293 22191608402358018976065485)
          ·
            refine ⟨8321853150884257116024557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22191608402358018976065485 8321853150884257116024557)
            ·
              refine ⟨3120694931581596418509209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8321853150884257116024557 3120694931581596418509209)
              ·
                refine ⟨2340521198686197313881907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3120694931581596418509209 2340521198686197313881907)
                ·
                  refine ⟨3510781798029295970822861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2340521198686197313881907 3510781798029295970822861)
                  ·
                    refine ⟨1316543174260985989058573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3510781798029295970822861 1316543174260985989058573)
                    ·
                      rfl

theorem cell22_3845938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_3845938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845938 prefixEnd_3845938 := by exact prefixLift 3845938
  have htrace : WordTrace (prefixWord ++ tailWord_3845938) baseStart_3845938 baseEnd_3845938 := by
    simpa [prefixWord, tailWord_3845938, baseEnd_3845938] using wordTrace_append hprefix tailTrace_3845938
  have hstable : (prefixWord ++ tailWord_3845938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845938).length < 2 ^ (prefixWord ++ tailWord_3845938).sum := by decide
  have hdescent : baseEnd_3845938 < baseStart_3845938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845951 : List Nat := [1, 1, 2, 2, 6, 2, 2, 1, 5]
def baseStart_3845951 : Nat := 118140960795 + 3845951 * 2 ^ 59
def prefixEnd_3845951 : Nat := 4983230072969 + 3 ^ 40 * 3845951 * 2
def baseEnd_3845951 : Nat := 438849208142219429494511

theorem tailTrace_3845951 : CollatzResearch.WordTrace tailWord_3845951 prefixEnd_3845951 438849208142219429494511 := by
  unfold tailWord_3845951
  simp only [CollatzResearch.WordTrace]
  refine ⟨140273356889783837982513707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93515571259855891988342471 140273356889783837982513707)
  ·
    refine ⟨210410035334675756973770561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140273356889783837982513707 210410035334675756973770561)
    ·
      refine ⟨157807526501006817730327921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210410035334675756973770561 157807526501006817730327921)
      ·
        refine ⟨118355644875755113297745941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157807526501006817730327921 118355644875755113297745941)
        ·
          refine ⟨5547920853551020935831841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 118355644875755113297745941 5547920853551020935831841)
          ·
            refine ⟨4160940640163265701873881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5547920853551020935831841 4160940640163265701873881)
            ·
              refine ⟨3120705480122449276405411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4160940640163265701873881 3120705480122449276405411)
              ·
                refine ⟨4681058220183673914608117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3120705480122449276405411 4681058220183673914608117)
                ·
                  refine ⟨438849208142219429494511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4681058220183673914608117 438849208142219429494511)
                  ·
                    rfl

theorem cell22_3845951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 5].length) (baseStart_3845951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845951 prefixEnd_3845951 := by exact prefixLift 3845951
  have htrace : WordTrace (prefixWord ++ tailWord_3845951) baseStart_3845951 baseEnd_3845951 := by
    simpa [prefixWord, tailWord_3845951, baseEnd_3845951] using wordTrace_append hprefix tailTrace_3845951
  have hstable : (prefixWord ++ tailWord_3845951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845951).length < 2 ^ (prefixWord ++ tailWord_3845951).sum := by decide
  have hdescent : baseEnd_3845951 < baseStart_3845951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845964 : List Nat := [2, 2, 1, 3, 4, 1, 1, 1, 3, 4]
def baseStart_3845964 : Nat := 118140960795 + 3845964 * 2 ^ 59
def prefixEnd_3845964 : Nat := 4983230072969 + 3 ^ 40 * 3845964 * 2
def baseEnd_3845964 : Nat := 1316552074592330587908493

theorem tailTrace_3845964 : CollatzResearch.WordTrace tailWord_3845964 prefixEnd_3845964 1316552074592330587908493 := by
  unfold tailWord_3845964
  simp only [CollatzResearch.WordTrace]
  refine ⟨70136915519368370601368473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93515887359157827468491297 70136915519368370601368473)
  ·
    refine ⟨52602686639526277951026355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70136915519368370601368473 52602686639526277951026355)
    ·
      refine ⟨78904029959289416926539533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52602686639526277951026355 78904029959289416926539533)
      ·
        refine ⟨29589011234733531347452325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78904029959289416926539533 29589011234733531347452325)
        ·
          refine ⟨5547939606512537127647311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29589011234733531347452325 5547939606512537127647311)
          ·
            refine ⟨8321909409768805691470967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5547939606512537127647311 8321909409768805691470967)
            ·
              refine ⟨12482864114653208537206451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8321909409768805691470967 12482864114653208537206451)
              ·
                refine ⟨18724296171979812805809677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12482864114653208537206451 18724296171979812805809677)
                ·
                  refine ⟨7021611064492429802178629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18724296171979812805809677 7021611064492429802178629)
                  ·
                    refine ⟨1316552074592330587908493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7021611064492429802178629 1316552074592330587908493)
                    ·
                      rfl

theorem cell22_3845964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_3845964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845964 prefixEnd_3845964 := by exact prefixLift 3845964
  have htrace : WordTrace (prefixWord ++ tailWord_3845964) baseStart_3845964 baseEnd_3845964 := by
    simpa [prefixWord, tailWord_3845964, baseEnd_3845964] using wordTrace_append hprefix tailTrace_3845964
  have hstable : (prefixWord ++ tailWord_3845964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845964).length < 2 ^ (prefixWord ++ tailWord_3845964).sum := by decide
  have hdescent : baseEnd_3845964 < baseStart_3845964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845977 : List Nat := [1, 2, 1, 2, 2, 3, 3, 2, 1, 5]
def baseStart_3845977 : Nat := 118140960795 + 3845977 * 2 ^ 59
def prefixEnd_3845977 : Nat := 4983230072969 + 3 ^ 40 * 3845977 * 2
def baseEnd_3845977 : Nat := 1316556524758002887333453

theorem tailTrace_3845977 : CollatzResearch.WordTrace tailWord_3845977 prefixEnd_3845977 1316556524758002887333453 := by
  unfold tailWord_3845977
  simp only [CollatzResearch.WordTrace]
  refine ⟨140274305187689644422960185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93516203458459762948640123 140274305187689644422960185)
  ·
    refine ⟨105205728890767233317220139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140274305187689644422960185 105205728890767233317220139)
    ·
      refine ⟨157808593336150849975830209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105205728890767233317220139 157808593336150849975830209)
      ·
        refine ⟨118356445002113137481872657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157808593336150849975830209 118356445002113137481872657)
        ·
          refine ⟨88767333751584853111404493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118356445002113137481872657 88767333751584853111404493)
          ·
            refine ⟨33287750156844319916776685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88767333751584853111404493 33287750156844319916776685)
            ·
              refine ⟨12482906308816619968791257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33287750156844319916776685 12482906308816619968791257)
              ·
                refine ⟨9362179731612464976593443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12482906308816619968791257 9362179731612464976593443)
                ·
                  refine ⟨14043269597418697464890165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9362179731612464976593443 14043269597418697464890165)
                  ·
                    refine ⟨1316556524758002887333453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14043269597418697464890165 1316556524758002887333453)
                    ·
                      rfl

theorem cell22_3845977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 5].length) (baseStart_3845977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845977 prefixEnd_3845977 := by exact prefixLift 3845977
  have htrace : WordTrace (prefixWord ++ tailWord_3845977) baseStart_3845977 baseEnd_3845977 := by
    simpa [prefixWord, tailWord_3845977, baseEnd_3845977] using wordTrace_append hprefix tailTrace_3845977
  have hstable : (prefixWord ++ tailWord_3845977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845977).length < 2 ^ (prefixWord ++ tailWord_3845977).sum := by decide
  have hdescent : baseEnd_3845977 < baseStart_3845977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845996 : List Nat := [2, 2, 1, 1, 4, 2, 4, 2, 4]
def baseStart_3845996 : Nat := 118140960795 + 3845996 * 2 ^ 59
def prefixEnd_3845996 : Nat := 4983230072969 + 3 ^ 40 * 3845996 * 2
def baseEnd_3845996 : Nat := 438854342948764390369465

theorem tailTrace_3845996 : CollatzResearch.WordTrace tailWord_3845996 prefixEnd_3845996 438854342948764390369465 := by
  unfold tailWord_3845996
  simp only [CollatzResearch.WordTrace]
  refine ⟨70137499087310405333950921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93516665449747207111934561 70137499087310405333950921)
  ·
    refine ⟨52603124315482804000463191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70137499087310405333950921 52603124315482804000463191)
    ·
      refine ⟨78904686473224206000694787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52603124315482804000463191 78904686473224206000694787)
      ·
        refine ⟨118357029709836309001042181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78904686473224206000694787 118357029709836309001042181)
        ·
          refine ⟨22191943070594307937695409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118357029709836309001042181 22191943070594307937695409)
          ·
            refine ⟨16643957302945730953271557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22191943070594307937695409 16643957302945730953271557)
            ·
              refine ⟨3120741994302324553738417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16643957302945730953271557 3120741994302324553738417)
              ·
                refine ⟨2340556495726743415303813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3120741994302324553738417 2340556495726743415303813)
                ·
                  refine ⟨438854342948764390369465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2340556495726743415303813 438854342948764390369465)
                  ·
                    rfl

theorem cell22_3845996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2, 4].length) (baseStart_3845996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3845996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3845996 prefixEnd_3845996 := by exact prefixLift 3845996
  have htrace : WordTrace (prefixWord ++ tailWord_3845996) baseStart_3845996 baseEnd_3845996 := by
    simpa [prefixWord, tailWord_3845996, baseEnd_3845996] using wordTrace_append hprefix tailTrace_3845996
  have hstable : (prefixWord ++ tailWord_3845996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845996).length < 2 ^ (prefixWord ++ tailWord_3845996).sum := by decide
  have hdescent : baseEnd_3845996 < baseStart_3845996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846062 : List Nat := [4, 1, 5, 1, 2, 1, 1, 1, 1, 5]
def baseStart_3846062 : Nat := 118140960795 + 3846062 * 2 ^ 59
def prefixEnd_3846062 : Nat := 4983230072969 + 3 ^ 40 * 3846062 * 2
def baseEnd_3846062 : Nat := 1316585621995090998958193

theorem tailTrace_3846062 : CollatzResearch.WordTrace tailWord_3846062 prefixEnd_3846062 1316585621995090998958193 := by
  unfold tailWord_3846062
  simp only [CollatzResearch.WordTrace]
  refine ⟨17534675674047712992475555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93518270261587802626536293 17534675674047712992475555)
  ·
    refine ⟨26302013511071569488713333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17534675674047712992475555 26302013511071569488713333)
    ·
      refine ⟨2465813766662959639566875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26302013511071569488713333 2465813766662959639566875)
      ·
        refine ⟨3698720649994439459350313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2465813766662959639566875 3698720649994439459350313)
        ·
          refine ⟨2774040487495829594512735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3698720649994439459350313 2774040487495829594512735)
          ·
            refine ⟨4161060731243744391769103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2774040487495829594512735 4161060731243744391769103)
            ·
              refine ⟨6241591096865616587653655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4161060731243744391769103 6241591096865616587653655)
              ·
                refine ⟨9362386645298424881480483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6241591096865616587653655 9362386645298424881480483)
                ·
                  refine ⟨14043579967947637322220725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9362386645298424881480483 14043579967947637322220725)
                  ·
                    refine ⟨1316585621995090998958193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14043579967947637322220725 1316585621995090998958193)
                    ·
                      rfl

theorem cell22_3846062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_3846062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846062 prefixEnd_3846062 := by exact prefixLift 3846062
  have htrace : WordTrace (prefixWord ++ tailWord_3846062) baseStart_3846062 baseEnd_3846062 := by
    simpa [prefixWord, tailWord_3846062, baseEnd_3846062] using wordTrace_append hprefix tailTrace_3846062
  have hstable : (prefixWord ++ tailWord_3846062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846062).length < 2 ^ (prefixWord ++ tailWord_3846062).sum := by decide
  have hdescent : baseEnd_3846062 < baseStart_3846062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846067 : List Nat := [1, 1, 1, 2, 3, 1, 3, 3, 2, 5]
def baseStart_3846067 : Nat := 118140960795 + 3846067 * 2 ^ 59
def prefixEnd_3846067 : Nat := 4983230072969 + 3 ^ 40 * 3846067 * 2
def baseEnd_3846067 : Nat := 1316587333597272652583177

theorem tailTrace_3846067 : CollatzResearch.WordTrace tailWord_3846067 prefixEnd_3846067 1316587333597272652583177 := by
  unfold tailWord_3846067
  simp only [CollatzResearch.WordTrace]
  refine ⟨140277587757363589793736455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93518391838242393195824303 140277587757363589793736455)
  ·
    refine ⟨210416381636045384690604683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140277587757363589793736455 210416381636045384690604683)
    ·
      refine ⟨315624572454068077035907025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210416381636045384690604683 315624572454068077035907025)
      ·
        refine ⟨236718429340551057776930269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315624572454068077035907025 236718429340551057776930269)
        ·
          refine ⟨88769411002706646666348851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236718429340551057776930269 88769411002706646666348851)
          ·
            refine ⟨133154116504059969999523277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88769411002706646666348851 133154116504059969999523277)
            ·
              refine ⟨49932793689022488749821229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133154116504059969999523277 49932793689022488749821229)
              ·
                refine ⟨18724797633383433281182961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49932793689022488749821229 18724797633383433281182961)
                ·
                  refine ⟨14043598225037574960887221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18724797633383433281182961 14043598225037574960887221)
                  ·
                    refine ⟨1316587333597272652583177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14043598225037574960887221 1316587333597272652583177)
                    ·
                      rfl

theorem cell22_3846067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 5].length) (baseStart_3846067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846067 prefixEnd_3846067 := by exact prefixLift 3846067
  have htrace : WordTrace (prefixWord ++ tailWord_3846067) baseStart_3846067 baseEnd_3846067 := by
    simpa [prefixWord, tailWord_3846067, baseEnd_3846067] using wordTrace_append hprefix tailTrace_3846067
  have hstable : (prefixWord ++ tailWord_3846067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846067).length < 2 ^ (prefixWord ++ tailWord_3846067).sum := by decide
  have hdescent : baseEnd_3846067 < baseStart_3846067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846165 : List Nat := [1, 3, 2, 1, 5, 2, 2, 2, 4]
def baseStart_3846165 : Nat := 118140960795 + 3846165 * 2 ^ 59
def prefixEnd_3846165 : Nat := 4983230072969 + 3 ^ 40 * 3846165 * 2
def baseEnd_3846165 : Nat := 438873627000011021210959

theorem tailTrace_3846165 : CollatzResearch.WordTrace tailWord_3846165 prefixEnd_3846165 438873627000011021210959 := by
  unfold tailWord_3846165
  simp only [CollatzResearch.WordTrace]
  refine ⟨140281162111008552530803949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93520774740672368353869299 140281162111008552530803949)
  ·
    refine ⟨52605435791628207199051481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140281162111008552530803949 52605435791628207199051481)
    ·
      refine ⟨39454076843721155399288611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52605435791628207199051481 39454076843721155399288611)
      ·
        refine ⟨59181115265581733098932917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39454076843721155399288611 59181115265581733098932917)
        ·
          refine ⟨5548229556148287478024961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59181115265581733098932917 5548229556148287478024961)
          ·
            refine ⟨4161172167111215608518721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5548229556148287478024961 4161172167111215608518721)
            ·
              refine ⟨3120879125333411706389041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4161172167111215608518721 3120879125333411706389041)
              ·
                refine ⟨2340659344000058779791781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3120879125333411706389041 2340659344000058779791781)
                ·
                  refine ⟨438873627000011021210959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2340659344000058779791781 438873627000011021210959)
                  ·
                    rfl

theorem cell22_3846165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 2, 4].length) (baseStart_3846165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846165 prefixEnd_3846165 := by exact prefixLift 3846165
  have htrace : WordTrace (prefixWord ++ tailWord_3846165) baseStart_3846165 baseEnd_3846165 := by
    simpa [prefixWord, tailWord_3846165, baseEnd_3846165] using wordTrace_append hprefix tailTrace_3846165
  have hstable : (prefixWord ++ tailWord_3846165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846165).length < 2 ^ (prefixWord ++ tailWord_3846165).sum := by decide
  have hdescent : baseEnd_3846165 < baseStart_3846165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846204 : List Nat := [2, 2, 2, 2, 2, 1, 2, 2, 7]
def baseStart_3846204 : Nat := 118140960795 + 3846204 * 2 ^ 59
def prefixEnd_3846204 : Nat := 4983230072969 + 3 ^ 40 * 3846204 * 2
def baseEnd_3846204 : Nat := 438878077165683320635919

theorem tailTrace_3846204 : CollatzResearch.WordTrace tailWord_3846204 prefixEnd_3846204 438878077165683320635919 := by
  unfold tailWord_3846204
  simp only [CollatzResearch.WordTrace]
  refine ⟨70141292278933631095736833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93521723038578174794315777 70141292278933631095736833)
  ·
    refine ⟨52605969209200223321802625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70141292278933631095736833 52605969209200223321802625)
    ·
      refine ⟨39454476906900167491351969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52605969209200223321802625 39454476906900167491351969)
      ·
        refine ⟨29590857680175125618513977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39454476906900167491351969 29590857680175125618513977)
        ·
          refine ⟨22193143260131344213885483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29590857680175125618513977 22193143260131344213885483)
          ·
            refine ⟨33289714890197016320828225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22193143260131344213885483 33289714890197016320828225)
            ·
              refine ⟨24967286167647762240621169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33289714890197016320828225 24967286167647762240621169)
              ·
                refine ⟨18725464625735821680465877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24967286167647762240621169 18725464625735821680465877)
                ·
                  refine ⟨438878077165683320635919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18725464625735821680465877 438878077165683320635919)
                  ·
                    rfl

theorem cell22_3846204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 7].length) (baseStart_3846204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846204 prefixEnd_3846204 := by exact prefixLift 3846204
  have htrace : WordTrace (prefixWord ++ tailWord_3846204) baseStart_3846204 baseEnd_3846204 := by
    simpa [prefixWord, tailWord_3846204, baseEnd_3846204] using wordTrace_append hprefix tailTrace_3846204
  have hstable : (prefixWord ++ tailWord_3846204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846204).length < 2 ^ (prefixWord ++ tailWord_3846204).sum := by decide
  have hdescent : baseEnd_3846204 < baseStart_3846204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846208 : List Nat := [2, 1, 1, 2, 2, 4, 1, 5, 1, 3]
def baseStart_3846208 : Nat := 118140960795 + 3846208 * 2 ^ 59
def prefixEnd_3846208 : Nat := 4983230072969 + 3 ^ 40 * 3846208 * 2
def baseEnd_3846208 : Nat := 1316635600778795284807745

theorem tailTrace_3846208 : CollatzResearch.WordTrace tailWord_3846208 prefixEnd_3846208 1316635600778795284807745 := by
  unfold tailWord_3846208
  simp only [CollatzResearch.WordTrace]
  refine ⟨70141365224926385437309639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93521820299901847249746185 70141365224926385437309639)
  ·
    refine ⟨105212047837389578155964459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70141365224926385437309639 105212047837389578155964459)
    ·
      refine ⟨157818071756084367233946689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105212047837389578155964459 157818071756084367233946689)
      ·
        refine ⟨118363553817063275425460017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157818071756084367233946689 118363553817063275425460017)
        ·
          refine ⟨88772665362797456569095013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118363553817063275425460017 88772665362797456569095013)
          ·
            refine ⟨16644874755524523106705315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88772665362797456569095013 16644874755524523106705315)
            ·
              refine ⟨24967312133286784660057973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16644874755524523106705315 24967312133286784660057973)
              ·
                refine ⟨2340685512495636061880435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24967312133286784660057973 2340685512495636061880435)
                ·
                  refine ⟨3511028268743454092820653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2340685512495636061880435 3511028268743454092820653)
                  ·
                    refine ⟨1316635600778795284807745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3511028268743454092820653 1316635600778795284807745)
                    ·
                      rfl

theorem cell22_3846208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 5, 1, 3].length) (baseStart_3846208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846208 prefixEnd_3846208 := by exact prefixLift 3846208
  have htrace : WordTrace (prefixWord ++ tailWord_3846208) baseStart_3846208 baseEnd_3846208 := by
    simpa [prefixWord, tailWord_3846208, baseEnd_3846208] using wordTrace_append hprefix tailTrace_3846208
  have hstable : (prefixWord ++ tailWord_3846208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846208).length < 2 ^ (prefixWord ++ tailWord_3846208).sum := by decide
  have hdescent : baseEnd_3846208 < baseStart_3846208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846221 : List Nat := [1, 6, 1, 1, 1, 1, 3, 1, 7]
def baseStart_3846221 : Nat := 118140960795 + 3846221 * 2 ^ 59
def prefixEnd_3846221 : Nat := 4983230072969 + 3 ^ 40 * 3846221 * 2
def baseEnd_3846221 : Nat := 438880016981489194744235

theorem tailTrace_3846221 : CollatzResearch.WordTrace tailWord_3846221 prefixEnd_3846221 438880016981489194744235 := by
  unfold tailWord_3846221
  simp only [CollatzResearch.WordTrace]
  refine ⟨140283204598805674094842517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93522136399203782729895011 140283204598805674094842517)
  ·
    refine ⟨6575775215569015973195743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 140283204598805674094842517 6575775215569015973195743)
    ·
      refine ⟨9863662823353523959793615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6575775215569015973195743 9863662823353523959793615)
      ·
        refine ⟨14795494235030285939690423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9863662823353523959793615 14795494235030285939690423)
        ·
          refine ⟨22193241352545428909535635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14795494235030285939690423 22193241352545428909535635)
          ·
            refine ⟨33289862028818143364303453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22193241352545428909535635 33289862028818143364303453)
            ·
              refine ⟨12483698260806803761613795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33289862028818143364303453 12483698260806803761613795)
              ·
                refine ⟨18725547391210205642420693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12483698260806803761613795 18725547391210205642420693)
                ·
                  refine ⟨438880016981489194744235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18725547391210205642420693 438880016981489194744235)
                  ·
                    rfl

theorem cell22_3846221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_3846221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846221 prefixEnd_3846221 := by exact prefixLift 3846221
  have htrace : WordTrace (prefixWord ++ tailWord_3846221) baseStart_3846221 baseEnd_3846221 := by
    simpa [prefixWord, tailWord_3846221, baseEnd_3846221] using wordTrace_append hprefix tailTrace_3846221
  have hstable : (prefixWord ++ tailWord_3846221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846221).length < 2 ^ (prefixWord ++ tailWord_3846221).sum := by decide
  have hdescent : baseEnd_3846221 < baseStart_3846221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846236 : List Nat := [2, 2, 4, 1, 1, 2, 2, 1, 2, 5]
def baseStart_3846236 : Nat := 118140960795 + 3846236 * 2 ^ 59
def prefixEnd_3846236 : Nat := 4983230072969 + 3 ^ 40 * 3846236 * 2
def baseEnd_3846236 : Nat := 1316645185751012545107659

theorem tailTrace_3846236 : CollatzResearch.WordTrace tailWord_3846236 prefixEnd_3846236 1316645185751012545107659 := by
  unfold tailWord_3846236
  simp only [CollatzResearch.WordTrace]
  refine ⟨70141875846875665828319281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93522501129167554437759041 70141875846875665828319281)
  ·
    refine ⟨52606406885156749371239461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70141875846875665828319281 52606406885156749371239461)
    ·
      refine ⟨9863701290966890507107399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52606406885156749371239461 9863701290966890507107399)
      ·
        refine ⟨14795551936450335760661099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9863701290966890507107399 14795551936450335760661099)
        ·
          refine ⟨22193327904675503640991649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14795551936450335760661099 22193327904675503640991649)
          ·
            refine ⟨16644995928506627730743737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22193327904675503640991649 16644995928506627730743737)
            ·
              refine ⟨12483746946379970798057803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16644995928506627730743737 12483746946379970798057803)
              ·
                refine ⟨18725620419569956197086705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12483746946379970798057803 18725620419569956197086705)
                ·
                  refine ⟨14044215314677467147815029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18725620419569956197086705 14044215314677467147815029)
                  ·
                    refine ⟨1316645185751012545107659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14044215314677467147815029 1316645185751012545107659)
                    ·
                      rfl

theorem cell22_3846236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_3846236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846236 prefixEnd_3846236 := by exact prefixLift 3846236
  have htrace : WordTrace (prefixWord ++ tailWord_3846236) baseStart_3846236 baseEnd_3846236 := by
    simpa [prefixWord, tailWord_3846236, baseEnd_3846236] using wordTrace_append hprefix tailTrace_3846236
  have hstable : (prefixWord ++ tailWord_3846236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846236).length < 2 ^ (prefixWord ++ tailWord_3846236).sum := by decide
  have hdescent : baseEnd_3846236 < baseStart_3846236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846249 : List Nat := [1, 2, 1, 1, 1, 5, 1, 4, 6]
def baseStart_3846249 : Nat := 118140960795 + 3846249 * 2 ^ 59
def prefixEnd_3846249 : Nat := 4983230072969 + 3 ^ 40 * 3846249 * 2
def baseEnd_3846249 : Nat := 438883211972228281510873

theorem tailTrace_3846249 : CollatzResearch.WordTrace tailWord_3846249 prefixEnd_3846249 438883211972228281510873 := by
  unfold tailWord_3846249
  simp only [CollatzResearch.WordTrace]
  refine ⟨140284225842704234876861801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93522817228469489917907867 140284225842704234876861801)
  ·
    refine ⟨105213169382028176157646351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140284225842704234876861801 105213169382028176157646351)
    ·
      refine ⟨157819754073042264236469527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105213169382028176157646351 157819754073042264236469527)
      ·
        refine ⟨236729631109563396354704291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157819754073042264236469527 236729631109563396354704291)
        ·
          refine ⟨355094446664345094532056437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236729631109563396354704291 355094446664345094532056437)
          ·
            refine ⟨33290104374782352612380291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 355094446664345094532056437 33290104374782352612380291)
            ·
              refine ⟨49935156562173528918570437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33290104374782352612380291 49935156562173528918570437)
              ·
                refine ⟨9362841855407536672231957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49935156562173528918570437 9362841855407536672231957)
                ·
                  refine ⟨438883211972228281510873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9362841855407536672231957 438883211972228281510873)
                  ·
                    rfl

theorem cell22_3846249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 6].length) (baseStart_3846249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846249 prefixEnd_3846249 := by exact prefixLift 3846249
  have htrace : WordTrace (prefixWord ++ tailWord_3846249) baseStart_3846249 baseEnd_3846249 := by
    simpa [prefixWord, tailWord_3846249, baseEnd_3846249] using wordTrace_append hprefix tailTrace_3846249
  have hstable : (prefixWord ++ tailWord_3846249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846249).length < 2 ^ (prefixWord ++ tailWord_3846249).sum := by decide
  have hdescent : baseEnd_3846249 < baseStart_3846249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846264 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 3, 5]
def baseStart_3846264 : Nat := 118140960795 + 3846264 * 2 ^ 59
def prefixEnd_3846264 : Nat := 4983230072969 + 3 ^ 40 * 3846264 * 2
def baseEnd_3846264 : Nat := 1316654770723229805407573

theorem tailTrace_3846264 : CollatzResearch.WordTrace tailWord_3846264 prefixEnd_3846264 1316654770723229805407573 := by
  unfold tailWord_3846264
  simp only [CollatzResearch.WordTrace]
  refine ⟨70142386468824946219328923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93523181958433261625771897 70142386468824946219328923)
  ·
    refine ⟨105213579703237419328993385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70142386468824946219328923 105213579703237419328993385)
    ·
      refine ⟨78910184777428064496745039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105213579703237419328993385 78910184777428064496745039)
      ·
        refine ⟨118365277166142096745117559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78910184777428064496745039 118365277166142096745117559)
        ·
          refine ⟨177547915749213145117676339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118365277166142096745117559 177547915749213145117676339)
          ·
            refine ⟨266321873623819717676514509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177547915749213145117676339 266321873623819717676514509)
            ·
              refine ⟨99870702608932394128692941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 266321873623819717676514509 99870702608932394128692941)
              ·
                refine ⟨37451513478349647798259853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99870702608932394128692941 37451513478349647798259853)
                ·
                  refine ⟨14044317554381117924347445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37451513478349647798259853 14044317554381117924347445)
                  ·
                    refine ⟨1316654770723229805407573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14044317554381117924347445 1316654770723229805407573)
                    ·
                      rfl

theorem cell22_3846264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_3846264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846264 prefixEnd_3846264 := by exact prefixLift 3846264
  have htrace : WordTrace (prefixWord ++ tailWord_3846264) baseStart_3846264 baseEnd_3846264 := by
    simpa [prefixWord, tailWord_3846264, baseEnd_3846264] using wordTrace_append hprefix tailTrace_3846264
  have hstable : (prefixWord ++ tailWord_3846264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846264).length < 2 ^ (prefixWord ++ tailWord_3846264).sum := by decide
  have hdescent : baseEnd_3846264 < baseStart_3846264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846281 : List Nat := [1, 2, 1, 1, 4, 2, 1, 3, 4, 3]
def baseStart_3846281 : Nat := 118140960795 + 3846281 * 2 ^ 59
def prefixEnd_3846281 : Nat := 4983230072969 + 3 ^ 40 * 3846281 * 2
def baseEnd_3846281 : Nat := 1316660590170647427732521

theorem tailTrace_3846281 : CollatzResearch.WordTrace tailWord_3846281 prefixEnd_3846281 1316660590170647427732521 := by
  unfold tailWord_3846281
  simp only [CollatzResearch.WordTrace]
  refine ⟨140285392978588304342026697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93523595319058869561351131 140285392978588304342026697)
  ·
    refine ⟨105214044733941228256520023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140285392978588304342026697 105214044733941228256520023)
    ·
      refine ⟨157821067100911842384780035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105214044733941228256520023 157821067100911842384780035)
      ·
        refine ⟨236731600651367763577170053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157821067100911842384780035 236731600651367763577170053)
        ·
          refine ⟨44387175122131455670719385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236731600651367763577170053 44387175122131455670719385)
          ·
            refine ⟨33290381341598591753039539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44387175122131455670719385 33290381341598591753039539)
            ·
              refine ⟨49935572012397887629559309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33290381341598591753039539 49935572012397887629559309)
              ·
                refine ⟨18725839504649207861084741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49935572012397887629559309 18725839504649207861084741)
                ·
                  refine ⟨3511094907121726473953389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18725839504649207861084741 3511094907121726473953389)
                  ·
                    refine ⟨1316660590170647427732521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3511094907121726473953389 1316660590170647427732521)
                    ·
                      rfl

theorem cell22_3846281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 4, 3].length) (baseStart_3846281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846281 prefixEnd_3846281 := by exact prefixLift 3846281
  have htrace : WordTrace (prefixWord ++ tailWord_3846281) baseStart_3846281 baseEnd_3846281 := by
    simpa [prefixWord, tailWord_3846281, baseEnd_3846281] using wordTrace_append hprefix tailTrace_3846281
  have hstable : (prefixWord ++ tailWord_3846281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846281).length < 2 ^ (prefixWord ++ tailWord_3846281).sum := by decide
  have hdescent : baseEnd_3846281 < baseStart_3846281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846302 : List Nat := [4, 3, 1, 1, 3, 2, 1, 2, 1, 4]
def baseStart_3846302 : Nat := 118140960795 + 3846302 * 2 ^ 59
def prefixEnd_3846302 : Nat := 4983230072969 + 3 ^ 40 * 3846302 * 2
def baseEnd_3846302 : Nat := 1316667778899810372957457

theorem tailTrace_3846302 : CollatzResearch.WordTrace tailWord_3846302 prefixEnd_3846302 1316667778899810372957457 := by
  unfold tailWord_3846302
  simp only [CollatzResearch.WordTrace]
  refine ⟨17535769863939028116067645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93524105941008149952360773 17535769863939028116067645)
  ·
    refine ⟨6575913698977135543525367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17535769863939028116067645 6575913698977135543525367)
    ·
      refine ⟨9863870548465703315288051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6575913698977135543525367 9863870548465703315288051)
      ·
        refine ⟨14795805822698554972932077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9863870548465703315288051 14795805822698554972932077)
        ·
          refine ⟨5548427183511958114849529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14795805822698554972932077 5548427183511958114849529)
          ·
            refine ⟨4161320387633968586137147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5548427183511958114849529 4161320387633968586137147)
            ·
              refine ⟨6241980581450952879205721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4161320387633968586137147 6241980581450952879205721)
              ·
                refine ⟨4681485436088214659404291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6241980581450952879205721 4681485436088214659404291)
                ·
                  refine ⟨7022228154132321989106437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4681485436088214659404291 7022228154132321989106437)
                  ·
                    refine ⟨1316667778899810372957457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7022228154132321989106437 1316667778899810372957457)
                    ·
                      rfl

theorem cell22_3846302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_3846302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846302 prefixEnd_3846302 := by exact prefixLift 3846302
  have htrace : WordTrace (prefixWord ++ tailWord_3846302) baseStart_3846302 baseEnd_3846302 := by
    simpa [prefixWord, tailWord_3846302, baseEnd_3846302] using wordTrace_append hprefix tailTrace_3846302
  have hstable : (prefixWord ++ tailWord_3846302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846302).length < 2 ^ (prefixWord ++ tailWord_3846302).sum := by decide
  have hdescent : baseEnd_3846302 < baseStart_3846302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846334 : List Nat := [4, 2, 1, 1, 5, 1, 2, 2, 4]
def baseStart_3846334 : Nat := 118140960795 + 3846334 * 2 ^ 59
def prefixEnd_3846334 : Nat := 4983230072969 + 3 ^ 40 * 3846334 * 2
def baseEnd_3846334 : Nat := 438892911051257652052453

theorem tailTrace_3846334 : CollatzResearch.WordTrace tailWord_3846334 prefixEnd_3846334 438892911051257652052453 := by
  unfold tailWord_3846334
  simp only [CollatzResearch.WordTrace]
  refine ⟨17535915755924536799213257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93524884031597529595804037 17535915755924536799213257)
  ·
    refine ⟨13151936816943402599409943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17535915755924536799213257 13151936816943402599409943)
    ·
      refine ⟨19727905225415103899114915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13151936816943402599409943 19727905225415103899114915)
      ·
        refine ⟨29591857838122655848672373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19727905225415103899114915 29591857838122655848672373)
        ·
          refine ⟨2774236672323998985813035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29591857838122655848672373 2774236672323998985813035)
          ·
            refine ⟨4161355008485998478719553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2774236672323998985813035 4161355008485998478719553)
            ·
              refine ⟨3121016256364498859039665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4161355008485998478719553 3121016256364498859039665)
              ·
                refine ⟨2340762192273374144279749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3121016256364498859039665 2340762192273374144279749)
                ·
                  refine ⟨438892911051257652052453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2340762192273374144279749 438892911051257652052453)
                  ·
                    rfl

theorem cell22_3846334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_3846334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846334 prefixEnd_3846334 := by exact prefixLift 3846334
  have htrace : WordTrace (prefixWord ++ tailWord_3846334) baseStart_3846334 baseEnd_3846334 := by
    simpa [prefixWord, tailWord_3846334, baseEnd_3846334] using wordTrace_append hprefix tailTrace_3846334
  have hstable : (prefixWord ++ tailWord_3846334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846334).length < 2 ^ (prefixWord ++ tailWord_3846334).sum := by decide
  have hdescent : baseEnd_3846334 < baseStart_3846334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846339 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 11]
def baseStart_3846339 : Nat := 118140960795 + 3846339 * 2 ^ 59
def prefixEnd_3846339 : Nat := 4983230072969 + 3 ^ 40 * 3846339 * 2
def baseEnd_3846339 : Nat := 438893481585318203260781

theorem tailTrace_3846339 : CollatzResearch.WordTrace tailWord_3846339 prefixEnd_3846339 438893481585318203260781 := by
  unfold tailWord_3846339
  simp only [CollatzResearch.WordTrace]
  refine ⟨140287508412378180247638071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93525005608252120165092047 140287508412378180247638071)
  ·
    refine ⟨210431262618567270371457107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140287508412378180247638071 210431262618567270371457107)
    ·
      refine ⟨315646893927850905557185661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210431262618567270371457107 315646893927850905557185661)
      ·
        refine ⟨118367585222944089583944623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315646893927850905557185661 118367585222944089583944623)
        ·
          refine ⟨177551377834416134375916935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118367585222944089583944623 177551377834416134375916935)
          ·
            refine ⟨266327066751624201563875403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177551377834416134375916935 266327066751624201563875403)
            ·
              refine ⟨399490600127436302345813105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266327066751624201563875403 399490600127436302345813105)
              ·
                refine ⟨299617950095577226759359829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 399490600127436302345813105 299617950095577226759359829)
                ·
                  refine ⟨438893481585318203260781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 299617950095577226759359829 438893481585318203260781)
                  ·
                    rfl

theorem cell22_3846339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 11].length) (baseStart_3846339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846339 prefixEnd_3846339 := by exact prefixLift 3846339
  have htrace : WordTrace (prefixWord ++ tailWord_3846339) baseStart_3846339 baseEnd_3846339 := by
    simpa [prefixWord, tailWord_3846339, baseEnd_3846339] using wordTrace_append hprefix tailTrace_3846339
  have hstable : (prefixWord ++ tailWord_3846339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846339).length < 2 ^ (prefixWord ++ tailWord_3846339).sum := by decide
  have hdescent : baseEnd_3846339 < baseStart_3846339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846364 : List Nat := [2, 2, 5, 2, 2, 1, 1, 1, 2, 4]
def baseStart_3846364 : Nat := 118140960795 + 3846364 * 2 ^ 59
def prefixEnd_3846364 : Nat := 4983230072969 + 3 ^ 40 * 3846364 * 2
def baseEnd_3846364 : Nat := 1316689002766862877907267

theorem tailTrace_3846364 : CollatzResearch.WordTrace tailWord_3846364 prefixEnd_3846364 1316689002766862877907267 := by
  unfold tailWord_3846364
  simp only [CollatzResearch.WordTrace]
  refine ⟨70144210118643804758649073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93525613491525073011532097 70144210118643804758649073)
  ·
    refine ⟨52608157588982853568986805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70144210118643804758649073 52608157588982853568986805)
    ·
      refine ⟨4932014773967142522092513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52608157588982853568986805 4932014773967142522092513)
      ·
        refine ⟨3699011080475356891569385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4932014773967142522092513 3699011080475356891569385)
        ·
          refine ⟨2774258310356517668677039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3699011080475356891569385 2774258310356517668677039)
          ·
            refine ⟨4161387465534776503015559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2774258310356517668677039 4161387465534776503015559)
            ·
              refine ⟨6242081198302164754523339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4161387465534776503015559 6242081198302164754523339)
              ·
                refine ⟨9363121797453247131785009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6242081198302164754523339 9363121797453247131785009)
                ·
                  refine ⟨7022341348089935348838757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9363121797453247131785009 7022341348089935348838757)
                  ·
                    refine ⟨1316689002766862877907267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7022341348089935348838757 1316689002766862877907267)
                    ·
                      rfl

theorem cell22_3846364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_3846364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846364 prefixEnd_3846364 := by exact prefixLift 3846364
  have htrace : WordTrace (prefixWord ++ tailWord_3846364) baseStart_3846364 baseEnd_3846364 := by
    simpa [prefixWord, tailWord_3846364, baseEnd_3846364] using wordTrace_append hprefix tailTrace_3846364
  have hstable : (prefixWord ++ tailWord_3846364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846364).length < 2 ^ (prefixWord ++ tailWord_3846364).sum := by decide
  have hdescent : baseEnd_3846364 < baseStart_3846364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846407 : List Nat := [1, 1, 4, 5, 1, 1, 3, 1, 5]
def baseStart_3846407 : Nat := 118140960795 + 3846407 * 2 ^ 59
def prefixEnd_3846407 : Nat := 4983230072969 + 3 ^ 40 * 3846407 * 2
def baseEnd_3846407 : Nat := 438901240848541699694045

theorem tailTrace_3846407 : CollatzResearch.WordTrace tailWord_3846407 prefixEnd_3846407 438901240848541699694045 := by
  unfold tailWord_3846407
  simp only [CollatzResearch.WordTrace]
  refine ⟨140289988576131827861113475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93526659050754551907408983 140289988576131827861113475)
  ·
    refine ⟨210434982864197741791670213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140289988576131827861113475 210434982864197741791670213)
    ·
      refine ⟨39456559287037076585938165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210434982864197741791670213 39456559287037076585938165)
      ·
        refine ⟨3699052433159725929931703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39456559287037076585938165 3699052433159725929931703)
        ·
          refine ⟨5548578649739588894897555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3699052433159725929931703 5548578649739588894897555)
          ·
            refine ⟨8322867974609383342346333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5548578649739588894897555 8322867974609383342346333)
            ·
              refine ⟨3121075490478518753379875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8322867974609383342346333 3121075490478518753379875)
              ·
                refine ⟨4681613235717778130069813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3121075490478518753379875 4681613235717778130069813)
                ·
                  refine ⟨438901240848541699694045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4681613235717778130069813 438901240848541699694045)
                  ·
                    rfl

theorem cell22_3846407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 5].length) (baseStart_3846407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846407 prefixEnd_3846407 := by exact prefixLift 3846407
  have htrace : WordTrace (prefixWord ++ tailWord_3846407) baseStart_3846407 baseEnd_3846407 := by
    simpa [prefixWord, tailWord_3846407, baseEnd_3846407] using wordTrace_append hprefix tailTrace_3846407
  have hstable : (prefixWord ++ tailWord_3846407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846407).length < 2 ^ (prefixWord ++ tailWord_3846407).sum := by decide
  have hdescent : baseEnd_3846407 < baseStart_3846407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846433 : List Nat := [1, 2, 3, 2, 1, 1, 3, 2, 4, 3]
def baseStart_3846433 : Nat := 118140960795 + 3846433 * 2 ^ 59
def prefixEnd_3846433 : Nat := 4983230072969 + 3 ^ 40 * 3846433 * 2
def baseEnd_3846433 : Nat := 1316712622876969697932055

theorem tailTrace_3846433 : CollatzResearch.WordTrace tailWord_3846433 prefixEnd_3846433 1316712622876969697932055 := by
  unfold tailWord_3846433
  simp only [CollatzResearch.WordTrace]
  refine ⟨140290936874037634301559953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93527291249358422867706635 140290936874037634301559953)
  ·
    refine ⟨105218202655528225726169965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140290936874037634301559953 105218202655528225726169965)
    ·
      refine ⟨39456825995823084647313737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105218202655528225726169965 39456825995823084647313737)
      ·
        refine ⟨29592619496867313485485303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39456825995823084647313737 29592619496867313485485303)
        ·
          refine ⟨44388929245300970228227955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29592619496867313485485303 44388929245300970228227955)
          ·
            refine ⟨66583393867951455342341933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44388929245300970228227955 66583393867951455342341933)
            ·
              refine ⟨24968772700481795753378225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66583393867951455342341933 24968772700481795753378225)
              ·
                refine ⟨18726579525361346815033669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24968772700481795753378225 18726579525361346815033669)
                ·
                  refine ⟨3511233661005252527818813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18726579525361346815033669 3511233661005252527818813)
                  ·
                    refine ⟨1316712622876969697932055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3511233661005252527818813 1316712622876969697932055)
                    ·
                      rfl

theorem cell22_3846433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_3846433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846433 prefixEnd_3846433 := by exact prefixLift 3846433
  have htrace : WordTrace (prefixWord ++ tailWord_3846433) baseStart_3846433 baseEnd_3846433 := by
    simpa [prefixWord, tailWord_3846433, baseEnd_3846433] using wordTrace_append hprefix tailTrace_3846433
  have hstable : (prefixWord ++ tailWord_3846433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846433).length < 2 ^ (prefixWord ++ tailWord_3846433).sum := by decide
  have hdescent : baseEnd_3846433 < baseStart_3846433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846512 : List Nat := [2, 1, 1, 1, 4, 4, 1, 4, 1, 3]
def baseStart_3846512 : Nat := 118140960795 + 3846512 * 2 ^ 59
def prefixEnd_3846512 : Nat := 4983230072969 + 3 ^ 40 * 3846512 * 2
def baseEnd_3846512 : Nat := 1316739666191439825206813

theorem tailTrace_3846512 : CollatzResearch.WordTrace tailWord_3846512 prefixEnd_3846512 1316739666191439825206813 := by
  unfold tailWord_3846512
  simp only [CollatzResearch.WordTrace]
  refine ⟨70146909120375715396842895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93529212160500953862457193 70146909120375715396842895)
  ·
    refine ⟨105220363680563573095264343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70146909120375715396842895 105220363680563573095264343)
    ·
      refine ⟨157830545520845359642896515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105220363680563573095264343 157830545520845359642896515)
      ·
        refine ⟨236745818281268039464344773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157830545520845359642896515 236745818281268039464344773)
        ·
          refine ⟨44389840927737757399564645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236745818281268039464344773 44389840927737757399564645)
          ·
            refine ⟨8323095173950829512418371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44389840927737757399564645 8323095173950829512418371)
            ·
              refine ⟨12484642760926244268627557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8323095173950829512418371 12484642760926244268627557)
              ·
                refine ⟨2340870517673670800367667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12484642760926244268627557 2340870517673670800367667)
                ·
                  refine ⟨3511305776510506200551501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2340870517673670800367667 3511305776510506200551501)
                  ·
                    refine ⟨1316739666191439825206813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3511305776510506200551501 1316739666191439825206813)
                    ·
                      rfl

theorem cell22_3846512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 4, 1, 3].length) (baseStart_3846512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846512 prefixEnd_3846512 := by exact prefixLift 3846512
  have htrace : WordTrace (prefixWord ++ tailWord_3846512) baseStart_3846512 baseEnd_3846512 := by
    simpa [prefixWord, tailWord_3846512, baseEnd_3846512] using wordTrace_append hprefix tailTrace_3846512
  have hstable : (prefixWord ++ tailWord_3846512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846512).length < 2 ^ (prefixWord ++ tailWord_3846512).sum := by decide
  have hdescent : baseEnd_3846512 < baseStart_3846512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846523 : List Nat := [1, 1, 1, 1, 1, 8, 1, 1, 2, 5]
def baseStart_3846523 : Nat := 118140960795 + 3846523 * 2 ^ 59
def prefixEnd_3846523 : Nat := 4983230072969 + 3 ^ 40 * 3846523 * 2
def baseEnd_3846523 : Nat := 1316743431716239463181779

theorem tailTrace_3846523 : CollatzResearch.WordTrace tailWord_3846523 prefixEnd_3846523 1316743431716239463181779 := by
  unfold tailWord_3846523
  simp only [CollatzResearch.WordTrace]
  refine ⟨140294219443711579672336223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93529479629141053114890815 140294219443711579672336223)
  ·
    refine ⟨210441329165567369508504335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140294219443711579672336223 210441329165567369508504335)
    ·
      refine ⟨315661993748351054262756503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210441329165567369508504335 315661993748351054262756503)
      ·
        refine ⟨473492990622526581394134755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315661993748351054262756503 473492990622526581394134755)
        ·
          refine ⟨710239485933789872091202133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473492990622526581394134755 710239485933789872091202133)
          ·
            refine ⟨8323118975786600063568775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 710239485933789872091202133 8323118975786600063568775)
            ·
              refine ⟨12484678463679900095353163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8323118975786600063568775 12484678463679900095353163)
              ·
                refine ⟨18727017695519850143029745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12484678463679900095353163 18727017695519850143029745)
                ·
                  refine ⟨14045263271639887607272309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18727017695519850143029745 14045263271639887607272309)
                  ·
                    refine ⟨1316743431716239463181779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14045263271639887607272309 1316743431716239463181779)
                    ·
                      rfl

theorem cell22_3846523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 5].length) (baseStart_3846523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846523 prefixEnd_3846523 := by exact prefixLift 3846523
  have htrace : WordTrace (prefixWord ++ tailWord_3846523) baseStart_3846523 baseEnd_3846523 := by
    simpa [prefixWord, tailWord_3846523, baseEnd_3846523] using wordTrace_append hprefix tailTrace_3846523
  have hstable : (prefixWord ++ tailWord_3846523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846523).length < 2 ^ (prefixWord ++ tailWord_3846523).sum := by decide
  have hdescent : baseEnd_3846523 < baseStart_3846523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846583 : List Nat := [1, 1, 3, 1, 3, 3, 1, 2, 1, 6]
def baseStart_3846583 : Nat := 118140960795 + 3846583 * 2 ^ 59
def prefixEnd_3846583 : Nat := 4983230072969 + 3 ^ 40 * 3846583 * 2
def baseEnd_3846583 : Nat := 1316763970942419306681595

theorem tailTrace_3846583 : CollatzResearch.WordTrace tailWord_3846583 prefixEnd_3846583 1316763970942419306681595 := by
  unfold tailWord_3846583
  simp only [CollatzResearch.WordTrace]
  refine ⟨140296407823494209919520403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93530938548996139946346935 140296407823494209919520403)
  ·
    refine ⟨210444611735241314879280605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140296407823494209919520403 210444611735241314879280605)
    ·
      refine ⟨78916729400715493079730227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210444611735241314879280605 78916729400715493079730227)
      ·
        refine ⟨118375094101073239619595341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78916729400715493079730227 118375094101073239619595341)
        ·
          refine ⟨44390660287902464857348253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118375094101073239619595341 44390660287902464857348253)
          ·
            refine ⟨16646497607963424321505595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44390660287902464857348253 16646497607963424321505595)
            ·
              refine ⟨24969746411945136482258393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16646497607963424321505595 24969746411945136482258393)
              ·
                refine ⟨18727309808958852361693795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24969746411945136482258393 18727309808958852361693795)
                ·
                  refine ⟨28090964713438278542540693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18727309808958852361693795 28090964713438278542540693)
                  ·
                    refine ⟨1316763970942419306681595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28090964713438278542540693 1316763970942419306681595)
                    ·
                      rfl

theorem cell22_3846583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_3846583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846583 prefixEnd_3846583 := by exact prefixLift 3846583
  have htrace : WordTrace (prefixWord ++ tailWord_3846583) baseStart_3846583 baseEnd_3846583 := by
    simpa [prefixWord, tailWord_3846583, baseEnd_3846583] using wordTrace_append hprefix tailTrace_3846583
  have hstable : (prefixWord ++ tailWord_3846583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846583).length < 2 ^ (prefixWord ++ tailWord_3846583).sum := by decide
  have hdescent : baseEnd_3846583 < baseStart_3846583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846585 : List Nat := [1, 2, 1, 4, 3, 1, 3, 1, 1, 5]
def baseStart_3846585 : Nat := 118140960795 + 3846585 * 2 ^ 59
def prefixEnd_3846585 : Nat := 4983230072969 + 3 ^ 40 * 3846585 * 2
def baseEnd_3846585 : Nat := 1316764655583291968131589

theorem tailTrace_3846585 : CollatzResearch.WordTrace tailWord_3846585 prefixEnd_3846585 1316764655583291968131589 := by
  unfold tailWord_3846585
  simp only [CollatzResearch.WordTrace]
  refine ⟨140296480769486964261093209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93530987179657976174062139 140296480769486964261093209)
  ·
    refine ⟨105222360577115223195819907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140296480769486964261093209 105222360577115223195819907)
    ·
      refine ⟨157833540865672834793729861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105222360577115223195819907 157833540865672834793729861)
      ·
        refine ⟨29593788912313656523824349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157833540865672834793729861 29593788912313656523824349)
        ·
          refine ⟨11097670842117621196434131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29593788912313656523824349 11097670842117621196434131)
          ·
            refine ⟨16646506263176431794651197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11097670842117621196434131 16646506263176431794651197)
            ·
              refine ⟨6242439848691161922994199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16646506263176431794651197 6242439848691161922994199)
              ·
                refine ⟨9363659773036742884491299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6242439848691161922994199 9363659773036742884491299)
                ·
                  refine ⟨14045489659555114326736949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9363659773036742884491299 14045489659555114326736949)
                  ·
                    refine ⟨1316764655583291968131589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14045489659555114326736949 1316764655583291968131589)
                    ·
                      rfl

theorem cell22_3846585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 5].length) (baseStart_3846585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846585 prefixEnd_3846585 := by exact prefixLift 3846585
  have htrace : WordTrace (prefixWord ++ tailWord_3846585) baseStart_3846585 baseEnd_3846585 := by
    simpa [prefixWord, tailWord_3846585, baseEnd_3846585] using wordTrace_append hprefix tailTrace_3846585
  have hstable : (prefixWord ++ tailWord_3846585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846585).length < 2 ^ (prefixWord ++ tailWord_3846585).sum := by decide
  have hdescent : baseEnd_3846585 < baseStart_3846585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846604 : List Nat := [2, 2, 1, 4, 3, 2, 1, 3, 4]
def baseStart_3846604 : Nat := 118140960795 + 3846604 * 2 ^ 59
def prefixEnd_3846604 : Nat := 4983230072969 + 3 ^ 40 * 3846604 * 2
def baseEnd_3846604 : Nat := 438923719890527417302177

theorem tailTrace_3846604 : CollatzResearch.WordTrace tailWord_3846604 prefixEnd_3846604 438923719890527417302177 := by
  unfold tailWord_3846604
  simp only [CollatzResearch.WordTrace]
  refine ⟨70148586878209065253017433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93531449170945420337356577 70148586878209065253017433)
  ·
    refine ⟨52611440158656798939763075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70148586878209065253017433 52611440158656798939763075)
    ·
      refine ⟨78917160237985198409644613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52611440158656798939763075 78917160237985198409644613)
      ·
        refine ⟨14796967544622224701808365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78917160237985198409644613 14796967544622224701808365)
        ·
          refine ⟨5548862829233334263178137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14796967544622224701808365 5548862829233334263178137)
          ·
            refine ⟨4161647121925000697383603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5548862829233334263178137 4161647121925000697383603)
            ·
              refine ⟨6242470682887501046075405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4161647121925000697383603 6242470682887501046075405)
              ·
                refine ⟨2340926506082812892278277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6242470682887501046075405 2340926506082812892278277)
                ·
                  refine ⟨438923719890527417302177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2340926506082812892278277 438923719890527417302177)
                  ·
                    rfl

theorem cell22_3846604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 3, 4].length) (baseStart_3846604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846604 prefixEnd_3846604 := by exact prefixLift 3846604
  have htrace : WordTrace (prefixWord ++ tailWord_3846604) baseStart_3846604 baseEnd_3846604 := by
    simpa [prefixWord, tailWord_3846604, baseEnd_3846604] using wordTrace_append hprefix tailTrace_3846604
  have hstable : (prefixWord ++ tailWord_3846604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846604).length < 2 ^ (prefixWord ++ tailWord_3846604).sum := by decide
  have hdescent : baseEnd_3846604 < baseStart_3846604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846720 : List Nat := [2, 1, 1, 2, 2, 2, 4, 2, 1, 5]
def baseStart_3846720 : Nat := 118140960795 + 3846720 * 2 ^ 59
def prefixEnd_3846720 : Nat := 4983230072969 + 3 ^ 40 * 3846720 * 2
def baseEnd_3846720 : Nat := 1316810868842196616006175

theorem tailTrace_3846720 : CollatzResearch.WordTrace tailWord_3846720 prefixEnd_3846720 1316810868842196616006175 := by
  unfold tailWord_3846720
  simp only [CollatzResearch.WordTrace]
  refine ⟨70150702311998941158628807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93534269749331921544838409 70150702311998941158628807)
  ·
    refine ⟨105226053467998411737943211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70150702311998941158628807 105226053467998411737943211)
    ·
      refine ⟨157839080201997617606914817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105226053467998411737943211 157839080201997617606914817)
      ·
        refine ⟨118379310151498213205186113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157839080201997617606914817 118379310151498213205186113)
        ·
          refine ⟨88784482613623659903889585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118379310151498213205186113 88784482613623659903889585)
          ·
            refine ⟨66588361960217744927917189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88784482613623659903889585 66588361960217744927917189)
            ·
              refine ⟨12485317867540827173984473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66588361960217744927917189 12485317867540827173984473)
              ·
                refine ⟨9363988400655620380488355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12485317867540827173984473 9363988400655620380488355)
                ·
                  refine ⟨14045982600983430570732533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9363988400655620380488355 14045982600983430570732533)
                  ·
                    refine ⟨1316810868842196616006175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14045982600983430570732533 1316810868842196616006175)
                    ·
                      rfl

theorem cell22_3846720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 1, 5].length) (baseStart_3846720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846720 prefixEnd_3846720 := by exact prefixLift 3846720
  have htrace : WordTrace (prefixWord ++ tailWord_3846720) baseStart_3846720 baseEnd_3846720 := by
    simpa [prefixWord, tailWord_3846720, baseEnd_3846720] using wordTrace_append hprefix tailTrace_3846720
  have hstable : (prefixWord ++ tailWord_3846720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846720).length < 2 ^ (prefixWord ++ tailWord_3846720).sum := by decide
  have hdescent : baseEnd_3846720 < baseStart_3846720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846735 : List Nat := [1, 1, 2, 1, 1, 2, 4, 4, 2, 4]
def baseStart_3846735 : Nat := 118140960795 + 3846735 * 2 ^ 59
def prefixEnd_3846735 : Nat := 4983230072969 + 3 ^ 40 * 3846735 * 2
def baseEnd_3846735 : Nat := 1316816003648741576881129

theorem tailTrace_3846735 : CollatzResearch.WordTrace tailWord_3846735 prefixEnd_3846735 1316816003648741576881129 := by
  unfold tailWord_3846735
  simp only [CollatzResearch.WordTrace]
  refine ⟨140301951718943539879053659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93534634479295693252702439 140301951718943539879053659)
  ·
    refine ⟨210452927578415309818580489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140301951718943539879053659 210452927578415309818580489)
    ·
      refine ⟨157839695683811482363935367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210452927578415309818580489 157839695683811482363935367)
      ·
        refine ⟨236759543525717223545903051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157839695683811482363935367 236759543525717223545903051)
        ·
          refine ⟨355139315288575835318854577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236759543525717223545903051 355139315288575835318854577)
          ·
            refine ⟨266354486466431876489140933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355139315288575835318854577 266354486466431876489140933)
            ·
              refine ⟨49941466212455976841713925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 266354486466431876489140933 49941466212455976841713925)
              ·
                refine ⟨9364024914835495657821361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49941466212455976841713925 9364024914835495657821361)
                ·
                  refine ⟨7023018686126621743366021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9364024914835495657821361 7023018686126621743366021)
                  ·
                    refine ⟨1316816003648741576881129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7023018686126621743366021 1316816003648741576881129)
                    ·
                      rfl

theorem cell22_3846735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 4].length) (baseStart_3846735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846735 prefixEnd_3846735 := by exact prefixLift 3846735
  have htrace : WordTrace (prefixWord ++ tailWord_3846735) baseStart_3846735 baseEnd_3846735 := by
    simpa [prefixWord, tailWord_3846735, baseEnd_3846735] using wordTrace_append hprefix tailTrace_3846735
  have hstable : (prefixWord ++ tailWord_3846735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846735).length < 2 ^ (prefixWord ++ tailWord_3846735).sum := by decide
  have hdescent : baseEnd_3846735 < baseStart_3846735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846737 : List Nat := [1, 2, 2, 1, 3, 4, 1, 1, 4, 3]
def baseStart_3846737 : Nat := 118140960795 + 3846737 * 2 ^ 59
def prefixEnd_3846737 : Nat := 4983230072969 + 3 ^ 40 * 3846737 * 2
def baseEnd_3846737 : Nat := 1316816688289614238331123

theorem tailTrace_3846737 : CollatzResearch.WordTrace tailWord_3846737 prefixEnd_3846737 1316816688289614238331123 := by
  unfold tailWord_3846737
  simp only [CollatzResearch.WordTrace]
  refine ⟨140302024664936294220626465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93534683109957529480417643 140302024664936294220626465)
  ·
    refine ⟨105226518498702220665469849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140302024664936294220626465 105226518498702220665469849)
    ·
      refine ⟨78919888874026665499102387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105226518498702220665469849 78919888874026665499102387)
      ·
        refine ⟨118379833311039998248653581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78919888874026665499102387 118379833311039998248653581)
        ·
          refine ⟨44392437491639999343245093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118379833311039998248653581 44392437491639999343245093)
          ·
            refine ⟨8323582029682499876858455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44392437491639999343245093 8323582029682499876858455)
            ·
              refine ⟨12485373044523749815287683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8323582029682499876858455 12485373044523749815287683)
              ·
                refine ⟨18728059566785624722931525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12485373044523749815287683 18728059566785624722931525)
                ·
                  refine ⟨3511511168772304635549661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18728059566785624722931525 3511511168772304635549661)
                  ·
                    refine ⟨1316816688289614238331123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3511511168772304635549661 1316816688289614238331123)
                    ·
                      rfl

theorem cell22_3846737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 4, 3].length) (baseStart_3846737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846737 prefixEnd_3846737 := by exact prefixLift 3846737
  have htrace : WordTrace (prefixWord ++ tailWord_3846737) baseStart_3846737 baseEnd_3846737 := by
    simpa [prefixWord, tailWord_3846737, baseEnd_3846737] using wordTrace_append hprefix tailTrace_3846737
  have hstable : (prefixWord ++ tailWord_3846737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846737).length < 2 ^ (prefixWord ++ tailWord_3846737).sum := by decide
  have hdescent : baseEnd_3846737 < baseStart_3846737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846773 : List Nat := [1, 3, 4, 2, 3, 1, 1, 3, 4]
def baseStart_3846773 : Nat := 118140960795 + 3846773 * 2 ^ 59
def prefixEnd_3846773 : Nat := 4983230072969 + 3 ^ 40 * 3846773 * 2
def baseEnd_3846773 : Nat := 438943003941774048143671

theorem tailTrace_3846773 : CollatzResearch.WordTrace tailWord_3846773 prefixEnd_3846773 438943003941774048143671 := by
  unfold tailWord_3846773
  simp only [CollatzResearch.WordTrace]
  refine ⟨140303337692805872368936973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93535558461870581579291315 140303337692805872368936973)
  ·
    refine ⟨52613751634802202138351365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140303337692805872368936973 52613751634802202138351365)
    ·
      refine ⟨9865078431525412900940881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52613751634802202138351365 9865078431525412900940881)
      ·
        refine ⟨7398808823644059675705661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9865078431525412900940881 7398808823644059675705661)
        ·
          refine ⟨2774553308866522378389623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7398808823644059675705661 2774553308866522378389623)
          ·
            refine ⟨4161829963299783567584435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2774553308866522378389623 4161829963299783567584435)
            ·
              refine ⟨6242744944949675351376653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4161829963299783567584435 6242744944949675351376653)
              ·
                refine ⟨2341029354356128256766245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6242744944949675351376653 2341029354356128256766245)
                ·
                  refine ⟨438943003941774048143671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2341029354356128256766245 438943003941774048143671)
                  ·
                    rfl

theorem cell22_3846773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 3, 4].length) (baseStart_3846773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846773 prefixEnd_3846773 := by exact prefixLift 3846773
  have htrace : WordTrace (prefixWord ++ tailWord_3846773) baseStart_3846773 baseEnd_3846773 := by
    simpa [prefixWord, tailWord_3846773, baseEnd_3846773] using wordTrace_append hprefix tailTrace_3846773
  have hstable : (prefixWord ++ tailWord_3846773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846773).length < 2 ^ (prefixWord ++ tailWord_3846773).sum := by decide
  have hdescent : baseEnd_3846773 < baseStart_3846773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846861 : List Nat := [1, 6, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_3846861 : Nat := 118140960795 + 3846861 * 2 ^ 59
def prefixEnd_3846861 : Nat := 4983230072969 + 3 ^ 40 * 3846861 * 2
def baseEnd_3846861 : Nat := 1316859136023719248230743

theorem tailTrace_3846861 : CollatzResearch.WordTrace tailWord_3846861 prefixEnd_3846861 1316859136023719248230743 := by
  unfold tailWord_3846861
  simp only [CollatzResearch.WordTrace]
  refine ⟨140306547316487063398140437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93537698210991375598760291 140306547316487063398140437)
  ·
    refine ⟨6576869405460331096787833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 140306547316487063398140437 6576869405460331096787833)
    ·
      refine ⟨4932652054095248322590875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6576869405460331096787833 4932652054095248322590875)
      ·
        refine ⟨7398978081142872483886313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4932652054095248322590875 7398978081142872483886313)
        ·
          refine ⟨5549233560857154362914735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7398978081142872483886313 5549233560857154362914735)
          ·
            refine ⟨8323850341285731544372103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5549233560857154362914735 8323850341285731544372103)
            ·
              refine ⟨12485775511928597316558155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8323850341285731544372103 12485775511928597316558155)
              ·
                refine ⟨18728663267892895974837233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12485775511928597316558155 18728663267892895974837233)
                ·
                  refine ⟨14046497450919671981127925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18728663267892895974837233 14046497450919671981127925)
                  ·
                    refine ⟨1316859136023719248230743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14046497450919671981127925 1316859136023719248230743)
                    ·
                      rfl

theorem cell22_3846861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_3846861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846861 prefixEnd_3846861 := by exact prefixLift 3846861
  have htrace : WordTrace (prefixWord ++ tailWord_3846861) baseStart_3846861 baseEnd_3846861 := by
    simpa [prefixWord, tailWord_3846861, baseEnd_3846861] using wordTrace_append hprefix tailTrace_3846861
  have hstable : (prefixWord ++ tailWord_3846861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846861).length < 2 ^ (prefixWord ++ tailWord_3846861).sum := by decide
  have hdescent : baseEnd_3846861 < baseStart_3846861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846872 : List Nat := [2, 1, 2, 2, 3, 2, 1, 3, 1, 5]
def baseStart_3846872 : Nat := 118140960795 + 3846872 * 2 ^ 59
def prefixEnd_3846872 : Nat := 4983230072969 + 3 ^ 40 * 3846872 * 2
def baseEnd_3846872 : Nat := 1316862901548518886205709

theorem tailTrace_3846872 : CollatzResearch.WordTrace tailWord_3846872 prefixEnd_3846872 1316862901548518886205709 := by
  unfold tailWord_3846872
  simp only [CollatzResearch.WordTrace]
  refine ⟨70153474259723606138395435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93537965679631474851193913 70153474259723606138395435)
  ·
    refine ⟨105230211389585409207593153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70153474259723606138395435 105230211389585409207593153)
    ·
      refine ⟨78922658542189056905694865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105230211389585409207593153 78922658542189056905694865)
      ·
        refine ⟨59191993906641792679271149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78922658542189056905694865 59191993906641792679271149)
        ·
          refine ⟨22196997714990672254726681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59191993906641792679271149 22196997714990672254726681)
          ·
            refine ⟨16647748286243004191045011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22196997714990672254726681 16647748286243004191045011)
            ·
              refine ⟨24971622429364506286567517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16647748286243004191045011 24971622429364506286567517)
              ·
                refine ⟨9364358411011689857462819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24971622429364506286567517 9364358411011689857462819)
                ·
                  refine ⟨14046537616517534786194229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9364358411011689857462819 14046537616517534786194229)
                  ·
                    refine ⟨1316862901548518886205709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14046537616517534786194229 1316862901548518886205709)
                    ·
                      rfl

theorem cell22_3846872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_3846872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846872 prefixEnd_3846872 := by exact prefixLift 3846872
  have htrace : WordTrace (prefixWord ++ tailWord_3846872) baseStart_3846872 baseEnd_3846872 := by
    simpa [prefixWord, tailWord_3846872, baseEnd_3846872] using wordTrace_append hprefix tailTrace_3846872
  have hstable : (prefixWord ++ tailWord_3846872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846872).length < 2 ^ (prefixWord ++ tailWord_3846872).sum := by decide
  have hdescent : baseEnd_3846872 < baseStart_3846872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846902 : List Nat := [5, 1, 1, 1, 1, 2, 11]
def baseStart_3846902 : Nat := 118140960795 + 3846902 * 2 ^ 59
def prefixEnd_3846902 : Nat := 4983230072969 + 3 ^ 40 * 3846902 * 2
def baseEnd_3846902 : Nat := 48773080413392918813171

theorem tailTrace_3846902 : CollatzResearch.WordTrace tailWord_3846902 prefixEnd_3846902 48773080413392918813171 := by
  unfold tailWord_3846902
  simp only [CollatzResearch.WordTrace]
  refine ⟨8769252669333657962523935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93538695139559018266921973 8769252669333657962523935)
  ·
    refine ⟨13153879004000486943785903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8769252669333657962523935 13153879004000486943785903)
    ·
      refine ⟨19730818506000730415678855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13153879004000486943785903 19730818506000730415678855)
      ·
        refine ⟨29596227759001095623518283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19730818506000730415678855 29596227759001095623518283)
        ·
          refine ⟨44394341638501643435277425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29596227759001095623518283 44394341638501643435277425)
          ·
            refine ⟨33295756228876232576458069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44394341638501643435277425 33295756228876232576458069)
            ·
              refine ⟨48773080413392918813171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 33295756228876232576458069 48773080413392918813171)
              ·
                rfl

theorem cell22_3846902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 11].length) (baseStart_3846902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846902 prefixEnd_3846902 := by exact prefixLift 3846902
  have htrace : WordTrace (prefixWord ++ tailWord_3846902) baseStart_3846902 baseEnd_3846902 := by
    simpa [prefixWord, tailWord_3846902, baseEnd_3846902] using wordTrace_append hprefix tailTrace_3846902
  have hstable : (prefixWord ++ tailWord_3846902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846902).length < 2 ^ (prefixWord ++ tailWord_3846902).sum := by decide
  have hdescent : baseEnd_3846902 < baseStart_3846902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846968 : List Nat := [2, 1, 2, 1, 3, 2, 5, 2, 1, 3]
def baseStart_3846968 : Nat := 118140960795 + 3846968 * 2 ^ 59
def prefixEnd_3846968 : Nat := 4983230072969 + 3 ^ 40 * 3846968 * 2
def baseEnd_3846968 : Nat := 1316895764310406635805415

theorem tailTrace_3846968 : CollatzResearch.WordTrace tailWord_3846968 prefixEnd_3846968 1316895764310406635805415 := by
  unfold tailWord_3846968
  simp only [CollatzResearch.WordTrace]
  refine ⟨70155224963549710336142779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93540299951399613781523705 70155224963549710336142779)
  ·
    refine ⟨105232837445324565504214169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70155224963549710336142779 105232837445324565504214169)
    ·
      refine ⟨78924628083993424128160627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105232837445324565504214169 78924628083993424128160627)
      ·
        refine ⟨118386942125990136192240941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78924628083993424128160627 118386942125990136192240941)
        ·
          refine ⟨44395103297246301072090353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118386942125990136192240941 44395103297246301072090353)
          ·
            refine ⟨33296327472934725804067765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44395103297246301072090353 33296327472934725804067765)
            ·
              refine ⟨3121530700587630544131353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33296327472934725804067765 3121530700587630544131353)
              ·
                refine ⟨2341148025440722908098515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3121530700587630544131353 2341148025440722908098515)
                ·
                  refine ⟨3511722038161084362147773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2341148025440722908098515 3511722038161084362147773)
                  ·
                    refine ⟨1316895764310406635805415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3511722038161084362147773 1316895764310406635805415)
                    ·
                      rfl

theorem cell22_3846968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 2, 1, 3].length) (baseStart_3846968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846968 prefixEnd_3846968 := by exact prefixLift 3846968
  have htrace : WordTrace (prefixWord ++ tailWord_3846968) baseStart_3846968 baseEnd_3846968 := by
    simpa [prefixWord, tailWord_3846968, baseEnd_3846968] using wordTrace_append hprefix tailTrace_3846968
  have hstable : (prefixWord ++ tailWord_3846968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846968).length < 2 ^ (prefixWord ++ tailWord_3846968).sum := by decide
  have hdescent : baseEnd_3846968 < baseStart_3846968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846992 : List Nat := [2, 1, 1, 1, 1, 4, 2, 4, 6]
def baseStart_3846992 : Nat := 118140960795 + 3846992 * 2 ^ 59
def prefixEnd_3846992 : Nat := 4983230072969 + 3 ^ 40 * 3846992 * 2
def baseEnd_3846992 : Nat := 438967993333626191068447

theorem tailTrace_3846992 : CollatzResearch.WordTrace tailWord_3846992 prefixEnd_3846992 438967993333626191068447 := by
  unfold tailWord_3846992
  simp only [CollatzResearch.WordTrace]
  refine ⟨70155662639506236385579615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93540883519341648514106153 70155662639506236385579615)
  ·
    refine ⟨105233493959259354578369423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70155662639506236385579615 105233493959259354578369423)
    ·
      refine ⟨157850240938889031867554135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105233493959259354578369423 157850240938889031867554135)
      ·
        refine ⟨236775361408333547801331203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157850240938889031867554135 236775361408333547801331203)
        ·
          refine ⟨355163042112500321701996805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236775361408333547801331203 355163042112500321701996805)
          ·
            refine ⟨66593070396093810319124401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 355163042112500321701996805 66593070396093810319124401)
            ·
              refine ⟨49944802797070357739343301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66593070396093810319124401 49944802797070357739343301)
              ·
                refine ⟨9364650524450692076126869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49944802797070357739343301 9364650524450692076126869)
                ·
                  refine ⟨438967993333626191068447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9364650524450692076126869 438967993333626191068447)
                  ·
                    rfl

theorem cell22_3846992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 6].length) (baseStart_3846992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846992 prefixEnd_3846992 := by exact prefixLift 3846992
  have htrace : WordTrace (prefixWord ++ tailWord_3846992) baseStart_3846992 baseEnd_3846992 := by
    simpa [prefixWord, tailWord_3846992, baseEnd_3846992] using wordTrace_append hprefix tailTrace_3846992
  have hstable : (prefixWord ++ tailWord_3846992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846992).length < 2 ^ (prefixWord ++ tailWord_3846992).sum := by decide
  have hdescent : baseEnd_3846992 < baseStart_3846992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846994 : List Nat := [3, 2, 2, 1, 1, 2, 3, 1, 3, 4]
def baseStart_3846994 : Nat := 118140960795 + 3846994 * 2 ^ 59
def prefixEnd_3846994 : Nat := 4983230072969 + 3 ^ 40 * 3846994 * 2
def baseEnd_3846994 : Nat := 1316904664641751234655335

theorem tailTrace_3846994 : CollatzResearch.WordTrace tailWord_3846994 prefixEnd_3846994 1316904664641751234655335 := by
  unfold tailWord_3846994
  simp only [CollatzResearch.WordTrace]
  refine ⟨35077849556251306778183009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93540932150003484741821357 35077849556251306778183009)
  ·
    refine ⟨26308387167188480083637257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35077849556251306778183009 26308387167188480083637257)
    ·
      refine ⟨19731290375391360062727943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26308387167188480083637257 19731290375391360062727943)
      ·
        refine ⟨29596935563087040094091915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19731290375391360062727943 29596935563087040094091915)
        ·
          refine ⟨44395403344630560141137873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29596935563087040094091915 44395403344630560141137873)
          ·
            refine ⟨33296552508472920105853405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44395403344630560141137873 33296552508472920105853405)
            ·
              refine ⟨12486207190677345039695027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33296552508472920105853405 12486207190677345039695027)
              ·
                refine ⟨18729310786016017559542541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12486207190677345039695027 18729310786016017559542541)
                ·
                  refine ⟨7023491544756006584828453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18729310786016017559542541 7023491544756006584828453)
                  ·
                    refine ⟨1316904664641751234655335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7023491544756006584828453 1316904664641751234655335)
                    ·
                      rfl

theorem cell22_3846994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_3846994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3846994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3846994 prefixEnd_3846994 := by exact prefixLift 3846994
  have htrace : WordTrace (prefixWord ++ tailWord_3846994) baseStart_3846994 baseEnd_3846994 := by
    simpa [prefixWord, tailWord_3846994, baseEnd_3846994] using wordTrace_append hprefix tailTrace_3846994
  have hstable : (prefixWord ++ tailWord_3846994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846994).length < 2 ^ (prefixWord ++ tailWord_3846994).sum := by decide
  have hdescent : baseEnd_3846994 < baseStart_3846994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847024 : List Nat := [2, 1, 1, 1, 4, 1, 2, 3, 4, 3]
def baseStart_3847024 : Nat := 118140960795 + 3847024 * 2 ^ 59
def prefixEnd_3847024 : Nat := 4983230072969 + 3 ^ 40 * 3847024 * 2
def baseEnd_3847024 : Nat := 1316914934254841156405243

theorem tailTrace_3847024 : CollatzResearch.WordTrace tailWord_3847024 prefixEnd_3847024 1316914934254841156405243 := by
  unfold tailWord_3847024
  simp only [CollatzResearch.WordTrace]
  refine ⟨70156246207448271118162063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93541661609931028157549417 70156246207448271118162063)
  ·
    refine ⟨105234369311172406677243095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70156246207448271118162063 105234369311172406677243095)
    ·
      refine ⟨157851553966758610015864643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105234369311172406677243095 157851553966758610015864643)
      ·
        refine ⟨236777330950137915023796965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157851553966758610015864643 236777330950137915023796965)
        ·
          refine ⟨44395749553150859066961931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236777330950137915023796965 44395749553150859066961931)
          ·
            refine ⟨66593624329726288600442897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44395749553150859066961931 66593624329726288600442897)
            ·
              refine ⟨49945218247294716450332173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66593624329726288600442897 49945218247294716450332173)
              ·
                refine ⟨18729456842735518668874565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49945218247294716450332173 18729456842735518668874565)
                ·
                  refine ⟨3511773158012909750413981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18729456842735518668874565 3511773158012909750413981)
                  ·
                    refine ⟨1316914934254841156405243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3511773158012909750413981 1316914934254841156405243)
                    ·
                      rfl

theorem cell22_3847024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 4, 3].length) (baseStart_3847024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847024 prefixEnd_3847024 := by exact prefixLift 3847024
  have htrace : WordTrace (prefixWord ++ tailWord_3847024) baseStart_3847024 baseEnd_3847024 := by
    simpa [prefixWord, tailWord_3847024, baseEnd_3847024] using wordTrace_append hprefix tailTrace_3847024
  have hstable : (prefixWord ++ tailWord_3847024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847024).length < 2 ^ (prefixWord ++ tailWord_3847024).sum := by decide
  have hdescent : baseEnd_3847024 < baseStart_3847024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847062 : List Nat := [5, 3, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_3847062 : Nat := 118140960795 + 3847062 * 2 ^ 59
def prefixEnd_3847062 : Nat := 4983230072969 + 3 ^ 40 * 3847062 * 2
def baseEnd_3847062 : Nat := 1316927942431421723955127

theorem tailTrace_3847062 : CollatzResearch.WordTrace tailWord_3847062 prefixEnd_3847062 1316927942431421723955127 := by
  unfold tailWord_3847062
  simp only [CollatzResearch.WordTrace]
  refine ⟨8769617399297429670387965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93542585592505916484138293 8769617399297429670387965)
  ·
    refine ⟨3288606524736536126395487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8769617399297429670387965 3288606524736536126395487)
    ·
      refine ⟨4932909787104804189593231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3288606524736536126395487 4932909787104804189593231)
      ·
        refine ⟨7399364680657206284389847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4932909787104804189593231 7399364680657206284389847)
        ·
          refine ⟨11099047020985809426584771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7399364680657206284389847 11099047020985809426584771)
          ·
            refine ⟨16648570531478714139877157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11099047020985809426584771 16648570531478714139877157)
            ·
              refine ⟨3121606974652258901226967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16648570531478714139877157 3121606974652258901226967)
              ·
                refine ⟨4682410461978388351840451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3121606974652258901226967 4682410461978388351840451)
                ·
                  refine ⟨7023615692967582527760677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4682410461978388351840451 7023615692967582527760677)
                  ·
                    refine ⟨1316927942431421723955127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7023615692967582527760677 1316927942431421723955127)
                    ·
                      rfl

theorem cell22_3847062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_3847062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847062 prefixEnd_3847062 := by exact prefixLift 3847062
  have htrace : WordTrace (prefixWord ++ tailWord_3847062) baseStart_3847062 baseEnd_3847062 := by
    simpa [prefixWord, tailWord_3847062, baseEnd_3847062] using wordTrace_append hprefix tailTrace_3847062
  have hstable : (prefixWord ++ tailWord_3847062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847062).length < 2 ^ (prefixWord ++ tailWord_3847062).sum := by decide
  have hdescent : baseEnd_3847062 < baseStart_3847062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847092 : List Nat := [2, 5, 2, 1, 1, 2, 3, 1, 2, 3]
def baseStart_3847092 : Nat := 118140960795 + 3847092 * 2 ^ 59
def prefixEnd_3847092 : Nat := 4983230072969 + 3 ^ 40 * 3847092 * 2
def baseEnd_3847092 : Nat := 1316938212044511645705035

theorem tailTrace_3847092 : CollatzResearch.WordTrace tailWord_3847092 prefixEnd_3847092 1316938212044511645705035 := by
  unfold tailWord_3847092
  simp only [CollatzResearch.WordTrace]
  refine ⟨70157486289325094924899765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93543315052433459899866353 70157486289325094924899765)
  ·
    refine ⟨6577264339624227649209353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70157486289325094924899765 6577264339624227649209353)
    ·
      refine ⟨4932948254718170736907015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6577264339624227649209353 4932948254718170736907015)
      ·
        refine ⟨7399422382077256105360523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4932948254718170736907015 7399422382077256105360523)
        ·
          refine ⟨11099133573115884158040785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7399422382077256105360523 11099133573115884158040785)
          ·
            refine ⟨8324350179836913118530589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11099133573115884158040785 8324350179836913118530589)
            ·
              refine ⟨3121631317438842419448971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8324350179836913118530589 3121631317438842419448971)
              ·
                refine ⟨4682446976158263629173457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3121631317438842419448971 4682446976158263629173457)
                ·
                  refine ⟨3511835232118697721880093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4682446976158263629173457 3511835232118697721880093)
                  ·
                    refine ⟨1316938212044511645705035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3511835232118697721880093 1316938212044511645705035)
                    ·
                      rfl

theorem cell22_3847092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_3847092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847092 prefixEnd_3847092 := by exact prefixLift 3847092
  have htrace : WordTrace (prefixWord ++ tailWord_3847092) baseStart_3847092 baseEnd_3847092 := by
    simpa [prefixWord, tailWord_3847092, baseEnd_3847092] using wordTrace_append hprefix tailTrace_3847092
  have hstable : (prefixWord ++ tailWord_3847092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847092).length < 2 ^ (prefixWord ++ tailWord_3847092).sum := by decide
  have hdescent : baseEnd_3847092 < baseStart_3847092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847150 : List Nat := [4, 1, 2, 1, 4, 2, 2, 1, 5]
def baseStart_3847150 : Nat := 118140960795 + 3847150 * 2 ^ 59
def prefixEnd_3847150 : Nat := 4983230072969 + 3 ^ 40 * 3847150 * 2
def baseEnd_3847150 : Nat := 438986022209939609251619

theorem tailTrace_3847150 : CollatzResearch.WordTrace tailWord_3847150 prefixEnd_3847150 438986022209939609251619 := by
  unfold tailWord_3847150
  simp only [CollatzResearch.WordTrace]
  refine ⟨17539636001555008219426363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93544725341626710503607269 17539636001555008219426363)
  ·
    refine ⟨26309454002332512329139545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17539636001555008219426363 26309454002332512329139545)
    ·
      refine ⟨19732090501749384246854659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26309454002332512329139545 19732090501749384246854659)
      ·
        refine ⟨29598135752624076370281989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19732090501749384246854659 29598135752624076370281989)
        ·
          refine ⟨5549650453617014319427873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29598135752624076370281989 5549650453617014319427873)
          ·
            refine ⟨4162237840212760739570905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5549650453617014319427873 4162237840212760739570905)
            ·
              refine ⟨3121678380159570554678179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4162237840212760739570905 3121678380159570554678179)
              ·
                refine ⟨4682517570239355832017269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3121678380159570554678179 4682517570239355832017269)
                ·
                  refine ⟨438986022209939609251619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4682517570239355832017269 438986022209939609251619)
                  ·
                    rfl

theorem cell22_3847150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_3847150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847150 prefixEnd_3847150 := by exact prefixLift 3847150
  have htrace : WordTrace (prefixWord ++ tailWord_3847150) baseStart_3847150 baseEnd_3847150 := by
    simpa [prefixWord, tailWord_3847150, baseEnd_3847150] using wordTrace_append hprefix tailTrace_3847150
  have hstable : (prefixWord ++ tailWord_3847150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847150).length < 2 ^ (prefixWord ++ tailWord_3847150).sum := by decide
  have hdescent : baseEnd_3847150 < baseStart_3847150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847176 : List Nat := [2, 1, 3, 2, 1, 4, 1, 2, 1, 5]
def baseStart_3847176 : Nat := 118140960795 + 3847176 * 2 ^ 59
def prefixEnd_3847176 : Nat := 4983230072969 + 3 ^ 40 * 3847176 * 2
def baseEnd_3847176 : Nat := 1316966966961163426604777

theorem tailTrace_3847176 : CollatzResearch.WordTrace tailWord_3847176 prefixEnd_3847176 1316966966961163426604777 := by
  unfold tailWord_3847176
  simp only [CollatzResearch.WordTrace]
  refine ⟨70159018155172936097928691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93545357540230581463904921 70159018155172936097928691)
  ·
    refine ⟨105238527232759404146893037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70159018155172936097928691 105238527232759404146893037)
    ·
      refine ⟨39464447712284776555084889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105238527232759404146893037 39464447712284776555084889)
      ·
        refine ⟨29598335784213582416313667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39464447712284776555084889 29598335784213582416313667)
        ·
          refine ⟨44397503676320373624470501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29598335784213582416313667 44397503676320373624470501)
          ·
            refine ⟨8324531939310070054588219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44397503676320373624470501 8324531939310070054588219)
            ·
              refine ⟨12486797908965105081882329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8324531939310070054588219 12486797908965105081882329)
              ·
                refine ⟨9365098431723828811411747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12486797908965105081882329 9365098431723828811411747)
                ·
                  refine ⟨14047647647585743217117621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9365098431723828811411747 14047647647585743217117621)
                  ·
                    refine ⟨1316966966961163426604777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14047647647585743217117621 1316966966961163426604777)
                    ·
                      rfl

theorem cell22_3847176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_3847176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847176 prefixEnd_3847176 := by exact prefixLift 3847176
  have htrace : WordTrace (prefixWord ++ tailWord_3847176) baseStart_3847176 baseEnd_3847176 := by
    simpa [prefixWord, tailWord_3847176, baseEnd_3847176] using wordTrace_append hprefix tailTrace_3847176
  have hstable : (prefixWord ++ tailWord_3847176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847176).length < 2 ^ (prefixWord ++ tailWord_3847176).sum := by decide
  have hdescent : baseEnd_3847176 < baseStart_3847176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847189 : List Nat := [1, 3, 2, 1, 4, 11]
def baseStart_3847189 : Nat := 118140960795 + 3847189 * 2 ^ 59
def prefixEnd_3847189 : Nat := 4983230072969 + 3 ^ 40 * 3847189 * 2
def baseEnd_3847189 : Nat := 16258906384281922543577

theorem tailTrace_3847189 : CollatzResearch.WordTrace tailWord_3847189 prefixEnd_3847189 16258906384281922543577 := by
  unfold tailWord_3847189
  simp only [CollatzResearch.WordTrace]
  refine ⟨140318510459298775416080621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93545673639532516944053747 140318510459298775416080621)
  ·
    refine ⟨52619441422237040781030233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140318510459298775416080621 52619441422237040781030233)
    ·
      refine ⟨39464581066677780585772675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52619441422237040781030233 39464581066677780585772675)
      ·
        refine ⟨59196871600016670878659013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39464581066677780585772675 59196871600016670878659013)
        ·
          refine ⟨11099413425003125789748565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59196871600016670878659013 11099413425003125789748565)
          ·
            refine ⟨16258906384281922543577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11099413425003125789748565 16258906384281922543577)
            ·
              rfl

theorem cell22_3847189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 11].length) (baseStart_3847189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847189 prefixEnd_3847189 := by exact prefixLift 3847189
  have htrace : WordTrace (prefixWord ++ tailWord_3847189) baseStart_3847189 baseEnd_3847189 := by
    simpa [prefixWord, tailWord_3847189, baseEnd_3847189] using wordTrace_append hprefix tailTrace_3847189
  have hstable : (prefixWord ++ tailWord_3847189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847189).length < 2 ^ (prefixWord ++ tailWord_3847189).sum := by decide
  have hdescent : baseEnd_3847189 < baseStart_3847189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847219 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 4, 6]
def baseStart_3847219 : Nat := 118140960795 + 3847219 * 2 ^ 59
def prefixEnd_3847219 : Nat := 4983230072969 + 3 ^ 40 * 3847219 * 2
def baseEnd_3847219 : Nat := 1316981686739925647779645

theorem tailTrace_3847219 : CollatzResearch.WordTrace tailWord_3847219 prefixEnd_3847219 1316981686739925647779645 := by
  unfold tailWord_3847219
  simp only [CollatzResearch.WordTrace]
  refine ⟨140319604649190090539672711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93546403099460060359781807 140319604649190090539672711)
  ·
    refine ⟨210479406973785135809509067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140319604649190090539672711 210479406973785135809509067)
    ·
      refine ⟨315719110460677703714263601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210479406973785135809509067 315719110460677703714263601)
      ·
        refine ⟨236789332845508277785697701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315719110460677703714263601 236789332845508277785697701)
        ·
          refine ⟨44397999908532802084818319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236789332845508277785697701 44397999908532802084818319)
          ·
            refine ⟨66596999862799203127227479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44397999908532802084818319 66596999862799203127227479)
            ·
              refine ⟨99895499794198804690841219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66596999862799203127227479 99895499794198804690841219)
              ·
                refine ⟨149843249691298207036261829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99895499794198804690841219 149843249691298207036261829)
                ·
                  refine ⟨28095609317118413819299093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149843249691298207036261829 28095609317118413819299093)
                  ·
                    refine ⟨1316981686739925647779645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28095609317118413819299093 1316981686739925647779645)
                    ·
                      rfl

theorem cell22_3847219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 6].length) (baseStart_3847219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847219 prefixEnd_3847219 := by exact prefixLift 3847219
  have htrace : WordTrace (prefixWord ++ tailWord_3847219) baseStart_3847219 baseEnd_3847219 := by
    simpa [prefixWord, tailWord_3847219, baseEnd_3847219] using wordTrace_append hprefix tailTrace_3847219
  have hstable : (prefixWord ++ tailWord_3847219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847219).length < 2 ^ (prefixWord ++ tailWord_3847219).sum := by decide
  have hdescent : baseEnd_3847219 < baseStart_3847219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847289 : List Nat := [1, 2, 1, 3, 6, 1, 1, 3, 1, 3]
def baseStart_3847289 : Nat := 118140960795 + 3847289 * 2 ^ 59
def prefixEnd_3847289 : Nat := 4983230072969 + 3 ^ 40 * 3847289 * 2
def baseEnd_3847289 : Nat := 1317005649170468798529431

theorem tailTrace_3847289 : CollatzResearch.WordTrace tailWord_3847289 prefixEnd_3847289 1317005649170468798529431 := by
  unfold tailWord_3847289
  simp only [CollatzResearch.WordTrace]
  refine ⟨140322157758936492494720921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93548105172624328329813947 140322157758936492494720921)
  ·
    refine ⟨105241618319202369371040691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140322157758936492494720921 105241618319202369371040691)
    ·
      refine ⟨157862427478803554056561037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105241618319202369371040691 157862427478803554056561037)
      ·
        refine ⟨59198410304551332771210389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157862427478803554056561037 59198410304551332771210389)
        ·
          refine ⟨2774925483025843723650487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 59198410304551332771210389 2774925483025843723650487)
          ·
            refine ⟨4162388224538765585475731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2774925483025843723650487 4162388224538765585475731)
            ·
              refine ⟨6243582336808148378213597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4162388224538765585475731 6243582336808148378213597)
              ·
                refine ⟨2341343376303055641830099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6243582336808148378213597 2341343376303055641830099)
                ·
                  refine ⟨3512015064454583462745149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2341343376303055641830099 3512015064454583462745149)
                  ·
                    refine ⟨1317005649170468798529431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3512015064454583462745149 1317005649170468798529431)
                    ·
                      rfl

theorem cell22_3847289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 3, 1, 3].length) (baseStart_3847289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847289 prefixEnd_3847289 := by exact prefixLift 3847289
  have htrace : WordTrace (prefixWord ++ tailWord_3847289) baseStart_3847289 baseEnd_3847289 := by
    simpa [prefixWord, tailWord_3847289, baseEnd_3847289] using wordTrace_append hprefix tailTrace_3847289
  have hstable : (prefixWord ++ tailWord_3847289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847289).length < 2 ^ (prefixWord ++ tailWord_3847289).sum := by decide
  have hdescent : baseEnd_3847289 < baseStart_3847289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847364 : List Nat := [2, 3, 3, 1, 3, 2, 2, 2, 4]
def baseStart_3847364 : Nat := 118140960795 + 3847364 * 2 ^ 59
def prefixEnd_3847364 : Nat := 4983230072969 + 3 ^ 40 * 3847364 * 2
def baseEnd_3847364 : Nat := 439010441067731200968067

theorem tailTrace_3847364 : CollatzResearch.WordTrace tailWord_3847364 prefixEnd_3847364 439010441067731200968067 := by
  unfold tailWord_3847364
  simp only [CollatzResearch.WordTrace]
  refine ⟨70162446616832390151850573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93549928822443186869134097 70162446616832390151850573)
  ·
    refine ⟨26310917481312146306943965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70162446616832390151850573 26310917481312146306943965)
    ·
      refine ⟨9866594055492054865103987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26310917481312146306943965 9866594055492054865103987)
      ·
        refine ⟨14799891083238082297655981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9866594055492054865103987 14799891083238082297655981)
        ·
          refine ⟨5549959156214280861620993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14799891083238082297655981 5549959156214280861620993)
          ·
            refine ⟨4162469367160710646215745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5549959156214280861620993 4162469367160710646215745)
            ·
              refine ⟨3121852025370532984661809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4162469367160710646215745 3121852025370532984661809)
              ·
                refine ⟨2341389019027899738496357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3121852025370532984661809 2341389019027899738496357)
                ·
                  refine ⟨439010441067731200968067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2341389019027899738496357 439010441067731200968067)
                  ·
                    rfl

theorem cell22_3847364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_3847364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847364 prefixEnd_3847364 := by exact prefixLift 3847364
  have htrace : WordTrace (prefixWord ++ tailWord_3847364) baseStart_3847364 baseEnd_3847364 := by
    simpa [prefixWord, tailWord_3847364, baseEnd_3847364] using wordTrace_append hprefix tailTrace_3847364
  have hstable : (prefixWord ++ tailWord_3847364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847364).length < 2 ^ (prefixWord ++ tailWord_3847364).sum := by decide
  have hdescent : baseEnd_3847364 < baseStart_3847364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847386 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 9]
def baseStart_3847386 : Nat := 118140960795 + 3847386 * 2 ^ 59
def prefixEnd_3847386 : Nat := 4983230072969 + 3 ^ 40 * 3847386 * 2
def baseEnd_3847386 : Nat := 439012951417597626284711

theorem tailTrace_3847386 : CollatzResearch.WordTrace tailWord_3847386 prefixEnd_3847386 439012951417597626284711 := by
  unfold tailWord_3847386
  simp only [CollatzResearch.WordTrace]
  refine ⟨35081423909896269515250503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93550463759723385374001341 35081423909896269515250503)
  ·
    refine ⟨52622135864844404272875755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35081423909896269515250503 52622135864844404272875755)
    ·
      refine ⟨78933203797266606409313633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52622135864844404272875755 78933203797266606409313633)
      ·
        refine ⟨59199902847949954806985225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78933203797266606409313633 59199902847949954806985225)
        ·
          refine ⟨44399927135962466105238919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59199902847949954806985225 44399927135962466105238919)
          ·
            refine ⟨66599890703943699157858379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44399927135962466105238919 66599890703943699157858379)
            ·
              refine ⟨99899836055915548736787569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66599890703943699157858379 99899836055915548736787569)
              ·
                refine ⟨74924877041936661552590677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99899836055915548736787569 74924877041936661552590677)
                ·
                  refine ⟨439012951417597626284711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74924877041936661552590677 439012951417597626284711)
                  ·
                    rfl

theorem cell22_3847386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 9].length) (baseStart_3847386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847386 prefixEnd_3847386 := by exact prefixLift 3847386
  have htrace : WordTrace (prefixWord ++ tailWord_3847386) baseStart_3847386 baseEnd_3847386 := by
    simpa [prefixWord, tailWord_3847386, baseEnd_3847386] using wordTrace_append hprefix tailTrace_3847386
  have hstable : (prefixWord ++ tailWord_3847386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847386).length < 2 ^ (prefixWord ++ tailWord_3847386).sum := by decide
  have hdescent : baseEnd_3847386 < baseStart_3847386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847401 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 6, 5]
def baseStart_3847401 : Nat := 118140960795 + 3847401 * 2 ^ 59
def prefixEnd_3847401 : Nat := 4983230072969 + 3 ^ 40 * 3847401 * 2
def baseEnd_3847401 : Nat := 1317043989059337839729087

theorem tailTrace_3847401 : CollatzResearch.WordTrace tailWord_3847401 prefixEnd_3847401 1317043989059337839729087 := by
  unfold tailWord_3847401
  simp only [CollatzResearch.WordTrace]
  refine ⟨140326242734530735622798057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93550828489687157081865371 140326242734530735622798057)
  ·
    refine ⟨105244682050898051717098543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140326242734530735622798057 105244682050898051717098543)
    ·
      refine ⟨157867023076347077575647815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105244682050898051717098543 157867023076347077575647815)
      ·
        refine ⟨236800534614520616363471723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157867023076347077575647815 236800534614520616363471723)
        ·
          refine ⟨355200801921780924545207585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236800534614520616363471723 355200801921780924545207585)
          ·
            refine ⟨266400601441335693408905689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355200801921780924545207585 266400601441335693408905689)
            ·
              refine ⟨199800451081001770056679267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266400601441335693408905689 199800451081001770056679267)
              ·
                refine ⟨299700676621502655085018901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199800451081001770056679267 299700676621502655085018901)
                ·
                  refine ⟨14048469216632936957110261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 299700676621502655085018901 14048469216632936957110261)
                  ·
                    refine ⟨1317043989059337839729087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14048469216632936957110261 1317043989059337839729087)
                    ·
                      rfl

theorem cell22_3847401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 5].length) (baseStart_3847401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847401 prefixEnd_3847401 := by exact prefixLift 3847401
  have htrace : WordTrace (prefixWord ++ tailWord_3847401) baseStart_3847401 baseEnd_3847401 := by
    simpa [prefixWord, tailWord_3847401, baseEnd_3847401] using wordTrace_append hprefix tailTrace_3847401
  have hstable : (prefixWord ++ tailWord_3847401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847401).length < 2 ^ (prefixWord ++ tailWord_3847401).sum := by decide
  have hdescent : baseEnd_3847401 < baseStart_3847401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847448 : List Nat := [2, 1, 2, 3, 1, 3, 2, 2, 6]
def baseStart_3847448 : Nat := 118140960795 + 3847448 * 2 ^ 59
def prefixEnd_3847448 : Nat := 4983230072969 + 3 ^ 40 * 3847448 * 2
def baseEnd_3847448 : Nat := 439020026039948461267981

theorem tailTrace_3847448 : CollatzResearch.WordTrace tailWord_3847448 prefixEnd_3847448 439020026039948461267981 := by
  unfold tailWord_3847448
  simp only [CollatzResearch.WordTrace]
  refine ⟨70163978482680231324879499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93551971310240308433172665 70163978482680231324879499)
  ·
    refine ⟨105245967724020346987319249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70163978482680231324879499 105245967724020346987319249)
    ·
      refine ⟨78934475793015260240489437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105245967724020346987319249 78934475793015260240489437)
      ·
        refine ⟨29600428422380722590183539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78934475793015260240489437 29600428422380722590183539)
        ·
          refine ⟨44400642633571083885275309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29600428422380722590183539 44400642633571083885275309)
          ·
            refine ⟨16650240987589156456978241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44400642633571083885275309 16650240987589156456978241)
            ·
              refine ⟨12487680740691867342733681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16650240987589156456978241 12487680740691867342733681)
              ·
                refine ⟨9365760555518900507050261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12487680740691867342733681 9365760555518900507050261)
                ·
                  refine ⟨439020026039948461267981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9365760555518900507050261 439020026039948461267981)
                  ·
                    rfl

theorem cell22_3847448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 6].length) (baseStart_3847448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847448 prefixEnd_3847448 := by exact prefixLift 3847448
  have htrace : WordTrace (prefixWord ++ tailWord_3847448) baseStart_3847448 baseEnd_3847448 := by
    simpa [prefixWord, tailWord_3847448, baseEnd_3847448] using wordTrace_append hprefix tailTrace_3847448
  have hstable : (prefixWord ++ tailWord_3847448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847448).length < 2 ^ (prefixWord ++ tailWord_3847448).sum := by decide
  have hdescent : baseEnd_3847448 < baseStart_3847448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847450 : List Nat := [3, 1, 1, 3, 3, 1, 1, 4, 1, 4]
def baseStart_3847450 : Nat := 118140960795 + 3847450 * 2 ^ 59
def prefixEnd_3847450 : Nat := 4983230072969 + 3 ^ 40 * 3847450 * 2
def baseEnd_3847450 : Nat := 1317060762760718045253937

theorem tailTrace_3847450 : CollatzResearch.WordTrace tailWord_3847450 prefixEnd_3847450 1317060762760718045253937 := by
  unfold tailWord_3847450
  simp only [CollatzResearch.WordTrace]
  refine ⟨35082007477838304247832951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93552019940902144660887869 35082007477838304247832951)
  ·
    refine ⟨52623011216757456371749427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35082007477838304247832951 52623011216757456371749427)
    ·
      refine ⟨78934516825136184557624141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52623011216757456371749427 78934516825136184557624141)
      ·
        refine ⟨29600443809426069209109053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78934516825136184557624141 29600443809426069209109053)
        ·
          refine ⟨11100166428534775953415895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29600443809426069209109053 11100166428534775953415895)
          ·
            refine ⟨16650249642802163930123843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11100166428534775953415895 16650249642802163930123843)
            ·
              refine ⟨24975374464203245895185765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16650249642802163930123843 24975374464203245895185765)
              ·
                refine ⟨4682882712038108605347331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24975374464203245895185765 4682882712038108605347331)
                ·
                  refine ⟨7024324068057162908020997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4682882712038108605347331 7024324068057162908020997)
                  ·
                    refine ⟨1317060762760718045253937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7024324068057162908020997 1317060762760718045253937)
                    ·
                      rfl

theorem cell22_3847450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_3847450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847450 prefixEnd_3847450 := by exact prefixLift 3847450
  have htrace : WordTrace (prefixWord ++ tailWord_3847450) baseStart_3847450 baseEnd_3847450 := by
    simpa [prefixWord, tailWord_3847450, baseEnd_3847450] using wordTrace_append hprefix tailTrace_3847450
  have hstable : (prefixWord ++ tailWord_3847450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847450).length < 2 ^ (prefixWord ++ tailWord_3847450).sum := by decide
  have hdescent : baseEnd_3847450 < baseStart_3847450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847480 : List Nat := [2, 1, 2, 1, 3, 1, 1, 6, 2, 3]
def baseStart_3847480 : Nat := 118140960795 + 3847480 * 2 ^ 59
def prefixEnd_3847480 : Nat := 4983230072969 + 3 ^ 40 * 3847480 * 2
def baseEnd_3847480 : Nat := 1317071032373807967003845

theorem tailTrace_3847480 : CollatzResearch.WordTrace tailWord_3847480 prefixEnd_3847480 1317071032373807967003845 := by
  unfold tailWord_3847480
  simp only [CollatzResearch.WordTrace]
  refine ⟨70164562050622266057461947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93552749400829688076615929 70164562050622266057461947)
  ·
    refine ⟨105246843075933399086192921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70164562050622266057461947 105246843075933399086192921)
    ·
      refine ⟨78935132306950049314644691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105246843075933399086192921 78935132306950049314644691)
      ·
        refine ⟨118402698460425073971967037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78935132306950049314644691 118402698460425073971967037)
        ·
          refine ⟨44401011922659402739487639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118402698460425073971967037 44401011922659402739487639)
          ·
            refine ⟨66601517883989104109231459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44401011922659402739487639 66601517883989104109231459)
            ·
              refine ⟨99902276825983656163847189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66601517883989104109231459 99902276825983656163847189)
              ·
                refine ⟨4682919226217983882680337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99902276825983656163847189 4682919226217983882680337)
                ·
                  refine ⟨3512189419663487912010253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4682919226217983882680337 3512189419663487912010253)
                  ·
                    refine ⟨1317071032373807967003845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3512189419663487912010253 1317071032373807967003845)
                    ·
                      rfl

theorem cell22_3847480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 2, 3].length) (baseStart_3847480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847480 prefixEnd_3847480 := by exact prefixLift 3847480
  have htrace : WordTrace (prefixWord ++ tailWord_3847480) baseStart_3847480 baseEnd_3847480 := by
    simpa [prefixWord, tailWord_3847480, baseEnd_3847480] using wordTrace_append hprefix tailTrace_3847480
  have hstable : (prefixWord ++ tailWord_3847480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847480).length < 2 ^ (prefixWord ++ tailWord_3847480).sum := by decide
  have hdescent : baseEnd_3847480 < baseStart_3847480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847482 : List Nat := [3, 1, 1, 1, 4, 1, 5, 2, 4]
def baseStart_3847482 : Nat := 118140960795 + 3847482 * 2 ^ 59
def prefixEnd_3847482 : Nat := 4983230072969 + 3 ^ 40 * 3847482 * 2
def baseEnd_3847482 : Nat := 439023905671560209484613

theorem tailTrace_3847482 : CollatzResearch.WordTrace tailWord_3847482 prefixEnd_3847482 439023905671560209484613 := by
  unfold tailWord_3847482
  simp only [CollatzResearch.WordTrace]
  refine ⟨35082299261809321614124175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93552798031491524304331133 35082299261809321614124175)
  ·
    refine ⟨52623448892713982421186263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35082299261809321614124175 52623448892713982421186263)
    ·
      refine ⟨78935173339070973631779395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52623448892713982421186263 78935173339070973631779395)
      ·
        refine ⟨118402760008606460447669093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78935173339070973631779395 118402760008606460447669093)
        ·
          refine ⟨22200517501613711333937955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118402760008606460447669093 22200517501613711333937955)
          ·
            refine ⟨33300776252420567000906933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22200517501613711333937955 33300776252420567000906933)
            ·
              refine ⟨3121947773664428156335025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33300776252420567000906933 3121947773664428156335025)
              ·
                refine ⟨2341460830248321117251269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3121947773664428156335025 2341460830248321117251269)
                ·
                  refine ⟨439023905671560209484613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2341460830248321117251269 439023905671560209484613)
                  ·
                    rfl

theorem cell22_3847482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 2, 4].length) (baseStart_3847482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847482 prefixEnd_3847482 := by exact prefixLift 3847482
  have htrace : WordTrace (prefixWord ++ tailWord_3847482) baseStart_3847482 baseEnd_3847482 := by
    simpa [prefixWord, tailWord_3847482, baseEnd_3847482] using wordTrace_append hprefix tailTrace_3847482
  have hstable : (prefixWord ++ tailWord_3847482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847482).length < 2 ^ (prefixWord ++ tailWord_3847482).sum := by decide
  have hdescent : baseEnd_3847482 < baseStart_3847482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847497 : List Nat := [1, 2, 1, 1, 2, 3, 6, 1, 2, 3]
def baseStart_3847497 : Nat := 118140960795 + 3847497 * 2 ^ 59
def prefixEnd_3847497 : Nat := 4983230072969 + 3 ^ 40 * 3847497 * 2
def baseEnd_3847497 : Nat := 1317076851821225589328793

theorem tailTrace_3847497 : CollatzResearch.WordTrace tailWord_3847497 prefixEnd_3847497 1317076851821225589328793 := by
  unfold tailWord_3847497
  simp only [CollatzResearch.WordTrace]
  refine ⟨140329744142182944018292745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93553162761455296012195163 140329744142182944018292745)
  ·
    refine ⟨105247308106637208013719559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140329744142182944018292745 105247308106637208013719559)
    ·
      refine ⟨157870962159955812020579339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105247308106637208013719559 157870962159955812020579339)
      ·
        refine ⟨236806443239933718030869009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157870962159955812020579339 236806443239933718030869009)
        ·
          refine ⟨177604832429950288523151757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236806443239933718030869009 177604832429950288523151757)
          ·
            refine ⟨66601812161231358196181909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177604832429950288523151757 66601812161231358196181909)
            ·
              refine ⟨3121959945057719915446027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66601812161231358196181909 3121959945057719915446027)
              ·
                refine ⟨4682939917586579873169041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3121959945057719915446027 4682939917586579873169041)
                ·
                  refine ⟨3512204938189934904876781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4682939917586579873169041 3512204938189934904876781)
                  ·
                    refine ⟨1317076851821225589328793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3512204938189934904876781 1317076851821225589328793)
                    ·
                      rfl

theorem cell22_3847497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 2, 3].length) (baseStart_3847497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847497 prefixEnd_3847497 := by exact prefixLift 3847497
  have htrace : WordTrace (prefixWord ++ tailWord_3847497) baseStart_3847497 baseEnd_3847497 := by
    simpa [prefixWord, tailWord_3847497, baseEnd_3847497] using wordTrace_append hprefix tailTrace_3847497
  have hstable : (prefixWord ++ tailWord_3847497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847497).length < 2 ^ (prefixWord ++ tailWord_3847497).sum := by decide
  have hdescent : baseEnd_3847497 < baseStart_3847497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847501 : List Nat := [1, 6, 1, 3, 1, 2, 1, 2, 1, 4]
def baseStart_3847501 : Nat := 118140960795 + 3847501 * 2 ^ 59
def prefixEnd_3847501 : Nat := 4983230072969 + 3 ^ 40 * 3847501 * 2
def baseEnd_3847501 : Nat := 1317078221102970912228781

theorem tailTrace_3847501 : CollatzResearch.WordTrace tailWord_3847501 prefixEnd_3847501 1317078221102970912228781 := by
  unfold tailWord_3847501
  simp only [CollatzResearch.WordTrace]
  refine ⟨140329890034168452701438357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93553260022778968467625571 140329890034168452701438357)
  ·
    refine ⟨6577963595351646220379923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 140329890034168452701438357 6577963595351646220379923)
    ·
      refine ⟨9866945393027469330569885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6577963595351646220379923 9866945393027469330569885)
      ·
        refine ⟨3700104522385300998963707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9866945393027469330569885 3700104522385300998963707)
        ·
          refine ⟨5550156783577951498445561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3700104522385300998963707 5550156783577951498445561)
          ·
            refine ⟨4162617587683463623834171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5550156783577951498445561 4162617587683463623834171)
            ·
              refine ⟨6243926381525195435751257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4162617587683463623834171 6243926381525195435751257)
              ·
                refine ⟨4682944786143896576813443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6243926381525195435751257 4682944786143896576813443)
                ·
                  refine ⟨7024417179215844865220165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4682944786143896576813443 7024417179215844865220165)
                  ·
                    refine ⟨1317078221102970912228781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7024417179215844865220165 1317078221102970912228781)
                    ·
                      rfl

theorem cell22_3847501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_3847501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847501 prefixEnd_3847501 := by exact prefixLift 3847501
  have htrace : WordTrace (prefixWord ++ tailWord_3847501) baseStart_3847501 baseEnd_3847501 := by
    simpa [prefixWord, tailWord_3847501, baseEnd_3847501] using wordTrace_append hprefix tailTrace_3847501
  have hstable : (prefixWord ++ tailWord_3847501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847501).length < 2 ^ (prefixWord ++ tailWord_3847501).sum := by decide
  have hdescent : baseEnd_3847501 < baseStart_3847501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847555 : List Nat := [1, 1, 1, 3, 5, 1, 2, 3, 5]
def baseStart_3847555 : Nat := 118140960795 + 3847555 * 2 ^ 59
def prefixEnd_3847555 : Nat := 4983230072969 + 3 ^ 40 * 3847555 * 2
def baseEnd_3847555 : Nat := 439032235468844257126205

theorem tailTrace_3847555 : CollatzResearch.WordTrace tailWord_3847555 prefixEnd_3847555 439032235468844257126205 := by
  unfold tailWord_3847555
  simp only [CollatzResearch.WordTrace]
  refine ⟨140331859575972819923904119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93554573050648546615936079 140331859575972819923904119)
  ·
    refine ⟨210497789363959229885856179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140331859575972819923904119 210497789363959229885856179)
    ·
      refine ⟨315746684045938844828784269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210497789363959229885856179 315746684045938844828784269)
      ·
        refine ⟨118405006517227066810794101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315746684045938844828784269 118405006517227066810794101)
        ·
          refine ⟨11100469360990037513511947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118405006517227066810794101 11100469360990037513511947)
          ·
            refine ⟨16650704041485056270267921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11100469360990037513511947 16650704041485056270267921)
            ·
              refine ⟨12488028031113792202700941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16650704041485056270267921 12488028031113792202700941)
              ·
                refine ⟨4683010511667672076012853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12488028031113792202700941 4683010511667672076012853)
                ·
                  refine ⟨439032235468844257126205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4683010511667672076012853 439032235468844257126205)
                  ·
                    rfl

theorem cell22_3847555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 5].length) (baseStart_3847555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847555 prefixEnd_3847555 := by exact prefixLift 3847555
  have htrace : WordTrace (prefixWord ++ tailWord_3847555) baseStart_3847555 baseEnd_3847555 := by
    simpa [prefixWord, tailWord_3847555, baseEnd_3847555] using wordTrace_append hprefix tailTrace_3847555
  have hstable : (prefixWord ++ tailWord_3847555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847555).length < 2 ^ (prefixWord ++ tailWord_3847555).sum := by decide
  have hdescent : baseEnd_3847555 < baseStart_3847555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847576 : List Nat := [2, 1, 2, 5, 2, 1, 2, 3, 1, 3]
def baseStart_3847576 : Nat := 118140960795 + 3847576 * 2 ^ 59
def prefixEnd_3847576 : Nat := 4983230072969 + 3 ^ 40 * 3847576 * 2
def baseEnd_3847576 : Nat := 1317103895135695716603551

theorem tailTrace_3847576 : CollatzResearch.WordTrace tailWord_3847576 prefixEnd_3847576 1317103895135695716603551 := by
  unfold tailWord_3847576
  simp only [CollatzResearch.WordTrace]
  refine ⟨70166312754448370255209291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93555083672597827006945721 70166312754448370255209291)
  ·
    refine ⟨105249469131672555382813937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70166312754448370255209291 105249469131672555382813937)
    ·
      refine ⟨78937101848754416537110453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105249469131672555382813937 78937101848754416537110453)
      ·
        refine ⟨7400353298320726550354105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78937101848754416537110453 7400353298320726550354105)
        ·
          refine ⟨5550264973740544912765579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7400353298320726550354105 5550264973740544912765579)
          ·
            refine ⟨8325397460610817369148369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5550264973740544912765579 8325397460610817369148369)
            ·
              refine ⟨6244048095458113026861277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8325397460610817369148369 6244048095458113026861277)
              ·
                refine ⟨2341518035796792385072979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6244048095458113026861277 2341518035796792385072979)
                ·
                  refine ⟨3512277053695188577609469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2341518035796792385072979 3512277053695188577609469)
                  ·
                    refine ⟨1317103895135695716603551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3512277053695188577609469 1317103895135695716603551)
                    ·
                      rfl

theorem cell22_3847576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 3, 1, 3].length) (baseStart_3847576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847576 prefixEnd_3847576 := by exact prefixLift 3847576
  have htrace : WordTrace (prefixWord ++ tailWord_3847576) baseStart_3847576 baseEnd_3847576 := by
    simpa [prefixWord, tailWord_3847576, baseEnd_3847576] using wordTrace_append hprefix tailTrace_3847576
  have hstable : (prefixWord ++ tailWord_3847576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847576).length < 2 ^ (prefixWord ++ tailWord_3847576).sum := by decide
  have hdescent : baseEnd_3847576 < baseStart_3847576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847630 : List Nat := [4, 1, 1, 1, 2, 1, 4, 1, 1, 6]
def baseStart_3847630 : Nat := 118140960795 + 3847630 * 2 ^ 59
def prefixEnd_3847630 : Nat := 4983230072969 + 3 ^ 40 * 3847630 * 2
def baseEnd_3847630 : Nat := 1317122380439257575753385

theorem tailTrace_3847630 : CollatzResearch.WordTrace tailWord_3847630 prefixEnd_3847630 1317122380439257575753385 := by
  unfold tailWord_3847630
  simp only [CollatzResearch.WordTrace]
  refine ⟨17541824381337638466610543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93556396700467405155256229 17541824381337638466610543)
  ·
    refine ⟨26312736572006457699915815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17541824381337638466610543 26312736572006457699915815)
    ·
      refine ⟨39469104858009686549873723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26312736572006457699915815 39469104858009686549873723)
      ·
        refine ⟨59203657287014529824810585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39469104858009686549873723 59203657287014529824810585)
        ·
          refine ⟨44402742965260897368607939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59203657287014529824810585 44402742965260897368607939)
          ·
            refine ⟨66604114447891346052911909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44402742965260897368607939 66604114447891346052911909)
            ·
              refine ⟨12488271458979627384920983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66604114447891346052911909 12488271458979627384920983)
              ·
                refine ⟨18732407188469441077381475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12488271458979627384920983 18732407188469441077381475)
                ·
                  refine ⟨28098610782704161616072213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18732407188469441077381475 28098610782704161616072213)
                  ·
                    refine ⟨1317122380439257575753385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28098610782704161616072213 1317122380439257575753385)
                    ·
                      rfl

theorem cell22_3847630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_3847630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847630 prefixEnd_3847630 := by exact prefixLift 3847630
  have htrace : WordTrace (prefixWord ++ tailWord_3847630) baseStart_3847630 baseEnd_3847630 := by
    simpa [prefixWord, tailWord_3847630, baseEnd_3847630] using wordTrace_append hprefix tailTrace_3847630
  have hstable : (prefixWord ++ tailWord_3847630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847630).length < 2 ^ (prefixWord ++ tailWord_3847630).sum := by decide
  have hdescent : baseEnd_3847630 < baseStart_3847630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847645 : List Nat := [1, 4, 3, 1, 1, 2, 10]
def baseStart_3847645 : Nat := 118140960795 + 3847645 * 2 ^ 59
def prefixEnd_3847645 : Nat := 4983230072969 + 3 ^ 40 * 3847645 * 2
def baseEnd_3847645 : Nat := 48782500564659353208457

theorem tailTrace_3847645 : CollatzResearch.WordTrace tailWord_3847645 prefixEnd_3847645 48782500564659353208457 := by
  unfold tailWord_3847645
  simp only [CollatzResearch.WordTrace]
  refine ⟨140335142145646765294680389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93556761430431176863120259 140335142145646765294680389)
  ·
    refine ⟨26312839152308768492752573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140335142145646765294680389 26312839152308768492752573)
    ·
      refine ⟨9867314682115788184782215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26312839152308768492752573 9867314682115788184782215)
      ·
        refine ⟨14800972023173682277173323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9867314682115788184782215 14800972023173682277173323)
        ·
          refine ⟨22201458034760523415759985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14800972023173682277173323 22201458034760523415759985)
          ·
            refine ⟨16651093526070392561819989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22201458034760523415759985 16651093526070392561819989)
            ·
              refine ⟨48782500564659353208457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16651093526070392561819989 48782500564659353208457)
              ·
                rfl

theorem cell22_3847645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 10].length) (baseStart_3847645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847645 prefixEnd_3847645 := by exact prefixLift 3847645
  have htrace : WordTrace (prefixWord ++ tailWord_3847645) baseStart_3847645 baseEnd_3847645 := by
    simpa [prefixWord, tailWord_3847645, baseEnd_3847645] using wordTrace_append hprefix tailTrace_3847645
  have hstable : (prefixWord ++ tailWord_3847645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847645).length < 2 ^ (prefixWord ++ tailWord_3847645).sum := by decide
  have hdescent : baseEnd_3847645 < baseStart_3847645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847666 : List Nat := [3, 2, 1, 4, 1, 1, 4, 1, 2, 3]
def baseStart_3847666 : Nat := 118140960795 + 3847666 * 2 ^ 59
def prefixEnd_3847666 : Nat := 4983230072969 + 3 ^ 40 * 3847666 * 2
def baseEnd_3847666 : Nat := 1317134703974965481853275

theorem tailTrace_3847666 : CollatzResearch.WordTrace tailWord_3847666 prefixEnd_3847666 1317134703974965481853275 := by
  unfold tailWord_3847666
  simp only [CollatzResearch.WordTrace]
  refine ⟨35083977019642671470298713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93557272052380457254129901 35083977019642671470298713)
  ·
    refine ⟨26312982764732003602724035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35083977019642671470298713 26312982764732003602724035)
    ·
      refine ⟨39469474147098005404086053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26312982764732003602724035 39469474147098005404086053)
      ·
        refine ⟨7400526402580876013266135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39469474147098005404086053 7400526402580876013266135)
        ·
          refine ⟨11100789603871314019899203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7400526402580876013266135 11100789603871314019899203)
          ·
            refine ⟨16651184405806971029848805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11100789603871314019899203 16651184405806971029848805)
            ·
              refine ⟨3122097076088807068096651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16651184405806971029848805 3122097076088807068096651)
              ·
                refine ⟨4683145614133210602144977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3122097076088807068096651 4683145614133210602144977)
                ·
                  refine ⟨3512359210599907951608733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4683145614133210602144977 3512359210599907951608733)
                  ·
                    refine ⟨1317134703974965481853275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3512359210599907951608733 1317134703974965481853275)
                    ·
                      rfl

theorem cell22_3847666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_3847666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847666 prefixEnd_3847666 := by exact prefixLift 3847666
  have htrace : WordTrace (prefixWord ++ tailWord_3847666) baseStart_3847666 baseEnd_3847666 := by
    simpa [prefixWord, tailWord_3847666, baseEnd_3847666] using wordTrace_append hprefix tailTrace_3847666
  have hstable : (prefixWord ++ tailWord_3847666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847666).length < 2 ^ (prefixWord ++ tailWord_3847666).sum := by decide
  have hdescent : baseEnd_3847666 < baseStart_3847666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847711 : List Nat := [1, 1, 2, 4, 1, 1, 6, 2, 1, 3]
def baseStart_3847711 : Nat := 118140960795 + 3847711 * 2 ^ 59
def prefixEnd_3847711 : Nat := 4983230072969 + 3 ^ 40 * 3847711 * 2
def baseEnd_3847711 : Nat := 1317150108394600364478137

theorem tailTrace_3847711 : CollatzResearch.WordTrace tailWord_3847711 prefixEnd_3847711 1317150108394600364478137 := by
  unfold tailWord_3847711
  simp only [CollatzResearch.WordTrace]
  refine ⟨140337549363407658566582987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93558366242271772377721991 140337549363407658566582987)
  ·
    refine ⟨210506324045111487849874481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140337549363407658566582987 210506324045111487849874481)
    ·
      refine ⟨157879743033833615887405861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210506324045111487849874481 157879743033833615887405861)
      ·
        refine ⟨29602451818843802978888599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157879743033833615887405861 29602451818843802978888599)
        ·
          refine ⟨44403677728265704468332899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29602451818843802978888599 44403677728265704468332899)
          ·
            refine ⟨66605516592398556702499349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44403677728265704468332899 66605516592398556702499349)
            ·
              refine ⟨3122133590268682345429657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66605516592398556702499349 3122133590268682345429657)
              ·
                refine ⟨2341600192701511759072243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3122133590268682345429657 2341600192701511759072243)
                ·
                  refine ⟨3512400289052267638608365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2341600192701511759072243 3512400289052267638608365)
                  ·
                    refine ⟨1317150108394600364478137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3512400289052267638608365 1317150108394600364478137)
                    ·
                      rfl

theorem cell22_3847711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 2, 1, 3].length) (baseStart_3847711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847711 prefixEnd_3847711 := by exact prefixLift 3847711
  have htrace : WordTrace (prefixWord ++ tailWord_3847711) baseStart_3847711 baseEnd_3847711 := by
    simpa [prefixWord, tailWord_3847711, baseEnd_3847711] using wordTrace_append hprefix tailTrace_3847711
  have hstable : (prefixWord ++ tailWord_3847711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847711).length < 2 ^ (prefixWord ++ tailWord_3847711).sum := by decide
  have hdescent : baseEnd_3847711 < baseStart_3847711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847722 : List Nat := [3, 1, 4, 1, 1, 1, 3, 1, 2, 5]
def baseStart_3847722 : Nat := 118140960795 + 3847722 * 2 ^ 59
def prefixEnd_3847722 : Nat := 4983230072969 + 3 ^ 40 * 3847722 * 2
def baseEnd_3847722 : Nat := 1317153873919400002453103

theorem tailTrace_3847722 : CollatzResearch.WordTrace tailWord_3847722 prefixEnd_3847722 1317153873919400002453103 := by
  unfold tailWord_3847722
  simp only [CollatzResearch.WordTrace]
  refine ⟨35084487641591951861308355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93558633710911871630155613 35084487641591951861308355)
  ·
    refine ⟨52626731462387927791962533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35084487641591951861308355 52626731462387927791962533)
    ·
      refine ⟨9867512149197736460992975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52626731462387927791962533 9867512149197736460992975)
      ·
        refine ⟨14801268223796604691489463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9867512149197736460992975 14801268223796604691489463)
        ·
          refine ⟨22201902335694907037234195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14801268223796604691489463 22201902335694907037234195)
          ·
            refine ⟨33302853503542360555851293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22201902335694907037234195 33302853503542360555851293)
            ·
              refine ⟨12488570063828385208444235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33302853503542360555851293 12488570063828385208444235)
              ·
                refine ⟨18732855095742577812666353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12488570063828385208444235 18732855095742577812666353)
                ·
                  refine ⟨14049641321806933359499765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18732855095742577812666353 14049641321806933359499765)
                  ·
                    refine ⟨1317153873919400002453103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14049641321806933359499765 1317153873919400002453103)
                    ·
                      rfl

theorem cell22_3847722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_3847722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847722 prefixEnd_3847722 := by exact prefixLift 3847722
  have htrace : WordTrace (prefixWord ++ tailWord_3847722) baseStart_3847722 baseEnd_3847722 := by
    simpa [prefixWord, tailWord_3847722, baseEnd_3847722] using wordTrace_append hprefix tailTrace_3847722
  have hstable : (prefixWord ++ tailWord_3847722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847722).length < 2 ^ (prefixWord ++ tailWord_3847722).sum := by decide
  have hdescent : baseEnd_3847722 < baseStart_3847722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847735 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 8]
def baseStart_3847735 : Nat := 118140960795 + 3847735 * 2 ^ 59
def prefixEnd_3847735 : Nat := 4983230072969 + 3 ^ 40 * 3847735 * 2
def baseEnd_3847735 : Nat := 439052774695024100626021

theorem tailTrace_3847735 : CollatzResearch.WordTrace tailWord_3847735 prefixEnd_3847735 439052774695024100626021 := by
  unfold tailWord_3847735
  simp only [CollatzResearch.WordTrace]
  refine ⟨140338424715320710665456659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93558949810213807110304439 140338424715320710665456659)
  ·
    refine ⟨210507637072981065998184989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140338424715320710665456659 210507637072981065998184989)
    ·
      refine ⟨78940363902367899749319371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210507637072981065998184989 78940363902367899749319371)
      ·
        refine ⟨118410545853551849623979057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78940363902367899749319371 118410545853551849623979057)
        ·
          refine ⟨88807909390163887217984293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118410545853551849623979057 88807909390163887217984293)
          ·
            refine ⟨16651483010655728853372055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88807909390163887217984293 16651483010655728853372055)
            ·
              refine ⟨24977224515983593280058083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16651483010655728853372055 24977224515983593280058083)
              ·
                refine ⟨37465836773975389920087125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24977224515983593280058083 37465836773975389920087125)
                ·
                  refine ⟨439052774695024100626021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37465836773975389920087125 439052774695024100626021)
                  ·
                    rfl

theorem cell22_3847735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 8].length) (baseStart_3847735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847735 prefixEnd_3847735 := by exact prefixLift 3847735
  have htrace : WordTrace (prefixWord ++ tailWord_3847735) baseStart_3847735 baseEnd_3847735 := by
    simpa [prefixWord, tailWord_3847735, baseEnd_3847735] using wordTrace_append hprefix tailTrace_3847735
  have hstable : (prefixWord ++ tailWord_3847735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847735).length < 2 ^ (prefixWord ++ tailWord_3847735).sum := by decide
  have hdescent : baseEnd_3847735 < baseStart_3847735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847737 : List Nat := [1, 2, 1, 5, 1, 2, 2, 1, 3, 4]
def baseStart_3847737 : Nat := 118140960795 + 3847737 * 2 ^ 59
def prefixEnd_3847737 : Nat := 4983230072969 + 3 ^ 40 * 3847737 * 2
def baseEnd_3847737 : Nat := 1317159008725944963328057

theorem tailTrace_3847737 : CollatzResearch.WordTrace tailWord_3847737 prefixEnd_3847737 1317159008725944963328057 := by
  unfold tailWord_3847737
  simp only [CollatzResearch.WordTrace]
  refine ⟨140338497661313465007029465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93558998440875643338019643 140338497661313465007029465)
  ·
    refine ⟨105253873245985098755272099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140338497661313465007029465 105253873245985098755272099)
    ·
      refine ⟨157880809868977648132908149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105253873245985098755272099 157880809868977648132908149)
      ·
        refine ⟨14801325925216654512460139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157880809868977648132908149 14801325925216654512460139)
        ·
          refine ⟨22201988887824981768690209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14801325925216654512460139 22201988887824981768690209)
          ·
            refine ⟨16651491665868736326517657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22201988887824981768690209 16651491665868736326517657)
            ·
              refine ⟨12488618749401552244888243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16651491665868736326517657 12488618749401552244888243)
              ·
                refine ⟨18732928124102328367332365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12488618749401552244888243 18732928124102328367332365)
                ·
                  refine ⟨7024848046538373137749637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18732928124102328367332365 7024848046538373137749637)
                  ·
                    refine ⟨1317159008725944963328057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7024848046538373137749637 1317159008725944963328057)
                    ·
                      rfl

theorem cell22_3847737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 4].length) (baseStart_3847737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847737 prefixEnd_3847737 := by exact prefixLift 3847737
  have htrace : WordTrace (prefixWord ++ tailWord_3847737) baseStart_3847737 baseEnd_3847737 := by
    simpa [prefixWord, tailWord_3847737, baseEnd_3847737] using wordTrace_append hprefix tailTrace_3847737
  have hstable : (prefixWord ++ tailWord_3847737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847737).length < 2 ^ (prefixWord ++ tailWord_3847737).sum := by decide
  have hdescent : baseEnd_3847737 < baseStart_3847737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847784 : List Nat := [2, 1, 4, 3, 1, 1, 3, 1, 1, 5]
def baseStart_3847784 : Nat := 118140960795 + 3847784 * 2 ^ 59
def prefixEnd_3847784 : Nat := 4983230072969 + 3 ^ 40 * 3847784 * 2
def baseEnd_3847784 : Nat := 1317175097786452507402913

theorem tailTrace_3847784 : CollatzResearch.WordTrace tailWord_3847784 prefixEnd_3847784 1317175097786452507402913 := by
  unfold tailWord_3847784
  simp only [CollatzResearch.WordTrace]
  refine ⟨70170105946071596016995203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93560141261428794689326937 70170105946071596016995203)
  ·
    refine ⟨105255158919107394025492805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70170105946071596016995203 105255158919107394025492805)
    ·
      refine ⟨19735342297332636379779901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105255158919107394025492805 19735342297332636379779901)
      ·
        refine ⟨7400753361499738642417463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19735342297332636379779901 7400753361499738642417463)
        ·
          refine ⟨11101130042249607963626195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7400753361499738642417463 11101130042249607963626195)
          ·
            refine ⟨16651695063374411945439293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11101130042249607963626195 16651695063374411945439293)
            ·
              refine ⟨6244385648765404479539735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16651695063374411945439293 6244385648765404479539735)
              ·
                refine ⟨9366578473148106719309603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6244385648765404479539735 9366578473148106719309603)
                ·
                  refine ⟨14049867709722160078964405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9366578473148106719309603 14049867709722160078964405)
                  ·
                    refine ⟨1317175097786452507402913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14049867709722160078964405 1317175097786452507402913)
                    ·
                      rfl

theorem cell22_3847784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_3847784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847784 prefixEnd_3847784 := by exact prefixLift 3847784
  have htrace : WordTrace (prefixWord ++ tailWord_3847784) baseStart_3847784 baseEnd_3847784 := by
    simpa [prefixWord, tailWord_3847784, baseEnd_3847784] using wordTrace_append hprefix tailTrace_3847784
  have hstable : (prefixWord ++ tailWord_3847784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847784).length < 2 ^ (prefixWord ++ tailWord_3847784).sum := by decide
  have hdescent : baseEnd_3847784 < baseStart_3847784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847816 : List Nat := [2, 1, 3, 5, 1, 1, 1, 2, 2, 4]
def baseStart_3847816 : Nat := 118140960795 + 3847816 * 2 ^ 59
def prefixEnd_3847816 : Nat := 4983230072969 + 3 ^ 40 * 3847816 * 2
def baseEnd_3847816 : Nat := 1317186052040415090602815

theorem tailTrace_3847816 : CollatzResearch.WordTrace tailWord_3847816 prefixEnd_3847816 1317186052040415090602815 := by
  unfold tailWord_3847816
  simp only [CollatzResearch.WordTrace]
  refine ⟨70170689514013630749577651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93560919352018174332770201 70170689514013630749577651)
  ·
    refine ⟨105256034271020446124366477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70170689514013630749577651 105256034271020446124366477)
    ·
      refine ⟨39471012851632667296637429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105256034271020446124366477 39471012851632667296637429)
      ·
        refine ⟨3700407454840562559059759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39471012851632667296637429 3700407454840562559059759)
        ·
          refine ⟨5550611182260843838589639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3700407454840562559059759 5550611182260843838589639)
          ·
            refine ⟨8325916773391265757884459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5550611182260843838589639 8325916773391265757884459)
            ·
              refine ⟨12488875160086898636826689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8325916773391265757884459 12488875160086898636826689)
              ·
                refine ⟨9366656370065173977620017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12488875160086898636826689 9366656370065173977620017)
                ·
                  refine ⟨7024992277548880483215013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9366656370065173977620017 7024992277548880483215013)
                  ·
                    refine ⟨1317186052040415090602815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7024992277548880483215013 1317186052040415090602815)
                    ·
                      rfl

theorem cell22_3847816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_3847816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847816 prefixEnd_3847816 := by exact prefixLift 3847816
  have htrace : WordTrace (prefixWord ++ tailWord_3847816) baseStart_3847816 baseEnd_3847816 := by
    simpa [prefixWord, tailWord_3847816, baseEnd_3847816] using wordTrace_append hprefix tailTrace_3847816
  have hstable : (prefixWord ++ tailWord_3847816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847816).length < 2 ^ (prefixWord ++ tailWord_3847816).sum := by decide
  have hdescent : baseEnd_3847816 < baseStart_3847816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847919 : List Nat := [1, 1, 2, 1, 5, 1, 2, 2, 4, 3]
def baseStart_3847919 : Nat := 118140960795 + 3847919 * 2 ^ 59
def prefixEnd_3847919 : Nat := 4983230072969 + 3 ^ 40 * 3847919 * 2
def baseEnd_3847919 : Nat := 1317221311045357155277499

theorem tailTrace_3847919 : CollatzResearch.WordTrace tailWord_3847919 prefixEnd_3847919 1317221311045357155277499 := by
  unfold tailWord_3847919
  simp only [CollatzResearch.WordTrace]
  refine ⟨140345135746654110090154811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93563423831102740060103207 140345135746654110090154811)
  ·
    refine ⟨210517703619981165135232217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140345135746654110090154811 210517703619981165135232217)
    ·
      refine ⟨157888277714985873851424163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210517703619981165135232217 157888277714985873851424163)
      ·
        refine ⟨236832416572478810777136245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157888277714985873851424163 236832416572478810777136245)
        ·
          refine ⟨22203039053669888510356523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 236832416572478810777136245 22203039053669888510356523)
          ·
            refine ⟨33304558580504832765534785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22203039053669888510356523 33304558580504832765534785)
            ·
              refine ⟨24978418935378624574151089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33304558580504832765534785 24978418935378624574151089)
              ·
                refine ⟨18733814201533968430613317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24978418935378624574151089 18733814201533968430613317)
                ·
                  refine ⟨3512590162787619080739997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18733814201533968430613317 3512590162787619080739997)
                  ·
                    refine ⟨1317221311045357155277499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3512590162787619080739997 1317221311045357155277499)
                    ·
                      rfl

theorem cell22_3847919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 4, 3].length) (baseStart_3847919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847919 prefixEnd_3847919 := by exact prefixLift 3847919
  have htrace : WordTrace (prefixWord ++ tailWord_3847919) baseStart_3847919 baseEnd_3847919 := by
    simpa [prefixWord, tailWord_3847919, baseEnd_3847919] using wordTrace_append hprefix tailTrace_3847919
  have hstable : (prefixWord ++ tailWord_3847919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847919).length < 2 ^ (prefixWord ++ tailWord_3847919).sum := by decide
  have hdescent : baseEnd_3847919 < baseStart_3847919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847921 : List Nat := [1, 2, 2, 2, 2, 4, 2, 3, 4]
def baseStart_3847921 : Nat := 118140960795 + 3847921 * 2 ^ 59
def prefixEnd_3847921 : Nat := 4983230072969 + 3 ^ 40 * 3847921 * 2
def baseEnd_3847921 : Nat := 439073998562076605575831

theorem tailTrace_3847921 : CollatzResearch.WordTrace tailWord_3847921 prefixEnd_3847921 439073998562076605575831 := by
  unfold tailWord_3847921
  simp only [CollatzResearch.WordTrace]
  refine ⟨140345208692646864431727617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93563472461764576287818411 140345208692646864431727617)
  ·
    refine ⟨105258906519485148323795713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140345208692646864431727617 105258906519485148323795713)
    ·
      refine ⟨78944179889613861242846785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105258906519485148323795713 78944179889613861242846785)
      ·
        refine ⟨59208134917210395932135089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78944179889613861242846785 59208134917210395932135089)
        ·
          refine ⟨44406101187907796949101317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59208134917210395932135089 44406101187907796949101317)
          ·
            refine ⟨8326143972732711927956497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44406101187907796949101317 8326143972732711927956497)
            ·
              refine ⟨6244607979549533945967373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8326143972732711927956497 6244607979549533945967373)
              ·
                refine ⟨2341727992331075229737765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6244607979549533945967373 2341727992331075229737765)
                ·
                  refine ⟨439073998562076605575831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2341727992331075229737765 439073998562076605575831)
                  ·
                    rfl

theorem cell22_3847921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 3, 4].length) (baseStart_3847921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847921 prefixEnd_3847921 := by exact prefixLift 3847921
  have htrace : WordTrace (prefixWord ++ tailWord_3847921) baseStart_3847921 baseEnd_3847921 := by
    simpa [prefixWord, tailWord_3847921, baseEnd_3847921] using wordTrace_append hprefix tailTrace_3847921
  have hstable : (prefixWord ++ tailWord_3847921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847921).length < 2 ^ (prefixWord ++ tailWord_3847921).sum := by decide
  have hdescent : baseEnd_3847921 < baseStart_3847921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847932 : List Nat := [2, 2, 2, 1, 3, 1, 11]
def baseStart_3847932 : Nat := 118140960795 + 3847932 * 2 ^ 59
def prefixEnd_3847932 : Nat := 4983230072969 + 3 ^ 40 * 3847932 * 2
def baseEnd_3847932 : Nat := 48786139304112202026017

theorem tailTrace_3847932 : CollatzResearch.WordTrace tailWord_3847932 prefixEnd_3847932 48786139304112202026017 := by
  unfold tailWord_3847932
  simp only [CollatzResearch.WordTrace]
  refine ⟨70172804947803506655189025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93563739930404675540252033 70172804947803506655189025)
  ·
    refine ⟨52629603710852629991391769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70172804947803506655189025 52629603710852629991391769)
    ·
      refine ⟨39472202783139472493543827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52629603710852629991391769 39472202783139472493543827)
      ·
        refine ⟨59208304174709208740315741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39472202783139472493543827 59208304174709208740315741)
        ·
          refine ⟨22203114065515953277618403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59208304174709208740315741 22203114065515953277618403)
          ·
            refine ⟨33304671098273929916427605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22203114065515953277618403 33304671098273929916427605)
            ·
              refine ⟨48786139304112202026017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 33304671098273929916427605 48786139304112202026017)
              ·
                rfl

theorem cell22_3847932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 11].length) (baseStart_3847932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847932 prefixEnd_3847932 := by exact prefixLift 3847932
  have htrace : WordTrace (prefixWord ++ tailWord_3847932) baseStart_3847932 baseEnd_3847932 := by
    simpa [prefixWord, tailWord_3847932, baseEnd_3847932] using wordTrace_append hprefix tailTrace_3847932
  have hstable : (prefixWord ++ tailWord_3847932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847932).length < 2 ^ (prefixWord ++ tailWord_3847932).sum := by decide
  have hdescent : baseEnd_3847932 < baseStart_3847932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847994 : List Nat := [3, 1, 1, 1, 5, 1, 2, 1, 7]
def baseStart_3847994 : Nat := 118140960795 + 3847994 * 2 ^ 59
def prefixEnd_3847994 : Nat := 4983230072969 + 3 ^ 40 * 3847994 * 2
def baseEnd_3847994 : Nat := 439082328359360653217423

theorem tailTrace_3847994 : CollatzResearch.WordTrace tailWord_3847994 prefixEnd_3847994 439082328359360653217423 := by
  unfold tailWord_3847994
  simp only [CollatzResearch.WordTrace]
  refine ⟨35086967805345599474783759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93565247480921598599423357 35086967805345599474783759)
  ·
    refine ⟨52630451708018399212175639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35086967805345599474783759 52630451708018399212175639)
    ·
      refine ⟨78945677562027598818263459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52630451708018399212175639 78945677562027598818263459)
      ·
        refine ⟨118418516343041398227395189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78945677562027598818263459 118418516343041398227395189)
        ·
          refine ⟨11101735907160131083818299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118418516343041398227395189 11101735907160131083818299)
          ·
            refine ⟨16652603860740196625727449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11101735907160131083818299 16652603860740196625727449)
            ·
              refine ⟨12489452895555147469295587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16652603860740196625727449 12489452895555147469295587)
              ·
                refine ⟨18734179343332721203943381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12489452895555147469295587 18734179343332721203943381)
                ·
                  refine ⟨439082328359360653217423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18734179343332721203943381 439082328359360653217423)
                  ·
                    rfl

theorem cell22_3847994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 7].length) (baseStart_3847994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847994 prefixEnd_3847994 := by exact prefixLift 3847994
  have htrace : WordTrace (prefixWord ++ tailWord_3847994) baseStart_3847994 baseEnd_3847994 := by
    simpa [prefixWord, tailWord_3847994, baseEnd_3847994] using wordTrace_append hprefix tailTrace_3847994
  have hstable : (prefixWord ++ tailWord_3847994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847994).length < 2 ^ (prefixWord ++ tailWord_3847994).sum := by decide
  have hdescent : baseEnd_3847994 < baseStart_3847994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847998 : List Nat := [4, 2, 1, 2, 2, 1, 3, 1, 3, 3]
def baseStart_3847998 : Nat := 118140960795 + 3847998 * 2 ^ 59
def prefixEnd_3847998 : Nat := 4983230072969 + 3 ^ 40 * 3847998 * 2
def baseEnd_3847998 : Nat := 1317248354359827282552257

theorem tailTrace_3847998 : CollatzResearch.WordTrace tailWord_3847998 prefixEnd_3847998 1317248354359827282552257 := by
  unfold tailWord_3847998
  simp only [CollatzResearch.WordTrace]
  refine ⟨17543502139170988322785081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93565344742245271054853765 17543502139170988322785081)
  ·
    refine ⟨13157626604378241242088811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17543502139170988322785081 13157626604378241242088811)
    ·
      refine ⟨19736439906567361863133217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13157626604378241242088811 19736439906567361863133217)
      ·
        refine ⟨14802329929925521397349913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19736439906567361863133217 14802329929925521397349913)
        ·
          refine ⟨11101747447444141048012435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14802329929925521397349913 11101747447444141048012435)
          ·
            refine ⟨16652621171166211572018653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11101747447444141048012435 16652621171166211572018653)
            ·
              refine ⟨6244732939187329339506995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16652621171166211572018653 6244732939187329339506995)
              ·
                refine ⟨9367099408780994009260493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6244732939187329339506995 9367099408780994009260493)
                ·
                  refine ⟨3512662278292872753472685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9367099408780994009260493 3512662278292872753472685)
                  ·
                    refine ⟨1317248354359827282552257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3512662278292872753472685 1317248354359827282552257)
                    ·
                      rfl

theorem cell22_3847998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_3847998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3847998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3847998 prefixEnd_3847998 := by exact prefixLift 3847998
  have htrace : WordTrace (prefixWord ++ tailWord_3847998) baseStart_3847998 baseEnd_3847998 := by
    simpa [prefixWord, tailWord_3847998, baseEnd_3847998] using wordTrace_append hprefix tailTrace_3847998
  have hstable : (prefixWord ++ tailWord_3847998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847998).length < 2 ^ (prefixWord ++ tailWord_3847998).sum := by decide
  have hdescent : baseEnd_3847998 < baseStart_3847998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848069 : List Nat := [1, 3, 1, 1, 3, 2, 2, 2, 1, 6]
def baseStart_3848069 : Nat := 118140960795 + 3848069 * 2 ^ 59
def prefixEnd_3848069 : Nat := 4983230072969 + 3 ^ 40 * 3848069 * 2
def baseEnd_3848069 : Nat := 1317272659110806764027039

theorem tailTrace_3848069 : CollatzResearch.WordTrace tailWord_3848069 prefixEnd_3848069 1317272659110806764027039 := by
  unfold tailWord_3848069
  simp only [CollatzResearch.WordTrace]
  refine ⟨140350606696110685708115261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93567071130740457138743507 140350606696110685708115261)
  ·
    refine ⟨52631477511041507140543223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140350606696110685708115261 52631477511041507140543223)
    ·
      refine ⟨78947216266562260710814835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52631477511041507140543223 78947216266562260710814835)
      ·
        refine ⟨118420824399843391066222253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78947216266562260710814835 118420824399843391066222253)
        ·
          refine ⟨44407809149941271649833345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118420824399843391066222253 44407809149941271649833345)
          ·
            refine ⟨33305856862455953737375009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44407809149941271649833345 33305856862455953737375009)
            ·
              refine ⟨24979392646841965303031257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33305856862455953737375009 24979392646841965303031257)
              ·
                refine ⟨18734544485131473977273443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24979392646841965303031257 18734544485131473977273443)
                ·
                  refine ⟨28101816727697210965910165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18734544485131473977273443 28101816727697210965910165)
                  ·
                    refine ⟨1317272659110806764027039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28101816727697210965910165 1317272659110806764027039)
                    ·
                      rfl

theorem cell22_3848069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_3848069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3848069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3848069 prefixEnd_3848069 := by exact prefixLift 3848069
  have htrace : WordTrace (prefixWord ++ tailWord_3848069) baseStart_3848069 baseEnd_3848069 := by
    simpa [prefixWord, tailWord_3848069, baseEnd_3848069] using wordTrace_append hprefix tailTrace_3848069
  have hstable : (prefixWord ++ tailWord_3848069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848069).length < 2 ^ (prefixWord ++ tailWord_3848069).sum := by decide
  have hdescent : baseEnd_3848069 < baseStart_3848069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848114 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 1, 8]
def baseStart_3848114 : Nat := 118140960795 + 3848114 * 2 ^ 59
def prefixEnd_3848114 : Nat := 4983230072969 + 3 ^ 40 * 3848114 * 2
def baseEnd_3848114 : Nat := 1317288063530441646651901

theorem tailTrace_3848114 : CollatzResearch.WordTrace tailWord_3848114 prefixEnd_3848114 1317288063530441646651901 := by
  unfold tailWord_3848114
  simp only [CollatzResearch.WordTrace]
  refine ⟨35088061995236914598375849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93568165320631772262335597 35088061995236914598375849)
  ·
    refine ⟨26316046496427685948781887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35088061995236914598375849 26316046496427685948781887)
    ·
      refine ⟨39474069744641528923172831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26316046496427685948781887 39474069744641528923172831)
      ·
        refine ⟨59211104616962293384759247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39474069744641528923172831 59211104616962293384759247)
        ·
          refine ⟨88816656925443440077138871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59211104616962293384759247 88816656925443440077138871)
          ·
            refine ⟨133224985388165160115708307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88816656925443440077138871 133224985388165160115708307)
            ·
              refine ⟨199837478082247740173562461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133224985388165160115708307 199837478082247740173562461)
              ·
                refine ⟨74939054280842902565085923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199837478082247740173562461 74939054280842902565085923)
                ·
                  refine ⟨112408581421264353847628885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74939054280842902565085923 112408581421264353847628885)
                  ·
                    refine ⟨1317288063530441646651901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112408581421264353847628885 1317288063530441646651901)
                    ·
                      rfl

theorem cell22_3848114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_3848114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3848114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3848114 prefixEnd_3848114 := by exact prefixLift 3848114
  have htrace : WordTrace (prefixWord ++ tailWord_3848114) baseStart_3848114 baseEnd_3848114 := by
    simpa [prefixWord, tailWord_3848114, baseEnd_3848114] using wordTrace_append hprefix tailTrace_3848114
  have hstable : (prefixWord ++ tailWord_3848114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848114).length < 2 ^ (prefixWord ++ tailWord_3848114).sum := by decide
  have hdescent : baseEnd_3848114 < baseStart_3848114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848144 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 1, 7]
def baseStart_3848144 : Nat := 118140960795 + 3848144 * 2 ^ 59
def prefixEnd_3848144 : Nat := 4983230072969 + 3 ^ 40 * 3848144 * 2
def baseEnd_3848144 : Nat := 1317298333143531568401809

theorem tailTrace_3848144 : CollatzResearch.WordTrace tailWord_3848144 prefixEnd_3848144 1317298333143531568401809 := by
  unfold tailWord_3848144
  simp only [CollatzResearch.WordTrace]
  refine ⟨70176671085419486758547743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93568894780559315678063657 70176671085419486758547743)
  ·
    refine ⟨105265006628129230137821615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70176671085419486758547743 105265006628129230137821615)
    ·
      refine ⟨157897509942193845206732423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105265006628129230137821615 157897509942193845206732423)
      ·
        refine ⟨236846264913290767810098635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157897509942193845206732423 236846264913290767810098635)
        ·
          refine ⟨355269397369936151715147953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236846264913290767810098635 355269397369936151715147953)
          ·
            refine ⟨266452048027452113786360965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355269397369936151715147953 266452048027452113786360965)
            ·
              refine ⟨49959759005147271334942681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 266452048027452113786360965 49959759005147271334942681)
              ·
                refine ⟨37469819253860453501207011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49959759005147271334942681 37469819253860453501207011)
                ·
                  refine ⟨56204728880790680251810517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37469819253860453501207011 56204728880790680251810517)
                  ·
                    refine ⟨1317298333143531568401809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56204728880790680251810517 1317298333143531568401809)
                    ·
                      rfl

theorem cell22_3848144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 1, 7].length) (baseStart_3848144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3848144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3848144 prefixEnd_3848144 := by exact prefixLift 3848144
  have htrace : WordTrace (prefixWord ++ tailWord_3848144) baseStart_3848144 baseEnd_3848144 := by
    simpa [prefixWord, tailWord_3848144, baseEnd_3848144] using wordTrace_append hprefix tailTrace_3848144
  have hstable : (prefixWord ++ tailWord_3848144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848144).length < 2 ^ (prefixWord ++ tailWord_3848144).sum := by decide
  have hdescent : baseEnd_3848144 < baseStart_3848144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848167 : List Nat := [1, 1, 5, 2, 4, 1, 1, 1, 3, 3]
def baseStart_3848167 : Nat := 118140960795 + 3848167 * 2 ^ 59
def prefixEnd_3848167 : Nat := 4983230072969 + 3 ^ 40 * 3848167 * 2
def baseEnd_3848167 : Nat := 1317306206513567175076739

theorem tailTrace_3848167 : CollatzResearch.WordTrace tailWord_3848167 prefixEnd_3848167 1317306206513567175076739 := by
  unfold tailWord_3848167
  simp only [CollatzResearch.WordTrace]
  refine ⟨140354181049755648445182755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93569454033170432296788503 140354181049755648445182755)
  ·
    refine ⟨210531271574633472667774133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140354181049755648445182755 210531271574633472667774133)
    ·
      refine ⟨19737306710121888062603825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 210531271574633472667774133 19737306710121888062603825)
      ·
        refine ⟨14802980032591416046952869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19737306710121888062603825 14802980032591416046952869)
        ·
          refine ⟨2775558756110890508803663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14802980032591416046952869 2775558756110890508803663)
          ·
            refine ⟨4163338134166335763205495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2775558756110890508803663 4163338134166335763205495)
            ·
              refine ⟨6245007201249503644808243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4163338134166335763205495 6245007201249503644808243)
              ·
                refine ⟨9367510801874255467212365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6245007201249503644808243 9367510801874255467212365)
                ·
                  refine ⟨3512816550702845800204637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9367510801874255467212365 3512816550702845800204637)
                  ·
                    refine ⟨1317306206513567175076739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3512816550702845800204637 1317306206513567175076739)
                    ·
                      rfl

theorem cell22_3848167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_3848167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3848167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3848167 prefixEnd_3848167 := by exact prefixLift 3848167
  have htrace : WordTrace (prefixWord ++ tailWord_3848167) baseStart_3848167 baseEnd_3848167 := by
    simpa [prefixWord, tailWord_3848167, baseEnd_3848167] using wordTrace_append hprefix tailTrace_3848167
  have hstable : (prefixWord ++ tailWord_3848167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848167).length < 2 ^ (prefixWord ++ tailWord_3848167).sum := by decide
  have hdescent : baseEnd_3848167 < baseStart_3848167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848225 : List Nat := [1, 2, 3, 2, 4, 1, 1, 4, 4]
def baseStart_3848225 : Nat := 118140960795 + 3848225 * 2 ^ 59
def prefixEnd_3848225 : Nat := 4983230072969 + 3 ^ 40 * 3848225 * 2
def baseEnd_3848225 : Nat := 439108687032958119042187

theorem tailTrace_3848225 : CollatzResearch.WordTrace tailWord_3848225 prefixEnd_3848225 439108687032958119042187 := by
  unfold tailWord_3848225
  simp only [CollatzResearch.WordTrace]
  refine ⟨140356296483545524350794129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93570864322363682900529419 140356296483545524350794129)
  ·
    refine ⟨105267222362659143263095597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140356296483545524350794129 105267222362659143263095597)
    ·
      refine ⟨39475208385997178723660849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105267222362659143263095597 39475208385997178723660849)
      ·
        refine ⟨29606406289497884042745637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39475208385997178723660849 29606406289497884042745637)
        ·
          refine ⟨5551201179280853258014807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29606406289497884042745637 5551201179280853258014807)
          ·
            refine ⟨8326801768921279887022211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5551201179280853258014807 8326801768921279887022211)
            ·
              refine ⟨12490202653381919830533317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8326801768921279887022211 12490202653381919830533317)
              ·
                refine ⟨2341912997509109968224997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12490202653381919830533317 2341912997509109968224997)
                ·
                  refine ⟨439108687032958119042187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2341912997509109968224997 439108687032958119042187)
                  ·
                    rfl

theorem cell22_3848225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 4, 4].length) (baseStart_3848225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3848225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3848225 prefixEnd_3848225 := by exact prefixLift 3848225
  have htrace : WordTrace (prefixWord ++ tailWord_3848225) baseStart_3848225 baseEnd_3848225 := by
    simpa [prefixWord, tailWord_3848225, baseEnd_3848225] using wordTrace_append hprefix tailTrace_3848225
  have hstable : (prefixWord ++ tailWord_3848225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848225).length < 2 ^ (prefixWord ++ tailWord_3848225).sum := by decide
  have hdescent : baseEnd_3848225 < baseStart_3848225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848253 : List Nat := [1, 4, 1, 3, 1, 1, 5, 6]
def baseStart_3848253 : Nat := 118140960795 + 3848253 * 2 ^ 59
def prefixEnd_3848253 : Nat := 4983230072969 + 3 ^ 40 * 3848253 * 2
def baseEnd_3848253 : Nat := 146370627341232401936275

theorem tailTrace_3848253 : CollatzResearch.WordTrace tailWord_3848253 prefixEnd_3848253 146370627341232401936275 := by
  unfold tailWord_3848253
  simp only [CollatzResearch.WordTrace]
  refine ⟨140357317727444085132813413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93571545151629390088542275 140357317727444085132813413)
  ·
    refine ⟨26316997073895765962402515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140357317727444085132813413 26316997073895765962402515)
    ·
      refine ⟨39475495610843648943603773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26316997073895765962402515 39475495610843648943603773)
      ·
        refine ⟨14803310854066368353851415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39475495610843648943603773 14803310854066368353851415)
        ·
          refine ⟨22204966281099552530777123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14803310854066368353851415 22204966281099552530777123)
          ·
            refine ⟨33307449421649328796165685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22204966281099552530777123 33307449421649328796165685)
            ·
              refine ⟨3122573383279624574640533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33307449421649328796165685 3122573383279624574640533)
              ·
                refine ⟨146370627341232401936275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3122573383279624574640533 146370627341232401936275)
                ·
                  rfl

theorem cell22_3848253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 6].length) (baseStart_3848253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3848253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3848253 prefixEnd_3848253 := by exact prefixLift 3848253
  have htrace : WordTrace (prefixWord ++ tailWord_3848253) baseStart_3848253 baseEnd_3848253 := by
    simpa [prefixWord, tailWord_3848253, baseEnd_3848253] using wordTrace_append hprefix tailTrace_3848253
  have hstable : (prefixWord ++ tailWord_3848253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848253).length < 2 ^ (prefixWord ++ tailWord_3848253).sum := by decide
  have hdescent : baseEnd_3848253 < baseStart_3848253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848274 : List Nat := [3, 2, 2, 1, 5, 1, 1, 2, 2, 3]
def baseStart_3848274 : Nat := 118140960795 + 3848274 * 2 ^ 59
def prefixEnd_3848274 : Nat := 4983230072969 + 3 ^ 40 * 3848274 * 2
def baseEnd_3848274 : Nat := 1317342834800254562651411

theorem tailTrace_3848274 : CollatzResearch.WordTrace tailWord_3848274 prefixEnd_3848274 1317342834800254562651411 := by
  unfold tailWord_3848274
  simp only [CollatzResearch.WordTrace]
  refine ⟨35089520915092001429831969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93572055773578670479551917 35089520915092001429831969)
  ·
    refine ⟨26317140686319001072373977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35089520915092001429831969 26317140686319001072373977)
    ·
      refine ⟨19737855514739250804280483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26317140686319001072373977 19737855514739250804280483)
      ·
        refine ⟨29606783272108876206420725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19737855514739250804280483 29606783272108876206420725)
        ·
          refine ⟨2775635931760207144351943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29606783272108876206420725 2775635931760207144351943)
          ·
            refine ⟨4163453897640310716527915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2775635931760207144351943 4163453897640310716527915)
            ·
              refine ⟨6245180846460466074791873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4163453897640310716527915 6245180846460466074791873)
              ·
                refine ⟨4683885634845349556093905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6245180846460466074791873 4683885634845349556093905)
                ·
                  refine ⟨3512914226134012167070429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4683885634845349556093905 3512914226134012167070429)
                  ·
                    refine ⟨1317342834800254562651411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3512914226134012167070429 1317342834800254562651411)
                    ·
                      rfl

theorem cell22_3848274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_3848274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3848274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3848274 prefixEnd_3848274 := by exact prefixLift 3848274
  have htrace : WordTrace (prefixWord ++ tailWord_3848274) baseStart_3848274 baseEnd_3848274 := by
    simpa [prefixWord, tailWord_3848274, baseEnd_3848274] using wordTrace_append hprefix tailTrace_3848274
  have hstable : (prefixWord ++ tailWord_3848274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848274).length < 2 ^ (prefixWord ++ tailWord_3848274).sum := by decide
  have hdescent : baseEnd_3848274 < baseStart_3848274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848281 : List Nat := [1, 2, 1, 2, 2, 1, 5, 1, 7]
def baseStart_3848281 : Nat := 118140960795 + 3848281 * 2 ^ 59
def prefixEnd_3848281 : Nat := 4983230072969 + 3 ^ 40 * 3848281 * 2
def baseEnd_3848281 : Nat := 439115077014436292575463

theorem tailTrace_3848281 : CollatzResearch.WordTrace tailWord_3848281 prefixEnd_3848281 439115077014436292575463 := by
  unfold tailWord_3848281
  simp only [CollatzResearch.WordTrace]
  refine ⟨140358338971342645914832697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93572225980895097276555131 140358338971342645914832697)
  ·
    refine ⟨105268754228506984436124523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140358338971342645914832697 105268754228506984436124523)
    ·
      refine ⟨157903131342760476654186785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105268754228506984436124523 157903131342760476654186785)
      ·
        refine ⟨118427348507070357490640089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157903131342760476654186785 118427348507070357490640089)
        ·
          refine ⟨88820511380302768117980067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118427348507070357490640089 88820511380302768117980067)
          ·
            refine ⟨133230767070454152176970101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88820511380302768117980067 133230767070454152176970101)
            ·
              refine ⟨12490384412855076766590947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133230767070454152176970101 12490384412855076766590947)
              ·
                refine ⟨18735576619282615149886421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12490384412855076766590947 18735576619282615149886421)
                ·
                  refine ⟨439115077014436292575463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18735576619282615149886421 439115077014436292575463)
                  ·
                    rfl

theorem cell22_3848281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 7].length) (baseStart_3848281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3848281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3848281 prefixEnd_3848281 := by exact prefixLift 3848281
  have htrace : WordTrace (prefixWord ++ tailWord_3848281) baseStart_3848281 baseEnd_3848281 := by
    simpa [prefixWord, tailWord_3848281, baseEnd_3848281] using wordTrace_append hprefix tailTrace_3848281
  have hstable : (prefixWord ++ tailWord_3848281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848281).length < 2 ^ (prefixWord ++ tailWord_3848281).sum := by decide
  have hdescent : baseEnd_3848281 < baseStart_3848281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848342 : List Nat := [5, 3, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_3848342 : Nat := 118140960795 + 3848342 * 2 ^ 59
def prefixEnd_3848342 : Nat := 4983230072969 + 3 ^ 40 * 3848342 * 2
def baseEnd_3848342 : Nat := 1317366112589925051951203

theorem tailTrace_3848342 : CollatzResearch.WordTrace tailWord_3848342 prefixEnd_3848342 1317366112589925051951203 := by
  unfold tailWord_3848342
  simp only [CollatzResearch.WordTrace]
  refine ⟨8772535239007603333300205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93573709216081102221868853 8772535239007603333300205)
  ·
    refine ⟨3289700714627851249987577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8772535239007603333300205 3289700714627851249987577)
    ·
      refine ⟨2467275535970888437490683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3289700714627851249987577 2467275535970888437490683)
      ·
        refine ⟨3700913303956332656236025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2467275535970888437490683 3700913303956332656236025)
        ·
          refine ⟨2775684977967249492177019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3700913303956332656236025 2775684977967249492177019)
          ·
            refine ⟨4163527466950874238265529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2775684977967249492177019 4163527466950874238265529)
            ·
              refine ⟨3122645600213155678699147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4163527466950874238265529 3122645600213155678699147)
              ·
                refine ⟨4683968400319733518048721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3122645600213155678699147 4683968400319733518048721)
                ·
                  refine ⟨3512976300239800138536541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4683968400319733518048721 3512976300239800138536541)
                  ·
                    refine ⟨1317366112589925051951203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3512976300239800138536541 1317366112589925051951203)
                    ·
                      rfl

theorem cell22_3848342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_3848342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3848342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3848342 prefixEnd_3848342 := by exact prefixLift 3848342
  have htrace : WordTrace (prefixWord ++ tailWord_3848342) baseStart_3848342 baseEnd_3848342 := by
    simpa [prefixWord, tailWord_3848342, baseEnd_3848342] using wordTrace_append hprefix tailTrace_3848342
  have hstable : (prefixWord ++ tailWord_3848342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848342).length < 2 ^ (prefixWord ++ tailWord_3848342).sum := by decide
  have hdescent : baseEnd_3848342 < baseStart_3848342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848362 : List Nat := [3, 1, 5, 1, 2, 1, 1, 1, 3, 4]
def baseStart_3848362 : Nat := 118140960795 + 3848362 * 2 ^ 59
def prefixEnd_3848362 : Nat := 4983230072969 + 3 ^ 40 * 3848362 * 2
def baseEnd_3848362 : Nat := 1317372958998651666451141

theorem tailTrace_3848362 : CollatzResearch.WordTrace tailWord_3848362 prefixEnd_3848362 1317372958998651666451141 := by
  unfold tailWord_3848362
  simp only [CollatzResearch.WordTrace]
  refine ⟨35090323321012299187132835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93574195522699464499020893 35090323321012299187132835)
  ·
    refine ⟨52635484981518448780699253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35090323321012299187132835 52635484981518448780699253)
    ·
      refine ⟨4934576717017354573190555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52635484981518448780699253 4934576717017354573190555)
      ·
        refine ⟨7401865075526031859785833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4934576717017354573190555 7401865075526031859785833)
        ·
          refine ⟨5551398806644523894839375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7401865075526031859785833 5551398806644523894839375)
          ·
            refine ⟨8327098209966785842259063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5551398806644523894839375 8327098209966785842259063)
            ·
              refine ⟨12490647314950178763388595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8327098209966785842259063 12490647314950178763388595)
              ·
                refine ⟨18735970972425268145082893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12490647314950178763388595 18735970972425268145082893)
                ·
                  refine ⟨7025989114659475554406085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18735970972425268145082893 7025989114659475554406085)
                  ·
                    refine ⟨1317372958998651666451141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7025989114659475554406085 1317372958998651666451141)
                    ·
                      rfl

theorem cell22_3848362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_3848362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3848362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3848362 prefixEnd_3848362 := by exact prefixLift 3848362
  have htrace : WordTrace (prefixWord ++ tailWord_3848362) baseStart_3848362 baseEnd_3848362 := by
    simpa [prefixWord, tailWord_3848362, baseEnd_3848362] using wordTrace_append hprefix tailTrace_3848362
  have hstable : (prefixWord ++ tailWord_3848362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848362).length < 2 ^ (prefixWord ++ tailWord_3848362).sum := by decide
  have hdescent : baseEnd_3848362 < baseStart_3848362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848388 : List Nat := [2, 3, 3, 1, 2, 11]
def baseStart_3848388 : Nat := 118140960795 + 3848388 * 2 ^ 59
def prefixEnd_3848388 : Nat := 4983230072969 + 3 ^ 40 * 3848388 * 2
def baseEnd_3848388 : Nat := 16263973571975262534581

theorem tailTrace_3848388 : CollatzResearch.WordTrace tailWord_3848388 prefixEnd_3848388 16263973571975262534581 := by
  unfold tailWord_3848388
  simp only [CollatzResearch.WordTrace]
  refine ⟨70181120790977501594488909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93574827721303335459318545 70181120790977501594488909)
  ·
    refine ⟨26317920296616563097933341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70181120790977501594488909 26317920296616563097933341)
    ·
      refine ⟨9869220111231211161725003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26317920296616563097933341 9869220111231211161725003)
      ·
        refine ⟨14803830166846816742587505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9869220111231211161725003 14803830166846816742587505)
        ·
          refine ⟨11102872625135112556940629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14803830166846816742587505 11102872625135112556940629)
          ·
            refine ⟨16263973571975262534581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11102872625135112556940629 16263973571975262534581)
            ·
              rfl

theorem cell22_3848388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 11].length) (baseStart_3848388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3848388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3848388 prefixEnd_3848388 := by exact prefixLift 3848388
  have htrace : WordTrace (prefixWord ++ tailWord_3848388) baseStart_3848388 baseEnd_3848388 := by
    simpa [prefixWord, tailWord_3848388, baseEnd_3848388] using wordTrace_append hprefix tailTrace_3848388
  have hstable : (prefixWord ++ tailWord_3848388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848388).length < 2 ^ (prefixWord ++ tailWord_3848388).sum := by decide
  have hdescent : baseEnd_3848388 < baseStart_3848388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848448 : List Nat := [2, 1, 1, 2, 1, 1, 5, 2, 2, 5]
def baseStart_3848448 : Nat := 118140960795 + 3848448 * 2 ^ 59
def prefixEnd_3848448 : Nat := 4983230072969 + 3 ^ 40 * 3848448 * 2
def baseEnd_3848448 : Nat := 1317402398556176108800877

theorem tailTrace_3848448 : CollatzResearch.WordTrace tailWord_3848448 prefixEnd_3848448 1317402398556176108800877 := by
  unfold tailWord_3848448
  simp only [CollatzResearch.WordTrace]
  refine ⟨70182214980868816718080999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93576286641158422290774665 70182214980868816718080999)
  ·
    refine ⟨105273322471303225077121499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70182214980868816718080999 105273322471303225077121499)
    ·
      refine ⟨157909983706954837615682249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105273322471303225077121499 157909983706954837615682249)
      ·
        refine ⟨118432487780216128211761687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157909983706954837615682249 118432487780216128211761687)
        ·
          refine ⟨177648731670324192317642531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118432487780216128211761687 177648731670324192317642531)
          ·
            refine ⟨266473097505486288476463797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177648731670324192317642531 266473097505486288476463797)
            ·
              refine ⟨24981852891139339544668481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 266473097505486288476463797 24981852891139339544668481)
              ·
                refine ⟨18736389668354504658501361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24981852891139339544668481 18736389668354504658501361)
                ·
                  refine ⟨14052292251265878493876021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18736389668354504658501361 14052292251265878493876021)
                  ·
                    refine ⟨1317402398556176108800877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14052292251265878493876021 1317402398556176108800877)
                    ·
                      rfl

theorem cell22_3848448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 2, 5].length) (baseStart_3848448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3848448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3848448 prefixEnd_3848448 := by exact prefixLift 3848448
  have htrace : WordTrace (prefixWord ++ tailWord_3848448) baseStart_3848448 baseEnd_3848448 := by
    simpa [prefixWord, tailWord_3848448, baseEnd_3848448] using wordTrace_append hprefix tailTrace_3848448
  have hstable : (prefixWord ++ tailWord_3848448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848448).length < 2 ^ (prefixWord ++ tailWord_3848448).sum := by decide
  have hdescent : baseEnd_3848448 < baseStart_3848448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848463 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 5, 4]
def baseStart_3848463 : Nat := 118140960795 + 3848463 * 2 ^ 59
def prefixEnd_3848463 : Nat := 4983230072969 + 3 ^ 40 * 3848463 * 2
def baseEnd_3848463 : Nat := 1317407533362721069675831

theorem tailTrace_3848463 : CollatzResearch.WordTrace tailWord_3848463 prefixEnd_3848463 1317407533362721069675831 := by
  unfold tailWord_3848463
  simp only [CollatzResearch.WordTrace]
  refine ⟨140364977056683290997958043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93576651371122193998638695 140364977056683290997958043)
  ·
    refine ⟨210547465585024936496937065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140364977056683290997958043 210547465585024936496937065)
    ·
      refine ⟨157910599188768702372702799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210547465585024936496937065 157910599188768702372702799)
      ·
        refine ⟨236865898783153053559054199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157910599188768702372702799 236865898783153053559054199)
        ·
          refine ⟨355298848174729580338581299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236865898783153053559054199 355298848174729580338581299)
          ·
            refine ⟨532948272262094370507871949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355298848174729580338581299 532948272262094370507871949)
            ·
              refine ⟨199855602098285388940451981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 532948272262094370507871949 199855602098285388940451981)
              ·
                refine ⟨74945850786857020852669493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199855602098285388940451981 74945850786857020852669493)
                ·
                  refine ⟨7026173511267845704937765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74945850786857020852669493 7026173511267845704937765)
                  ·
                    refine ⟨1317407533362721069675831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7026173511267845704937765 1317407533362721069675831)
                    ·
                      rfl

theorem cell22_3848463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 4].length) (baseStart_3848463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3848463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3848463 prefixEnd_3848463 := by exact prefixLift 3848463
  have htrace : WordTrace (prefixWord ++ tailWord_3848463) baseStart_3848463 baseEnd_3848463 := by
    simpa [prefixWord, tailWord_3848463, baseEnd_3848463] using wordTrace_append hprefix tailTrace_3848463
  have hstable : (prefixWord ++ tailWord_3848463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848463).length < 2 ^ (prefixWord ++ tailWord_3848463).sum := by decide
  have hdescent : baseEnd_3848463 < baseStart_3848463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848488 : List Nat := [2, 1, 5, 1, 4, 1, 1, 3, 1, 3]
def baseStart_3848488 : Nat := 118140960795 + 3848488 * 2 ^ 59
def prefixEnd_3848488 : Nat := 4983230072969 + 3 ^ 40 * 3848488 * 2
def baseEnd_3848488 : Nat := 1317416091373629337800755

theorem tailTrace_3848488 : CollatzResearch.WordTrace tailWord_3848488 prefixEnd_3848488 1317416091373629337800755 := by
  unfold tailWord_3848488
  simp only [CollatzResearch.WordTrace]
  refine ⟨70182944440796360133809059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93577259254395146845078745 70182944440796360133809059)
  ·
    refine ⟨105274416661194540200713589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70182944440796360133809059 105274416661194540200713589)
    ·
      refine ⟨9869476561986988143816899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105274416661194540200713589 9869476561986988143816899)
      ·
        refine ⟨14804214842980482215725349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9869476561986988143816899 14804214842980482215725349)
        ·
          refine ⟨2775790283058840415448503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14804214842980482215725349 2775790283058840415448503)
          ·
            refine ⟨4163685424588260623172755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2775790283058840415448503 4163685424588260623172755)
            ·
              refine ⟨6245528136882390934759133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4163685424588260623172755 6245528136882390934759133)
              ·
                refine ⟨2342073051330896600534675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6245528136882390934759133 2342073051330896600534675)
                ·
                  refine ⟨3513109576996344900802013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2342073051330896600534675 3513109576996344900802013)
                  ·
                    refine ⟨1317416091373629337800755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3513109576996344900802013 1317416091373629337800755)
                    ·
                      rfl

theorem cell22_3848488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_3848488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3848488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3848488 prefixEnd_3848488 := by exact prefixLift 3848488
  have htrace : WordTrace (prefixWord ++ tailWord_3848488) baseStart_3848488 baseEnd_3848488 := by
    simpa [prefixWord, tailWord_3848488, baseEnd_3848488] using wordTrace_append hprefix tailTrace_3848488
  have hstable : (prefixWord ++ tailWord_3848488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848488).length < 2 ^ (prefixWord ++ tailWord_3848488).sum := by decide
  have hdescent : baseEnd_3848488 < baseStart_3848488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848555 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 5, 3]
def baseStart_3848555 : Nat := 118140960795 + 3848555 * 2 ^ 59
def prefixEnd_3848555 : Nat := 4983230072969 + 3 ^ 40 * 3848555 * 2
def baseEnd_3848555 : Nat := 1317439026842863496375549

theorem tailTrace_3848555 : CollatzResearch.WordTrace tailWord_3848555 prefixEnd_3848555 1317439026842863496375549 := by
  unfold tailWord_3848555
  simp only [CollatzResearch.WordTrace]
  refine ⟨140368332572349990710307119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93578888381566660473538079 140368332572349990710307119)
  ·
    refine ⟨210552498858524986065460679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140368332572349990710307119 210552498858524986065460679)
    ·
      refine ⟨315828748287787479098191019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210552498858524986065460679 315828748287787479098191019)
      ·
        refine ⟨473743122431681218647286529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315828748287787479098191019 473743122431681218647286529)
        ·
          refine ⟨355307341823760913985464897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473743122431681218647286529 355307341823760913985464897)
          ·
            refine ⟨266480506367820685489098673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355307341823760913985464897 266480506367820685489098673)
            ·
              refine ⟨199860379775865514116824005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266480506367820685489098673 199860379775865514116824005)
              ·
                refine ⟨37473821207974783896904501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199860379775865514116824005 37473821207974783896904501)
                ·
                  refine ⟨3513170738247635990334797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37473821207974783896904501 3513170738247635990334797)
                  ·
                    refine ⟨1317439026842863496375549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3513170738247635990334797 1317439026842863496375549)
                    ·
                      rfl

theorem cell22_3848555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5, 3].length) (baseStart_3848555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3848555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3848555 prefixEnd_3848555 := by exact prefixLift 3848555
  have htrace : WordTrace (prefixWord ++ tailWord_3848555) baseStart_3848555 baseEnd_3848555 := by
    simpa [prefixWord, tailWord_3848555, baseEnd_3848555] using wordTrace_append hprefix tailTrace_3848555
  have hstable : (prefixWord ++ tailWord_3848555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848555).length < 2 ^ (prefixWord ++ tailWord_3848555).sum := by decide
  have hdescent : baseEnd_3848555 < baseStart_3848555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848679 : List Nat := [1, 1, 5, 2, 1, 1, 2, 4, 2, 3]
def baseStart_3848679 : Nat := 118140960795 + 3848679 * 2 ^ 59
def prefixEnd_3848679 : Nat := 4983230072969 + 3 ^ 40 * 3848679 * 2
def baseEnd_3848679 : Nat := 1317481474576968506275169

theorem tailTrace_3848679 : CollatzResearch.WordTrace tailWord_3848679 prefixEnd_3848679 1317481474576968506275169 := by
  unfold tailWord_3848679
  simp only [CollatzResearch.WordTrace]
  refine ⟨140372855223900759887821091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93581903482600506591880727 140372855223900759887821091)
  ·
    refine ⟨210559282835851139831731637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140372855223900759887821091 210559282835851139831731637)
    ·
      refine ⟨19739932765861044359224841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 210559282835851139831731637 19739932765861044359224841)
      ·
        refine ⟨14804949574395783269418631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19739932765861044359224841 14804949574395783269418631)
        ·
          refine ⟨22207424361593674904127947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14804949574395783269418631 22207424361593674904127947)
          ·
            refine ⟨33311136542390512356191921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22207424361593674904127947 33311136542390512356191921)
            ·
              refine ⟨24983352406792884267143941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33311136542390512356191921 24983352406792884267143941)
              ·
                refine ⟨4684378576273665800089489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24983352406792884267143941 4684378576273665800089489)
                ·
                  refine ⟨3513283932205249350067117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4684378576273665800089489 3513283932205249350067117)
                  ·
                    refine ⟨1317481474576968506275169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3513283932205249350067117 1317481474576968506275169)
                    ·
                      rfl

theorem cell22_3848679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_3848679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3848679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3848679 prefixEnd_3848679 := by exact prefixLift 3848679
  have htrace : WordTrace (prefixWord ++ tailWord_3848679) baseStart_3848679 baseEnd_3848679 := by
    simpa [prefixWord, tailWord_3848679, baseEnd_3848679] using wordTrace_append hprefix tailTrace_3848679
  have hstable : (prefixWord ++ tailWord_3848679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848679).length < 2 ^ (prefixWord ++ tailWord_3848679).sum := by decide
  have hdescent : baseEnd_3848679 < baseStart_3848679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848707 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 5, 3]
def baseStart_3848707 : Nat := 118140960795 + 3848707 * 2 ^ 59
def prefixEnd_3848707 : Nat := 4983230072969 + 3 ^ 40 * 3848707 * 2
def baseEnd_3848707 : Nat := 1317491059549185766575083

theorem tailTrace_3848707 : CollatzResearch.WordTrace tailWord_3848707 prefixEnd_3848707 1317491059549185766575083 := by
  unfold tailWord_3848707
  simp only [CollatzResearch.WordTrace]
  refine ⟨140373876467799320669840375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93582584311866213779893583 140373876467799320669840375)
  ·
    refine ⟨210560814701698981004760563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140373876467799320669840375 210560814701698981004760563)
    ·
      refine ⟨315841222052548471507140845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210560814701698981004760563 315841222052548471507140845)
      ·
        refine ⟨118440458269705676815177817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315841222052548471507140845 118440458269705676815177817)
        ·
          refine ⟨88830343702279257611383363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118440458269705676815177817 88830343702279257611383363)
          ·
            refine ⟨133245515553418886417075045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88830343702279257611383363 133245515553418886417075045)
            ·
              refine ⟨24983534166266041203201571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133245515553418886417075045 24983534166266041203201571)
              ·
                refine ⟨37475301249399061804802357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24983534166266041203201571 37475301249399061804802357)
                ·
                  refine ⟨3513309492131162044200221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37475301249399061804802357 3513309492131162044200221)
                  ·
                    refine ⟨1317491059549185766575083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3513309492131162044200221 1317491059549185766575083)
                    ·
                      rfl

theorem cell22_3848707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 5, 3].length) (baseStart_3848707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3848707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3848707 prefixEnd_3848707 := by exact prefixLift 3848707
  have htrace : WordTrace (prefixWord ++ tailWord_3848707) baseStart_3848707 baseEnd_3848707 := by
    simpa [prefixWord, tailWord_3848707, baseEnd_3848707] using wordTrace_append hprefix tailTrace_3848707
  have hstable : (prefixWord ++ tailWord_3848707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848707).length < 2 ^ (prefixWord ++ tailWord_3848707).sum := by decide
  have hdescent : baseEnd_3848707 < baseStart_3848707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848743 : List Nat := [1, 1, 7, 2, 2, 1, 1, 7]
def baseStart_3848743 : Nat := 118140960795 + 3848743 * 2 ^ 59
def prefixEnd_3848743 : Nat := 4983230072969 + 3 ^ 40 * 3848743 * 2
def baseEnd_3848743 : Nat := 146389264787210408074997

theorem tailTrace_3848743 : CollatzResearch.WordTrace tailWord_3848743 prefixEnd_3848743 146389264787210408074997 := by
  unfold tailWord_3848743
  simp only [CollatzResearch.WordTrace]
  refine ⟨140375189495668898818150883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93583459663779265878767255 140375189495668898818150883)
  ·
    refine ⟨210562784243503348227226325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140375189495668898818150883 210562784243503348227226325)
    ·
      refine ⟨4935065255707109724075617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 210562784243503348227226325 4935065255707109724075617)
      ·
        refine ⟨3701298941780332293056713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4935065255707109724075617 3701298941780332293056713)
        ·
          refine ⟨2775974206335249219792535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3701298941780332293056713 2775974206335249219792535)
          ·
            refine ⟨4163961309502873829688803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2775974206335249219792535 4163961309502873829688803)
            ·
              refine ⟨6245941964254310744533205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4163961309502873829688803 6245941964254310744533205)
              ·
                refine ⟨146389264787210408074997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6245941964254310744533205 146389264787210408074997)
                ·
                  rfl

theorem cell22_3848743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 7].length) (baseStart_3848743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3848743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3848743 prefixEnd_3848743 := by exact prefixLift 3848743
  have htrace : WordTrace (prefixWord ++ tailWord_3848743) baseStart_3848743 baseEnd_3848743 := by
    simpa [prefixWord, tailWord_3848743, baseEnd_3848743] using wordTrace_append hprefix tailTrace_3848743
  have hstable : (prefixWord ++ tailWord_3848743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848743).length < 2 ^ (prefixWord ++ tailWord_3848743).sum := by decide
  have hdescent : baseEnd_3848743 < baseStart_3848743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848767 : List Nat := [1, 1, 2, 2, 3, 2, 1, 3, 3, 4]
def baseStart_3848767 : Nat := 118140960795 + 3848767 * 2 ^ 59
def prefixEnd_3848767 : Nat := 4983230072969 + 3 ^ 40 * 3848767 * 2
def baseEnd_3848767 : Nat := 1317511598775365610074899

theorem tailTrace_3848767 : CollatzResearch.WordTrace tailWord_3848767 prefixEnd_3848767 1317511598775365610074899 := by
  unfold tailWord_3848767
  simp only [CollatzResearch.WordTrace]
  refine ⟨140376064847581950917024555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93584043231721300611349703 140376064847581950917024555)
  ·
    refine ⟨210564097271372926375536833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140376064847581950917024555 210564097271372926375536833)
    ·
      refine ⟨157923072953529694781652625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210564097271372926375536833 157923072953529694781652625)
      ·
        refine ⟨118442304715147271086239469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157923072953529694781652625 118442304715147271086239469)
        ·
          refine ⟨44415864268180226657339801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118442304715147271086239469 44415864268180226657339801)
          ·
            refine ⟨33311898201135169993004851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44415864268180226657339801 33311898201135169993004851)
            ·
              refine ⟨49967847301702754989507277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33311898201135169993004851 49967847301702754989507277)
              ·
                refine ⟨18737942738138533121065229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49967847301702754989507277 18737942738138533121065229)
                ·
                  refine ⟨7026728526801949920399461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18737942738138533121065229 7026728526801949920399461)
                  ·
                    refine ⟨1317511598775365610074899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7026728526801949920399461 1317511598775365610074899)
                    ·
                      rfl

theorem cell22_3848767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 4].length) (baseStart_3848767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3848767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3848767 prefixEnd_3848767 := by exact prefixLift 3848767
  have htrace : WordTrace (prefixWord ++ tailWord_3848767) baseStart_3848767 baseEnd_3848767 := by
    simpa [prefixWord, tailWord_3848767, baseEnd_3848767] using wordTrace_append hprefix tailTrace_3848767
  have hstable : (prefixWord ++ tailWord_3848767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848767).length < 2 ^ (prefixWord ++ tailWord_3848767).sum := by decide
  have hdescent : baseEnd_3848767 < baseStart_3848767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848812 : List Nat := [2, 2, 1, 1, 3, 1, 3, 2, 1, 6]
def baseStart_3848812 : Nat := 118140960795 + 3848812 * 2 ^ 59
def prefixEnd_3848812 : Nat := 4983230072969 + 3 ^ 40 * 3848812 * 2
def baseEnd_3848812 : Nat := 1317527003195000492699761

theorem tailTrace_3848812 : CollatzResearch.WordTrace tailWord_3848812 prefixEnd_3848812 1317527003195000492699761 := by
  unfold tailWord_3848812
  simp only [CollatzResearch.WordTrace]
  refine ⟨70188853066209461801206345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93585137421612615734941793 70188853066209461801206345)
  ·
    refine ⟨52641639799657096350904759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70188853066209461801206345 52641639799657096350904759)
    ·
      refine ⟨78962459699485644526357139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52641639799657096350904759 78962459699485644526357139)
      ·
        refine ⟨118443689549228466789535709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78962459699485644526357139 118443689549228466789535709)
        ·
          refine ⟨44416383580960675046075891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118443689549228466789535709 44416383580960675046075891)
          ·
            refine ⟨66624575371441012569113837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44416383580960675046075891 66624575371441012569113837)
            ·
              refine ⟨24984215764290379713417689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66624575371441012569113837 24984215764290379713417689)
              ·
                refine ⟨18738161823217784785063267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24984215764290379713417689 18738161823217784785063267)
                ·
                  refine ⟨28107242734826677177594901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18738161823217784785063267 28107242734826677177594901)
                  ·
                    refine ⟨1317527003195000492699761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28107242734826677177594901 1317527003195000492699761)
                    ·
                      rfl

theorem cell22_3848812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_3848812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3848812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3848812 prefixEnd_3848812 := by exact prefixLift 3848812
  have htrace : WordTrace (prefixWord ++ tailWord_3848812) baseStart_3848812 baseEnd_3848812 := by
    simpa [prefixWord, tailWord_3848812, baseEnd_3848812] using wordTrace_append hprefix tailTrace_3848812
  have hstable : (prefixWord ++ tailWord_3848812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848812).length < 2 ^ (prefixWord ++ tailWord_3848812).sum := by decide
  have hdescent : baseEnd_3848812 < baseStart_3848812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848857 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 2, 6]
def baseStart_3848857 : Nat := 118140960795 + 3848857 * 2 ^ 59
def prefixEnd_3848857 : Nat := 4983230072969 + 3 ^ 40 * 3848857 * 2
def baseEnd_3848857 : Nat := 1317542407614635375324623

theorem tailTrace_3848857 : CollatzResearch.WordTrace tailWord_3848857 prefixEnd_3848857 1317542407614635375324623 := by
  unfold tailWord_3848857
  simp only [CollatzResearch.WordTrace]
  refine ⟨140379347417255896287800825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93586231611503930858533883 140379347417255896287800825)
  ·
    refine ⟨105284510562941922215850619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140379347417255896287800825 105284510562941922215850619)
    ·
      refine ⟨157926765844412883323775929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105284510562941922215850619 157926765844412883323775929)
      ·
        refine ⟨118445074383309662492831947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157926765844412883323775929 118445074383309662492831947)
        ·
          refine ⟨177667611574964493739247921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118445074383309662492831947 177667611574964493739247921)
          ·
            refine ⟨133250708681223370304435941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177667611574964493739247921 133250708681223370304435941)
            ·
              refine ⟨24984507877729381932081739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133250708681223370304435941 24984507877729381932081739)
              ·
                refine ⟨37476761816594072898122609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24984507877729381932081739 37476761816594072898122609)
                ·
                  refine ⟨28107571362445554673591957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37476761816594072898122609 28107571362445554673591957)
                  ·
                    refine ⟨1317542407614635375324623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28107571362445554673591957 1317542407614635375324623)
                    ·
                      rfl

theorem cell22_3848857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 6].length) (baseStart_3848857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3848857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3848857 prefixEnd_3848857 := by exact prefixLift 3848857
  have htrace : WordTrace (prefixWord ++ tailWord_3848857) baseStart_3848857 baseEnd_3848857 := by
    simpa [prefixWord, tailWord_3848857, baseEnd_3848857] using wordTrace_append hprefix tailTrace_3848857
  have hstable : (prefixWord ++ tailWord_3848857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848857).length < 2 ^ (prefixWord ++ tailWord_3848857).sum := by decide
  have hdescent : baseEnd_3848857 < baseStart_3848857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848865 : List Nat := [1, 2, 3, 3, 3, 2, 2, 1, 2, 3]
def baseStart_3848865 : Nat := 118140960795 + 3848865 * 2 ^ 59
def prefixEnd_3848865 : Nat := 4983230072969 + 3 ^ 40 * 3848865 * 2
def baseEnd_3848865 : Nat := 1317545146178126021124599

theorem tailTrace_3848865 : CollatzResearch.WordTrace tailWord_3848865 prefixEnd_3848865 1317545146178126021124599 := by
  unfold tailWord_3848865
  simp only [CollatzResearch.WordTrace]
  refine ⟨140379639201226913654092049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93586426134151275769394699 140379639201226913654092049)
  ·
    refine ⟨105284729400920185240569037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140379639201226913654092049 105284729400920185240569037)
    ·
      refine ⟨39481773525345069465213389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105284729400920185240569037 39481773525345069465213389)
      ·
        refine ⟨14805665072004401049455021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39481773525345069465213389 14805665072004401049455021)
        ·
          refine ⟨5552124402001650393545633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14805665072004401049455021 5552124402001650393545633)
          ·
            refine ⟨4164093301501237795159225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5552124402001650393545633 4164093301501237795159225)
            ·
              refine ⟨3123069976125928346369419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4164093301501237795159225 3123069976125928346369419)
              ·
                refine ⟨4684604964188892519554129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3123069976125928346369419 4684604964188892519554129)
                ·
                  refine ⟨3513453723141669389665597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4684604964188892519554129 3513453723141669389665597)
                  ·
                    refine ⟨1317545146178126021124599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3513453723141669389665597 1317545146178126021124599)
                    ·
                      rfl

theorem cell22_3848865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_3848865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3848865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3848865 prefixEnd_3848865 := by exact prefixLift 3848865
  have htrace : WordTrace (prefixWord ++ tailWord_3848865) baseStart_3848865 baseEnd_3848865 := by
    simpa [prefixWord, tailWord_3848865, baseEnd_3848865] using wordTrace_append hprefix tailTrace_3848865
  have hstable : (prefixWord ++ tailWord_3848865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848865).length < 2 ^ (prefixWord ++ tailWord_3848865).sum := by decide
  have hdescent : baseEnd_3848865 < baseStart_3848865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848906 : List Nat := [3, 1, 2, 1, 4, 2, 2, 2, 5]
def baseStart_3848906 : Nat := 118140960795 + 3848906 * 2 ^ 59
def prefixEnd_3848906 : Nat := 4983230072969 + 3 ^ 40 * 3848906 * 2
def baseEnd_3848906 : Nat := 439186393772005193616491

theorem tailTrace_3848906 : CollatzResearch.WordTrace tailWord_3848906 prefixEnd_3848906 439186393772005193616491 := by
  unfold tailWord_3848906
  simp only [CollatzResearch.WordTrace]
  refine ⟨35095283648519594414083643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93587423062718918437556381 35095283648519594414083643)
  ·
    refine ⟨52642925472779391621125465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35095283648519594414083643 52642925472779391621125465)
    ·
      refine ⟨39482194104584543715844099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52642925472779391621125465 39482194104584543715844099)
      ·
        refine ⟨59223291156876815573766149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39482194104584543715844099 59223291156876815573766149)
        ·
          refine ⟨11104367091914402920081153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59223291156876815573766149 11104367091914402920081153)
          ·
            refine ⟨8328275318935802190060865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11104367091914402920081153 8328275318935802190060865)
            ·
              refine ⟨6246206489201851642545649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8328275318935802190060865 6246206489201851642545649)
              ·
                refine ⟨4684654866901388731909237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6246206489201851642545649 4684654866901388731909237)
                ·
                  refine ⟨439186393772005193616491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4684654866901388731909237 439186393772005193616491)
                  ·
                    rfl

theorem cell22_3848906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 5].length) (baseStart_3848906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3848906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3848906 prefixEnd_3848906 := by exact prefixLift 3848906
  have htrace : WordTrace (prefixWord ++ tailWord_3848906) baseStart_3848906 baseEnd_3848906 := by
    simpa [prefixWord, tailWord_3848906, baseEnd_3848906] using wordTrace_append hprefix tailTrace_3848906
  have hstable : (prefixWord ++ tailWord_3848906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848906).length < 2 ^ (prefixWord ++ tailWord_3848906).sum := by decide
  have hdescent : baseEnd_3848906 < baseStart_3848906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848910 : List Nat := [4, 1, 1, 1, 3, 2, 4, 2, 1, 3]
def baseStart_3848910 : Nat := 118140960795 + 3848910 * 2 ^ 59
def prefixEnd_3848910 : Nat := 4983230072969 + 3 ^ 40 * 3848910 * 2
def baseEnd_3848910 : Nat := 1317560550597760903749461

theorem tailTrace_3848910 : CollatzResearch.WordTrace tailWord_3848910 prefixEnd_3848910 1317560550597760903749461 := by
  unfold tailWord_3848910
  simp only [CollatzResearch.WordTrace]
  refine ⟨17547660060757985792435023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93587520324042590892986789 17547660060757985792435023)
  ·
    refine ⟨26321490091136978688652535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17547660060757985792435023 26321490091136978688652535)
    ·
      refine ⟨39482235136705468032978803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26321490091136978688652535 39482235136705468032978803)
      ·
        refine ⟨59223352705058202049468205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39482235136705468032978803 59223352705058202049468205)
        ·
          refine ⟨22208757264396825768550577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59223352705058202049468205 22208757264396825768550577)
          ·
            refine ⟨16656567948297619326412933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22208757264396825768550577 16656567948297619326412933)
            ·
              refine ⟨3123106490305803623702425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16656567948297619326412933 3123106490305803623702425)
              ·
                refine ⟨2342329867729352717776819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3123106490305803623702425 2342329867729352717776819)
                ·
                  refine ⟨3513494801594029076665229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2342329867729352717776819 3513494801594029076665229)
                  ·
                    refine ⟨1317560550597760903749461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3513494801594029076665229 1317560550597760903749461)
                    ·
                      rfl

theorem cell22_3848910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_3848910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3848910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3848910 prefixEnd_3848910 := by exact prefixLift 3848910
  have htrace : WordTrace (prefixWord ++ tailWord_3848910) baseStart_3848910 baseEnd_3848910 := by
    simpa [prefixWord, tailWord_3848910, baseEnd_3848910] using wordTrace_append hprefix tailTrace_3848910
  have hstable : (prefixWord ++ tailWord_3848910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848910).length < 2 ^ (prefixWord ++ tailWord_3848910).sum := by decide
  have hdescent : baseEnd_3848910 < baseStart_3848910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848919 : List Nat := [1, 1, 3, 2, 1, 4, 1, 2, 3, 4]
def baseStart_3848919 : Nat := 118140960795 + 3848919 * 2 ^ 59
def prefixEnd_3848919 : Nat := 4983230072969 + 3 ^ 40 * 3848919 * 2
def baseEnd_3848919 : Nat := 1317563631481687880274433

theorem tailTrace_3848919 : CollatzResearch.WordTrace tailWord_3848919 prefixEnd_3848919 1317563631481687880274433 := by
  unfold tailWord_3848919
  simp only [CollatzResearch.WordTrace]
  refine ⟨140381608743031280876557811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93587739162020853917705207 140381608743031280876557811)
  ·
    refine ⟨210572413114546921314836717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140381608743031280876557811 210572413114546921314836717)
    ·
      refine ⟨78964654917955095493063769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210572413114546921314836717 78964654917955095493063769)
      ·
        refine ⟨59223491188466321619797827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78964654917955095493063769 59223491188466321619797827)
        ·
          refine ⟨88835236782699482429696741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59223491188466321619797827 88835236782699482429696741)
          ·
            refine ⟨16656606896756152955568139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88835236782699482429696741 16656606896756152955568139)
            ·
              refine ⟨24984910345134229433352209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16656606896756152955568139 24984910345134229433352209)
              ·
                refine ⟨18738682758850672075014157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24984910345134229433352209 18738682758850672075014157)
                ·
                  refine ⟨7027006034569002028130309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18738682758850672075014157 7027006034569002028130309)
                  ·
                    refine ⟨1317563631481687880274433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7027006034569002028130309 1317563631481687880274433)
                    ·
                      rfl

theorem cell22_3848919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_3848919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3848919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3848919 prefixEnd_3848919 := by exact prefixLift 3848919
  have htrace : WordTrace (prefixWord ++ tailWord_3848919) baseStart_3848919 baseEnd_3848919 := by
    simpa [prefixWord, tailWord_3848919, baseEnd_3848919] using wordTrace_append hprefix tailTrace_3848919
  have hstable : (prefixWord ++ tailWord_3848919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848919).length < 2 ^ (prefixWord ++ tailWord_3848919).sum := by decide
  have hdescent : baseEnd_3848919 < baseStart_3848919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848983 : List Nat := [1, 1, 3, 4, 3, 2, 1, 1, 1, 5]
def baseStart_3848983 : Nat := 118140960795 + 3848983 * 2 ^ 59
def prefixEnd_3848983 : Nat := 4983230072969 + 3 ^ 40 * 3848983 * 2
def baseEnd_3848983 : Nat := 1317585539989613046674237

theorem tailTrace_3848983 : CollatzResearch.WordTrace tailWord_3848983 prefixEnd_3848983 1317585539989613046674237 := by
  unfold tailWord_3848983
  simp only [CollatzResearch.WordTrace]
  refine ⟨140383943014799419806887603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93589295343199613204591735 140383943014799419806887603)
  ·
    refine ⟨210575914522199129710331405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140383943014799419806887603 210575914522199129710331405)
    ·
      refine ⟨78965967945824673641374277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210575914522199129710331405 78965967945824673641374277)
      ·
        refine ⟨14806118989842126307757677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78965967945824673641374277 14806118989842126307757677)
        ·
          refine ⟨5552294621190797365409129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14806118989842126307757677 5552294621190797365409129)
          ·
            refine ⟨4164220965893098024056847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5552294621190797365409129 4164220965893098024056847)
            ·
              refine ⟨6246331448839647036085271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4164220965893098024056847 6246331448839647036085271)
              ·
                refine ⟨9369497173259470554127907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6246331448839647036085271 9369497173259470554127907)
                ·
                  refine ⟨14054245759889205831191861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9369497173259470554127907 14054245759889205831191861)
                  ·
                    refine ⟨1317585539989613046674237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14054245759889205831191861 1317585539989613046674237)
                    ·
                      rfl

theorem cell22_3848983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 5].length) (baseStart_3848983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3848983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3848983 prefixEnd_3848983 := by exact prefixLift 3848983
  have htrace : WordTrace (prefixWord ++ tailWord_3848983) baseStart_3848983 baseEnd_3848983 := by
    simpa [prefixWord, tailWord_3848983, baseEnd_3848983] using wordTrace_append hprefix tailTrace_3848983
  have hstable : (prefixWord ++ tailWord_3848983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848983).length < 2 ^ (prefixWord ++ tailWord_3848983).sum := by decide
  have hdescent : baseEnd_3848983 < baseStart_3848983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848996 : List Nat := [2, 3, 1, 3, 3, 1, 1, 8]
def baseStart_3848996 : Nat := 118140960795 + 3848996 * 2 ^ 59
def prefixEnd_3848996 : Nat := 4983230072969 + 3 ^ 40 * 3848996 * 2
def baseEnd_3848996 : Nat := 146398887795031705122133

theorem tailTrace_3848996 : CollatzResearch.WordTrace tailWord_3848996 prefixEnd_3848996 146398887795031705122133 := by
  unfold tailWord_3848996
  simp only [CollatzResearch.WordTrace]
  refine ⟨70192208581876161513555421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93589611442501548684740561 70192208581876161513555421)
  ·
    refine ⟨26322078218203560567583283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70192208581876161513555421 26322078218203560567583283)
    ·
      refine ⟨39483117327305340851374925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26322078218203560567583283 39483117327305340851374925)
      ·
        refine ⟨14806168997739502819265597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39483117327305340851374925 14806168997739502819265597)
        ·
          refine ⟨5552313374152313557224599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14806168997739502819265597 5552313374152313557224599)
          ·
            refine ⟨8328470061228470335836899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5552313374152313557224599 8328470061228470335836899)
            ·
              refine ⟨12492705091842705503755349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8328470061228470335836899 12492705091842705503755349)
              ·
                refine ⟨146398887795031705122133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12492705091842705503755349 146398887795031705122133)
                ·
                  rfl

theorem cell22_3848996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 8].length) (baseStart_3848996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3848996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3848996 prefixEnd_3848996 := by exact prefixLift 3848996
  have htrace : WordTrace (prefixWord ++ tailWord_3848996) baseStart_3848996 baseEnd_3848996 := by
    simpa [prefixWord, tailWord_3848996, baseEnd_3848996] using wordTrace_append hprefix tailTrace_3848996
  have hstable : (prefixWord ++ tailWord_3848996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848996).length < 2 ^ (prefixWord ++ tailWord_3848996).sum := by decide
  have hdescent : baseEnd_3848996 < baseStart_3848996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849002 : List Nat := [3, 1, 4, 3, 1, 2, 1, 3, 4]
def baseStart_3849002 : Nat := 118140960795 + 3849002 * 2 ^ 59
def prefixEnd_3849002 : Nat := 4983230072969 + 3 ^ 40 * 3849002 * 2
def baseEnd_3849002 : Nat := 439197348025967776816393

theorem tailTrace_3849002 : CollatzResearch.WordTrace tailWord_3849002 prefixEnd_3849002 439197348025967776816393 := by
  unfold tailWord_3849002
  simp only [CollatzResearch.WordTrace]
  refine ⟨35096159000432646512957315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93589757334487057367886173 35096159000432646512957315)
  ·
    refine ⟨52644238500648969769435973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35096159000432646512957315 52644238500648969769435973)
    ·
      refine ⟨9870794718871681831769245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52644238500648969769435973 9870794718871681831769245)
      ·
        refine ⟨3701548019576880686913467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9870794718871681831769245 3701548019576880686913467)
        ·
          refine ⟨5552322029365321030370201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3701548019576880686913467 5552322029365321030370201)
          ·
            refine ⟨4164241522023990772777651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5552322029365321030370201 4164241522023990772777651)
            ·
              refine ⟨6246362283035986159166477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4164241522023990772777651 6246362283035986159166477)
              ·
                refine ⟨2342385856138494809687429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6246362283035986159166477 2342385856138494809687429)
                ·
                  refine ⟨439197348025967776816393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2342385856138494809687429 439197348025967776816393)
                  ·
                    rfl

theorem cell22_3849002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 3, 4].length) (baseStart_3849002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849002 prefixEnd_3849002 := by exact prefixLift 3849002
  have htrace : WordTrace (prefixWord ++ tailWord_3849002) baseStart_3849002 baseEnd_3849002 := by
    simpa [prefixWord, tailWord_3849002, baseEnd_3849002] using wordTrace_append hprefix tailTrace_3849002
  have hstable : (prefixWord ++ tailWord_3849002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849002).length < 2 ^ (prefixWord ++ tailWord_3849002).sum := by decide
  have hdescent : baseEnd_3849002 < baseStart_3849002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849030 : List Nat := [6, 1, 1, 2, 2, 1, 2, 7]
def baseStart_3849030 : Nat := 118140960795 + 3849030 * 2 ^ 59
def prefixEnd_3849030 : Nat := 4983230072969 + 3 ^ 40 * 3849030 * 2
def baseEnd_3849030 : Nat := 146400181005568954527677

theorem tailTrace_3849030 : CollatzResearch.WordTrace tailWord_3849030 prefixEnd_3849030 146400181005568954527677 := by
  unfold tailWord_3849030
  simp only [CollatzResearch.WordTrace]
  refine ⟨4387051788925910838557767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 93590438163752764555899029 4387051788925910838557767)
  ·
    refine ⟨6580577683388866257836651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4387051788925910838557767 6580577683388866257836651)
    ·
      refine ⟨9870866525083299386754977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6580577683388866257836651 9870866525083299386754977)
      ·
        refine ⟨7403149893812474540066233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9870866525083299386754977 7403149893812474540066233)
        ·
          refine ⟨5552362420359355905049675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7403149893812474540066233 5552362420359355905049675)
          ·
            refine ⟨8328543630539033857574513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5552362420359355905049675 8328543630539033857574513)
            ·
              refine ⟨6246407722904275393180885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8328543630539033857574513 6246407722904275393180885)
              ·
                refine ⟨146400181005568954527677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6246407722904275393180885 146400181005568954527677)
                ·
                  rfl

theorem cell22_3849030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_3849030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849030 prefixEnd_3849030 := by exact prefixLift 3849030
  have htrace : WordTrace (prefixWord ++ tailWord_3849030) baseStart_3849030 baseEnd_3849030 := by
    simpa [prefixWord, tailWord_3849030, baseEnd_3849030] using wordTrace_append hprefix tailTrace_3849030
  have hstable : (prefixWord ++ tailWord_3849030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849030).length < 2 ^ (prefixWord ++ tailWord_3849030).sum := by decide
  have hdescent : baseEnd_3849030 < baseStart_3849030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849071 : List Nat := [1, 1, 2, 1, 3, 1, 1, 7, 1, 4]
def baseStart_3849071 : Nat := 118140960795 + 3849071 * 2 ^ 59
def prefixEnd_3849071 : Nat := 4983230072969 + 3 ^ 40 * 3849071 * 2
def baseEnd_3849071 : Nat := 1317615664188010150473967

theorem tailTrace_3849071 : CollatzResearch.WordTrace tailWord_3849071 prefixEnd_3849071 1317615664188010150473967 := by
  unfold tailWord_3849071
  simp only [CollatzResearch.WordTrace]
  refine ⟨140387152638480610836091067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93591435092320407224060711 140387152638480610836091067)
  ·
    refine ⟨210580728957720916254136601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140387152638480610836091067 210580728957720916254136601)
    ·
      refine ⟨157935546718290687190602451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210580728957720916254136601 157935546718290687190602451)
      ·
        refine ⟨236903320077436030785903677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157935546718290687190602451 236903320077436030785903677)
        ·
          refine ⟨88838745029038511544713879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236903320077436030785903677 88838745029038511544713879)
          ·
            refine ⟨133258117543557767317070819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88838745029038511544713879 133258117543557767317070819)
            ·
              refine ⟨199887176315336650975606229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133258117543557767317070819 199887176315336650975606229)
              ·
                refine ⟨4684855694890702757240771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 199887176315336650975606229 4684855694890702757240771)
                ·
                  refine ⟨7027283542336054135861157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4684855694890702757240771 7027283542336054135861157)
                  ·
                    refine ⟨1317615664188010150473967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7027283542336054135861157 1317615664188010150473967)
                    ·
                      rfl

theorem cell22_3849071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 4].length) (baseStart_3849071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849071 prefixEnd_3849071 := by exact prefixLift 3849071
  have htrace : WordTrace (prefixWord ++ tailWord_3849071) baseStart_3849071 baseEnd_3849071 := by
    simpa [prefixWord, tailWord_3849071, baseEnd_3849071] using wordTrace_append hprefix tailTrace_3849071
  have hstable : (prefixWord ++ tailWord_3849071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849071).length < 2 ^ (prefixWord ++ tailWord_3849071).sum := by decide
  have hdescent : baseEnd_3849071 < baseStart_3849071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849122 : List Nat := [3, 3, 1, 2, 2, 3, 2, 1, 1, 4]
def baseStart_3849122 : Nat := 118140960795 + 3849122 * 2 ^ 59
def prefixEnd_3849122 : Nat := 4983230072969 + 3 ^ 40 * 3849122 * 2
def baseEnd_3849122 : Nat := 1317633122530263017448811

theorem tailTrace_3849122 : CollatzResearch.WordTrace tailWord_3849122 prefixEnd_3849122 1317633122530263017448811 := by
  unfold tailWord_3849122
  simp only [CollatzResearch.WordTrace]
  refine ⟨35097253190323961636549405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93592675174197231030798413 35097253190323961636549405)
  ·
    refine ⟨13161469946371485613706027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35097253190323961636549405 13161469946371485613706027)
    ·
      refine ⟨19742204919557228420559041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13161469946371485613706027 19742204919557228420559041)
      ·
        refine ⟨14806653689667921315419281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19742204919557228420559041 14806653689667921315419281)
        ·
          refine ⟨11104990267250940986564461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14806653689667921315419281 11104990267250940986564461)
          ·
            refine ⟨4164371350219102869961673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11104990267250940986564461 4164371350219102869961673)
            ·
              refine ⟨3123278512664327152471255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4164371350219102869961673 3123278512664327152471255)
              ·
                refine ⟨4684917768996490728706883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3123278512664327152471255 4684917768996490728706883)
                ·
                  refine ⟨7027376653494736093060325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4684917768996490728706883 7027376653494736093060325)
                  ·
                    refine ⟨1317633122530263017448811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7027376653494736093060325 1317633122530263017448811)
                    ·
                      rfl

theorem cell22_3849122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_3849122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849122 prefixEnd_3849122 := by exact prefixLift 3849122
  have htrace : WordTrace (prefixWord ++ tailWord_3849122) baseStart_3849122 baseEnd_3849122 := by
    simpa [prefixWord, tailWord_3849122, baseEnd_3849122] using wordTrace_append hprefix tailTrace_3849122
  have hstable : (prefixWord ++ tailWord_3849122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849122).length < 2 ^ (prefixWord ++ tailWord_3849122).sum := by decide
  have hdescent : baseEnd_3849122 < baseStart_3849122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849163 : List Nat := [1, 1, 1, 1, 3, 5, 2, 2, 3, 3]
def baseStart_3849163 : Nat := 118140960795 + 3849163 * 2 ^ 59
def prefixEnd_3849163 : Nat := 4983230072969 + 3 ^ 40 * 3849163 * 2
def baseEnd_3849163 : Nat := 1317647157668152577173685

theorem tailTrace_3849163 : CollatzResearch.WordTrace tailWord_3849163 prefixEnd_3849163 1317647157668152577173685 := by
  unfold tailWord_3849163
  simp only [CollatzResearch.WordTrace]
  refine ⟨140390508154147310548440143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93593672102764873698960095 140390508154147310548440143)
  ·
    refine ⟨210585762231220965822660215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140390508154147310548440143 210585762231220965822660215)
    ·
      refine ⟨315878643346831448733990323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210585762231220965822660215 315878643346831448733990323)
      ·
        refine ⟨473817965020247173100985485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315878643346831448733990323 473817965020247173100985485)
        ·
          refine ⟨177681736882592689912869557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 473817965020247173100985485 177681736882592689912869557)
          ·
            refine ⟨16657662832743064679331521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 177681736882592689912869557 16657662832743064679331521)
            ·
              refine ⟨12493247124557298509498641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16657662832743064679331521 12493247124557298509498641)
              ·
                refine ⟨9369935343417973882123981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12493247124557298509498641 9369935343417973882123981)
                ·
                  refine ⟨3513725753781740205796493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9369935343417973882123981 3513725753781740205796493)
                  ·
                    refine ⟨1317647157668152577173685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3513725753781740205796493 1317647157668152577173685)
                    ·
                      rfl

theorem cell22_3849163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 3, 3].length) (baseStart_3849163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849163 prefixEnd_3849163 := by exact prefixLift 3849163
  have htrace : WordTrace (prefixWord ++ tailWord_3849163) baseStart_3849163 baseEnd_3849163 := by
    simpa [prefixWord, tailWord_3849163, baseEnd_3849163] using wordTrace_append hprefix tailTrace_3849163
  have hstable : (prefixWord ++ tailWord_3849163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849163).length < 2 ^ (prefixWord ++ tailWord_3849163).sum := by decide
  have hdescent : baseEnd_3849163 < baseStart_3849163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849176 : List Nat := [2, 1, 2, 2, 2, 3, 1, 2, 7]
def baseStart_3849176 : Nat := 118140960795 + 3849176 * 2 ^ 59
def prefixEnd_3849176 : Nat := 4983230072969 + 3 ^ 40 * 3849176 * 2
def baseEnd_3849176 : Nat := 439217202611274958866215

theorem tailTrace_3849176 : CollatzResearch.WordTrace tailWord_3849176 prefixEnd_3849176 439217202611274958866215 := by
  unfold tailWord_3849176
  simp only [CollatzResearch.WordTrace]
  refine ⟨70195491151550106884331691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93593988202066809179108921 70195491151550106884331691)
  ·
    refine ⟨105293236727325160326497537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70195491151550106884331691 105293236727325160326497537)
    ·
      refine ⟨78969927545493870244873153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105293236727325160326497537 78969927545493870244873153)
      ·
        refine ⟨59227445659120402683654865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78969927545493870244873153 59227445659120402683654865)
        ·
          refine ⟨44420584244340302012741149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59227445659120402683654865 44420584244340302012741149)
          ·
            refine ⟨16657719091627613254777931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44420584244340302012741149 16657719091627613254777931)
            ·
              refine ⟨24986578637441419882166897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16657719091627613254777931 24986578637441419882166897)
              ·
                refine ⟨18739933978081064911625173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24986578637441419882166897 18739933978081064911625173)
                ·
                  refine ⟨439217202611274958866215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18739933978081064911625173 439217202611274958866215)
                  ·
                    rfl

theorem cell22_3849176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 7].length) (baseStart_3849176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849176 prefixEnd_3849176 := by exact prefixLift 3849176
  have htrace : WordTrace (prefixWord ++ tailWord_3849176) baseStart_3849176 baseEnd_3849176 := by
    simpa [prefixWord, tailWord_3849176, baseEnd_3849176] using wordTrace_append hprefix tailTrace_3849176
  have hstable : (prefixWord ++ tailWord_3849176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849176).length < 2 ^ (prefixWord ++ tailWord_3849176).sum := by decide
  have hdescent : baseEnd_3849176 < baseStart_3849176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849221 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 8]
def baseStart_3849221 : Nat := 118140960795 + 3849221 * 2 ^ 59
def prefixEnd_3849221 : Nat := 4983230072969 + 3 ^ 40 * 3849221 * 2
def baseEnd_3849221 : Nat := 439222337417819919741169

theorem tailTrace_3849221 : CollatzResearch.WordTrace tailWord_3849221 prefixEnd_3849221 439222337417819919741169 := by
  unfold tailWord_3849221
  simp only [CollatzResearch.WordTrace]
  refine ⟨140392623587937186454051517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93595082391958124302701011 140392623587937186454051517)
  ·
    refine ⟨52647233845476444920269319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140392623587937186454051517 52647233845476444920269319)
    ·
      refine ⟨78970850768214667380403979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52647233845476444920269319 78970850768214667380403979)
      ·
        refine ⟨118456276152322001070605969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78970850768214667380403979 118456276152322001070605969)
        ·
          refine ⟨88842207114241500802954477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118456276152322001070605969 88842207114241500802954477)
          ·
            refine ⟨33315827667840562801107929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88842207114241500802954477 33315827667840562801107929)
            ·
              refine ⟨24986870750880422100830947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33315827667840562801107929 24986870750880422100830947)
              ·
                refine ⟨37480306126320633151246421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24986870750880422100830947 37480306126320633151246421)
                ·
                  refine ⟨439222337417819919741169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37480306126320633151246421 439222337417819919741169)
                  ·
                    rfl

theorem cell22_3849221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 8].length) (baseStart_3849221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849221 prefixEnd_3849221 := by exact prefixLift 3849221
  have htrace : WordTrace (prefixWord ++ tailWord_3849221) baseStart_3849221 baseEnd_3849221 := by
    simpa [prefixWord, tailWord_3849221, baseEnd_3849221] using wordTrace_append hprefix tailTrace_3849221
  have hstable : (prefixWord ++ tailWord_3849221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849221).length < 2 ^ (prefixWord ++ tailWord_3849221).sum := by decide
  have hdescent : baseEnd_3849221 < baseStart_3849221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849223 : List Nat := [1, 1, 4, 3, 1, 1, 3, 1, 3, 4]
def baseStart_3849223 : Nat := 118140960795 + 3849223 * 2 ^ 59
def prefixEnd_3849223 : Nat := 4983230072969 + 3 ^ 40 * 3849223 * 2
def baseEnd_3849223 : Nat := 1317667696894332420673501

theorem tailTrace_3849223 : CollatzResearch.WordTrace tailWord_3849223 prefixEnd_3849223 1317667696894332420673501 := by
  unfold tailWord_3849223
  simp only [CollatzResearch.WordTrace]
  refine ⟨140392696533929940795624323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93595131022619960530416215 140392696533929940795624323)
  ·
    refine ⟨210589044800894911193436485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140392696533929940795624323 210589044800894911193436485)
    ·
      refine ⟨39485445900167795848769341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210589044800894911193436485 39485445900167795848769341)
      ·
        refine ⟨14807042212562923443288503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39485445900167795848769341 14807042212562923443288503)
        ·
          refine ⟨22210563318844385164932755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14807042212562923443288503 22210563318844385164932755)
          ·
            refine ⟨33315844978266577747399133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22210563318844385164932755 33315844978266577747399133)
            ·
              refine ⟨12493441866849966655274675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33315844978266577747399133 12493441866849966655274675)
              ·
                refine ⟨18740162800274949982912013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12493441866849966655274675 18740162800274949982912013)
                ·
                  refine ⟨7027561050103106243592005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18740162800274949982912013 7027561050103106243592005)
                  ·
                    refine ⟨1317667696894332420673501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7027561050103106243592005 1317667696894332420673501)
                    ·
                      rfl

theorem cell22_3849223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_3849223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849223 prefixEnd_3849223 := by exact prefixLift 3849223
  have htrace : WordTrace (prefixWord ++ tailWord_3849223) baseStart_3849223 baseEnd_3849223 := by
    simpa [prefixWord, tailWord_3849223, baseEnd_3849223] using wordTrace_append hprefix tailTrace_3849223
  have hstable : (prefixWord ++ tailWord_3849223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849223).length < 2 ^ (prefixWord ++ tailWord_3849223).sum := by decide
  have hdescent : baseEnd_3849223 < baseStart_3849223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849248 : List Nat := [2, 1, 1, 7, 2, 1, 2, 2, 1, 3]
def baseStart_3849248 : Nat := 118140960795 + 3849248 * 2 ^ 59
def prefixEnd_3849248 : Nat := 4983230072969 + 3 ^ 40 * 3849248 * 2
def baseEnd_3849248 : Nat := 1317676254905240688798425

theorem tailTrace_3849248 : CollatzResearch.WordTrace tailWord_3849248 prefixEnd_3849248 1317676254905240688798425 := by
  unfold tailWord_3849248
  simp only [CollatzResearch.WordTrace]
  refine ⟨70196804179419685032642199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93595738905892913376856265 70196804179419685032642199)
  ·
    refine ⟨105295206269129527548963299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70196804179419685032642199 105295206269129527548963299)
    ·
      refine ⟨157942809403694291323444949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105295206269129527548963299 157942809403694291323444949)
      ·
        refine ⟨3701784595399084952893241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 157942809403694291323444949 3701784595399084952893241)
        ·
          refine ⟨2776338446549313714669931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3701784595399084952893241 2776338446549313714669931)
          ·
            refine ⟨4164507669823970572004897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2776338446549313714669931 4164507669823970572004897)
            ·
              refine ⟨3123380752367977929003673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4164507669823970572004897 3123380752367977929003673)
              ·
                refine ⟨2342535564275983446752755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3123380752367977929003673 2342535564275983446752755)
                ·
                  refine ⟨3513803346413975170129133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2342535564275983446752755 3513803346413975170129133)
                  ·
                    refine ⟨1317676254905240688798425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3513803346413975170129133 1317676254905240688798425)
                    ·
                      rfl

theorem cell22_3849248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 2, 1, 3].length) (baseStart_3849248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849248 prefixEnd_3849248 := by exact prefixLift 3849248
  have htrace : WordTrace (prefixWord ++ tailWord_3849248) baseStart_3849248 baseEnd_3849248 := by
    simpa [prefixWord, tailWord_3849248, baseEnd_3849248] using wordTrace_append hprefix tailTrace_3849248
  have hstable : (prefixWord ++ tailWord_3849248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849248).length < 2 ^ (prefixWord ++ tailWord_3849248).sum := by decide
  have hdescent : baseEnd_3849248 < baseStart_3849248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849270 : List Nat := [5, 1, 2, 1, 1, 2, 1, 3, 1, 5]
def baseStart_3849270 : Nat := 118140960795 + 3849270 * 2 ^ 59
def prefixEnd_3849270 : Nat := 4983230072969 + 3 ^ 40 * 3849270 * 2
def baseEnd_3849270 : Nat := 1317683785954839964748357

theorem tailTrace_3849270 : CollatzResearch.WordTrace tailWord_3849270 prefixEnd_3849270 1317683785954839964748357 := by
  unfold tailWord_3849270
  simp only [CollatzResearch.WordTrace]
  refine ⟨8774650672797479238911579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93596273843173111881723509 8774650672797479238911579)
  ·
    refine ⟨13161976009196218858367369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8774650672797479238911579 13161976009196218858367369)
    ·
      refine ⟨9871482006897164143775527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13161976009196218858367369 9871482006897164143775527)
      ·
        refine ⟨14807223010345746215663291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9871482006897164143775527 14807223010345746215663291)
        ·
          refine ⟨22210834515518619323494937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14807223010345746215663291 22210834515518619323494937)
          ·
            refine ⟨16658125886638964492621203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22210834515518619323494937 16658125886638964492621203)
            ·
              refine ⟨24987188829958446738931805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16658125886638964492621203 24987188829958446738931805)
              ·
                refine ⟨9370195811234417527099427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24987188829958446738931805 9370195811234417527099427)
                ·
                  refine ⟨14055293716851626290649141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9370195811234417527099427 14055293716851626290649141)
                  ·
                    refine ⟨1317683785954839964748357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14055293716851626290649141 1317683785954839964748357)
                    ·
                      rfl

theorem cell22_3849270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_3849270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849270 prefixEnd_3849270 := by exact prefixLift 3849270
  have htrace : WordTrace (prefixWord ++ tailWord_3849270) baseStart_3849270 baseEnd_3849270 := by
    simpa [prefixWord, tailWord_3849270, baseEnd_3849270] using wordTrace_append hprefix tailTrace_3849270
  have hstable : (prefixWord ++ tailWord_3849270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849270).length < 2 ^ (prefixWord ++ tailWord_3849270).sum := by decide
  have hdescent : baseEnd_3849270 < baseStart_3849270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849283 : List Nat := [1, 1, 1, 3, 1, 2, 7, 6]
def baseStart_3849283 : Nat := 118140960795 + 3849283 * 2 ^ 59
def prefixEnd_3849283 : Nat := 4983230072969 + 3 ^ 40 * 3849283 * 2
def baseEnd_3849283 : Nat := 146409804013390251574813

theorem tailTrace_3849283 : CollatzResearch.WordTrace tailWord_3849283 prefixEnd_3849283 146409804013390251574813 := by
  unfold tailWord_3849283
  simp only [CollatzResearch.WordTrace]
  refine ⟨140394884913712571042808503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93596589942475047361872335 140394884913712571042808503)
  ·
    refine ⟨210592327370568856564212755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140394884913712571042808503 210592327370568856564212755)
    ·
      refine ⟨315888491055853284846319133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210592327370568856564212755 315888491055853284846319133)
      ·
        refine ⟨118458184145944981817369675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315888491055853284846319133 118458184145944981817369675)
        ·
          refine ⟨177687276218917472726054513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118458184145944981817369675 177687276218917472726054513)
          ·
            refine ⟨133265457164188104544540885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177687276218917472726054513 133265457164188104544540885)
            ·
              refine ⟨3123409152285658700262677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 133265457164188104544540885 3123409152285658700262677)
              ·
                refine ⟨146409804013390251574813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3123409152285658700262677 146409804013390251574813)
                ·
                  rfl

theorem cell22_3849283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 6].length) (baseStart_3849283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849283 prefixEnd_3849283 := by exact prefixLift 3849283
  have htrace : WordTrace (prefixWord ++ tailWord_3849283) baseStart_3849283 baseEnd_3849283 := by
    simpa [prefixWord, tailWord_3849283, baseEnd_3849283] using wordTrace_append hprefix tailTrace_3849283
  have hstable : (prefixWord ++ tailWord_3849283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849283).length < 2 ^ (prefixWord ++ tailWord_3849283).sum := by decide
  have hdescent : baseEnd_3849283 < baseStart_3849283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849405 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 6, 3]
def baseStart_3849405 : Nat := 118140960795 + 3849405 * 2 ^ 59
def prefixEnd_3849405 : Nat := 4983230072969 + 3 ^ 40 * 3849405 * 2
def baseEnd_3849405 : Nat := 1317729999213744612622943

theorem tailTrace_3849405 : CollatzResearch.WordTrace tailWord_3849405 prefixEnd_3849405 1317729999213744612622943 := by
  unfold tailWord_3849405
  simp only [CollatzResearch.WordTrace]
  refine ⟨140399334619270585878749669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93599556412847057252499779 140399334619270585878749669)
  ·
    refine ⟨26324875241113234852265563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140399334619270585878749669 26324875241113234852265563)
    ·
      refine ⟨39487312861669852278398345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26324875241113234852265563 39487312861669852278398345)
      ·
        refine ⟨29615484646252389208798759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39487312861669852278398345 29615484646252389208798759)
        ·
          refine ⟨44423226969378583813198139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29615484646252389208798759 44423226969378583813198139)
          ·
            refine ⟨66634840454067875719797209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44423226969378583813198139 66634840454067875719797209)
            ·
              refine ⟨49976130340550906789847907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66634840454067875719797209 49976130340550906789847907)
              ·
                refine ⟨74964195510826360184771861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49976130340550906789847907 74964195510826360184771861)
                ·
                  refine ⟨3513946664569985633661181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 74964195510826360184771861 3513946664569985633661181)
                  ·
                    refine ⟨1317729999213744612622943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3513946664569985633661181 1317729999213744612622943)
                    ·
                      rfl

theorem cell22_3849405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_3849405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849405 prefixEnd_3849405 := by exact prefixLift 3849405
  have htrace : WordTrace (prefixWord ++ tailWord_3849405) baseStart_3849405 baseEnd_3849405 := by
    simpa [prefixWord, tailWord_3849405, baseEnd_3849405] using wordTrace_append hprefix tailTrace_3849405
  have hstable : (prefixWord ++ tailWord_3849405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849405).length < 2 ^ (prefixWord ++ tailWord_3849405).sum := by decide
  have hdescent : baseEnd_3849405 < baseStart_3849405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849418 : List Nat := [3, 1, 2, 1, 3, 12]
def baseStart_3849418 : Nat := 118140960795 + 3849418 * 2 ^ 59
def prefixEnd_3849418 : Nat := 4983230072969 + 3 ^ 40 * 3849418 * 2
def baseEnd_3849418 : Nat := 16268326535548356938863

theorem tailTrace_3849418 : CollatzResearch.WordTrace tailWord_3849418 prefixEnd_3849418 16268326535548356938863 := by
  unfold tailWord_3849418
  simp only [CollatzResearch.WordTrace]
  refine ⟨35099952192055872274743227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93599872512148992732648605 35099952192055872274743227)
  ·
    refine ⟨52649928288083808412114841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35099952192055872274743227 52649928288083808412114841)
    ·
      refine ⟨39487446216062856309086131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52649928288083808412114841 39487446216062856309086131)
      ·
        refine ⟨59231169324094284463629197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39487446216062856309086131 59231169324094284463629197)
        ·
          refine ⟨22211688496535356673860949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59231169324094284463629197 22211688496535356673860949)
          ·
            refine ⟨16268326535548356938863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 22211688496535356673860949 16268326535548356938863)
            ·
              rfl

theorem cell22_3849418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 12].length) (baseStart_3849418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849418 prefixEnd_3849418 := by exact prefixLift 3849418
  have htrace : WordTrace (prefixWord ++ tailWord_3849418) baseStart_3849418 baseEnd_3849418 := by
    simpa [prefixWord, tailWord_3849418, baseEnd_3849418] using wordTrace_append hprefix tailTrace_3849418
  have hstable : (prefixWord ++ tailWord_3849418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849418).length < 2 ^ (prefixWord ++ tailWord_3849418).sum := by decide
  have hdescent : baseEnd_3849418 < baseStart_3849418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849433 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 2, 7]
def baseStart_3849433 : Nat := 118140960795 + 3849433 * 2 ^ 59
def prefixEnd_3849433 : Nat := 4983230072969 + 3 ^ 40 * 3849433 * 2
def baseEnd_3849433 : Nat := 1317739584185961872922857

theorem tailTrace_3849433 : CollatzResearch.WordTrace tailWord_3849433 prefixEnd_3849433 1317739584185961872922857 := by
  unfold tailWord_3849433
  simp only [CollatzResearch.WordTrace]
  refine ⟨140400355863169146660768953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93600237242112764440512635 140400355863169146660768953)
  ·
    refine ⟨105300266897376859995576715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140400355863169146660768953 105300266897376859995576715)
    ·
      refine ⟨157950400346065289993365073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105300266897376859995576715 157950400346065289993365073)
      ·
        refine ⟨118462800259548967495023805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157950400346065289993365073 118462800259548967495023805)
        ·
          refine ⟨44423550097330862810633927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118462800259548967495023805 44423550097330862810633927)
          ·
            refine ⟨66635325145996294215950891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44423550097330862810633927 66635325145996294215950891)
            ·
              refine ⟨99952987718994441323926337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66635325145996294215950891 99952987718994441323926337)
              ·
                refine ⟨74964740789245830992944753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99952987718994441323926337 74964740789245830992944753)
                ·
                  refine ⟨56223555591934373244708565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74964740789245830992944753 56223555591934373244708565)
                  ·
                    refine ⟨1317739584185961872922857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56223555591934373244708565 1317739584185961872922857)
                    ·
                      rfl

theorem cell22_3849433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 7].length) (baseStart_3849433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849433 prefixEnd_3849433 := by exact prefixLift 3849433
  have htrace : WordTrace (prefixWord ++ tailWord_3849433) baseStart_3849433 baseEnd_3849433 := by
    simpa [prefixWord, tailWord_3849433, baseEnd_3849433] using wordTrace_append hprefix tailTrace_3849433
  have hstable : (prefixWord ++ tailWord_3849433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849433).length < 2 ^ (prefixWord ++ tailWord_3849433).sum := by decide
  have hdescent : baseEnd_3849433 < baseStart_3849433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849460 : List Nat := [2, 6, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_3849460 : Nat := 118140960795 + 3849460 * 2 ^ 59
def prefixEnd_3849460 : Nat := 4983230072969 + 3 ^ 40 * 3849460 * 2
def baseEnd_3849460 : Nat := 1317748826837742802497775

theorem tailTrace_3849460 : CollatzResearch.WordTrace tailWord_3849460 prefixEnd_3849460 1317748826837742802497775 := by
  unfold tailWord_3849460
  simp only [CollatzResearch.WordTrace]
  refine ⟨70200670317035665136000917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93600893756047553514667889 70200670317035665136000917)
  ·
    refine ⟨3290656421111046803250043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70200670317035665136000917 3290656421111046803250043)
    ·
      refine ⟨4935984631666570204875065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3290656421111046803250043 4935984631666570204875065)
      ·
        refine ⟨3701988473749927653656299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4935984631666570204875065 3701988473749927653656299)
        ·
          refine ⟨5552982710624891480484449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3701988473749927653656299 5552982710624891480484449)
          ·
            refine ⟨4164737032968668610363337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5552982710624891480484449 4164737032968668610363337)
            ·
              refine ⟨3123552774726501457772503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4164737032968668610363337 3123552774726501457772503)
              ·
                refine ⟨4685329162089752186658755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3123552774726501457772503 4685329162089752186658755)
                ·
                  refine ⟨7027993743134628279988133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4685329162089752186658755 7027993743134628279988133)
                  ·
                    refine ⟨1317748826837742802497775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7027993743134628279988133 1317748826837742802497775)
                    ·
                      rfl

theorem cell22_3849460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_3849460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849460 prefixEnd_3849460 := by exact prefixLift 3849460
  have htrace : WordTrace (prefixWord ++ tailWord_3849460) baseStart_3849460 baseEnd_3849460 := by
    simpa [prefixWord, tailWord_3849460, baseEnd_3849460] using wordTrace_append hprefix tailTrace_3849460
  have hstable : (prefixWord ++ tailWord_3849460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849460).length < 2 ^ (prefixWord ++ tailWord_3849460).sum := by decide
  have hdescent : baseEnd_3849460 < baseStart_3849460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849463 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 9]
def baseStart_3849463 : Nat := 118140960795 + 3849463 * 2 ^ 59
def prefixEnd_3849463 : Nat := 4983230072969 + 3 ^ 40 * 3849463 * 2
def baseEnd_3849463 : Nat := 439249951266350598224255

theorem tailTrace_3849463 : CollatzResearch.WordTrace tailWord_3849463 prefixEnd_3849463 439249951266350598224255 := by
  unfold tailWord_3849463
  simp only [CollatzResearch.WordTrace]
  refine ⟨140401450053060461784361043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93600966702040307856240695 140401450053060461784361043)
  ·
    refine ⟨210602175079590692676541565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140401450053060461784361043 210602175079590692676541565)
    ·
      refine ⟨78975815654846509753703087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210602175079590692676541565 78975815654846509753703087)
      ·
        refine ⟨118463723482269764630554631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78975815654846509753703087 118463723482269764630554631)
        ·
          refine ⟨177695585223404646945831947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118463723482269764630554631 177695585223404646945831947)
          ·
            refine ⟨266543377835106970418747921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177695585223404646945831947 266543377835106970418747921)
            ·
              refine ⟨199907533376330227814060941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266543377835106970418747921 199907533376330227814060941)
              ·
                refine ⟨74965325016123835430272853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199907533376330227814060941 74965325016123835430272853)
                ·
                  refine ⟨439249951266350598224255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74965325016123835430272853 439249951266350598224255)
                  ·
                    rfl

theorem cell22_3849463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 9].length) (baseStart_3849463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849463 prefixEnd_3849463 := by exact prefixLift 3849463
  have htrace : WordTrace (prefixWord ++ tailWord_3849463) baseStart_3849463 baseEnd_3849463 := by
    simpa [prefixWord, tailWord_3849463, baseEnd_3849463] using wordTrace_append hprefix tailTrace_3849463
  have hstable : (prefixWord ++ tailWord_3849463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849463).length < 2 ^ (prefixWord ++ tailWord_3849463).sum := by decide
  have hdescent : baseEnd_3849463 < baseStart_3849463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849484 : List Nat := [2, 2, 1, 2, 2, 3, 2, 4, 1, 3]
def baseStart_3849484 : Nat := 118140960795 + 3849484 * 2 ^ 59
def prefixEnd_3849484 : Nat := 4983230072969 + 3 ^ 40 * 3849484 * 2
def baseEnd_3849484 : Nat := 1317757042528214739897701

theorem tailTrace_3849484 : CollatzResearch.WordTrace tailWord_3849484 prefixEnd_3849484 1317757042528214739897701 := by
  unfold tailWord_3849484
  simp only [CollatzResearch.WordTrace]
  refine ⟨70201107992992191185437753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93601477323989588247250337 70201107992992191185437753)
  ·
    refine ⟨52650830994744143389078315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70201107992992191185437753 52650830994744143389078315)
    ·
      refine ⟨78976246492116215083617473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52650830994744143389078315 78976246492116215083617473)
      ·
        refine ⟨59232184869087161312713105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78976246492116215083617473 59232184869087161312713105)
        ·
          refine ⟨44424138651815370984534829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59232184869087161312713105 44424138651815370984534829)
          ·
            refine ⟨16659051994430764119200561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44424138651815370984534829 16659051994430764119200561)
            ·
              refine ⟨12494288995823073089400421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16659051994430764119200561 12494288995823073089400421)
              ·
                refine ⟨2342679186716826204262579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12494288995823073089400421 2342679186716826204262579)
                ·
                  refine ⟨3514018780075239306393869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2342679186716826204262579 3514018780075239306393869)
                  ·
                    refine ⟨1317757042528214739897701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3514018780075239306393869 1317757042528214739897701)
                    ·
                      rfl

theorem cell22_3849484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 4, 1, 3].length) (baseStart_3849484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849484 prefixEnd_3849484 := by exact prefixLift 3849484
  have htrace : WordTrace (prefixWord ++ tailWord_3849484) baseStart_3849484 baseEnd_3849484 := by
    simpa [prefixWord, tailWord_3849484, baseEnd_3849484] using wordTrace_append hprefix tailTrace_3849484
  have hstable : (prefixWord ++ tailWord_3849484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849484).length < 2 ^ (prefixWord ++ tailWord_3849484).sum := by decide
  have hdescent : baseEnd_3849484 < baseStart_3849484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849495 : List Nat := [1, 1, 3, 4, 1, 1, 1, 3, 2, 5]
def baseStart_3849495 : Nat := 118140960795 + 3849495 * 2 ^ 59
def prefixEnd_3849495 : Nat := 4983230072969 + 3 ^ 40 * 3849495 * 2
def baseEnd_3849495 : Nat := 1317760808053014377872667

theorem tailTrace_3849495 : CollatzResearch.WordTrace tailWord_3849495 prefixEnd_3849495 1317760808053014377872667 := by
  unfold tailWord_3849495
  simp only [CollatzResearch.WordTrace]
  refine ⟨140402617188944531249525939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93601744792629687499683959 140402617188944531249525939)
  ·
    refine ⟨210603925783416796874288909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140402617188944531249525939 210603925783416796874288909)
    ·
      refine ⟨78976472168781298827858341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210603925783416796874288909 78976472168781298827858341)
      ·
        refine ⟨14808088531646493530223439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78976472168781298827858341 14808088531646493530223439)
        ·
          refine ⟨22212132797469740295335159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14808088531646493530223439 22212132797469740295335159)
          ·
            refine ⟨33318199196204610443002739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22212132797469740295335159 33318199196204610443002739)
            ·
              refine ⟨49977298794306915664504109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33318199196204610443002739 49977298794306915664504109)
              ·
                refine ⟨18741487047865093374189041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49977298794306915664504109 18741487047865093374189041)
                ·
                  refine ⟨14056115285898820030641781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18741487047865093374189041 14056115285898820030641781)
                  ·
                    refine ⟨1317760808053014377872667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14056115285898820030641781 1317760808053014377872667)
                    ·
                      rfl

theorem cell22_3849495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_3849495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849495 prefixEnd_3849495 := by exact prefixLift 3849495
  have htrace : WordTrace (prefixWord ++ tailWord_3849495) baseStart_3849495 baseEnd_3849495 := by
    simpa [prefixWord, tailWord_3849495, baseEnd_3849495] using wordTrace_append hprefix tailTrace_3849495
  have hstable : (prefixWord ++ tailWord_3849495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849495).length < 2 ^ (prefixWord ++ tailWord_3849495).sum := by decide
  have hdescent : baseEnd_3849495 < baseStart_3849495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849555 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 4, 4]
def baseStart_3849555 : Nat := 118140960795 + 3849555 * 2 ^ 59
def prefixEnd_3849555 : Nat := 4983230072969 + 3 ^ 40 * 3849555 * 2
def baseEnd_3849555 : Nat := 1317781347279194221372483

theorem tailTrace_3849555 : CollatzResearch.WordTrace tailWord_3849555 prefixEnd_3849555 1317781347279194221372483 := by
  unfold tailWord_3849555
  simp only [CollatzResearch.WordTrace]
  refine ⟨140404805568727161496710119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93603203712484774331140079 140404805568727161496710119)
  ·
    refine ⟨210607208353090742245065179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140404805568727161496710119 210607208353090742245065179)
    ·
      refine ⟨315910812529636113367597769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210607208353090742245065179 315910812529636113367597769)
      ·
        refine ⟨236933109397227085025698327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315910812529636113367597769 236933109397227085025698327)
        ·
          refine ⟨355399664095840627538547491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236933109397227085025698327 355399664095840627538547491)
          ·
            refine ⟨533099496143760941307821237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355399664095840627538547491 533099496143760941307821237)
            ·
              refine ⟨49978077763477588247608241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 533099496143760941307821237 49978077763477588247608241)
              ·
                refine ⟨37483558322608191185706181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49978077763477588247608241 37483558322608191185706181)
                ·
                  refine ⟨7028167185489035847319909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37483558322608191185706181 7028167185489035847319909)
                  ·
                    refine ⟨1317781347279194221372483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7028167185489035847319909 1317781347279194221372483)
                    ·
                      rfl

theorem cell22_3849555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 4].length) (baseStart_3849555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849555 prefixEnd_3849555 := by exact prefixLift 3849555
  have htrace : WordTrace (prefixWord ++ tailWord_3849555) baseStart_3849555 baseEnd_3849555 := by
    simpa [prefixWord, tailWord_3849555, baseEnd_3849555] using wordTrace_append hprefix tailTrace_3849555
  have hstable : (prefixWord ++ tailWord_3849555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849555).length < 2 ^ (prefixWord ++ tailWord_3849555).sum := by decide
  have hdescent : baseEnd_3849555 < baseStart_3849555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849572 : List Nat := [2, 3, 1, 1, 3, 2, 1, 3, 2, 4]
def baseStart_3849572 : Nat := 118140960795 + 3849572 * 2 ^ 59
def prefixEnd_3849572 : Nat := 4983230072969 + 3 ^ 40 * 3849572 * 2
def baseEnd_3849572 : Nat := 1317787166726611843697431

theorem tailTrace_3849572 : CollatzResearch.WordTrace tailWord_3849572 prefixEnd_3849572 1317787166726611843697431 := by
  unfold tailWord_3849572
  simp only [CollatzResearch.WordTrace]
  refine ⟨70202712804832786700039485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93603617073110382266719313 70202712804832786700039485)
  ·
    refine ⟨26326017301812295012514807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70202712804832786700039485 26326017301812295012514807)
    ·
      refine ⟨39489025952718442518772211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26326017301812295012514807 39489025952718442518772211)
      ·
        refine ⟨59233538929077663778158317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39489025952718442518772211 59233538929077663778158317)
        ·
          refine ⟨22212577098404123916809369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59233538929077663778158317 22212577098404123916809369)
          ·
            refine ⟨16659432823803092937607027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22212577098404123916809369 16659432823803092937607027)
            ·
              refine ⟨24989149235704639406410541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16659432823803092937607027 24989149235704639406410541)
              ·
                refine ⟨9370930963389239777403953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24989149235704639406410541 9370930963389239777403953)
                ·
                  refine ⟨7028198222541929833052965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9370930963389239777403953 7028198222541929833052965)
                  ·
                    refine ⟨1317787166726611843697431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7028198222541929833052965 1317787166726611843697431)
                    ·
                      rfl

theorem cell22_3849572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_3849572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849572 prefixEnd_3849572 := by exact prefixLift 3849572
  have htrace : WordTrace (prefixWord ++ tailWord_3849572) baseStart_3849572 baseEnd_3849572 := by
    simpa [prefixWord, tailWord_3849572, baseEnd_3849572] using wordTrace_append hprefix tailTrace_3849572
  have hstable : (prefixWord ++ tailWord_3849572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849572).length < 2 ^ (prefixWord ++ tailWord_3849572).sum := by decide
  have hdescent : baseEnd_3849572 < baseStart_3849572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849722 : List Nat := [3, 1, 1, 1, 1, 2, 6, 7]
def baseStart_3849722 : Nat := 118140960795 + 3849722 * 2 ^ 59
def prefixEnd_3849722 : Nat := 4983230072969 + 3 ^ 40 * 3849722 * 2
def baseEnd_3849722 : Nat := 146426501643562383605219

theorem tailTrace_3849722 : CollatzResearch.WordTrace tailWord_3849722 prefixEnd_3849722 146426501643562383605219 := by
  unfold tailWord_3849722
  simp only [CollatzResearch.WordTrace]
  refine ⟨35102724139780537254509855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93607264372748099345359613 35102724139780537254509855)
  ·
    refine ⟨52654086209670805881764783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35102724139780537254509855 52654086209670805881764783)
    ·
      refine ⟨78981129314506208822647175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52654086209670805881764783 78981129314506208822647175)
      ·
        refine ⟨118471693971759313233970763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78981129314506208822647175 118471693971759313233970763)
        ·
          refine ⟨177707540957638969850956145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118471693971759313233970763 177707540957638969850956145)
          ·
            refine ⟨133280655718229227388217109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177707540957638969850956145 133280655718229227388217109)
            ·
              refine ⟨6247530736791995033822677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 133280655718229227388217109 6247530736791995033822677)
              ·
                refine ⟨146426501643562383605219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6247530736791995033822677 146426501643562383605219)
                ·
                  rfl

theorem cell22_3849722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 7].length) (baseStart_3849722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849722 prefixEnd_3849722 := by exact prefixLift 3849722
  have htrace : WordTrace (prefixWord ++ tailWord_3849722) baseStart_3849722 baseEnd_3849722 := by
    simpa [prefixWord, tailWord_3849722, baseEnd_3849722] using wordTrace_append hprefix tailTrace_3849722
  have hstable : (prefixWord ++ tailWord_3849722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849722).length < 2 ^ (prefixWord ++ tailWord_3849722).sum := by decide
  have hdescent : baseEnd_3849722 < baseStart_3849722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849784 : List Nat := [2, 1, 2, 1, 4, 2, 2, 3, 5]
def baseStart_3849784 : Nat := 118140960795 + 3849784 * 2 ^ 59
def prefixEnd_3849784 : Nat := 4983230072969 + 3 ^ 40 * 3849784 * 2
def baseEnd_3849784 : Nat := 439286579553037985798927

theorem tailTrace_3849784 : CollatzResearch.WordTrace tailWord_3849784 prefixEnd_3849784 439286579553037985798927 := by
  unfold tailWord_3849784
  simp only [CollatzResearch.WordTrace]
  refine ⟨70206578942448766803398203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93608771923265022404530937 70206578942448766803398203)
  ·
    refine ⟨105309868413673150205097305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70206578942448766803398203 105309868413673150205097305)
    ·
      refine ⟨78982401310254862653822979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105309868413673150205097305 78982401310254862653822979)
      ·
        refine ⟨118473601965382293980734469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78982401310254862653822979 118473601965382293980734469)
        ·
          refine ⟨22213800368509180121387713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118473601965382293980734469 22213800368509180121387713)
          ·
            refine ⟨16660350276381885091040785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22213800368509180121387713 16660350276381885091040785)
            ·
              refine ⟨12495262707286413818280589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16660350276381885091040785 12495262707286413818280589)
              ·
                refine ⟨4685723515232405181855221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12495262707286413818280589 4685723515232405181855221)
                ·
                  refine ⟨439286579553037985798927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4685723515232405181855221 439286579553037985798927)
                  ·
                    rfl

theorem cell22_3849784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 5].length) (baseStart_3849784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849784 prefixEnd_3849784 := by exact prefixLift 3849784
  have htrace : WordTrace (prefixWord ++ tailWord_3849784) baseStart_3849784 baseEnd_3849784 := by
    simpa [prefixWord, tailWord_3849784, baseEnd_3849784] using wordTrace_append hprefix tailTrace_3849784
  have hstable : (prefixWord ++ tailWord_3849784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849784).length < 2 ^ (prefixWord ++ tailWord_3849784).sum := by decide
  have hdescent : baseEnd_3849784 < baseStart_3849784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849829 : List Nat := [1, 3, 1, 3, 3, 1, 1, 3, 6]
def baseStart_3849829 : Nat := 118140960795 + 3849829 * 2 ^ 59
def prefixEnd_3849829 : Nat := 4983230072969 + 3 ^ 40 * 3849829 * 2
def baseEnd_3849829 : Nat := 439291714359582946673881

theorem tailTrace_3849829 : CollatzResearch.WordTrace tailWord_3849829 prefixEnd_3849829 439291714359582946673881 := by
  unfold tailWord_3849829
  simp only [CollatzResearch.WordTrace]
  refine ⟨140414799169734506292184541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93609866113156337528123027 140414799169734506292184541)
  ·
    refine ⟨52655549688650439859569203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140414799169734506292184541 52655549688650439859569203)
    ·
      refine ⟨78983324532975659789353805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52655549688650439859569203 78983324532975659789353805)
      ·
        refine ⟨29618746699865872421007677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78983324532975659789353805 29618746699865872421007677)
        ·
          refine ⟨11107030012449702157877879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29618746699865872421007677 11107030012449702157877879)
          ·
            refine ⟨16660545018674553236816819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11107030012449702157877879 16660545018674553236816819)
            ·
              refine ⟨24990817528011829855225229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16660545018674553236816819 24990817528011829855225229)
              ·
                refine ⟨9371556573004436195709461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24990817528011829855225229 9371556573004436195709461)
                ·
                  refine ⟨439291714359582946673881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9371556573004436195709461 439291714359582946673881)
                  ·
                    rfl

theorem cell22_3849829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 6].length) (baseStart_3849829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849829 prefixEnd_3849829 := by exact prefixLift 3849829
  have htrace : WordTrace (prefixWord ++ tailWord_3849829) baseStart_3849829 baseEnd_3849829 := by
    simpa [prefixWord, tailWord_3849829, baseEnd_3849829] using wordTrace_append hprefix tailTrace_3849829
  have hstable : (prefixWord ++ tailWord_3849829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849829).length < 2 ^ (prefixWord ++ tailWord_3849829).sum := by decide
  have hdescent : baseEnd_3849829 < baseStart_3849829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849846 : List Nat := [5, 1, 1, 2, 2, 1, 2, 2, 6]
def baseStart_3849846 : Nat := 118140960795 + 3849846 * 2 ^ 59
def prefixEnd_3849846 : Nat := 4983230072969 + 3 ^ 40 * 3849846 * 2
def baseEnd_3849846 : Nat := 439293654175388820782197

theorem tailTrace_3849846 : CollatzResearch.WordTrace tailWord_3849846 prefixEnd_3849846 439293654175388820782197 := by
  unfold tailWord_3849846
  simp only [CollatzResearch.WordTrace]
  refine ⟨8775963700667057387222087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93610279473781945463702261 8775963700667057387222087)
  ·
    refine ⟨13163945551000586080833131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8775963700667057387222087 13163945551000586080833131)
    ·
      refine ⟨19745918326500879121249697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13163945551000586080833131 19745918326500879121249697)
      ·
        refine ⟨14809438744875659340937273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19745918326500879121249697 14809438744875659340937273)
        ·
          refine ⟨11107079058656744505702955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14809438744875659340937273 11107079058656744505702955)
          ·
            refine ⟨16660618587985116758554433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11107079058656744505702955 16660618587985116758554433)
            ·
              refine ⟨12495463940988837568915825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16660618587985116758554433 12495463940988837568915825)
              ·
                refine ⟨9371597955741628176686869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12495463940988837568915825 9371597955741628176686869)
                ·
                  refine ⟨439293654175388820782197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9371597955741628176686869 439293654175388820782197)
                  ·
                    rfl

theorem cell22_3849846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_3849846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849846 prefixEnd_3849846 := by exact prefixLift 3849846
  have htrace : WordTrace (prefixWord ++ tailWord_3849846) baseStart_3849846 baseEnd_3849846 := by
    simpa [prefixWord, tailWord_3849846, baseEnd_3849846] using wordTrace_append hprefix tailTrace_3849846
  have hstable : (prefixWord ++ tailWord_3849846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849846).length < 2 ^ (prefixWord ++ tailWord_3849846).sum := by decide
  have hdescent : baseEnd_3849846 < baseStart_3849846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849859 : List Nat := [1, 1, 1, 3, 3, 1, 1, 5, 2, 4]
def baseStart_3849859 : Nat := 118140960795 + 3849859 * 2 ^ 59
def prefixEnd_3849859 : Nat := 4983230072969 + 3 ^ 40 * 3849859 * 2
def baseEnd_3849859 : Nat := 1317885412691838761771551

theorem tailTrace_3849859 : CollatzResearch.WordTrace tailWord_3849859 prefixEnd_3849859 1317885412691838761771551 := by
  unfold tailWord_3849859
  simp only [CollatzResearch.WordTrace]
  refine ⟨140415893359625821415776631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93610595573083880943851087 140415893359625821415776631)
  ·
    refine ⟨210623840039438732123664947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140415893359625821415776631 210623840039438732123664947)
    ·
      refine ⟨315935760059158098185497421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210623840039438732123664947 315935760059158098185497421)
      ·
        refine ⟨118475910022184286819561533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315935760059158098185497421 118475910022184286819561533)
        ·
          refine ⟨44428466258319107557335575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118475910022184286819561533 44428466258319107557335575)
          ·
            refine ⟨66642699387478661336003363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44428466258319107557335575 66642699387478661336003363)
            ·
              refine ⟨99964049081217992004005045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66642699387478661336003363 99964049081217992004005045)
              ·
                refine ⟨9371629601364186750375473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99964049081217992004005045 9371629601364186750375473)
                ·
                  refine ⟨7028722201023140062781605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9371629601364186750375473 7028722201023140062781605)
                  ·
                    refine ⟨1317885412691838761771551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7028722201023140062781605 1317885412691838761771551)
                    ·
                      rfl

theorem cell22_3849859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 4].length) (baseStart_3849859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849859 prefixEnd_3849859 := by exact prefixLift 3849859
  have htrace : WordTrace (prefixWord ++ tailWord_3849859) baseStart_3849859 baseEnd_3849859 := by
    simpa [prefixWord, tailWord_3849859, baseEnd_3849859] using wordTrace_append hprefix tailTrace_3849859
  have hstable : (prefixWord ++ tailWord_3849859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849859).length < 2 ^ (prefixWord ++ tailWord_3849859).sum := by decide
  have hdescent : baseEnd_3849859 < baseStart_3849859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849863 : List Nat := [1, 1, 4, 2, 1, 5, 1, 3, 4]
def baseStart_3849863 : Nat := 118140960795 + 3849863 * 2 ^ 59
def prefixEnd_3849863 : Nat := 4983230072969 + 3 ^ 40 * 3849863 * 2
def baseEnd_3849863 : Nat := 439295593991194694890513

theorem tailTrace_3849863 : CollatzResearch.WordTrace tailWord_3849863 prefixEnd_3849863 439295593991194694890513 := by
  unfold tailWord_3849863
  simp only [CollatzResearch.WordTrace]
  refine ⟨140416039251611330098922243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93610692834407553399281495 140416039251611330098922243)
  ·
    refine ⟨210624058877416995148383365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140416039251611330098922243 210624058877416995148383365)
    ·
      refine ⟨39492011039515686590321881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210624058877416995148383365 39492011039515686590321881)
      ·
        refine ⟨29619008279636764942741411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39492011039515686590321881 29619008279636764942741411)
        ·
          refine ⟨44428512419455147414112117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29619008279636764942741411 44428512419455147414112117)
          ·
            refine ⟨4165173039323920070073011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44428512419455147414112117 4165173039323920070073011)
            ·
              refine ⟨6247759558985880105109517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4165173039323920070073011 6247759558985880105109517)
              ·
                refine ⟨2342909834619705039416069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6247759558985880105109517 2342909834619705039416069)
                ·
                  refine ⟨439295593991194694890513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2342909834619705039416069 439295593991194694890513)
                  ·
                    rfl

theorem cell22_3849863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 3, 4].length) (baseStart_3849863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849863 prefixEnd_3849863 := by exact prefixLift 3849863
  have htrace : WordTrace (prefixWord ++ tailWord_3849863) baseStart_3849863 baseEnd_3849863 := by
    simpa [prefixWord, tailWord_3849863, baseEnd_3849863] using wordTrace_append hprefix tailTrace_3849863
  have hstable : (prefixWord ++ tailWord_3849863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849863).length < 2 ^ (prefixWord ++ tailWord_3849863).sum := by decide
  have hdescent : baseEnd_3849863 < baseStart_3849863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849906 : List Nat := [3, 2, 1, 1, 1, 2, 2, 4, 3, 3]
def baseStart_3849906 : Nat := 118140960795 + 3849906 * 2 ^ 59
def prefixEnd_3849906 : Nat := 4983230072969 + 3 ^ 40 * 3849906 * 2
def baseEnd_3849906 : Nat := 1317901501752346305846407

theorem tailTrace_3849906 : CollatzResearch.WordTrace tailWord_3849906 prefixEnd_3849906 1317901501752346305846407 := by
  unfold tailWord_3849906
  simp only [CollatzResearch.WordTrace]
  refine ⟨35104401897613887110684393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93611738393637032295158381 35104401897613887110684393)
  ·
    refine ⟨26328301423210415333013295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35104401897613887110684393 26328301423210415333013295)
    ·
      refine ⟨39492452134815622999519943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26328301423210415333013295 39492452134815622999519943)
      ·
        refine ⟨59238678202223434499279915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39492452134815622999519943 59238678202223434499279915)
        ·
          refine ⟨88858017303335151748919873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59238678202223434499279915 88858017303335151748919873)
          ·
            refine ⟨66643512977501363811689905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88858017303335151748919873 66643512977501363811689905)
            ·
              refine ⟨49982634733126022858767429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66643512977501363811689905 49982634733126022858767429)
              ·
                refine ⟨9371744012461129286018893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49982634733126022858767429 9371744012461129286018893)
                ·
                  refine ⟨3514404004672923482257085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9371744012461129286018893 3514404004672923482257085)
                  ·
                    refine ⟨1317901501752346305846407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3514404004672923482257085 1317901501752346305846407)
                    ·
                      rfl

theorem cell22_3849906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_3849906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849906 prefixEnd_3849906 := by exact prefixLift 3849906
  have htrace : WordTrace (prefixWord ++ tailWord_3849906) baseStart_3849906 baseEnd_3849906 := by
    simpa [prefixWord, tailWord_3849906, baseEnd_3849906] using wordTrace_append hprefix tailTrace_3849906
  have hstable : (prefixWord ++ tailWord_3849906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849906).length < 2 ^ (prefixWord ++ tailWord_3849906).sum := by decide
  have hdescent : baseEnd_3849906 < baseStart_3849906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849910 : List Nat := [5, 1, 3, 1, 1, 2, 2, 1, 2, 4]
def baseStart_3849910 : Nat := 118140960795 + 3849910 * 2 ^ 59
def prefixEnd_3849910 : Nat := 4983230072969 + 3 ^ 40 * 3849910 * 2
def baseEnd_3849910 : Nat := 1317902871034091628746395

theorem tailTrace_3849910 : CollatzResearch.WordTrace tailWord_3849910 prefixEnd_3849910 1317902871034091628746395 := by
  unfold tailWord_3849910
  simp only [CollatzResearch.WordTrace]
  refine ⟨8776109592652566070367699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93611835654960704750588789 8776109592652566070367699)
  ·
    refine ⟨13164164388978849105551549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8776109592652566070367699 13164164388978849105551549)
    ·
      refine ⟨4936561645867068414581831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13164164388978849105551549 4936561645867068414581831)
      ·
        refine ⟨7404842468800602621872747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4936561645867068414581831 7404842468800602621872747)
        ·
          refine ⟨11107263703200903932809121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7404842468800602621872747 11107263703200903932809121)
          ·
            refine ⟨8330447777400677949606841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11107263703200903932809121 8330447777400677949606841)
            ·
              refine ⟨6247835833050508462205131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8330447777400677949606841 6247835833050508462205131)
              ·
                refine ⟨9371753749575762693307697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6247835833050508462205131 9371753749575762693307697)
                ·
                  refine ⟨7028815312181822019980773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9371753749575762693307697 7028815312181822019980773)
                  ·
                    refine ⟨1317902871034091628746395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7028815312181822019980773 1317902871034091628746395)
                    ·
                      rfl

theorem cell22_3849910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_3849910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849910 prefixEnd_3849910 := by exact prefixLift 3849910
  have htrace : WordTrace (prefixWord ++ tailWord_3849910) baseStart_3849910 baseEnd_3849910 := by
    simpa [prefixWord, tailWord_3849910, baseEnd_3849910] using wordTrace_append hprefix tailTrace_3849910
  have hstable : (prefixWord ++ tailWord_3849910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849910).length < 2 ^ (prefixWord ++ tailWord_3849910).sum := by decide
  have hdescent : baseEnd_3849910 < baseStart_3849910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849942 : List Nat := [5, 2, 1, 3, 2, 1, 1, 7]
def baseStart_3849942 : Nat := 118140960795 + 3849942 * 2 ^ 59
def prefixEnd_3849942 : Nat := 4983230072969 + 3 ^ 40 * 3849942 * 2
def baseEnd_3849942 : Nat := 146434869476450467994033

theorem tailTrace_3849942 : CollatzResearch.WordTrace tailWord_3849942 prefixEnd_3849942 146434869476450467994033 := by
  unfold tailWord_3849942
  simp only [CollatzResearch.WordTrace]
  refine ⟨8776182538645320411940505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93612613745550084394032053 8776182538645320411940505)
  ·
    refine ⟨6582136903983990308955379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8776182538645320411940505 6582136903983990308955379)
    ·
      refine ⟨9873205355975985463433069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6582136903983990308955379 9873205355975985463433069)
      ·
        refine ⟨3702452008490994548787401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9873205355975985463433069 3702452008490994548787401)
        ·
          refine ⟨2776839006368245911590551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3702452008490994548787401 2776839006368245911590551)
          ·
            refine ⟨4165258509552368867385827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2776839006368245911590551 4165258509552368867385827)
            ·
              refine ⟨6247887764328553301078741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4165258509552368867385827 6247887764328553301078741)
              ·
                refine ⟨146434869476450467994033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6247887764328553301078741 146434869476450467994033)
                ·
                  rfl

theorem cell22_3849942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_3849942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849942 prefixEnd_3849942 := by exact prefixLift 3849942
  have htrace : WordTrace (prefixWord ++ tailWord_3849942) baseStart_3849942 baseEnd_3849942 := by
    simpa [prefixWord, tailWord_3849942, baseEnd_3849942] using wordTrace_append hprefix tailTrace_3849942
  have hstable : (prefixWord ++ tailWord_3849942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849942).length < 2 ^ (prefixWord ++ tailWord_3849942).sum := by decide
  have hdescent : baseEnd_3849942 < baseStart_3849942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849964 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 8]
def baseStart_3849964 : Nat := 118140960795 + 3849964 * 2 ^ 59
def prefixEnd_3849964 : Nat := 4983230072969 + 3 ^ 40 * 3849964 * 2
def baseEnd_3849964 : Nat := 439307118779217829298743

theorem tailTrace_3849964 : CollatzResearch.WordTrace tailWord_3849964 prefixEnd_3849964 439307118779217829298743 := by
  unfold tailWord_3849964
  simp only [CollatzResearch.WordTrace]
  refine ⟨70209861512122712174174473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93613148682830282898899297 70209861512122712174174473)
  ·
    refine ⟨52657396134092034130630855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70209861512122712174174473 52657396134092034130630855)
    ·
      refine ⟨78986094201138051195946283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52657396134092034130630855 78986094201138051195946283)
      ·
        refine ⟨118479141301707076793919425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78986094201138051195946283 118479141301707076793919425)
        ·
          refine ⟨88859355976280307595439569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118479141301707076793919425 88859355976280307595439569)
          ·
            refine ⟨66644516982210230696579677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88859355976280307595439569 66644516982210230696579677)
            ·
              refine ⟨24991693868328836511217379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66644516982210230696579677 24991693868328836511217379)
              ·
                refine ⟨37487540802493254766826069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24991693868328836511217379 37487540802493254766826069)
                ·
                  refine ⟨439307118779217829298743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37487540802493254766826069 439307118779217829298743)
                  ·
                    rfl

theorem cell22_3849964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 8].length) (baseStart_3849964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849964 prefixEnd_3849964 := by exact prefixLift 3849964
  have htrace : WordTrace (prefixWord ++ tailWord_3849964) baseStart_3849964 baseEnd_3849964 := by
    simpa [prefixWord, tailWord_3849964, baseEnd_3849964] using wordTrace_append hprefix tailTrace_3849964
  have hstable : (prefixWord ++ tailWord_3849964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849964).length < 2 ^ (prefixWord ++ tailWord_3849964).sum := by decide
  have hdescent : baseEnd_3849964 < baseStart_3849964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849966 : List Nat := [4, 1, 2, 1, 1, 2, 1, 3, 3, 4]
def baseStart_3849966 : Nat := 118140960795 + 3849966 * 2 ^ 59
def prefixEnd_3849966 : Nat := 4983230072969 + 3 ^ 40 * 3849966 * 2
def baseEnd_3849966 : Nat := 1317922040978526149346223

theorem tailTrace_3849966 : CollatzResearch.WordTrace tailWord_3849966 prefixEnd_3849966 1317922040978526149346223 := by
  unfold tailWord_3849966
  simp only [CollatzResearch.WordTrace]
  refine ⟨17552474496279772336240219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93613197313492119126614501 17552474496279772336240219)
  ·
    refine ⟨26328711744419658504360329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17552474496279772336240219 26328711744419658504360329)
    ·
      refine ⟨19746533808314743878270247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26328711744419658504360329 19746533808314743878270247)
      ·
        refine ⟨29619800712472115817405371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19746533808314743878270247 29619800712472115817405371)
        ·
          refine ⟨44429701068708173726108057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29619800712472115817405371 44429701068708173726108057)
          ·
            refine ⟨33322275801531130294581043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44429701068708173726108057 33322275801531130294581043)
            ·
              refine ⟨49983413702296695441871565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33322275801531130294581043 49983413702296695441871565)
              ·
                refine ⟨18743780138361260790701837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49983413702296695441871565 18743780138361260790701837)
                ·
                  refine ⟨7028917551885472796513189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18743780138361260790701837 7028917551885472796513189)
                  ·
                    refine ⟨1317922040978526149346223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7028917551885472796513189 1317922040978526149346223)
                    ·
                      rfl

theorem cell22_3849966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_3849966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849966 prefixEnd_3849966 := by exact prefixLift 3849966
  have htrace : WordTrace (prefixWord ++ tailWord_3849966) baseStart_3849966 baseEnd_3849966 := by
    simpa [prefixWord, tailWord_3849966, baseEnd_3849966] using wordTrace_append hprefix tailTrace_3849966
  have hstable : (prefixWord ++ tailWord_3849966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849966).length < 2 ^ (prefixWord ++ tailWord_3849966).sum := by decide
  have hdescent : baseEnd_3849966 < baseStart_3849966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849979 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 3, 5]
def baseStart_3849979 : Nat := 118140960795 + 3849979 * 2 ^ 59
def prefixEnd_3849979 : Nat := 4983230072969 + 3 ^ 40 * 3849979 * 2
def baseEnd_3849979 : Nat := 1317926491144198448771183

theorem tailTrace_3849979 : CollatzResearch.WordTrace tailWord_3849979 prefixEnd_3849979 1317926491144198448771183 := by
  unfold tailWord_3849979
  simp only [CollatzResearch.WordTrace]
  refine ⟨140420270119191081910144991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93613513412794054606763327 140420270119191081910144991)
  ·
    refine ⟨210630405178786622865217487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140420270119191081910144991 210630405178786622865217487)
    ·
      refine ⟨315945607768179934297826231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210630405178786622865217487 315945607768179934297826231)
      ·
        refine ⟨473918411652269901446739347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315945607768179934297826231 473918411652269901446739347)
        ·
          refine ⟨710877617478404852170109021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473918411652269901446739347 710877617478404852170109021)
          ·
            refine ⟨266579106554401819563790883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 710877617478404852170109021 266579106554401819563790883)
            ·
              refine ⟨399868659831602729345686325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266579106554401819563790883 399868659831602729345686325)
              ·
                refine ⟨37487686859212755876158093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 399868659831602729345686325 37487686859212755876158093)
                ·
                  refine ⟨14057882572204783453559285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37487686859212755876158093 14057882572204783453559285)
                  ·
                    refine ⟨1317926491144198448771183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14057882572204783453559285 1317926491144198448771183)
                    ·
                      rfl

theorem cell22_3849979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 5].length) (baseStart_3849979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849979 prefixEnd_3849979 := by exact prefixLift 3849979
  have htrace : WordTrace (prefixWord ++ tailWord_3849979) baseStart_3849979 baseEnd_3849979 := by
    simpa [prefixWord, tailWord_3849979, baseEnd_3849979] using wordTrace_append hprefix tailTrace_3849979
  have hstable : (prefixWord ++ tailWord_3849979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849979).length < 2 ^ (prefixWord ++ tailWord_3849979).sum := by decide
  have hdescent : baseEnd_3849979 < baseStart_3849979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849983 : List Nat := [1, 1, 2, 2, 1, 3, 6, 1, 1, 4]
def baseStart_3849983 : Nat := 118140960795 + 3849983 * 2 ^ 59
def prefixEnd_3849983 : Nat := 4983230072969 + 3 ^ 40 * 3849983 * 2
def baseEnd_3849983 : Nat := 1317927860425943771671171

theorem tailTrace_3849983 : CollatzResearch.WordTrace tailWord_3849983 prefixEnd_3849983 1317927860425943771671171 := by
  unfold tailWord_3849983
  simp only [CollatzResearch.WordTrace]
  refine ⟨140420416011176590593290603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93613610674117727062193735 140420416011176590593290603)
  ·
    refine ⟨210630624016764885889935905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140420416011176590593290603 210630624016764885889935905)
    ·
      refine ⟨157972968012573664417451929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210630624016764885889935905 157972968012573664417451929)
      ·
        refine ⟨118479726009430248313088947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157972968012573664417451929 118479726009430248313088947)
        ·
          refine ⟨177719589014145372469633421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118479726009430248313088947 177719589014145372469633421)
          ·
            refine ⟨66644845880304514676112533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177719589014145372469633421 66644845880304514676112533)
            ·
              refine ⟨3123977150639274125442775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66644845880304514676112533 3123977150639274125442775)
              ·
                refine ⟨4685965725958911188164163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3123977150639274125442775 4685965725958911188164163)
                ·
                  refine ⟨7028948588938366782246245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4685965725958911188164163 7028948588938366782246245)
                  ·
                    refine ⟨1317927860425943771671171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7028948588938366782246245 1317927860425943771671171)
                    ·
                      rfl

theorem cell22_3849983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 1, 4].length) (baseStart_3849983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849983 prefixEnd_3849983 := by exact prefixLift 3849983
  have htrace : WordTrace (prefixWord ++ tailWord_3849983) baseStart_3849983 baseEnd_3849983 := by
    simpa [prefixWord, tailWord_3849983, baseEnd_3849983] using wordTrace_append hprefix tailTrace_3849983
  have hstable : (prefixWord ++ tailWord_3849983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849983).length < 2 ^ (prefixWord ++ tailWord_3849983).sum := by decide
  have hdescent : baseEnd_3849983 < baseStart_3849983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849998 : List Nat := [4, 1, 1, 2, 1, 1, 4, 4, 4]
def baseStart_3849998 : Nat := 118140960795 + 3849998 * 2 ^ 59
def prefixEnd_3849998 : Nat := 4983230072969 + 3 ^ 40 * 3849998 * 2
def baseEnd_3849998 : Nat := 439310998410829577515375

theorem tailTrace_3849998 : CollatzResearch.WordTrace tailWord_3849998 prefixEnd_3849998 439310998410829577515375 := by
  unfold tailWord_3849998
  simp only [CollatzResearch.WordTrace]
  refine ⟨17552620388265281019385831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93613975404081498770057765 17552620388265281019385831)
  ·
    refine ⟨26328930582397921529078747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17552620388265281019385831 26328930582397921529078747)
    ·
      refine ⟨39493395873596882293618121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26328930582397921529078747 39493395873596882293618121)
      ·
        refine ⟨29620046905197661720213591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39493395873596882293618121 29620046905197661720213591)
        ·
          refine ⟨44430070357796492580320387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29620046905197661720213591 44430070357796492580320387)
          ·
            refine ⟨66645105536694738870480581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44430070357796492580320387 66645105536694738870480581)
            ·
              refine ⟨12495957288130263538215109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66645105536694738870480581 12495957288130263538215109)
              ·
                refine ⟨2342991991524424413415333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12495957288130263538215109 2342991991524424413415333)
                ·
                  refine ⟨439310998410829577515375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2342991991524424413415333 439310998410829577515375)
                  ·
                    rfl

theorem cell22_3849998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_3849998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3849998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3849998 prefixEnd_3849998 := by exact prefixLift 3849998
  have htrace : WordTrace (prefixWord ++ tailWord_3849998) baseStart_3849998 baseEnd_3849998 := by
    simpa [prefixWord, tailWord_3849998, baseEnd_3849998] using wordTrace_append hprefix tailTrace_3849998
  have hstable : (prefixWord ++ tailWord_3849998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849998).length < 2 ^ (prefixWord ++ tailWord_3849998).sum := by decide
  have hdescent : baseEnd_3849998 < baseStart_3849998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850004 : List Nat := [2, 4, 4, 1, 1, 1, 3, 1, 5]
def baseStart_3850004 : Nat := 118140960795 + 3850004 * 2 ^ 59
def prefixEnd_3850004 : Nat := 4983230072969 + 3 ^ 40 * 3850004 * 2
def baseEnd_3850004 : Nat := 439311683051702238965369

theorem tailTrace_3850004 : CollatzResearch.WordTrace tailWord_3850004 prefixEnd_3850004 439311683051702238965369 := by
  unfold tailWord_3850004
  simp only [CollatzResearch.WordTrace]
  refine ⟨70210590972050255589902533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93614121296067007453203377 70210590972050255589902533)
  ·
    refine ⟨13164485807259422923106725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70210590972050255589902533 13164485807259422923106725)
    ·
      refine ⟨2468341088861141798082511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13164485807259422923106725 2468341088861141798082511)
      ·
        refine ⟨3702511633291712697123767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2468341088861141798082511 3702511633291712697123767)
        ·
          refine ⟨5553767449937569045685651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3702511633291712697123767 5553767449937569045685651)
          ·
            refine ⟨8330651174906353568528477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5553767449937569045685651 8330651174906353568528477)
            ·
              refine ⟨3123994190589882588198179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8330651174906353568528477 3123994190589882588198179)
              ·
                refine ⟨4685991285884823882297269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3123994190589882588198179 4685991285884823882297269)
                ·
                  refine ⟨439311683051702238965369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4685991285884823882297269 439311683051702238965369)
                  ·
                    rfl

theorem cell22_3850004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_3850004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3850004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3850004 prefixEnd_3850004 := by exact prefixLift 3850004
  have htrace : WordTrace (prefixWord ++ tailWord_3850004) baseStart_3850004 baseEnd_3850004 := by
    simpa [prefixWord, tailWord_3850004, baseEnd_3850004] using wordTrace_append hprefix tailTrace_3850004
  have hstable : (prefixWord ++ tailWord_3850004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850004).length < 2 ^ (prefixWord ++ tailWord_3850004).sum := by decide
  have hdescent : baseEnd_3850004 < baseStart_3850004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850148 : List Nat := [2, 3, 1, 2, 1, 3, 2, 2, 1, 5]
def baseStart_3850148 : Nat := 118140960795 + 3850148 * 2 ^ 59
def prefixEnd_3850148 : Nat := 4983230072969 + 3 ^ 40 * 3850148 * 2
def baseEnd_3850148 : Nat := 1317984343297938341295665

theorem tailTrace_3850148 : CollatzResearch.WordTrace tailWord_3850148 prefixEnd_3850148 1317984343297938341295665 := by
  unfold tailWord_3850148
  simp only [CollatzResearch.WordTrace]
  refine ⟨70213217027789411886523549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93617622703719215848698065 70213217027789411886523549)
  ·
    refine ⟨26329956385421029457446331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70213217027789411886523549 26329956385421029457446331)
    ·
      refine ⟨39494934578131544186169497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26329956385421029457446331 39494934578131544186169497)
      ·
        refine ⟨29621200933598658139627123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39494934578131544186169497 29621200933598658139627123)
        ·
          refine ⟨44431801400397987209440685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29621200933598658139627123 44431801400397987209440685)
          ·
            refine ⟨16661925525149245203540257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44431801400397987209440685 16661925525149245203540257)
            ·
              refine ⟨12496444143861933902655193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16661925525149245203540257 12496444143861933902655193)
              ·
                refine ⟨9372333107896450426991395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12496444143861933902655193 9372333107896450426991395)
                ·
                  refine ⟨14058499661844675640487093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9372333107896450426991395 14058499661844675640487093)
                  ·
                    refine ⟨1317984343297938341295665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14058499661844675640487093 1317984343297938341295665)
                    ·
                      rfl

theorem cell22_3850148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_3850148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3850148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3850148 prefixEnd_3850148 := by exact prefixLift 3850148
  have htrace : WordTrace (prefixWord ++ tailWord_3850148) baseStart_3850148 baseEnd_3850148 := by
    simpa [prefixWord, tailWord_3850148, baseEnd_3850148] using wordTrace_append hprefix tailTrace_3850148
  have hstable : (prefixWord ++ tailWord_3850148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850148).length < 2 ^ (prefixWord ++ tailWord_3850148).sum := by decide
  have hdescent : baseEnd_3850148 < baseStart_3850148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850165 : List Nat := [1, 3, 3, 2, 1, 3, 1, 1, 4, 3]
def baseStart_3850165 : Nat := 118140960795 + 3850165 * 2 ^ 59
def prefixEnd_3850165 : Nat := 4983230072969 + 3 ^ 40 * 3850165 * 2
def baseEnd_3850165 : Nat := 1317990162745355963620613

theorem tailTrace_3850165 : CollatzResearch.WordTrace tailWord_3850165 prefixEnd_3850165 1317990162745355963620613 := by
  unfold tailWord_3850165
  simp only [CollatzResearch.WordTrace]
  refine ⟨140427054096517235676415949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93618036064344823784277299 140427054096517235676415949)
  ·
    refine ⟨52660145286193963378655981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140427054096517235676415949 52660145286193963378655981)
    ·
      refine ⟨19747554482322736266995993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52660145286193963378655981 19747554482322736266995993)
      ·
        refine ⟨14810665861742052200246995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19747554482322736266995993 14810665861742052200246995)
        ·
          refine ⟨22215998792613078300370493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14810665861742052200246995 22215998792613078300370493)
          ·
            refine ⟨8330999547229904362638935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22215998792613078300370493 8330999547229904362638935)
            ·
              refine ⟨12496499320844856543958403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8330999547229904362638935 12496499320844856543958403)
              ·
                refine ⟨18744748981267284815937605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12496499320844856543958403 18744748981267284815937605)
                ·
                  refine ⟨3514640433987615902988301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18744748981267284815937605 3514640433987615902988301)
                  ·
                    refine ⟨1317990162745355963620613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3514640433987615902988301 1317990162745355963620613)
                    ·
                      rfl

theorem cell22_3850165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_3850165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3850165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3850165 prefixEnd_3850165 := by exact prefixLift 3850165
  have htrace : WordTrace (prefixWord ++ tailWord_3850165) baseStart_3850165 baseEnd_3850165 := by
    simpa [prefixWord, tailWord_3850165, baseEnd_3850165] using wordTrace_append hprefix tailTrace_3850165
  have hstable : (prefixWord ++ tailWord_3850165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850165).length < 2 ^ (prefixWord ++ tailWord_3850165).sum := by decide
  have hdescent : baseEnd_3850165 < baseStart_3850165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850193 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 5, 3]
def baseStart_3850193 : Nat := 118140960795 + 3850193 * 2 ^ 59
def prefixEnd_3850193 : Nat := 4983230072969 + 3 ^ 40 * 3850193 * 2
def baseEnd_3850193 : Nat := 1317999747717573223920527

theorem tailTrace_3850193 : CollatzResearch.WordTrace tailWord_3850193 prefixEnd_3850193 1317999747717573223920527 := by
  unfold tailWord_3850193
  simp only [CollatzResearch.WordTrace]
  refine ⟨140428075340415796458435233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93618716893610530972290155 140428075340415796458435233)
  ·
    refine ⟨105321056505311847343826425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140428075340415796458435233 105321056505311847343826425)
    ·
      refine ⟨78990792378983885507869819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105321056505311847343826425 78990792378983885507869819)
      ·
        refine ⟨118486188568475828261804729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78990792378983885507869819 118486188568475828261804729)
        ·
          refine ⟨88864641426356871196353547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118486188568475828261804729 88864641426356871196353547)
          ·
            refine ⟨133296962139535306794530321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88864641426356871196353547 133296962139535306794530321)
            ·
              refine ⟨99972721604651480095897741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133296962139535306794530321 99972721604651480095897741)
              ·
                refine ⟨37489770601744305035961653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99972721604651480095897741 37489770601744305035961653)
                ·
                  refine ⟨3514665993913528597121405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37489770601744305035961653 3514665993913528597121405)
                  ·
                    refine ⟨1317999747717573223920527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3514665993913528597121405 1317999747717573223920527)
                    ·
                      rfl

theorem cell22_3850193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 5, 3].length) (baseStart_3850193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3850193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3850193 prefixEnd_3850193 := by exact prefixLift 3850193
  have htrace : WordTrace (prefixWord ++ tailWord_3850193) baseStart_3850193 baseEnd_3850193 := by
    simpa [prefixWord, tailWord_3850193, baseEnd_3850193] using wordTrace_append hprefix tailTrace_3850193
  have hstable : (prefixWord ++ tailWord_3850193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850193).length < 2 ^ (prefixWord ++ tailWord_3850193).sum := by decide
  have hdescent : baseEnd_3850193 < baseStart_3850193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850223 : List Nat := [1, 1, 2, 1, 4, 2, 2, 4, 5]
def baseStart_3850223 : Nat := 118140960795 + 3850223 * 2 ^ 59
def prefixEnd_3850223 : Nat := 4983230072969 + 3 ^ 40 * 3850223 * 2
def baseEnd_3850223 : Nat := 439336672443554381890145

theorem tailTrace_3850223 : CollatzResearch.WordTrace tailWord_3850223 prefixEnd_3850223 439336672443554381890145 := by
  unfold tailWord_3850223
  simp only [CollatzResearch.WordTrace]
  refine ⟨140429169530307111582027323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93619446353538074388018215 140429169530307111582027323)
  ·
    refine ⟨210643754295460667373040985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140429169530307111582027323 210643754295460667373040985)
    ·
      refine ⟨157982815721595500529780739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210643754295460667373040985 157982815721595500529780739)
      ·
        refine ⟨236974223582393250794671109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157982815721595500529780739 236974223582393250794671109)
        ·
          refine ⟨44432666921698734524000833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236974223582393250794671109 44432666921698734524000833)
          ·
            refine ⟨33324500191274050893000625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44432666921698734524000833 33324500191274050893000625)
            ·
              refine ⟨24993375143455538169750469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33324500191274050893000625 24993375143455538169750469)
              ·
                refine ⟨4686257839397913406828213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24993375143455538169750469 4686257839397913406828213)
                ·
                  refine ⟨439336672443554381890145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4686257839397913406828213 439336672443554381890145)
                  ·
                    rfl

theorem cell22_3850223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 5].length) (baseStart_3850223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3850223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3850223 prefixEnd_3850223 := by exact prefixLift 3850223
  have htrace : WordTrace (prefixWord ++ tailWord_3850223) baseStart_3850223 baseEnd_3850223 := by
    simpa [prefixWord, tailWord_3850223, baseEnd_3850223] using wordTrace_append hprefix tailTrace_3850223
  have hstable : (prefixWord ++ tailWord_3850223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850223).length < 2 ^ (prefixWord ++ tailWord_3850223).sum := by decide
  have hdescent : baseEnd_3850223 < baseStart_3850223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850298 : List Nat := [3, 1, 1, 1, 3, 1, 1, 4, 1, 6]
def baseStart_3850298 : Nat := 118140960795 + 3850298 * 2 ^ 59
def prefixEnd_3850298 : Nat := 4983230072969 + 3 ^ 40 * 3850298 * 2
def baseEnd_3850298 : Nat := 1318035691363387950045205

theorem tailTrace_3850298 : CollatzResearch.WordTrace tailWord_3850298 prefixEnd_3850298 1318035691363387950045205 := by
  unfold tailWord_3850298
  simp only [CollatzResearch.WordTrace]
  refine ⟨35107976251258849847751887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93621270003356932927338365 35107976251258849847751887)
  ·
    refine ⟨52661964376888274771627831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35107976251258849847751887 52661964376888274771627831)
    ·
      refine ⟨78992946565332412157441747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52661964376888274771627831 78992946565332412157441747)
      ·
        refine ⟨118489419847998618236162621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78992946565332412157441747 118489419847998618236162621)
        ·
          refine ⟨44433532442999481838560983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118489419847998618236162621 44433532442999481838560983)
          ·
            refine ⟨66650298664499222757841475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44433532442999481838560983 66650298664499222757841475)
            ·
              refine ⟨99975447996748834136762213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66650298664499222757841475 99975447996748834136762213)
              ·
                refine ⟨18745396499390406400642915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99975447996748834136762213 18745396499390406400642915)
                ·
                  refine ⟨28118094749085609600964373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18745396499390406400642915 28118094749085609600964373)
                  ·
                    refine ⟨1318035691363387950045205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28118094749085609600964373 1318035691363387950045205)
                    ·
                      rfl

theorem cell22_3850298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_3850298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3850298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3850298 prefixEnd_3850298 := by exact prefixLift 3850298
  have htrace : WordTrace (prefixWord ++ tailWord_3850298) baseStart_3850298 baseEnd_3850298 := by
    simpa [prefixWord, tailWord_3850298, baseEnd_3850298] using wordTrace_append hprefix tailTrace_3850298
  have hstable : (prefixWord ++ tailWord_3850298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850298).length < 2 ^ (prefixWord ++ tailWord_3850298).sum := by decide
  have hdescent : baseEnd_3850298 < baseStart_3850298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850300 : List Nat := [2, 2, 2, 2, 2, 1, 4, 1, 1, 5]
def baseStart_3850300 : Nat := 118140960795 + 3850300 * 2 ^ 59
def prefixEnd_3850300 : Nat := 4983230072969 + 3 ^ 40 * 3850300 * 2
def baseEnd_3850300 : Nat := 1318036376004260611495199

theorem tailTrace_3850300 : CollatzResearch.WordTrace tailWord_3850300 prefixEnd_3850300 1318036376004260611495199 := by
  unfold tailWord_3850300
  simp only [CollatzResearch.WordTrace]
  refine ⟨70215988975514076866290177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93621318634018769155053569 70215988975514076866290177)
  ·
    refine ⟨52661991731635557649717633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70215988975514076866290177 52661991731635557649717633)
    ·
      refine ⟨39496493798726668237288225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52661991731635557649717633 39496493798726668237288225)
      ·
        refine ⟨29622370349045001177966169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39496493798726668237288225 29622370349045001177966169)
        ·
          refine ⟨22216777761783750883474627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29622370349045001177966169 22216777761783750883474627)
          ·
            refine ⟨33325166642675626325211941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22216777761783750883474627 33325166642675626325211941)
            ·
              refine ⟨6248468745501679935977239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33325166642675626325211941 6248468745501679935977239)
              ·
                refine ⟨9372703118252519903965859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6248468745501679935977239 9372703118252519903965859)
                ·
                  refine ⟨14059054677378779855948789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9372703118252519903965859 14059054677378779855948789)
                  ·
                    refine ⟨1318036376004260611495199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14059054677378779855948789 1318036376004260611495199)
                    ·
                      rfl

theorem cell22_3850300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_3850300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3850300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3850300 prefixEnd_3850300 := by exact prefixLift 3850300
  have htrace : WordTrace (prefixWord ++ tailWord_3850300) baseStart_3850300 baseEnd_3850300 := by
    simpa [prefixWord, tailWord_3850300, baseEnd_3850300] using wordTrace_append hprefix tailTrace_3850300
  have hstable : (prefixWord ++ tailWord_3850300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850300).length < 2 ^ (prefixWord ++ tailWord_3850300).sum := by decide
  have hdescent : baseEnd_3850300 < baseStart_3850300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850302 : List Nat := [4, 2, 1, 3, 2, 1, 1, 2, 6]
def baseStart_3850302 : Nat := 118140960795 + 3850302 * 2 ^ 59
def prefixEnd_3850302 : Nat := 4983230072969 + 3 ^ 40 * 3850302 * 2
def baseEnd_3850302 : Nat := 439345686881711090981731

theorem tailTrace_3850302 : CollatzResearch.WordTrace tailWord_3850302 prefixEnd_3850302 439345686881711090981731 := by
  unfold tailWord_3850302
  simp only [CollatzResearch.WordTrace]
  refine ⟨17554006362127613509269145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93621367264680605382768773 17554006362127613509269145)
  ·
    refine ⟨13165504771595710131951859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17554006362127613509269145 13165504771595710131951859)
    ·
      refine ⟨19748257157393565197927789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13165504771595710131951859 19748257157393565197927789)
      ·
        refine ⟨7405596434022586949222921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19748257157393565197927789 7405596434022586949222921)
        ·
          refine ⟨5554197325516940211917191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7405596434022586949222921 5554197325516940211917191)
          ·
            refine ⟨8331295988275410317875787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5554197325516940211917191 8331295988275410317875787)
            ·
              refine ⟨12496943982413115476813681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8331295988275410317875787 12496943982413115476813681)
              ·
                refine ⟨9372707986809836607610261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12496943982413115476813681 9372707986809836607610261)
                ·
                  refine ⟨439345686881711090981731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9372707986809836607610261 439345686881711090981731)
                  ·
                    rfl

theorem cell22_3850302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_3850302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3850302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3850302 prefixEnd_3850302 := by exact prefixLift 3850302
  have htrace : WordTrace (prefixWord ++ tailWord_3850302) baseStart_3850302 baseEnd_3850302 := by
    simpa [prefixWord, tailWord_3850302, baseEnd_3850302] using wordTrace_append hprefix tailTrace_3850302
  have hstable : (prefixWord ++ tailWord_3850302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850302).length < 2 ^ (prefixWord ++ tailWord_3850302).sum := by decide
  have hdescent : baseEnd_3850302 < baseStart_3850302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850317 : List Nat := [1, 6, 1, 1, 1, 1, 2, 2, 4, 3]
def baseStart_3850317 : Nat := 118140960795 + 3850317 * 2 ^ 59
def prefixEnd_3850317 : Nat := 4983230072969 + 3 ^ 40 * 3850317 * 2
def baseEnd_3850317 : Nat := 1318042195451678233820147

theorem tailTrace_3850317 : CollatzResearch.WordTrace tailWord_3850317 prefixEnd_3850317 1318042195451678233820147 := by
  unfold tailWord_3850317
  simp only [CollatzResearch.WordTrace]
  refine ⟨140432597991966565635949205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93621731994644377090632803 140432597991966565635949205)
  ·
    refine ⟨6582778030873432764185119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 140432597991966565635949205 6582778030873432764185119)
    ·
      refine ⟨9874167046310149146277679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6582778030873432764185119 9874167046310149146277679)
      ·
        refine ⟨14811250569465223719416519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9874167046310149146277679 14811250569465223719416519)
        ·
          refine ⟨22216875854197835579124779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14811250569465223719416519 22216875854197835579124779)
          ·
            refine ⟨33325313781296753368687169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22216875854197835579124779 33325313781296753368687169)
            ·
              refine ⟨24993985335972565026515377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33325313781296753368687169 24993985335972565026515377)
              ·
                refine ⟨18745489001979423769886533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24993985335972565026515377 18745489001979423769886533)
                ·
                  refine ⟨3514779187871141956853725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18745489001979423769886533 3514779187871141956853725)
                  ·
                    refine ⟨1318042195451678233820147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3514779187871141956853725 1318042195451678233820147)
                    ·
                      rfl

theorem cell22_3850317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_3850317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3850317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3850317 prefixEnd_3850317 := by exact prefixLift 3850317
  have htrace : WordTrace (prefixWord ++ tailWord_3850317) baseStart_3850317 baseEnd_3850317 := by
    simpa [prefixWord, tailWord_3850317, baseEnd_3850317] using wordTrace_append hprefix tailTrace_3850317
  have hstable : (prefixWord ++ tailWord_3850317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850317).length < 2 ^ (prefixWord ++ tailWord_3850317).sum := by decide
  have hdescent : baseEnd_3850317 < baseStart_3850317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850396 : List Nat := [2, 2, 3, 2, 1, 1, 5, 2, 1, 3]
def baseStart_3850396 : Nat := 118140960795 + 3850396 * 2 ^ 59
def prefixEnd_3850396 : Nat := 4983230072969 + 3 ^ 40 * 3850396 * 2
def baseEnd_3850396 : Nat := 1318069238766148361094905

theorem tailTrace_3850396 : CollatzResearch.WordTrace tailWord_3850396 prefixEnd_3850396 1318069238766148361094905 := by
  unfold tailWord_3850396
  simp only [CollatzResearch.WordTrace]
  refine ⟨70217739679340181064037521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93623652905786908085383361 70217739679340181064037521)
  ·
    refine ⟨52663304759505135798028141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70217739679340181064037521 52663304759505135798028141)
    ·
      refine ⟨19748739284814425924260553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52663304759505135798028141 19748739284814425924260553)
      ·
        refine ⟨14811554463610819443195415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19748739284814425924260553 14811554463610819443195415)
        ·
          refine ⟨22217331695416229164793123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14811554463610819443195415 22217331695416229164793123)
          ·
            refine ⟨33325997543124343747189685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22217331695416229164793123 33325997543124343747189685)
            ·
              refine ⟨3124312269667907226299033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33325997543124343747189685 3124312269667907226299033)
              ·
                refine ⟨2343234202250930419724275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3124312269667907226299033 2343234202250930419724275)
                ·
                  refine ⟨3514851303376395629586413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2343234202250930419724275 3514851303376395629586413)
                  ·
                    refine ⟨1318069238766148361094905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3514851303376395629586413 1318069238766148361094905)
                    ·
                      rfl

theorem cell22_3850396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_3850396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3850396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3850396 prefixEnd_3850396 := by exact prefixLift 3850396
  have htrace : WordTrace (prefixWord ++ tailWord_3850396) baseStart_3850396 baseEnd_3850396 := by
    simpa [prefixWord, tailWord_3850396, baseEnd_3850396] using wordTrace_append hprefix tailTrace_3850396
  have hstable : (prefixWord ++ tailWord_3850396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850396).length < 2 ^ (prefixWord ++ tailWord_3850396).sum := by decide
  have hdescent : baseEnd_3850396 < baseStart_3850396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850405 : List Nat := [1, 3, 1, 2, 1, 3, 2, 2, 3, 4]
def baseStart_3850405 : Nat := 118140960795 + 3850405 * 2 ^ 59
def prefixEnd_3850405 : Nat := 4983230072969 + 3 ^ 40 * 3850405 * 2
def baseEnd_3850405 : Nat := 1318072319650075337619877

theorem tailTrace_3850405 : CollatzResearch.WordTrace tailWord_3850405 prefixEnd_3850405 1318072319650075337619877 := by
  unfold tailWord_3850405
  simp only [CollatzResearch.WordTrace]
  refine ⟨140435807615647756665152669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93623871743765171110101779 140435807615647756665152669)
  ·
    refine ⟨52663427855867908749432251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140435807615647756665152669 52663427855867908749432251)
    ·
      refine ⟨78995141783801863124148377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52663427855867908749432251 78995141783801863124148377)
      ·
        refine ⟨59246356337851397343111283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78995141783801863124148377 59246356337851397343111283)
        ·
          refine ⟨88869534506777096014666925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59246356337851397343111283 88869534506777096014666925)
          ·
            refine ⟨33326075440041411005500097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88869534506777096014666925 33326075440041411005500097)
            ·
              refine ⟨24994556580031058254125073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33326075440041411005500097 24994556580031058254125073)
              ·
                refine ⟨18745917435023293690593805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24994556580031058254125073 18745917435023293690593805)
                ·
                  refine ⟨7029719038133735133972677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18745917435023293690593805 7029719038133735133972677)
                  ·
                    refine ⟨1318072319650075337619877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7029719038133735133972677 1318072319650075337619877)
                    ·
                      rfl

theorem cell22_3850405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_3850405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3850405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3850405 prefixEnd_3850405 := by exact prefixLift 3850405
  have htrace : WordTrace (prefixWord ++ tailWord_3850405) baseStart_3850405 baseEnd_3850405 := by
    simpa [prefixWord, tailWord_3850405, baseEnd_3850405] using wordTrace_append hprefix tailTrace_3850405
  have hstable : (prefixWord ++ tailWord_3850405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850405).length < 2 ^ (prefixWord ++ tailWord_3850405).sum := by decide
  have hdescent : baseEnd_3850405 < baseStart_3850405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850469 : List Nat := [1, 3, 1, 4, 2, 1, 2, 3, 2, 3]
def baseStart_3850469 : Nat := 118140960795 + 3850469 * 2 ^ 59
def prefixEnd_3850469 : Nat := 4983230072969 + 3 ^ 40 * 3850469 * 2
def baseEnd_3850469 : Nat := 1318094228158000504019681

theorem tailTrace_3850469 : CollatzResearch.WordTrace tailWord_3850469 prefixEnd_3850469 1318094228158000504019681 := by
  unfold tailWord_3850469
  simp only [CollatzResearch.WordTrace]
  refine ⟨140438141887415895595482461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93625427924943930396988307 140438141887415895595482461)
  ·
    refine ⟨52664303207780960848305923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140438141887415895595482461 52664303207780960848305923)
    ·
      refine ⟨78996454811671441272458885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52664303207780960848305923 78996454811671441272458885)
      ·
        refine ⟨14811835277188395238586041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78996454811671441272458885 14811835277188395238586041)
        ·
          refine ⟨11108876457891296428939531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14811835277188395238586041 11108876457891296428939531)
          ·
            refine ⟨16663314686836944643409297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11108876457891296428939531 16663314686836944643409297)
            ·
              refine ⟨12497486015127708482556973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16663314686836944643409297 12497486015127708482556973)
              ·
                refine ⟨4686557255672890680958865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12497486015127708482556973 4686557255672890680958865)
                ·
                  refine ⟨3514917941754668010719149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4686557255672890680958865 3514917941754668010719149)
                  ·
                    refine ⟨1318094228158000504019681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3514917941754668010719149 1318094228158000504019681)
                    ·
                      rfl

theorem cell22_3850469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 2, 3].length) (baseStart_3850469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3850469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3850469 prefixEnd_3850469 := by exact prefixLift 3850469
  have htrace : WordTrace (prefixWord ++ tailWord_3850469) baseStart_3850469 baseEnd_3850469 := by
    simpa [prefixWord, tailWord_3850469, baseEnd_3850469] using wordTrace_append hprefix tailTrace_3850469
  have hstable : (prefixWord ++ tailWord_3850469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850469).length < 2 ^ (prefixWord ++ tailWord_3850469).sum := by decide
  have hdescent : baseEnd_3850469 < baseStart_3850469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850497 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 5, 3]
def baseStart_3850497 : Nat := 118140960795 + 3850497 * 2 ^ 59
def prefixEnd_3850497 : Nat := 4983230072969 + 3 ^ 40 * 3850497 * 2
def baseEnd_3850497 : Nat := 1318103813130217764319595

theorem tailTrace_3850497 : CollatzResearch.WordTrace tailWord_3850497 prefixEnd_3850497 1318103813130217764319595 := by
  unfold tailWord_3850497
  simp only [CollatzResearch.WordTrace]
  refine ⟨140439163131314456377501745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93626108754209637585001163 140439163131314456377501745)
  ·
    refine ⟨105329372348485842283126309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140439163131314456377501745 105329372348485842283126309)
    ·
      refine ⟨19749257315341095428086183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105329372348485842283126309 19749257315341095428086183)
      ·
        refine ⟨29623885973011643142129275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19749257315341095428086183 29623885973011643142129275)
        ·
          refine ⟨44435828959517464713193913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29623885973011643142129275 44435828959517464713193913)
          ·
            refine ⟨33326871719638098534895435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44435828959517464713193913 33326871719638098534895435)
            ·
              refine ⟨49990307579457147802343153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33326871719638098534895435 49990307579457147802343153)
              ·
                refine ⟨37492730684592860851757365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49990307579457147802343153 37492730684592860851757365)
                ·
                  refine ⟨3514943501680580704852253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37492730684592860851757365 3514943501680580704852253)
                  ·
                    refine ⟨1318103813130217764319595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3514943501680580704852253 1318103813130217764319595)
                    ·
                      rfl

theorem cell22_3850497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_3850497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3850497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3850497 prefixEnd_3850497 := by exact prefixLift 3850497
  have htrace : WordTrace (prefixWord ++ tailWord_3850497) baseStart_3850497 baseEnd_3850497 := by
    simpa [prefixWord, tailWord_3850497, baseEnd_3850497] using wordTrace_append hprefix tailTrace_3850497
  have hstable : (prefixWord ++ tailWord_3850497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850497).length < 2 ^ (prefixWord ++ tailWord_3850497).sum := by decide
  have hdescent : baseEnd_3850497 < baseStart_3850497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850503 : List Nat := [1, 1, 4, 5, 1, 2, 1, 2, 2, 3]
def baseStart_3850503 : Nat := 118140960795 + 3850503 * 2 ^ 59
def prefixEnd_3850503 : Nat := 4983230072969 + 3 ^ 40 * 3850503 * 2
def baseEnd_3850503 : Nat := 1318105867052835748669577

theorem tailTrace_3850503 : CollatzResearch.WordTrace tailWord_3850503 prefixEnd_3850503 1318105867052835748669577 := by
  unfold tailWord_3850503
  simp only [CollatzResearch.WordTrace]
  refine ⟨140439381969292719402220163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93626254646195146268146775 140439381969292719402220163)
  ·
    refine ⟨210659072953939079103330245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140439381969292719402220163 210659072953939079103330245)
    ·
      refine ⟨39498576178863577331874421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210659072953939079103330245 39498576178863577331874421)
      ·
        refine ⟨3702991516768460374863227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39498576178863577331874421 3702991516768460374863227)
        ·
          refine ⟨5554487275152690562294841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3702991516768460374863227 5554487275152690562294841)
          ·
            refine ⟨4165865456364517921721131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5554487275152690562294841 4165865456364517921721131)
            ·
              refine ⟨6248798184546776882581697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4165865456364517921721131 6248798184546776882581697)
              ·
                refine ⟨4686598638410082661936273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6248798184546776882581697 4686598638410082661936273)
                ·
                  refine ⟨3514948978807561996452205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4686598638410082661936273 3514948978807561996452205)
                  ·
                    refine ⟨1318105867052835748669577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3514948978807561996452205 1318105867052835748669577)
                    ·
                      rfl

theorem cell22_3850503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_3850503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3850503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3850503 prefixEnd_3850503 := by exact prefixLift 3850503
  have htrace : WordTrace (prefixWord ++ tailWord_3850503) baseStart_3850503 baseEnd_3850503 := by
    simpa [prefixWord, tailWord_3850503, baseEnd_3850503] using wordTrace_append hprefix tailTrace_3850503
  have hstable : (prefixWord ++ tailWord_3850503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850503).length < 2 ^ (prefixWord ++ tailWord_3850503).sum := by decide
  have hdescent : baseEnd_3850503 < baseStart_3850503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850548 : List Nat := [2, 5, 1, 1, 1, 2, 3, 3, 1, 3]
def baseStart_3850548 : Nat := 118140960795 + 3850548 * 2 ^ 59
def prefixEnd_3850548 : Nat := 4983230072969 + 3 ^ 40 * 3850548 * 2
def baseEnd_3850548 : Nat := 1318121271472470631294439

theorem tailTrace_3850548 : CollatzResearch.WordTrace tailWord_3850548 prefixEnd_3850548 1318121271472470631294439 := by
  unfold tailWord_3850548
  simp only [CollatzResearch.WordTrace]
  refine ⟨70220511627064846043804149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93627348836086461391738865 70220511627064846043804149)
  ·
    refine ⟨6583172965037329316606639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70220511627064846043804149 6583172965037329316606639)
    ·
      refine ⟨9874759447555993974909959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6583172965037329316606639 9874759447555993974909959)
      ·
        refine ⟨14812139171333990962364939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9874759447555993974909959 14812139171333990962364939)
        ·
          refine ⟨22218208757000986443547409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14812139171333990962364939 22218208757000986443547409)
          ·
            refine ⟨16663656567750739832660557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22218208757000986443547409 16663656567750739832660557)
            ·
              refine ⟨6248871212906527437247709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16663656567750739832660557 6248871212906527437247709)
              ·
                refine ⟨2343326704839947788967891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6248871212906527437247709 2343326704839947788967891)
                ·
                  refine ⟨3514990057259921683451837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2343326704839947788967891 3514990057259921683451837)
                  ·
                    refine ⟨1318121271472470631294439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3514990057259921683451837 1318121271472470631294439)
                    ·
                      rfl

theorem cell22_3850548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_3850548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3850548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3850548 prefixEnd_3850548 := by exact prefixLift 3850548
  have htrace : WordTrace (prefixWord ++ tailWord_3850548) baseStart_3850548 baseEnd_3850548 := by
    simpa [prefixWord, tailWord_3850548, baseEnd_3850548] using wordTrace_append hprefix tailTrace_3850548
  have hstable : (prefixWord ++ tailWord_3850548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850548).length < 2 ^ (prefixWord ++ tailWord_3850548).sum := by decide
  have hdescent : baseEnd_3850548 < baseStart_3850548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850604 : List Nat := [2, 2, 1, 1, 6, 1, 1, 2, 1, 5]
def baseStart_3850604 : Nat := 118140960795 + 3850604 * 2 ^ 59
def prefixEnd_3850604 : Nat := 4983230072969 + 3 ^ 40 * 3850604 * 2
def baseEnd_3850604 : Nat := 1318140441416905151894267

theorem tailTrace_3850604 : CollatzResearch.WordTrace tailWord_3850604 prefixEnd_3850604 1318140441416905151894267 := by
  unfold tailWord_3850604
  simp only [CollatzResearch.WordTrace]
  refine ⟨70221532870963406825823433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93628710494617875767764577 70221532870963406825823433)
  ·
    refine ⟨52666149653222555119367575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70221532870963406825823433 52666149653222555119367575)
    ·
      refine ⟨78999224479833832679051363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52666149653222555119367575 78999224479833832679051363)
      ·
        refine ⟨118498836719750749018577045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78999224479833832679051363 118498836719750749018577045)
        ·
          refine ⟨5554632971238316360245799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 118498836719750749018577045 5554632971238316360245799)
          ·
            refine ⟨8331949456857474540368699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5554632971238316360245799 8331949456857474540368699)
            ·
              refine ⟨12497924185286211810553049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8331949456857474540368699 12497924185286211810553049)
              ·
                refine ⟨9373443138964658857914787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12497924185286211810553049 9373443138964658857914787)
                ·
                  refine ⟨14060164708446988286872181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9373443138964658857914787 14060164708446988286872181)
                  ·
                    refine ⟨1318140441416905151894267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14060164708446988286872181 1318140441416905151894267)
                    ·
                      rfl

theorem cell22_3850604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_3850604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3850604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3850604 prefixEnd_3850604 := by exact prefixLift 3850604
  have htrace : WordTrace (prefixWord ++ tailWord_3850604) baseStart_3850604 baseEnd_3850604 := by
    simpa [prefixWord, tailWord_3850604, baseEnd_3850604] using wordTrace_append hprefix tailTrace_3850604
  have hstable : (prefixWord ++ tailWord_3850604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850604).length < 2 ^ (prefixWord ++ tailWord_3850604).sum := by decide
  have hdescent : baseEnd_3850604 < baseStart_3850604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850621 : List Nat := [1, 4, 1, 1, 2, 4, 2, 2, 2, 3]
def baseStart_3850621 : Nat := 118140960795 + 3850621 * 2 ^ 59
def prefixEnd_3850621 : Nat := 4983230072969 + 3 ^ 40 * 3850621 * 2
def baseEnd_3850621 : Nat := 1318146260864322774219215

theorem tailTrace_3850621 : CollatzResearch.WordTrace tailWord_3850621 prefixEnd_3850621 1318146260864322774219215 := by
  unfold tailWord_3850621
  simp only [CollatzResearch.WordTrace]
  refine ⟨140443685782865225555015717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93629123855243483703343811 140443685782865225555015717)
  ·
    refine ⟨26333191084287229791565447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140443685782865225555015717 26333191084287229791565447)
    ·
      refine ⟨39499786626430844687348171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26333191084287229791565447 39499786626430844687348171)
      ·
        refine ⟨59249679939646267031022257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39499786626430844687348171 59249679939646267031022257)
        ·
          refine ⟨44437259954734700273266693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59249679939646267031022257 44437259954734700273266693)
          ·
            refine ⟨8331986241512756301237505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44437259954734700273266693 8331986241512756301237505)
            ·
              refine ⟨6248989681134567225928129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8331986241512756301237505 6248989681134567225928129)
              ·
                refine ⟨4686742260850925419446097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6248989681134567225928129 4686742260850925419446097)
                ·
                  refine ⟨3515056695638194064584573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4686742260850925419446097 3515056695638194064584573)
                  ·
                    refine ⟨1318146260864322774219215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3515056695638194064584573 1318146260864322774219215)
                    ·
                      rfl

theorem cell22_3850621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_3850621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3850621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3850621 prefixEnd_3850621 := by exact prefixLift 3850621
  have htrace : WordTrace (prefixWord ++ tailWord_3850621) baseStart_3850621 baseEnd_3850621 := by
    simpa [prefixWord, tailWord_3850621, baseEnd_3850621] using wordTrace_append hprefix tailTrace_3850621
  have hstable : (prefixWord ++ tailWord_3850621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850621).length < 2 ^ (prefixWord ++ tailWord_3850621).sum := by decide
  have hdescent : baseEnd_3850621 < baseStart_3850621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850649 : List Nat := [1, 2, 1, 2, 1, 4, 3, 2, 3, 3]
def baseStart_3850649 : Nat := 118140960795 + 3850649 * 2 ^ 59
def prefixEnd_3850649 : Nat := 4983230072969 + 3 ^ 40 * 3850649 * 2
def baseEnd_3850649 : Nat := 1318155845836540034519129

theorem tailTrace_3850649 : CollatzResearch.WordTrace tailWord_3850649 prefixEnd_3850649 1318155845836540034519129 := by
  unfold tailWord_3850649
  simp only [CollatzResearch.WordTrace]
  refine ⟨140444707026763786337035001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93629804684509190891356667 140444707026763786337035001)
  ·
    refine ⟨105333530270072839752776251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140444707026763786337035001 105333530270072839752776251)
    ·
      refine ⟨158000295405109259629164377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105333530270072839752776251 158000295405109259629164377)
      ·
        refine ⟨118500221553831944721873283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158000295405109259629164377 118500221553831944721873283)
        ·
          refine ⟨177750332330747917082809925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118500221553831944721873283 177750332330747917082809925)
          ·
            refine ⟨33328187312015234453026861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177750332330747917082809925 33328187312015234453026861)
            ·
              refine ⟨12498070242005712919885073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33328187312015234453026861 12498070242005712919885073)
              ·
                refine ⟨9373552681504284689913805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12498070242005712919885073 9373552681504284689913805)
                ·
                  refine ⟨3515082255564106758717677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9373552681504284689913805 3515082255564106758717677)
                  ·
                    refine ⟨1318155845836540034519129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3515082255564106758717677 1318155845836540034519129)
                    ·
                      rfl

theorem cell22_3850649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 3, 3].length) (baseStart_3850649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3850649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3850649 prefixEnd_3850649 := by exact prefixLift 3850649
  have htrace : WordTrace (prefixWord ++ tailWord_3850649) baseStart_3850649 baseEnd_3850649 := by
    simpa [prefixWord, tailWord_3850649, baseEnd_3850649] using wordTrace_append hprefix tailTrace_3850649
  have hstable : (prefixWord ++ tailWord_3850649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850649).length < 2 ^ (prefixWord ++ tailWord_3850649).sum := by decide
  have hdescent : baseEnd_3850649 < baseStart_3850649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850653 : List Nat := [1, 4, 2, 1, 5, 1, 1, 1, 2, 4]
def baseStart_3850653 : Nat := 118140960795 + 3850653 * 2 ^ 59
def prefixEnd_3850653 : Nat := 4983230072969 + 3 ^ 40 * 3850653 * 2
def baseEnd_3850653 : Nat := 1318157215118285357419117

theorem tailTrace_3850653 : CollatzResearch.WordTrace tailWord_3850653 prefixEnd_3850653 1318157215118285357419117 := by
  unfold tailWord_3850653
  simp only [CollatzResearch.WordTrace]
  refine ⟨140444852918749295020180613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93629901945832863346787075 140444852918749295020180613)
  ·
    refine ⟨26333409922265492816283865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140444852918749295020180613 26333409922265492816283865)
    ·
      refine ⟨19750057441699119612212899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26333409922265492816283865 19750057441699119612212899)
      ·
        refine ⟨29625086162548679418319349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19750057441699119612212899 29625086162548679418319349)
        ·
          refine ⟨2777351827738938695467439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29625086162548679418319349 2777351827738938695467439)
          ·
            refine ⟨4166027741608408043201159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2777351827738938695467439 4166027741608408043201159)
            ·
              refine ⟨6249041612412612064801739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4166027741608408043201159 6249041612412612064801739)
              ·
                refine ⟨9373562418618918097202609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6249041612412612064801739 9373562418618918097202609)
                ·
                  refine ⟨7030171813964188572901957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9373562418618918097202609 7030171813964188572901957)
                  ·
                    refine ⟨1318157215118285357419117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7030171813964188572901957 1318157215118285357419117)
                    ·
                      rfl

theorem cell22_3850653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_3850653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3850653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3850653 prefixEnd_3850653 := by exact prefixLift 3850653
  have htrace : WordTrace (prefixWord ++ tailWord_3850653) baseStart_3850653 baseEnd_3850653 := by
    simpa [prefixWord, tailWord_3850653, baseEnd_3850653] using wordTrace_append hprefix tailTrace_3850653
  have hstable : (prefixWord ++ tailWord_3850653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850653).length < 2 ^ (prefixWord ++ tailWord_3850653).sum := by decide
  have hdescent : baseEnd_3850653 < baseStart_3850653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850679 : List Nat := [1, 1, 3, 1, 3, 3, 3, 2, 5]
def baseStart_3850679 : Nat := 118140960795 + 3850679 * 2 ^ 59
def prefixEnd_3850679 : Nat := 4983230072969 + 3 ^ 40 * 3850679 * 2
def baseEnd_3850679 : Nat := 439388705149876652089679

theorem tailTrace_3850679 : CollatzResearch.WordTrace tailWord_3850679 prefixEnd_3850679 439388705149876652089679 := by
  unfold tailWord_3850679
  simp only [CollatzResearch.WordTrace]
  refine ⟨140445801216655101460627091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93630534144436734307084727 140445801216655101460627091)
  ·
    refine ⟨210668701824982652190940637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140445801216655101460627091 210668701824982652190940637)
    ·
      refine ⟨79000763184368494571602739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210668701824982652190940637 79000763184368494571602739)
      ·
        refine ⟨118501144776552741857404109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79000763184368494571602739 118501144776552741857404109)
        ·
          refine ⟨44437929291207278196526541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118501144776552741857404109 44437929291207278196526541)
          ·
            refine ⟨16664223484202729323697453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44437929291207278196526541 16664223484202729323697453)
            ·
              refine ⟨6249083806576023496386545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16664223484202729323697453 6249083806576023496386545)
              ·
                refine ⟨4686812854932017622289909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6249083806576023496386545 4686812854932017622289909)
                ·
                  refine ⟨439388705149876652089679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4686812854932017622289909 439388705149876652089679)
                  ·
                    rfl

theorem cell22_3850679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 5].length) (baseStart_3850679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3850679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3850679 prefixEnd_3850679 := by exact prefixLift 3850679
  have htrace : WordTrace (prefixWord ++ tailWord_3850679) baseStart_3850679 baseEnd_3850679 := by
    simpa [prefixWord, tailWord_3850679, baseEnd_3850679] using wordTrace_append hprefix tailTrace_3850679
  have hstable : (prefixWord ++ tailWord_3850679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850679).length < 2 ^ (prefixWord ++ tailWord_3850679).sum := by decide
  have hdescent : baseEnd_3850679 < baseStart_3850679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850696 : List Nat := [2, 1, 3, 1, 3, 3, 3, 1, 5]
def baseStart_3850696 : Nat := 118140960795 + 3850696 * 2 ^ 59
def prefixEnd_3850696 : Nat := 4983230072969 + 3 ^ 40 * 3850696 * 2
def baseEnd_3850696 : Nat := 439390644965682526197995

theorem tailTrace_3850696 : CollatzResearch.WordTrace tailWord_3850696 prefixEnd_3850696 439390644965682526197995 := by
  unfold tailWord_3850696
  simp only [CollatzResearch.WordTrace]
  refine ⟨70223210628796756681997971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93630947505062342242663961 70223210628796756681997971)
  ·
    refine ⟨105334815943195135022996957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70223210628796756681997971 105334815943195135022996957)
    ·
      refine ⟨39500555978698175633623859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105334815943195135022996957 39500555978698175633623859)
      ·
        refine ⟨59250833968047263450435789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39500555978698175633623859 59250833968047263450435789)
        ·
          refine ⟨22219062738017723793913421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59250833968047263450435789 22219062738017723793913421)
          ·
            refine ⟨8332148526756646422717533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22219062738017723793913421 8332148526756646422717533)
            ·
              refine ⟨3124555697533742408519075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8332148526756646422717533 3124555697533742408519075)
              ·
                refine ⟨4686833546300613612778613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3124555697533742408519075 4686833546300613612778613)
                ·
                  refine ⟨439390644965682526197995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4686833546300613612778613 439390644965682526197995)
                  ·
                    rfl

theorem cell22_3850696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 5].length) (baseStart_3850696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3850696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3850696 prefixEnd_3850696 := by exact prefixLift 3850696
  have htrace : WordTrace (prefixWord ++ tailWord_3850696) baseStart_3850696 baseEnd_3850696 := by
    simpa [prefixWord, tailWord_3850696, baseEnd_3850696] using wordTrace_append hprefix tailTrace_3850696
  have hstable : (prefixWord ++ tailWord_3850696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850696).length < 2 ^ (prefixWord ++ tailWord_3850696).sum := by decide
  have hdescent : baseEnd_3850696 < baseStart_3850696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850739 : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 4, 3]
def baseStart_3850739 : Nat := 118140960795 + 3850739 * 2 ^ 59
def prefixEnd_3850739 : Nat := 4983230072969 + 3 ^ 40 * 3850739 * 2
def baseEnd_3850739 : Nat := 1318186654675809799768853

theorem tailTrace_3850739 : CollatzResearch.WordTrace tailWord_3850739 prefixEnd_3850739 1318186654675809799768853 := by
  unfold tailWord_3850739
  simp only [CollatzResearch.WordTrace]
  refine ⟨140447989596437731707811271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93631993064291821138540847 140447989596437731707811271)
  ·
    refine ⟨210671984394656597561716907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140447989596437731707811271 210671984394656597561716907)
    ·
      refine ⟨316007976591984896342575361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210671984394656597561716907 316007976591984896342575361)
      ·
        refine ⟨237005982443988672256931521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316007976591984896342575361 237005982443988672256931521)
        ·
          refine ⟨177754486832991504192698641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237005982443988672256931521 177754486832991504192698641)
          ·
            refine ⟨133315865124743628144523981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177754486832991504192698641 133315865124743628144523981)
            ·
              refine ⟨49993449421778860554196493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133315865124743628144523981 49993449421778860554196493)
              ·
                refine ⟨18747543533167072707823685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49993449421778860554196493 18747543533167072707823685)
                ·
                  refine ⟨3515164412468826132716941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18747543533167072707823685 3515164412468826132716941)
                  ·
                    refine ⟨1318186654675809799768853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3515164412468826132716941 1318186654675809799768853)
                    ·
                      rfl

theorem cell22_3850739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 3].length) (baseStart_3850739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3850739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3850739 prefixEnd_3850739 := by exact prefixLift 3850739
  have htrace : WordTrace (prefixWord ++ tailWord_3850739) baseStart_3850739 baseEnd_3850739 := by
    simpa [prefixWord, tailWord_3850739, baseEnd_3850739] using wordTrace_append hprefix tailTrace_3850739
  have hstable : (prefixWord ++ tailWord_3850739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850739).length < 2 ^ (prefixWord ++ tailWord_3850739).sum := by decide
  have hdescent : baseEnd_3850739 < baseStart_3850739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850767 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 1, 9]
def baseStart_3850767 : Nat := 118140960795 + 3850767 * 2 ^ 59
def prefixEnd_3850767 : Nat := 4983230072969 + 3 ^ 40 * 3850767 * 2
def baseEnd_3850767 : Nat := 1318196239648027060068767

theorem tailTrace_3850767 : CollatzResearch.WordTrace tailWord_3850767 prefixEnd_3850767 1318196239648027060068767 := by
  unfold tailWord_3850767
  simp only [CollatzResearch.WordTrace]
  refine ⟨140449010840336292489830555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93632673893557528326553703 140449010840336292489830555)
  ·
    refine ⟨210673516260504438734745833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140449010840336292489830555 210673516260504438734745833)
    ·
      refine ⟨158005137195378329051059375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210673516260504438734745833 158005137195378329051059375)
      ·
        refine ⟨237007705793067493576589063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158005137195378329051059375 237007705793067493576589063)
        ·
          refine ⟨355511558689601240364883595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237007705793067493576589063 355511558689601240364883595)
          ·
            refine ⟨533267338034401860547325393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355511558689601240364883595 533267338034401860547325393)
            ·
              refine ⟨399950503525801395410494045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 533267338034401860547325393 399950503525801395410494045)
              ·
                refine ⟨149981438822175523278935267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 399950503525801395410494045 149981438822175523278935267)
                ·
                  refine ⟨224972158233263284918402901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149981438822175523278935267 224972158233263284918402901)
                  ·
                    refine ⟨1318196239648027060068767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 224972158233263284918402901 1318196239648027060068767)
                    ·
                      rfl

theorem cell22_3850767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 9].length) (baseStart_3850767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3850767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3850767 prefixEnd_3850767 := by exact prefixLift 3850767
  have htrace : WordTrace (prefixWord ++ tailWord_3850767) baseStart_3850767 baseEnd_3850767 := by
    simpa [prefixWord, tailWord_3850767, baseEnd_3850767] using wordTrace_append hprefix tailTrace_3850767
  have hstable : (prefixWord ++ tailWord_3850767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850767).length < 2 ^ (prefixWord ++ tailWord_3850767).sum := by decide
  have hdescent : baseEnd_3850767 < baseStart_3850767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850908 : List Nat := [2, 2, 3, 2, 2, 1, 2, 1, 4, 3]
def baseStart_3850908 : Nat := 118140960795 + 3850908 * 2 ^ 59
def prefixEnd_3850908 : Nat := 4983230072969 + 3 ^ 40 * 3850908 * 2
def baseEnd_3850908 : Nat := 1318244506829549692293335

theorem tailTrace_3850908 : CollatzResearch.WordTrace tailWord_3850908 prefixEnd_3850908 1318244506829549692293335 := by
  unfold tailWord_3850908
  simp only [CollatzResearch.WordTrace]
  refine ⟨70227076766412736785356689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93636102355216982380475585 70227076766412736785356689)
  ·
    refine ⟨52670307574809552589017517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70227076766412736785356689 52670307574809552589017517)
    ·
      refine ⟨19751365340553582220881569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52670307574809552589017517 19751365340553582220881569)
      ·
        refine ⟨14813524005415186665661177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19751365340553582220881569 14813524005415186665661177)
        ·
          refine ⟨11110143004061389999245883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14813524005415186665661177 11110143004061389999245883)
          ·
            refine ⟨16665214506092084998868825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11110143004061389999245883 16665214506092084998868825)
            ·
              refine ⟨12498910879569063749151619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16665214506092084998868825 12498910879569063749151619)
              ·
                refine ⟨18748366319353595623727429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12498910879569063749151619 18748366319353595623727429)
                ·
                  refine ⟨3515318684878799179448893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18748366319353595623727429 3515318684878799179448893)
                  ·
                    refine ⟨1318244506829549692293335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3515318684878799179448893 1318244506829549692293335)
                    ·
                      rfl

theorem cell22_3850908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_3850908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3850908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3850908 prefixEnd_3850908 := by exact prefixLift 3850908
  have htrace : WordTrace (prefixWord ++ tailWord_3850908) baseStart_3850908 baseEnd_3850908 := by
    simpa [prefixWord, tailWord_3850908, baseEnd_3850908] using wordTrace_append hprefix tailTrace_3850908
  have hstable : (prefixWord ++ tailWord_3850908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850908).length < 2 ^ (prefixWord ++ tailWord_3850908).sum := by decide
  have hdescent : baseEnd_3850908 < baseStart_3850908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850925 : List Nat := [1, 5, 2, 1, 1, 3, 1, 3, 2, 3]
def baseStart_3850925 : Nat := 118140960795 + 3850925 * 2 ^ 59
def prefixEnd_3850925 : Nat := 4983230072969 + 3 ^ 40 * 3850925 * 2
def baseEnd_3850925 : Nat := 1318250326276967314618283

theorem tailTrace_3850925 : CollatzResearch.WordTrace tailWord_3850925 prefixEnd_3850925 1318250326276967314618283 := by
  unfold tailWord_3850925
  simp only [CollatzResearch.WordTrace]
  refine ⟨140454773573763885474082229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93636515715842590316054819 140454773573763885474082229)
  ·
    refine ⟨13167635022540364263195209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140454773573763885474082229 13167635022540364263195209)
    ·
      refine ⟨9875726266905273197396407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13167635022540364263195209 9875726266905273197396407)
      ·
        refine ⟨14813589400357909796094611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9875726266905273197396407 14813589400357909796094611)
        ·
          refine ⟨22220384100536864694141917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14813589400357909796094611 22220384100536864694141917)
          ·
            refine ⟨8332644037701324260303219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22220384100536864694141917 8332644037701324260303219)
            ·
              refine ⟨12498966056551986390454829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8332644037701324260303219 12498966056551986390454829)
              ·
                refine ⟨4687112271206994896420561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12498966056551986390454829 4687112271206994896420561)
                ·
                  refine ⟨3515334203405246172315421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4687112271206994896420561 3515334203405246172315421)
                  ·
                    refine ⟨1318250326276967314618283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3515334203405246172315421 1318250326276967314618283)
                    ·
                      rfl

theorem cell22_3850925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_3850925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3850925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3850925 prefixEnd_3850925 := by exact prefixLift 3850925
  have htrace : WordTrace (prefixWord ++ tailWord_3850925) baseStart_3850925 baseEnd_3850925 := by
    simpa [prefixWord, tailWord_3850925, baseEnd_3850925] using wordTrace_append hprefix tailTrace_3850925
  have hstable : (prefixWord ++ tailWord_3850925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850925).length < 2 ^ (prefixWord ++ tailWord_3850925).sum := by decide
  have hdescent : baseEnd_3850925 < baseStart_3850925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850970 : List Nat := [3, 1, 1, 2, 2, 2, 3, 4, 1, 3]
def baseStart_3850970 : Nat := 118140960795 + 3850970 * 2 ^ 59
def prefixEnd_3850970 : Nat := 4983230072969 + 3 ^ 40 * 3850970 * 2
def baseEnd_3850970 : Nat := 1318265730696602197243145

theorem tailTrace_3850970 : CollatzResearch.WordTrace tailWord_3850970 prefixEnd_3850970 1318265730696602197243145 := by
  unfold tailWord_3850970
  simp only [CollatzResearch.WordTrace]
  refine ⟨35114103714650214539867591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93637609905733905439646909 35114103714650214539867591)
  ·
    refine ⟨52671155571975321809801387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35114103714650214539867591 52671155571975321809801387)
    ·
      refine ⟨79006733357962982714702081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52671155571975321809801387 79006733357962982714702081)
      ·
        refine ⟨59255050018472237036026561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79006733357962982714702081 59255050018472237036026561)
        ·
          refine ⟨44441287513854177777019921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59255050018472237036026561 44441287513854177777019921)
          ·
            refine ⟨33330965635390633332764941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44441287513854177777019921 33330965635390633332764941)
            ·
              refine ⟨12499112113271487499786853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33330965635390633332764941 12499112113271487499786853)
              ·
                refine ⟨2343583521238403906210035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12499112113271487499786853 2343583521238403906210035)
                ·
                  refine ⟨3515375281857605859315053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2343583521238403906210035 3515375281857605859315053)
                  ·
                    refine ⟨1318265730696602197243145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3515375281857605859315053 1318265730696602197243145)
                    ·
                      rfl

theorem cell22_3850970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 4, 1, 3].length) (baseStart_3850970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3850970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3850970 prefixEnd_3850970 := by exact prefixLift 3850970
  have htrace : WordTrace (prefixWord ++ tailWord_3850970) baseStart_3850970 baseEnd_3850970 := by
    simpa [prefixWord, tailWord_3850970, baseEnd_3850970] using wordTrace_append hprefix tailTrace_3850970
  have hstable : (prefixWord ++ tailWord_3850970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850970).length < 2 ^ (prefixWord ++ tailWord_3850970).sum := by decide
  have hdescent : baseEnd_3850970 < baseStart_3850970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3850981 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 1, 7]
def baseStart_3850981 : Nat := 118140960795 + 3850981 * 2 ^ 59
def prefixEnd_3850981 : Nat := 4983230072969 + 3 ^ 40 * 3850981 * 2
def baseEnd_3850981 : Nat := 1318269496221401835218111

theorem tailTrace_3850981 : CollatzResearch.WordTrace tailWord_3850981 prefixEnd_3850981 1318269496221401835218111 := by
  unfold tailWord_3850981
  simp only [CollatzResearch.WordTrace]
  refine ⟨140456816061561007038120797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93637877374374004692080531 140456816061561007038120797)
  ·
    refine ⟨52671306023085377639295299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140456816061561007038120797 52671306023085377639295299)
    ·
      refine ⟨79006959034628066458942949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52671306023085377639295299 79006959034628066458942949)
      ·
        refine ⟨14813804818992762461051803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79006959034628066458942949 14813804818992762461051803)
        ·
          refine ⟨22220707228489143691577705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14813804818992762461051803 22220707228489143691577705)
          ·
            refine ⟨16665530421366857768683279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22220707228489143691577705 16665530421366857768683279)
            ·
              refine ⟨24998295632050286653024919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16665530421366857768683279 24998295632050286653024919)
              ·
                refine ⟨37497443448075429979537379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24998295632050286653024919 37497443448075429979537379)
                ·
                  refine ⟨56246165172113144969306069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37497443448075429979537379 56246165172113144969306069)
                  ·
                    refine ⟨1318269496221401835218111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56246165172113144969306069 1318269496221401835218111)
                    ·
                      rfl

theorem cell22_3850981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_3850981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3850981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3850981 prefixEnd_3850981 := by exact prefixLift 3850981
  have htrace : WordTrace (prefixWord ++ tailWord_3850981) baseStart_3850981 baseEnd_3850981 := by
    simpa [prefixWord, tailWord_3850981, baseEnd_3850981] using wordTrace_append hprefix tailTrace_3850981
  have hstable : (prefixWord ++ tailWord_3850981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3850981).length < 2 ^ (prefixWord ++ tailWord_3850981).sum := by decide
  have hdescent : baseEnd_3850981 < baseStart_3850981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3850981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851041 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 3, 6]
def baseStart_3851041 : Nat := 118140960795 + 3851041 * 2 ^ 59
def prefixEnd_3851041 : Nat := 4983230072969 + 3 ^ 40 * 3851041 * 2
def baseEnd_3851041 : Nat := 1318290035447581678717927

theorem tailTrace_3851041 : CollatzResearch.WordTrace tailWord_3851041 prefixEnd_3851041 1318290035447581678717927 := by
  unfold tailWord_3851041
  simp only [CollatzResearch.WordTrace]
  refine ⟨140459004441343637285304977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93639336294229091523536651 140459004441343637285304977)
  ·
    refine ⟨105344253331007727963978733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140459004441343637285304977 105344253331007727963978733)
    ·
      refine ⟨39504094999127897986492025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105344253331007727963978733 39504094999127897986492025)
      ·
        refine ⟨29628071249345923489869019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39504094999127897986492025 29628071249345923489869019)
        ·
          refine ⟨44442106874018885234803529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29628071249345923489869019 44442106874018885234803529)
          ·
            refine ⟨33331580155514163926102647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44442106874018885234803529 33331580155514163926102647)
            ·
              refine ⟨49997370233271245889153971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33331580155514163926102647 49997370233271245889153971)
              ·
                refine ⟨74996055349906868833730957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49997370233271245889153971 74996055349906868833730957)
                ·
                  refine ⟨28123520756215075812649109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74996055349906868833730957 28123520756215075812649109)
                  ·
                    refine ⟨1318290035447581678717927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28123520756215075812649109 1318290035447581678717927)
                    ·
                      rfl

theorem cell22_3851041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_3851041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3851041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3851041 prefixEnd_3851041 := by exact prefixLift 3851041
  have htrace : WordTrace (prefixWord ++ tailWord_3851041) baseStart_3851041 baseEnd_3851041 := by
    simpa [prefixWord, tailWord_3851041, baseEnd_3851041] using wordTrace_append hprefix tailTrace_3851041
  have hstable : (prefixWord ++ tailWord_3851041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851041).length < 2 ^ (prefixWord ++ tailWord_3851041).sum := by decide
  have hdescent : baseEnd_3851041 < baseStart_3851041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851058 : List Nat := [3, 2, 1, 1, 3, 1, 2, 3, 2, 4]
def baseStart_3851058 : Nat := 118140960795 + 3851058 * 2 ^ 59
def prefixEnd_3851058 : Nat := 4983230072969 + 3 ^ 40 * 3851058 * 2
def baseEnd_3851058 : Nat := 1318295854894999301042875

theorem tailTrace_3851058 : CollatzResearch.WordTrace tailWord_3851058 prefixEnd_3851058 1318295854894999301042875 := by
  unfold tailWord_3851058
  simp only [CollatzResearch.WordTrace]
  refine ⟨35114906120570512297168457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93639749654854699459115885 35114906120570512297168457)
  ·
    refine ⟨26336179590427884222876343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35114906120570512297168457 26336179590427884222876343)
    ·
      refine ⟨39504269385641826334314515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26336179590427884222876343 39504269385641826334314515)
      ·
        refine ⟨59256404078462739501471773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39504269385641826334314515 59256404078462739501471773)
        ·
          refine ⟨22221151529423527313051915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59256404078462739501471773 22221151529423527313051915)
          ·
            refine ⟨33331727294135290969577873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22221151529423527313051915 33331727294135290969577873)
            ·
              refine ⟨24998795470601468227183405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33331727294135290969577873 24998795470601468227183405)
              ·
                refine ⟨9374548301475550585193777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24998795470601468227183405 9374548301475550585193777)
                ·
                  refine ⟨7030911226106662938895333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9374548301475550585193777 7030911226106662938895333)
                  ·
                    refine ⟨1318295854894999301042875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7030911226106662938895333 1318295854894999301042875)
                    ·
                      rfl

theorem cell22_3851058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_3851058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3851058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3851058 prefixEnd_3851058 := by exact prefixLift 3851058
  have htrace : WordTrace (prefixWord ++ tailWord_3851058) baseStart_3851058 baseEnd_3851058 := by
    simpa [prefixWord, tailWord_3851058, baseEnd_3851058] using wordTrace_append hprefix tailTrace_3851058
  have hstable : (prefixWord ++ tailWord_3851058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851058).length < 2 ^ (prefixWord ++ tailWord_3851058).sum := by decide
  have hdescent : baseEnd_3851058 < baseStart_3851058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851148 : List Nat := [2, 2, 1, 2, 1, 2, 3, 2, 3, 4]
def baseStart_3851148 : Nat := 118140960795 + 3851148 * 2 ^ 59
def prefixEnd_3851148 : Nat := 4983230072969 + 3 ^ 40 * 3851148 * 2
def baseEnd_3851148 : Nat := 1318326663734269066292599

theorem tailTrace_3851148 : CollatzResearch.WordTrace tailWord_3851148 prefixEnd_3851148 1318326663734269066292599 := by
  unfold tailWord_3851148
  simp only [CollatzResearch.WordTrace]
  refine ⟨70231453525977997279725049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93641938034637329706300065 70231453525977997279725049)
  ·
    refine ⟨52673590144483497959793787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70231453525977997279725049 52673590144483497959793787)
    ·
      refine ⟨79010385216725246939690681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52673590144483497959793787 79010385216725246939690681)
      ·
        refine ⟨59257788912543935204768011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79010385216725246939690681 59257788912543935204768011)
        ·
          refine ⟨88886683368815902807152017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59257788912543935204768011 88886683368815902807152017)
          ·
            refine ⟨66665012526611927105364013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88886683368815902807152017 66665012526611927105364013)
            ·
              refine ⟨24999379697479472664511505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66665012526611927105364013 24999379697479472664511505)
              ·
                refine ⟨18749534773109604498383629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24999379697479472664511505 18749534773109604498383629)
                ·
                  refine ⟨7031075539916101686893861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18749534773109604498383629 7031075539916101686893861)
                  ·
                    refine ⟨1318326663734269066292599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7031075539916101686893861 1318326663734269066292599)
                    ·
                      rfl

theorem cell22_3851148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_3851148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3851148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3851148 prefixEnd_3851148 := by exact prefixLift 3851148
  have htrace : WordTrace (prefixWord ++ tailWord_3851148) baseStart_3851148 baseEnd_3851148 := by
    simpa [prefixWord, tailWord_3851148, baseEnd_3851148] using wordTrace_append hprefix tailTrace_3851148
  have hstable : (prefixWord ++ tailWord_3851148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851148).length < 2 ^ (prefixWord ++ tailWord_3851148).sum := by decide
  have hdescent : baseEnd_3851148 < baseStart_3851148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851165 : List Nat := [1, 4, 2, 1, 2, 1, 2, 4, 1, 4]
def baseStart_3851165 : Nat := 118140960795 + 3851165 * 2 ^ 59
def prefixEnd_3851165 : Nat := 4983230072969 + 3 ^ 40 * 3851165 * 2
def baseEnd_3851165 : Nat := 1318332483181686688617547

theorem tailTrace_3851165 : CollatzResearch.WordTrace tailWord_3851165 prefixEnd_3851165 1318332483181686688617547 := by
  unfold tailWord_3851165
  simp only [CollatzResearch.WordTrace]
  refine ⟨140463527092894406462818949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93642351395262937641879299 140463527092894406462818949)
  ·
    refine ⟨26336911329917701211778553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140463527092894406462818949 26336911329917701211778553)
    ·
      refine ⟨19752683497438275908833915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26336911329917701211778553 19752683497438275908833915)
      ·
        refine ⟨29629025246157413863250873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19752683497438275908833915 29629025246157413863250873)
        ·
          refine ⟨22221768934618060397438155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29629025246157413863250873 22221768934618060397438155)
          ·
            refine ⟨33332653401927090596157233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22221768934618060397438155 33332653401927090596157233)
            ·
              refine ⟨24999490051445317947117925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33332653401927090596157233 24999490051445317947117925)
              ·
                refine ⟨4687404384645997115084611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24999490051445317947117925 4687404384645997115084611)
                ·
                  refine ⟨7031106576968995672626917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4687404384645997115084611 7031106576968995672626917)
                  ·
                    refine ⟨1318332483181686688617547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7031106576968995672626917 1318332483181686688617547)
                    ·
                      rfl

theorem cell22_3851165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_3851165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3851165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3851165 prefixEnd_3851165 := by exact prefixLift 3851165
  have htrace : WordTrace (prefixWord ++ tailWord_3851165) baseStart_3851165 baseEnd_3851165 := by
    simpa [prefixWord, tailWord_3851165, baseEnd_3851165] using wordTrace_append hprefix tailTrace_3851165
  have hstable : (prefixWord ++ tailWord_3851165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851165).length < 2 ^ (prefixWord ++ tailWord_3851165).sum := by decide
  have hdescent : baseEnd_3851165 < baseStart_3851165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851225 : List Nat := [1, 2, 1, 2, 5, 1, 4, 6]
def baseStart_3851225 : Nat := 118140960795 + 3851225 * 2 ^ 59
def prefixEnd_3851225 : Nat := 4983230072969 + 3 ^ 40 * 3851225 * 2
def baseEnd_3851225 : Nat := 146483669156429614679707

theorem tailTrace_3851225 : CollatzResearch.WordTrace tailWord_3851225 prefixEnd_3851225 146483669156429614679707 := by
  unfold tailWord_3851225
  simp only [CollatzResearch.WordTrace]
  refine ⟨140465715472677036710003129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93643810315118024473335419 140465715472677036710003129)
  ·
    refine ⟨105349286604507777532502347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140465715472677036710003129 105349286604507777532502347)
    ·
      refine ⟨158023929906761666298753521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105349286604507777532502347 158023929906761666298753521)
      ·
        refine ⟨118517947430071249724065141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158023929906761666298753521 118517947430071249724065141)
        ·
          refine ⟨11111057571569179661631107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118517947430071249724065141 11111057571569179661631107)
          ·
            refine ⟨16666586357353769492446661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11111057571569179661631107 16666586357353769492446661)
            ·
              refine ⟨3124984942003831779833749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16666586357353769492446661 3124984942003831779833749)
              ·
                refine ⟨146483669156429614679707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3124984942003831779833749 146483669156429614679707)
                ·
                  rfl

theorem cell22_3851225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 6].length) (baseStart_3851225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3851225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3851225 prefixEnd_3851225 := by exact prefixLift 3851225
  have htrace : WordTrace (prefixWord ++ tailWord_3851225) baseStart_3851225 baseEnd_3851225 := by
    simpa [prefixWord, tailWord_3851225, baseEnd_3851225] using wordTrace_append hprefix tailTrace_3851225
  have hstable : (prefixWord ++ tailWord_3851225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851225).length < 2 ^ (prefixWord ++ tailWord_3851225).sum := by decide
  have hdescent : baseEnd_3851225 < baseStart_3851225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851240 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 5, 3]
def baseStart_3851240 : Nat := 118140960795 + 3851240 * 2 ^ 59
def prefixEnd_3851240 : Nat := 4983230072969 + 3 ^ 40 * 3851240 * 2
def baseEnd_3851240 : Nat := 1318358157214411492992317

theorem tailTrace_3851240 : CollatzResearch.WordTrace tailWord_3851240 prefixEnd_3851240 1318358157214411492992317 := by
  unfold tailWord_3851240
  simp only [CollatzResearch.WordTrace]
  refine ⟨70233131283811347135899587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93644175045081796181199449 70233131283811347135899587)
  ·
    refine ⟨105349696925717020703849381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70233131283811347135899587 105349696925717020703849381)
    ·
      refine ⟨19753068173571941381971759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105349696925717020703849381 19753068173571941381971759)
      ·
        refine ⟨29629602260357912072957639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19753068173571941381971759 29629602260357912072957639)
        ·
          refine ⟨44444403390536868109436459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29629602260357912072957639 44444403390536868109436459)
          ·
            refine ⟨66666605085805302164154689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44444403390536868109436459 66666605085805302164154689)
            ·
              refine ⟨49999953814353976623116017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66666605085805302164154689 49999953814353976623116017)
              ·
                refine ⟨37499965360765482467337013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49999953814353976623116017 37499965360765482467337013)
                ·
                  refine ⟨3515621752571763981312845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37499965360765482467337013 3515621752571763981312845)
                  ·
                    refine ⟨1318358157214411492992317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3515621752571763981312845 1318358157214411492992317)
                    ·
                      rfl

theorem cell22_3851240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_3851240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3851240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3851240 prefixEnd_3851240 := by exact prefixLift 3851240
  have htrace : WordTrace (prefixWord ++ tailWord_3851240) baseStart_3851240 baseEnd_3851240 := by
    simpa [prefixWord, tailWord_3851240, baseEnd_3851240] using wordTrace_append hprefix tailTrace_3851240
  have hstable : (prefixWord ++ tailWord_3851240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851240).length < 2 ^ (prefixWord ++ tailWord_3851240).sum := by decide
  have hdescent : baseEnd_3851240 < baseStart_3851240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3851334 : List Nat := [6, 1, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_3851334 : Nat := 118140960795 + 3851334 * 2 ^ 59
def prefixEnd_3851334 : Nat := 4983230072969 + 3 ^ 40 * 3851334 * 2
def baseEnd_3851334 : Nat := 1318390335335426581142029

theorem tailTrace_3851334 : CollatzResearch.WordTrace tailWord_3851334 prefixEnd_3851334 1318390335335426581142029 := by
  unfold tailWord_3851334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4389677844665067135178783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 93646460686188098883814037 4389677844665067135178783)
  ·
    refine ⟨6584516766997600702768175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4389677844665067135178783 6584516766997600702768175)
    ·
      refine ⟨9876775150496401054152263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6584516766997600702768175 9876775150496401054152263)
      ·
        refine ⟨14815162725744601581228395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9876775150496401054152263 14815162725744601581228395)
        ·
          refine ⟨22222744088616902371842593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14815162725744601581228395 22222744088616902371842593)
          ·
            refine ⟨16667058066462676778881945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22222744088616902371842593 16667058066462676778881945)
            ·
              refine ⟨12500293549847007584161459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16667058066462676778881945 12500293549847007584161459)
              ·
                refine ⟨18750440324770511376242189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12500293549847007584161459 18750440324770511376242189)
                ·
                  refine ⟨7031415121788941766090821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18750440324770511376242189 7031415121788941766090821)
                  ·
                    refine ⟨1318390335335426581142029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7031415121788941766090821 1318390335335426581142029)
                    ·
                      rfl

theorem cell22_3851334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_3851334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3851334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3851334 prefixEnd_3851334 := by exact prefixLift 3851334
  have htrace : WordTrace (prefixWord ++ tailWord_3851334) baseStart_3851334 baseEnd_3851334 := by
    simpa [prefixWord, tailWord_3851334, baseEnd_3851334] using wordTrace_append hprefix tailTrace_3851334
  have hstable : (prefixWord ++ tailWord_3851334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3851334).length < 2 ^ (prefixWord ++ tailWord_3851334).sum := by decide
  have hdescent : baseEnd_3851334 < baseStart_3851334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3851334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
