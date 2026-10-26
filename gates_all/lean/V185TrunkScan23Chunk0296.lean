import V185TrunkScan23Chunk0295

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1749969 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 3, 4, 2]
def baseStart_1749969 : Nat := 118140960795 + 1749969 * 2 ^ 59
def prefixEnd_1749969 : Nat := 4983230072969 + 3 ^ 40 * 1749969 * 2
def baseEnd_1749969 : Nat := 898575227467968971939545

theorem tailTrace_1749969 : CollatzResearch.WordTrace tailWord_1749969 prefixEnd_1749969 898575227467968971939545 := by
  unfold tailWord_1749969
  simp only [CollatzResearch.WordTrace]
  refine ⟨63826612997168658755980961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42551075331445772503987307 63826612997168658755980961)
  ·
    refine ⟨47869959747876494066985721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63826612997168658755980961 47869959747876494066985721)
    ·
      refine ⟨35902469810907370550239291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47869959747876494066985721 35902469810907370550239291)
      ·
        refine ⟨53853704716361055825358937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35902469810907370550239291 53853704716361055825358937)
        ·
          refine ⟨40390278537270791869019203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53853704716361055825358937 40390278537270791869019203)
          ·
            refine ⟨60585417805906187803528805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40390278537270791869019203 60585417805906187803528805)
            ·
              refine ⟨11359765838607410213161651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60585417805906187803528805 11359765838607410213161651)
              ·
                refine ⟨17039648757911115319742477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11359765838607410213161651 17039648757911115319742477)
                ·
                  refine ⟨6389868284216668244903429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17039648757911115319742477 6389868284216668244903429)
                  ·
                    refine ⟨1198100303290625295919393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6389868284216668244903429 1198100303290625295919393)
                    ·
                      refine ⟨898575227467968971939545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1198100303290625295919393 898575227467968971939545)
                      ·
                        rfl

theorem cell23_1749969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 4, 2].length) (baseStart_1749969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1749969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1749969 prefixEnd_1749969 := by exact prefixLift 1749969
  have htrace : WordTrace (prefixWord ++ tailWord_1749969) baseStart_1749969 baseEnd_1749969 := by
    simpa [prefixWord, tailWord_1749969, baseEnd_1749969] using wordTrace_append hprefix tailTrace_1749969
  have hstable : (prefixWord ++ tailWord_1749969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749969).length < 2 ^ (prefixWord ++ tailWord_1749969).sum := by decide
  have hdescent : baseEnd_1749969 < baseStart_1749969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750049 : List Nat := [1, 2, 3, 2, 3, 1, 2, 1, 1, 2, 5]
def baseStart_1750049 : Nat := 118140960795 + 1750049 * 2 ^ 59
def prefixEnd_1750049 : Nat := 4983230072969 + 3 ^ 40 * 1750049 * 2
def baseEnd_1750049 : Nat := 898616305920328658939177

theorem tailTrace_1750049 : CollatzResearch.WordTrace tailWord_1750049 prefixEnd_1750049 898616305920328658939177 := by
  unfold tailWord_1750049
  simp only [CollatzResearch.WordTrace]
  refine ⟨63829530836878832418893201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42553020557919221612595467 63829530836878832418893201)
  ·
    refine ⟨47872148127659124314169901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63829530836878832418893201 47872148127659124314169901)
    ·
      refine ⟨17952055547872171617813713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47872148127659124314169901 17952055547872171617813713)
      ·
        refine ⟨13464041660904128713360285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17952055547872171617813713 13464041660904128713360285)
        ·
          refine ⟨5049015622839048267510107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13464041660904128713360285 5049015622839048267510107)
          ·
            refine ⟨7573523434258572401265161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5049015622839048267510107 7573523434258572401265161)
            ·
              refine ⟨5680142575693929300948871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7573523434258572401265161 5680142575693929300948871)
              ·
                refine ⟨8520213863540893951423307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5680142575693929300948871 8520213863540893951423307)
                ·
                  refine ⟨12780320795311340927134961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8520213863540893951423307 12780320795311340927134961)
                  ·
                    refine ⟨9585240596483505695351221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12780320795311340927134961 9585240596483505695351221)
                    ·
                      refine ⟨898616305920328658939177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9585240596483505695351221 898616305920328658939177)
                      ·
                        rfl

theorem cell23_1750049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_1750049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750049 prefixEnd_1750049 := by exact prefixLift 1750049
  have htrace : WordTrace (prefixWord ++ tailWord_1750049) baseStart_1750049 baseEnd_1750049 := by
    simpa [prefixWord, tailWord_1750049, baseEnd_1750049] using wordTrace_append hprefix tailTrace_1750049
  have hstable : (prefixWord ++ tailWord_1750049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750049).length < 2 ^ (prefixWord ++ tailWord_1750049).sum := by decide
  have hdescent : baseEnd_1750049 < baseStart_1750049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750076 : List Nat := [2, 2, 2, 2, 2, 2, 3, 1, 2, 1, 4]
def baseStart_1750076 : Nat := 118140960795 + 1750076 * 2 ^ 59
def prefixEnd_1750076 : Nat := 4983230072969 + 3 ^ 40 * 1750076 * 2
def baseEnd_1750076 : Nat := 898630169898000053301553

theorem tailTrace_1750076 : CollatzResearch.WordTrace tailWord_1750076 prefixEnd_1750076 898630169898000053301553 := by
  unfold tailWord_1750076
  simp only [CollatzResearch.WordTrace]
  refine ⟨31915257803890508015063041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42553677071854010686750721 31915257803890508015063041)
  ·
    refine ⟨23936443352917881011297281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31915257803890508015063041 23936443352917881011297281)
    ·
      refine ⟨17952332514688410758472961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23936443352917881011297281 17952332514688410758472961)
      ·
        refine ⟨13464249386016308068854721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17952332514688410758472961 13464249386016308068854721)
        ·
          refine ⟨10098187039512231051641041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13464249386016308068854721 10098187039512231051641041)
          ·
            refine ⟨7573640279634173288730781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10098187039512231051641041 7573640279634173288730781)
            ·
              refine ⟨2840115104862814983274043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7573640279634173288730781 2840115104862814983274043)
              ·
                refine ⟨4260172657294222474911065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2840115104862814983274043 4260172657294222474911065)
                ·
                  refine ⟨3195129492970666856183299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4260172657294222474911065 3195129492970666856183299)
                  ·
                    refine ⟨4792694239456000284274949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3195129492970666856183299 4792694239456000284274949)
                    ·
                      refine ⟨898630169898000053301553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4792694239456000284274949 898630169898000053301553)
                      ·
                        rfl

theorem cell23_1750076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_1750076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750076 prefixEnd_1750076 := by exact prefixLift 1750076
  have htrace : WordTrace (prefixWord ++ tailWord_1750076) baseStart_1750076 baseEnd_1750076 := by
    simpa [prefixWord, tailWord_1750076, baseEnd_1750076] using wordTrace_append hprefix tailTrace_1750076
  have hstable : (prefixWord ++ tailWord_1750076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750076).length < 2 ^ (prefixWord ++ tailWord_1750076).sum := by decide
  have hdescent : baseEnd_1750076 < baseStart_1750076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750093 : List Nat := [1, 6, 1, 1, 1, 2, 1, 2, 2, 4, 2]
def baseStart_1750093 : Nat := 118140960795 + 1750093 * 2 ^ 59
def prefixEnd_1750093 : Nat := 4983230072969 + 3 ^ 40 * 1750093 * 2
def baseEnd_1750093 : Nat := 898638899069126486788975

theorem tailTrace_1750093 : CollatzResearch.WordTrace tailWord_1750093 prefixEnd_1750093 898638899069126486788975 := by
  unfold tailWord_1750093
  simp only [CollatzResearch.WordTrace]
  refine ⟨63831135648719427933494933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42554090432479618622329955 63831135648719427933494933)
  ·
    refine ⟨2992084483533723184382575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63831135648719427933494933 2992084483533723184382575)
    ·
      refine ⟨4488126725300584776573863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2992084483533723184382575 4488126725300584776573863)
      ·
        refine ⟨6732190087950877164860795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4488126725300584776573863 6732190087950877164860795)
        ·
          refine ⟨10098285131926315747291193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6732190087950877164860795 10098285131926315747291193)
          ·
            refine ⟨7573713848944736810468395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10098285131926315747291193 7573713848944736810468395)
            ·
              refine ⟨11360570773417105215702593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7573713848944736810468395 11360570773417105215702593)
              ·
                refine ⟨8520428080062828911776945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11360570773417105215702593 8520428080062828911776945)
                ·
                  refine ⟨6390321060047121683832709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8520428080062828911776945 6390321060047121683832709)
                  ·
                    refine ⟨1198185198758835315718633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6390321060047121683832709 1198185198758835315718633)
                    ·
                      refine ⟨898638899069126486788975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1198185198758835315718633 898638899069126486788975)
                      ·
                        rfl

theorem cell23_1750093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_1750093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750093 prefixEnd_1750093 := by exact prefixLift 1750093
  have htrace : WordTrace (prefixWord ++ tailWord_1750093) baseStart_1750093 baseEnd_1750093 := by
    simpa [prefixWord, tailWord_1750093, baseEnd_1750093] using wordTrace_append hprefix tailTrace_1750093
  have hstable : (prefixWord ++ tailWord_1750093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750093).length < 2 ^ (prefixWord ++ tailWord_1750093).sum := by decide
  have hdescent : baseEnd_1750093 < baseStart_1750093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750136 : List Nat := [2, 1, 2, 1, 1, 1, 6, 1, 1, 5, 2]
def baseStart_1750136 : Nat := 118140960795 + 1750136 * 2 ^ 59
def prefixEnd_1750136 : Nat := 4983230072969 + 3 ^ 40 * 1750136 * 2
def baseEnd_1750136 : Nat := 898660978737269818551277

theorem tailTrace_1750136 : CollatzResearch.WordTrace tailWord_1750136 prefixEnd_1750136 898660978737269818551277 := by
  unfold tailWord_1750136
  simp only [CollatzResearch.WordTrace]
  refine ⟨31916351993781823138655131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42555135991709097518206841 31916351993781823138655131)
  ·
    refine ⟨47874527990672734707982697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31916351993781823138655131 47874527990672734707982697)
    ·
      refine ⟨35905895993004551030987023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47874527990672734707982697 35905895993004551030987023)
      ·
        refine ⟨53858843989506826546480535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35905895993004551030987023 53858843989506826546480535)
        ·
          refine ⟨80788265984260239819720803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53858843989506826546480535 80788265984260239819720803)
          ·
            refine ⟨121182398976390359729581205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80788265984260239819720803 121182398976390359729581205)
            ·
              refine ⟨5680424952018298112324119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121182398976390359729581205 5680424952018298112324119)
              ·
                refine ⟨8520637428027447168486179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5680424952018298112324119 8520637428027447168486179)
                ·
                  refine ⟨12780956142041170752729269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8520637428027447168486179 12780956142041170752729269)
                  ·
                    refine ⟨1198214638316359758068369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12780956142041170752729269 1198214638316359758068369)
                    ·
                      refine ⟨898660978737269818551277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1198214638316359758068369 898660978737269818551277)
                      ·
                        rfl

theorem cell23_1750136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 1, 5, 2].length) (baseStart_1750136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750136 prefixEnd_1750136 := by exact prefixLift 1750136
  have htrace : WordTrace (prefixWord ++ tailWord_1750136) baseStart_1750136 baseEnd_1750136 := by
    simpa [prefixWord, tailWord_1750136, baseEnd_1750136] using wordTrace_append hprefix tailTrace_1750136
  have hstable : (prefixWord ++ tailWord_1750136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750136).length < 2 ^ (prefixWord ++ tailWord_1750136).sum := by decide
  have hdescent : baseEnd_1750136 < baseStart_1750136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750137 : List Nat := [1, 2, 1, 3, 6, 1, 1, 3, 1, 4]
def baseStart_1750137 : Nat := 118140960795 + 1750137 * 2 ^ 59
def prefixEnd_1750137 : Nat := 4983230072969 + 3 ^ 40 * 1750137 * 2
def baseEnd_1750137 : Nat := 299553830739308104879591

theorem tailTrace_1750137 : CollatzResearch.WordTrace tailWord_1750137 prefixEnd_1750137 299553830739308104879591 := by
  unfold tailWord_1750137
  simp only [CollatzResearch.WordTrace]
  refine ⟨63832740460560023448096665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42555160307040015632064443 63832740460560023448096665)
  ·
    refine ⟨47874555345420017586072499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63832740460560023448096665 47874555345420017586072499)
    ·
      refine ⟨71811833018130026379108749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47874555345420017586072499 71811833018130026379108749)
      ·
        refine ⟨26929437381798759892165781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71811833018130026379108749 26929437381798759892165781)
        ·
          refine ⟨1262317377271816869945271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 26929437381798759892165781 1262317377271816869945271)
          ·
            refine ⟨1893476065907725304917907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1262317377271816869945271 1893476065907725304917907)
            ·
              refine ⟨2840214098861587957376861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1893476065907725304917907 2840214098861587957376861)
              ·
                refine ⟨1065080287073095484016323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2840214098861587957376861 1065080287073095484016323)
                ·
                  refine ⟨1597620430609643226024485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1065080287073095484016323 1597620430609643226024485)
                  ·
                    refine ⟨299553830739308104879591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1597620430609643226024485 299553830739308104879591)
                    ·
                      rfl

theorem cell23_1750137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 3, 1, 4].length) (baseStart_1750137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750137 prefixEnd_1750137 := by exact prefixLift 1750137
  have htrace : WordTrace (prefixWord ++ tailWord_1750137) baseStart_1750137 baseEnd_1750137 := by
    simpa [prefixWord, tailWord_1750137, baseEnd_1750137] using wordTrace_append hprefix tailTrace_1750137
  have hstable : (prefixWord ++ tailWord_1750137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750137).length < 2 ^ (prefixWord ++ tailWord_1750137).sum := by decide
  have hdescent : baseEnd_1750137 < baseStart_1750137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750153 : List Nat := [1, 2, 1, 1, 4, 4, 1, 2, 2, 3, 2]
def baseStart_1750153 : Nat := 118140960795 + 1750153 * 2 ^ 59
def prefixEnd_1750153 : Nat := 4983230072969 + 3 ^ 40 * 1750153 * 2
def baseEnd_1750153 : Nat := 898669707908396252038699

theorem tailTrace_1750153 : CollatzResearch.WordTrace tailWord_1750153 prefixEnd_1750153 898669707908396252038699 := by
  unfold tailWord_1750153
  simp only [CollatzResearch.WordTrace]
  refine ⟨63833324028502058180679113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42555549352334705453786075 63833324028502058180679113)
  ·
    refine ⟨47874993021376543635509335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63833324028502058180679113 47874993021376543635509335)
    ·
      refine ⟨71812489532064815453264003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47874993021376543635509335 71812489532064815453264003)
      ·
        refine ⟨107718734298097223179896005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71812489532064815453264003 107718734298097223179896005)
        ·
          refine ⟨20197262680893229346230501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107718734298097223179896005 20197262680893229346230501)
          ·
            refine ⟨3786986752667480502418219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20197262680893229346230501 3786986752667480502418219)
            ·
              refine ⟨5680480129001220753627329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3786986752667480502418219 5680480129001220753627329)
              ·
                refine ⟨4260360096750915565220497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5680480129001220753627329 4260360096750915565220497)
                ·
                  refine ⟨3195270072563186673915373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4260360096750915565220497 3195270072563186673915373)
                  ·
                    refine ⟨1198226277211195002718265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3195270072563186673915373 1198226277211195002718265)
                    ·
                      refine ⟨898669707908396252038699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1198226277211195002718265 898669707908396252038699)
                      ·
                        rfl

theorem cell23_1750153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 3, 2].length) (baseStart_1750153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750153 prefixEnd_1750153 := by exact prefixLift 1750153
  have htrace : WordTrace (prefixWord ++ tailWord_1750153) baseStart_1750153 baseEnd_1750153 := by
    simpa [prefixWord, tailWord_1750153, baseEnd_1750153] using wordTrace_append hprefix tailTrace_1750153
  have hstable : (prefixWord ++ tailWord_1750153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750153).length < 2 ^ (prefixWord ++ tailWord_1750153).sum := by decide
  have hdescent : baseEnd_1750153 < baseStart_1750153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750169 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 1, 8, 3]
def baseStart_1750169 : Nat := 118140960795 + 1750169 * 2 ^ 59
def prefixEnd_1750169 : Nat := 4983230072969 + 3 ^ 40 * 1750169 * 2
def baseEnd_1750169 : Nat := 898677923598868189438625

theorem tailTrace_1750169 : CollatzResearch.WordTrace tailWord_1750169 prefixEnd_1750169 898677923598868189438625 := by
  unfold tailWord_1750169
  simp only [CollatzResearch.WordTrace]
  refine ⟨63833907596444092913261561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42555938397629395275507707 63833907596444092913261561)
  ·
    refine ⟨47875430697333069684946171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63833907596444092913261561 47875430697333069684946171)
    ·
      refine ⟨71813146045999604527419257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47875430697333069684946171 71813146045999604527419257)
      ·
        refine ⟨53859859534499703395564443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71813146045999604527419257 53859859534499703395564443)
        ·
          refine ⟨80789789301749555093346665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53859859534499703395564443 80789789301749555093346665)
          ·
            refine ⟨60592341976312166320009999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80789789301749555093346665 60592341976312166320009999)
            ·
              refine ⟨90888512964468249480014999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60592341976312166320009999 90888512964468249480014999)
              ·
                refine ⟨136332769446702374220022499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90888512964468249480014999 136332769446702374220022499)
                ·
                  refine ⟨204499154170053561330033749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136332769446702374220022499 204499154170053561330033749)
                  ·
                    refine ⟨2396474462930315171836333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 204499154170053561330033749 2396474462930315171836333)
                    ·
                      refine ⟨898677923598868189438625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2396474462930315171836333 898677923598868189438625)
                      ·
                        rfl

theorem cell23_1750169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 8, 3].length) (baseStart_1750169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750169 prefixEnd_1750169 := by exact prefixLift 1750169
  have htrace : WordTrace (prefixWord ++ tailWord_1750169) baseStart_1750169 baseEnd_1750169 := by
    simpa [prefixWord, tailWord_1750169, baseEnd_1750169] using wordTrace_append hprefix tailTrace_1750169
  have hstable : (prefixWord ++ tailWord_1750169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750169).length < 2 ^ (prefixWord ++ tailWord_1750169).sum := by decide
  have hdescent : baseEnd_1750169 < baseStart_1750169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750179 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 4]
def baseStart_1750179 : Nat := 118140960795 + 1750179 * 2 ^ 59
def prefixEnd_1750179 : Nat := 4983230072969 + 3 ^ 40 * 1750179 * 2
def baseEnd_1750179 : Nat := 898683058405413150313579

theorem tailTrace_1750179 : CollatzResearch.WordTrace tailWord_1750179 prefixEnd_1750179 898683058405413150313579 := by
  unfold tailWord_1750179
  simp only [CollatzResearch.WordTrace]
  refine ⟨63834272326407864621125591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42556181550938576414083727 63834272326407864621125591)
  ·
    refine ⟨95751408489611796931688387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63834272326407864621125591 95751408489611796931688387)
    ·
      refine ⟨143627112734417695397532581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95751408489611796931688387 143627112734417695397532581)
      ·
        refine ⟨26930083637703317887037359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143627112734417695397532581 26930083637703317887037359)
        ·
          refine ⟨40395125456554976830556039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26930083637703317887037359 40395125456554976830556039)
          ·
            refine ⟨60592688184832465245834059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40395125456554976830556039 60592688184832465245834059)
            ·
              refine ⟨90889032277248697868751089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60592688184832465245834059 90889032277248697868751089)
              ·
                refine ⟨68166774207936523401563317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90889032277248697868751089 68166774207936523401563317)
                ·
                  refine ⟨6390635081994049068896561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68166774207936523401563317 6390635081994049068896561)
                  ·
                    refine ⟨4792976311495536801672421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6390635081994049068896561 4792976311495536801672421)
                    ·
                      refine ⟨898683058405413150313579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4792976311495536801672421 898683058405413150313579)
                      ·
                        rfl

theorem cell23_1750179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_1750179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750179 prefixEnd_1750179 := by exact prefixLift 1750179
  have htrace : WordTrace (prefixWord ++ tailWord_1750179) baseStart_1750179 baseEnd_1750179 := by
    simpa [prefixWord, tailWord_1750179, baseEnd_1750179] using wordTrace_append hprefix tailTrace_1750179
  have hstable : (prefixWord ++ tailWord_1750179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750179).length < 2 ^ (prefixWord ++ tailWord_1750179).sum := by decide
  have hdescent : baseEnd_1750179 < baseStart_1750179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750183 : List Nat := [1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_1750183 : Nat := 118140960795 + 1750183 * 2 ^ 59
def prefixEnd_1750183 : Nat := 4983230072969 + 3 ^ 40 * 1750183 * 2
def baseEnd_1750183 : Nat := 898685112328031134663561

theorem tailTrace_1750183 : CollatzResearch.WordTrace tailWord_1750183 prefixEnd_1750183 898685112328031134663561 := by
  unfold tailWord_1750183
  simp only [CollatzResearch.WordTrace]
  refine ⟨63834418218393373304271203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42556278812262248869514135 63834418218393373304271203)
  ·
    refine ⟨95751627327590059956406805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63834418218393373304271203 95751627327590059956406805)
    ·
      refine ⟨4488357530980784060456569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 95751627327590059956406805 4488357530980784060456569)
      ·
        refine ⟨3366268148235588045342427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4488357530980784060456569 3366268148235588045342427)
        ·
          refine ⟨5049402222353382068013641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3366268148235588045342427 5049402222353382068013641)
          ·
            refine ⟨3787051666765036551010231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5049402222353382068013641 3787051666765036551010231)
            ·
              refine ⟨5680577500147554826515347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3787051666765036551010231 5680577500147554826515347)
              ·
                refine ⟨8520866250221332239773021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5680577500147554826515347 8520866250221332239773021)
                ·
                  refine ⟨3195324843832999589914883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8520866250221332239773021 3195324843832999589914883)
                  ·
                    refine ⟨4792987265749499384872325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3195324843832999589914883 4792987265749499384872325)
                    ·
                      refine ⟨898685112328031134663561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4792987265749499384872325 898685112328031134663561)
                      ·
                        rfl

theorem cell23_1750183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_1750183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750183 prefixEnd_1750183 := by exact prefixLift 1750183
  have htrace : WordTrace (prefixWord ++ tailWord_1750183) baseStart_1750183 baseEnd_1750183 := by
    simpa [prefixWord, tailWord_1750183, baseEnd_1750183] using wordTrace_append hprefix tailTrace_1750183
  have hstable : (prefixWord ++ tailWord_1750183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750183).length < 2 ^ (prefixWord ++ tailWord_1750183).sum := by decide
  have hdescent : baseEnd_1750183 < baseStart_1750183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750249 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 6, 6]
def baseStart_1750249 : Nat := 118140960795 + 1750249 * 2 ^ 59
def prefixEnd_1750249 : Nat := 4983230072969 + 3 ^ 40 * 1750249 * 2
def baseEnd_1750249 : Nat := 299573000683742625479419

theorem tailTrace_1750249 : CollatzResearch.WordTrace tailWord_1750249 prefixEnd_1750249 299573000683742625479419 := by
  unfold tailWord_1750249
  simp only [CollatzResearch.WordTrace]
  refine ⟨63836825436154266576173801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42557883624102844384115867 63836825436154266576173801)
  ·
    refine ⟨47877619077115699932130351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63836825436154266576173801 47877619077115699932130351)
    ·
      refine ⟨71816428615673549898195527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47877619077115699932130351 71816428615673549898195527)
      ·
        refine ⟨107724642923510324847293291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71816428615673549898195527 107724642923510324847293291)
        ·
          refine ⟨161586964385265487270939937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107724642923510324847293291 161586964385265487270939937)
          ·
            refine ⟨121190223288949115453204953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161586964385265487270939937 121190223288949115453204953)
            ·
              refine ⟨90892667466711836589903715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121190223288949115453204953 90892667466711836589903715)
              ·
                refine ⟨136339001200067754884855573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90892667466711836589903715 136339001200067754884855573)
                ·
                  refine ⟨6390890681253176010227605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 136339001200067754884855573 6390890681253176010227605)
                  ·
                    refine ⟨299573000683742625479419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6390890681253176010227605 299573000683742625479419)
                    ·
                      rfl

theorem cell23_1750249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 6].length) (baseStart_1750249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750249 prefixEnd_1750249 := by exact prefixLift 1750249
  have htrace : WordTrace (prefixWord ++ tailWord_1750249) baseStart_1750249 baseEnd_1750249 := by
    simpa [prefixWord, tailWord_1750249, baseEnd_1750249] using wordTrace_append hprefix tailTrace_1750249
  have hstable : (prefixWord ++ tailWord_1750249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750249).length < 2 ^ (prefixWord ++ tailWord_1750249).sum := by decide
  have hdescent : baseEnd_1750249 < baseStart_1750249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750296 : List Nat := [2, 1, 2, 3, 1, 3, 2, 2, 7]
def baseStart_1750296 : Nat := 118140960795 + 1750296 * 2 ^ 59
def prefixEnd_1750296 : Nat := 4983230072969 + 3 ^ 40 * 1750296 * 2
def baseEnd_1750296 : Nat := 99860348404665465838949

theorem tailTrace_1750296 : CollatzResearch.WordTrace tailWord_1750296 prefixEnd_1750296 99860348404665465838949 := by
  unfold tailWord_1750296
  simp only [CollatzResearch.WordTrace]
  refine ⟨31919269833491996801567371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42559026444655995735423161 31919269833491996801567371)
  ·
    refine ⟨47878904750237995202351057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31919269833491996801567371 47878904750237995202351057)
    ·
      refine ⟨35909178562678496401763293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47878904750237995202351057 35909178562678496401763293)
      ·
        refine ⟨13465941961004436150661235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35909178562678496401763293 13465941961004436150661235)
        ·
          refine ⟨20198912941506654225991853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13465941961004436150661235 20198912941506654225991853)
          ·
            refine ⟨7574592353064995334746945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20198912941506654225991853 7574592353064995334746945)
            ·
              refine ⟨5680944264798746501060209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7574592353064995334746945 5680944264798746501060209)
              ·
                refine ⟨4260708198599059875795157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5680944264798746501060209 4260708198599059875795157)
                ·
                  refine ⟨99860348404665465838949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4260708198599059875795157 99860348404665465838949)
                  ·
                    rfl

theorem cell23_1750296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 7].length) (baseStart_1750296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750296 prefixEnd_1750296 := by exact prefixLift 1750296
  have htrace : WordTrace (prefixWord ++ tailWord_1750296) baseStart_1750296 baseEnd_1750296 := by
    simpa [prefixWord, tailWord_1750296, baseEnd_1750296] using wordTrace_append hprefix tailTrace_1750296
  have hstable : (prefixWord ++ tailWord_1750296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750296).length < 2 ^ (prefixWord ++ tailWord_1750296).sum := by decide
  have hdescent : baseEnd_1750296 < baseStart_1750296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750330 : List Nat := [3, 1, 1, 1, 4, 1, 5, 2, 5]
def baseStart_1750330 : Nat := 118140960795 + 1750330 * 2 ^ 59
def prefixEnd_1750330 : Nat := 4983230072969 + 3 ^ 40 * 1750330 * 2
def baseEnd_1750330 : Nat := 99862288220471339947265

theorem tailTrace_1750330 : CollatzResearch.WordTrace tailWord_1750330 prefixEnd_1750330 99862288220471339947265 := by
  unfold tailWord_1750330
  simp only [CollatzResearch.WordTrace]
  refine ⟨15959944937215204352468111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42559853165907211606581629 15959944937215204352468111)
  ·
    refine ⟨23939917405822806528702167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15959944937215204352468111 23939917405822806528702167)
    ·
      refine ⟨35909876108734209793053251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23939917405822806528702167 35909876108734209793053251)
      ·
        refine ⟨53864814163101314689579877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35909876108734209793053251 53864814163101314689579877)
        ·
          refine ⟨10099652655581496504296227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53864814163101314689579877 10099652655581496504296227)
          ·
            refine ⟨15149478983372244756444341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10099652655581496504296227 15149478983372244756444341)
            ·
              refine ⟨1420263654691147945916657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15149478983372244756444341 1420263654691147945916657)
              ·
                refine ⟨1065197741018360959437493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1420263654691147945916657 1065197741018360959437493)
                ·
                  refine ⟨99862288220471339947265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1065197741018360959437493 99862288220471339947265)
                  ·
                    rfl

theorem cell23_1750330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 2, 5].length) (baseStart_1750330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750330 prefixEnd_1750330 := by exact prefixLift 1750330
  have htrace : WordTrace (prefixWord ++ tailWord_1750330) baseStart_1750330 baseEnd_1750330 := by
    simpa [prefixWord, tailWord_1750330, baseEnd_1750330] using wordTrace_append hprefix tailTrace_1750330
  have hstable : (prefixWord ++ tailWord_1750330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750330).length < 2 ^ (prefixWord ++ tailWord_1750330).sum := by decide
  have hdescent : baseEnd_1750330 < baseStart_1750330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750336 : List Nat := [2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 5]
def baseStart_1750336 : Nat := 118140960795 + 1750336 * 2 ^ 59
def prefixEnd_1750336 : Nat := 4983230072969 + 3 ^ 40 * 1750336 * 2
def baseEnd_1750336 : Nat := 898763674868169036050357

theorem tailTrace_1750336 : CollatzResearch.WordTrace tailWord_1750336 prefixEnd_1750336 898763674868169036050357 := by
  unfold tailWord_1750336
  simp only [CollatzResearch.WordTrace]
  refine ⟨31919999293419540217295431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42559999057892720289727241 31919999293419540217295431)
  ·
    refine ⟨47879998940129310325943147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31919999293419540217295431 47879998940129310325943147)
    ·
      refine ⟨71819998410193965488914721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47879998940129310325943147 71819998410193965488914721)
      ·
        refine ⟨53864998807645474116686041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71819998410193965488914721 53864998807645474116686041)
        ·
          refine ⟨40398749105734105587514531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53864998807645474116686041 40398749105734105587514531)
          ·
            refine ⟨60598123658601158381271797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40398749105734105587514531 60598123658601158381271797)
            ·
              refine ⟨5681074092993858598244231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60598123658601158381271797 5681074092993858598244231)
              ·
                refine ⟨8521611139490787897366347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5681074092993858598244231 8521611139490787897366347)
                ·
                  refine ⟨12782416709236181846049521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8521611139490787897366347 12782416709236181846049521)
                  ·
                    refine ⟨9586812531927136384537141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12782416709236181846049521 9586812531927136384537141)
                    ·
                      refine ⟨898763674868169036050357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9586812531927136384537141 898763674868169036050357)
                      ·
                        rfl

theorem cell23_1750336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_1750336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750336 prefixEnd_1750336 := by exact prefixLift 1750336
  have htrace : WordTrace (prefixWord ++ tailWord_1750336) baseStart_1750336 baseEnd_1750336 := by
    simpa [prefixWord, tailWord_1750336, baseEnd_1750336] using wordTrace_append hprefix tailTrace_1750336
  have hstable : (prefixWord ++ tailWord_1750336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750336).length < 2 ^ (prefixWord ++ tailWord_1750336).sum := by decide
  have hdescent : baseEnd_1750336 < baseStart_1750336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750346 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 3, 3, 4]
def baseStart_1750346 : Nat := 118140960795 + 1750346 * 2 ^ 59
def prefixEnd_1750346 : Nat := 4983230072969 + 3 ^ 40 * 1750346 * 2
def baseEnd_1750346 : Nat := 898768809674713996925311

theorem tailTrace_1750346 : CollatzResearch.WordTrace tailWord_1750346 prefixEnd_1750346 898768809674713996925311 := by
  unfold tailWord_1750346
  simp only [CollatzResearch.WordTrace]
  refine ⟨15960090829200713035613723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42560242211201901428303261 15960090829200713035613723)
  ·
    refine ⟨23940136243801069553420585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15960090829200713035613723 23940136243801069553420585)
    ·
      refine ⟨17955102182850802165065439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23940136243801069553420585 17955102182850802165065439)
      ·
        refine ⟨26932653274276203247598159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17955102182850802165065439 26932653274276203247598159)
        ·
          refine ⟨40398979911414304871397239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26932653274276203247598159 40398979911414304871397239)
          ·
            refine ⟨60598469867121457307095859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40398979911414304871397239 60598469867121457307095859)
            ·
              refine ⟨90897704800682185960643789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60598469867121457307095859 90897704800682185960643789)
              ·
                refine ⟨34086639300255819735241421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90897704800682185960643789 34086639300255819735241421)
                ·
                  refine ⟨12782489737595932400715533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34086639300255819735241421 12782489737595932400715533)
                  ·
                    refine ⟨4793433651598474650268325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12782489737595932400715533 4793433651598474650268325)
                    ·
                      refine ⟨898768809674713996925311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4793433651598474650268325 898768809674713996925311)
                      ·
                        rfl

theorem cell23_1750346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_1750346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750346 prefixEnd_1750346 := by exact prefixLift 1750346
  have htrace : WordTrace (prefixWord ++ tailWord_1750346) baseStart_1750346 baseEnd_1750346 := by
    simpa [prefixWord, tailWord_1750346, baseEnd_1750346] using wordTrace_append hprefix tailTrace_1750346
  have hstable : (prefixWord ++ tailWord_1750346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750346).length < 2 ^ (prefixWord ++ tailWord_1750346).sum := by decide
  have hdescent : baseEnd_1750346 < baseStart_1750346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750383 : List Nat := [1, 1, 2, 1, 3, 1, 3, 4, 2, 2, 3]
def baseStart_1750383 : Nat := 118140960795 + 1750383 * 2 ^ 59
def prefixEnd_1750383 : Nat := 4983230072969 + 3 ^ 40 * 1750383 * 2
def baseEnd_1750383 : Nat := 898787808458930352162641

theorem tailTrace_1750383 : CollatzResearch.WordTrace tailWord_1750383 prefixEnd_1750383 898787808458930352162641 := by
  unfold tailWord_1750383
  simp only [CollatzResearch.WordTrace]
  refine ⟨63841712817668807461551803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42561141878445871641034535 63841712817668807461551803)
  ·
    refine ⟨95762569226503211192327705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63841712817668807461551803 95762569226503211192327705)
    ·
      refine ⟨71821926919877408394245779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95762569226503211192327705 71821926919877408394245779)
      ·
        refine ⟨107732890379816112591368669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71821926919877408394245779 107732890379816112591368669)
        ·
          refine ⟨40399833892431042221763251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107732890379816112591368669 40399833892431042221763251)
          ·
            refine ⟨60599750838646563332644877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40399833892431042221763251 60599750838646563332644877)
            ·
              refine ⟨22724906564492461249741829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60599750838646563332644877 22724906564492461249741829)
              ·
                refine ⟨4260919980842336484326593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22724906564492461249741829 4260919980842336484326593)
                ·
                  refine ⟨3195689985631752363244945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4260919980842336484326593 3195689985631752363244945)
                  ·
                    refine ⟨2396767489223814272433709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3195689985631752363244945 2396767489223814272433709)
                    ·
                      refine ⟨898787808458930352162641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2396767489223814272433709 898787808458930352162641)
                      ·
                        rfl

theorem cell23_1750383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 2, 3].length) (baseStart_1750383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750383 prefixEnd_1750383 := by exact prefixLift 1750383
  have htrace : WordTrace (prefixWord ++ tailWord_1750383) baseStart_1750383 baseEnd_1750383 := by
    simpa [prefixWord, tailWord_1750383, baseEnd_1750383] using wordTrace_append hprefix tailTrace_1750383
  have hstable : (prefixWord ++ tailWord_1750383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750383).length < 2 ^ (prefixWord ++ tailWord_1750383).sum := by decide
  have hdescent : baseEnd_1750383 < baseStart_1750383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750403 : List Nat := [1, 1, 1, 3, 5, 1, 2, 3, 6]
def baseStart_1750403 : Nat := 118140960795 + 1750403 * 2 ^ 59
def prefixEnd_1750403 : Nat := 4983230072969 + 3 ^ 40 * 1750403 * 2
def baseEnd_1750403 : Nat := 99866453119113363768061

theorem tailTrace_1750403 : CollatzResearch.WordTrace tailWord_1750403 prefixEnd_1750403 99866453119113363768061 := by
  unfold tailWord_1750403
  simp only [CollatzResearch.WordTrace]
  refine ⟨63842442277596350877279863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42561628185064233918186575 63842442277596350877279863)
  ·
    refine ⟨95763663416394526315919795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63842442277596350877279863 95763663416394526315919795)
    ·
      refine ⟨143645495124591789473879693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95763663416394526315919795 143645495124591789473879693)
      ·
        refine ⟨53867060671721921052704885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143645495124591789473879693 53867060671721921052704885)
        ·
          refine ⟨5050036937973930098691083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53867060671721921052704885 5050036937973930098691083)
          ·
            refine ⟨7575055406960895148036625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5050036937973930098691083 7575055406960895148036625)
            ·
              refine ⟨5681291555220671361027469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7575055406960895148036625 5681291555220671361027469)
              ·
                refine ⟨2130484333207751760385301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5681291555220671361027469 2130484333207751760385301)
                ·
                  refine ⟨99866453119113363768061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2130484333207751760385301 99866453119113363768061)
                  ·
                    rfl

theorem cell23_1750403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 6].length) (baseStart_1750403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750403 prefixEnd_1750403 := by exact prefixLift 1750403
  have htrace : WordTrace (prefixWord ++ tailWord_1750403) baseStart_1750403 baseEnd_1750403 := by
    simpa [prefixWord, tailWord_1750403, baseEnd_1750403] using wordTrace_append hprefix tailTrace_1750403
  have hstable : (prefixWord ++ tailWord_1750403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750403).length < 2 ^ (prefixWord ++ tailWord_1750403).sum := by decide
  have hdescent : baseEnd_1750403 < baseStart_1750403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750414 : List Nat := [4, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4]
def baseStart_1750414 : Nat := 118140960795 + 1750414 * 2 ^ 59
def prefixEnd_1750414 : Nat := 4983230072969 + 3 ^ 40 * 1750414 * 2
def baseEnd_1750414 : Nat := 898803726359219730874999

theorem tailTrace_1750414 : CollatzResearch.WordTrace tailWord_1750414 prefixEnd_1750414 898803726359219730874999 := by
  unfold tailWord_1750414
  simp only [CollatzResearch.WordTrace]
  refine ⟨7980355435069562469491287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42561895653704333170620197 7980355435069562469491287)
  ·
    refine ⟨11970533152604343704236931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7980355435069562469491287 11970533152604343704236931)
    ·
      refine ⟨17955799728906515556355397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11970533152604343704236931 17955799728906515556355397)
      ·
        refine ⟨3366712449169971666816637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17955799728906515556355397 3366712449169971666816637)
        ·
          refine ⟨1262517168438739375056239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3366712449169971666816637 1262517168438739375056239)
          ·
            refine ⟨1893775752658109062584359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1262517168438739375056239 1893775752658109062584359)
            ·
              refine ⟨2840663628987163593876539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1893775752658109062584359 2840663628987163593876539)
              ·
                refine ⟨4260995443480745390814809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2840663628987163593876539 4260995443480745390814809)
                ·
                  refine ⟨3195746582610559043111107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4260995443480745390814809 3195746582610559043111107)
                  ·
                    refine ⟨4793619873915838564666661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3195746582610559043111107 4793619873915838564666661)
                    ·
                      refine ⟨898803726359219730874999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4793619873915838564666661 898803726359219730874999)
                      ·
                        rfl

theorem cell23_1750414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_1750414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750414 prefixEnd_1750414 := by exact prefixLift 1750414
  have htrace : WordTrace (prefixWord ++ tailWord_1750414) baseStart_1750414 baseEnd_1750414 := by
    simpa [prefixWord, tailWord_1750414, baseEnd_1750414] using wordTrace_append hprefix tailTrace_1750414
  have hstable : (prefixWord ++ tailWord_1750414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750414).length < 2 ^ (prefixWord ++ tailWord_1750414).sum := by decide
  have hdescent : baseEnd_1750414 < baseStart_1750414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750424 : List Nat := [2, 1, 2, 5, 2, 1, 2, 3, 1, 4]
def baseStart_1750424 : Nat := 118140960795 + 1750424 * 2 ^ 59
def prefixEnd_1750424 : Nat := 4983230072969 + 3 ^ 40 * 1750424 * 2
def baseEnd_1750424 : Nat := 299602953721921563916651

theorem tailTrace_1750424 : CollatzResearch.WordTrace tailWord_1750424 prefixEnd_1750424 299602953721921563916651 := by
  unfold tailWord_1750424
  simp only [CollatzResearch.WordTrace]
  refine ⟨31921604105260135731897163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42562138807013514309196217 31921604105260135731897163)
  ·
    refine ⟨47882406157890203597845745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31921604105260135731897163 47882406157890203597845745)
    ·
      refine ⟨35911804618417652698384309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47882406157890203597845745 35911804618417652698384309)
      ·
        refine ⟨3366731682976654940473529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35911804618417652698384309 3366731682976654940473529)
        ·
          refine ⟨2525048762232491205355147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3366731682976654940473529 2525048762232491205355147)
          ·
            refine ⟨3787573143348736808032721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2525048762232491205355147 3787573143348736808032721)
            ·
              refine ⟨2840679857511552606024541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3787573143348736808032721 2840679857511552606024541)
              ·
                refine ⟨1065254946566832227259203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2840679857511552606024541 1065254946566832227259203)
                ·
                  refine ⟨1597882419850248340888805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1065254946566832227259203 1597882419850248340888805)
                  ·
                    refine ⟨299602953721921563916651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1597882419850248340888805 299602953721921563916651)
                    ·
                      rfl

theorem cell23_1750424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 3, 1, 4].length) (baseStart_1750424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750424 prefixEnd_1750424 := by exact prefixLift 1750424
  have htrace : WordTrace (prefixWord ++ tailWord_1750424) baseStart_1750424 baseEnd_1750424 := by
    simpa [prefixWord, tailWord_1750424, baseEnd_1750424] using wordTrace_append hprefix tailTrace_1750424
  have hstable : (prefixWord ++ tailWord_1750424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750424).length < 2 ^ (prefixWord ++ tailWord_1750424).sum := by decide
  have hdescent : baseEnd_1750424 < baseStart_1750424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750490 : List Nat := [3, 1, 1, 2, 3, 3, 2, 1, 1, 1, 5]
def baseStart_1750490 : Nat := 118140960795 + 1750490 * 2 ^ 59
def prefixEnd_1750490 : Nat := 4983230072969 + 3 ^ 40 * 1750490 * 2
def baseEnd_1750490 : Nat := 898842750888961433524649

theorem tailTrace_1750490 : CollatzResearch.WordTrace tailWord_1750490 prefixEnd_1750490 898842750888961433524649 := by
  unfold tailWord_1750490
  simp only [CollatzResearch.WordTrace]
  refine ⟨15961403857070291183924231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42563743618854109823797949 15961403857070291183924231)
  ·
    refine ⟨23942105785605436775886347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15961403857070291183924231 23942105785605436775886347)
    ·
      refine ⟨35913158678408155163829521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23942105785605436775886347 35913158678408155163829521)
      ·
        refine ⟨26934869008806116372872141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35913158678408155163829521 26934869008806116372872141)
        ·
          refine ⟨10100575878302293639827053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26934869008806116372872141 10100575878302293639827053)
          ·
            refine ⟨3787715954363360114935145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10100575878302293639827053 3787715954363360114935145)
            ·
              refine ⟨2840786965772520086201359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3787715954363360114935145 2840786965772520086201359)
              ·
                refine ⟨4261180448658780129302039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2840786965772520086201359 4261180448658780129302039)
                ·
                  refine ⟨6391770672988170193953059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4261180448658780129302039 6391770672988170193953059)
                  ·
                    refine ⟨9587656009482255290929589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6391770672988170193953059 9587656009482255290929589)
                    ·
                      refine ⟨898842750888961433524649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9587656009482255290929589 898842750888961433524649)
                      ·
                        rfl

theorem cell23_1750490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_1750490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750490 prefixEnd_1750490 := by exact prefixLift 1750490
  have htrace : WordTrace (prefixWord ++ tailWord_1750490) baseStart_1750490 baseEnd_1750490 := by
    simpa [prefixWord, tailWord_1750490, baseEnd_1750490] using wordTrace_append hprefix tailTrace_1750490
  have hstable : (prefixWord ++ tailWord_1750490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750490).length < 2 ^ (prefixWord ++ tailWord_1750490).sum := by decide
  have hdescent : baseEnd_1750490 < baseStart_1750490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750493 : List Nat := [1, 4, 3, 1, 1, 2, 11]
def baseStart_1750493 : Nat := 118140960795 + 1750493 * 2 ^ 59
def prefixEnd_1750493 : Nat := 4983230072969 + 3 ^ 40 * 1750493 * 2
def baseEnd_1750493 : Nat := 11096843102850924960335

theorem tailTrace_1750493 : CollatzResearch.WordTrace tailWord_1750493 prefixEnd_1750493 11096843102850924960335 := by
  unfold tailWord_1750493
  simp only [CollatzResearch.WordTrace]
  refine ⟨63845724847270296248056133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42563816564846864165370755 63845724847270296248056133)
  ·
    refine ⟨11971073408863180546510525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63845724847270296248056133 11971073408863180546510525)
    ·
      refine ⟨4489152528323692704941447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11971073408863180546510525 4489152528323692704941447)
      ·
        refine ⟨6733728792485539057412171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4489152528323692704941447 6733728792485539057412171)
        ·
          refine ⟨10100593188728308586118257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6733728792485539057412171 10100593188728308586118257)
          ·
            refine ⟨7575444891546231439588693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10100593188728308586118257 7575444891546231439588693)
            ·
              refine ⟨11096843102850924960335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7575444891546231439588693 11096843102850924960335)
              ·
                rfl

theorem cell23_1750493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 11].length) (baseStart_1750493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750493 prefixEnd_1750493 := by exact prefixLift 1750493
  have htrace : WordTrace (prefixWord ++ tailWord_1750493) baseStart_1750493 baseEnd_1750493 := by
    simpa [prefixWord, tailWord_1750493, baseEnd_1750493] using wordTrace_append hprefix tailTrace_1750493
  have hstable : (prefixWord ++ tailWord_1750493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750493).length < 2 ^ (prefixWord ++ tailWord_1750493).sum := by decide
  have hdescent : baseEnd_1750493 < baseStart_1750493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750514 : List Nat := [3, 2, 1, 4, 1, 1, 4, 1, 2, 4]
def baseStart_1750514 : Nat := 118140960795 + 1750514 * 2 ^ 59
def prefixEnd_1750514 : Nat := 4983230072969 + 3 ^ 40 * 1750514 * 2
def baseEnd_1750514 : Nat := 299618358141556446541513

theorem tailTrace_1750514 : CollatzResearch.WordTrace tailWord_1750514 prefixEnd_1750514 299618358141556446541513 := by
  unfold tailWord_1750514
  simp only [CollatzResearch.WordTrace]
  refine ⟨15961622695048554208642649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42564327186796144556380397 15961622695048554208642649)
  ·
    refine ⟨11971217021286415656481987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15961622695048554208642649 11971217021286415656481987)
    ·
      refine ⟨17956825531929623484722981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11971217021286415656481987 17956825531929623484722981)
      ·
        refine ⟨3366904787236804403385559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17956825531929623484722981 3366904787236804403385559)
        ·
          refine ⟨5050357180855206605078339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3366904787236804403385559 5050357180855206605078339)
          ·
            refine ⟨7575535771282809907617509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5050357180855206605078339 7575535771282809907617509)
            ·
              refine ⟨1420412957115526857678283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7575535771282809907617509 1420412957115526857678283)
              ·
                refine ⟨2130619435673290286517425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1420412957115526857678283 2130619435673290286517425)
                ·
                  refine ⟨1597964576754967714888069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2130619435673290286517425 1597964576754967714888069)
                  ·
                    refine ⟨299618358141556446541513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1597964576754967714888069 299618358141556446541513)
                    ·
                      rfl

theorem cell23_1750514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_1750514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750514 prefixEnd_1750514 := by exact prefixLift 1750514
  have htrace : WordTrace (prefixWord ++ tailWord_1750514) baseStart_1750514 baseEnd_1750514 := by
    simpa [prefixWord, tailWord_1750514, baseEnd_1750514] using wordTrace_append hprefix tailTrace_1750514
  have hstable : (prefixWord ++ tailWord_1750514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750514).length < 2 ^ (prefixWord ++ tailWord_1750514).sum := by decide
  have hdescent : baseEnd_1750514 < baseStart_1750514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750541 : List Nat := [1, 7, 1, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_1750541 : Nat := 118140960795 + 1750541 * 2 ^ 59
def prefixEnd_1750541 : Nat := 4983230072969 + 3 ^ 40 * 1750541 * 2
def baseEnd_1750541 : Nat := 898868938402340733986915

theorem tailTrace_1750541 : CollatzResearch.WordTrace tailWord_1750541 prefixEnd_1750541 898868938402340733986915 := by
  unfold tailWord_1750541
  simp only [CollatzResearch.WordTrace]
  refine ⟨63847475551096400445803477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42564983700730933630535651 63847475551096400445803477)
  ·
    refine ⟨1496425208228821885448519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 63847475551096400445803477 1496425208228821885448519)
    ·
      refine ⟨2244637812343232828172779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1496425208228821885448519 2244637812343232828172779)
      ·
        refine ⟨3366956718514849242259169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2244637812343232828172779 3366956718514849242259169)
        ·
          refine ⟨2525217538886136931694377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3366956718514849242259169 2525217538886136931694377)
          ·
            refine ⟨1893913154164602698770783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2525217538886136931694377 1893913154164602698770783)
            ·
              refine ⟨2840869731246904048156175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1893913154164602698770783 2840869731246904048156175)
              ·
                refine ⟨4261304596870356072234263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2840869731246904048156175 4261304596870356072234263)
                ·
                  refine ⟨6391956895305534108351395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4261304596870356072234263 6391956895305534108351395)
                  ·
                    refine ⟨9587935342958301162527093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6391956895305534108351395 9587935342958301162527093)
                    ·
                      refine ⟨898868938402340733986915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9587935342958301162527093 898868938402340733986915)
                      ·
                        rfl

theorem cell23_1750541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_1750541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750541 prefixEnd_1750541 := by exact prefixLift 1750541
  have htrace : WordTrace (prefixWord ++ tailWord_1750541) baseStart_1750541 baseEnd_1750541 := by
    simpa [prefixWord, tailWord_1750541, baseEnd_1750541] using wordTrace_append hprefix tailTrace_1750541
  have hstable : (prefixWord ++ tailWord_1750541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750541).length < 2 ^ (prefixWord ++ tailWord_1750541).sum := by decide
  have hdescent : baseEnd_1750541 < baseStart_1750541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750560 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 4]
def baseStart_1750560 : Nat := 118140960795 + 1750560 * 2 ^ 59
def prefixEnd_1750560 : Nat := 4983230072969 + 3 ^ 40 * 1750560 * 2
def baseEnd_1750560 : Nat := 898878694534776159649327

theorem tailTrace_1750560 : CollatzResearch.WordTrace tailWord_1750560 prefixEnd_1750560 898878694534776159649327 := by
  unfold tailWord_1750560
  simp only [CollatzResearch.WordTrace]
  refine ⟨31924084269013783345372567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42565445692018377793830089 31924084269013783345372567)
  ·
    refine ⟨47886126403520675018058851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31924084269013783345372567 47886126403520675018058851)
    ·
      refine ⟨71829189605281012527088277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47886126403520675018058851 71829189605281012527088277)
      ·
        refine ⟨3366993262747547462207263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 71829189605281012527088277 3366993262747547462207263)
        ·
          refine ⟨5050489894121321193310895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3366993262747547462207263 5050489894121321193310895)
          ·
            refine ⟨7575734841181981789966343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5050489894121321193310895 7575734841181981789966343)
            ·
              refine ⟨11363602261772972684949515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7575734841181981789966343 11363602261772972684949515)
              ·
                refine ⟨17045403392659459027424273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11363602261772972684949515 17045403392659459027424273)
                ·
                  refine ⟨12784052544494594270568205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17045403392659459027424273 12784052544494594270568205)
                  ·
                    refine ⟨4794019704185472851463077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12784052544494594270568205 4794019704185472851463077)
                    ·
                      refine ⟨898878694534776159649327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4794019704185472851463077 898878694534776159649327)
                      ·
                        rfl

theorem cell23_1750560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_1750560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750560 prefixEnd_1750560 := by exact prefixLift 1750560
  have htrace : WordTrace (prefixWord ++ tailWord_1750560) baseStart_1750560 baseEnd_1750560 := by
    simpa [prefixWord, tailWord_1750560, baseEnd_1750560] using wordTrace_append hprefix tailTrace_1750560
  have hstable : (prefixWord ++ tailWord_1750560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750560).length < 2 ^ (prefixWord ++ tailWord_1750560).sum := by decide
  have hdescent : baseEnd_1750560 < baseStart_1750560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750570 : List Nat := [3, 1, 4, 1, 1, 1, 3, 1, 2, 6]
def baseStart_1750570 : Nat := 118140960795 + 1750570 * 2 ^ 59
def prefixEnd_1750570 : Nat := 4983230072969 + 3 ^ 40 * 1750570 * 2
def baseEnd_1750570 : Nat := 299627943113773706841427

theorem tailTrace_1750570 : CollatzResearch.WordTrace tailWord_1750570 prefixEnd_1750570 299627943113773706841427 := by
  unfold tailWord_1750570
  simp only [CollatzResearch.WordTrace]
  refine ⟨15962133316997834599652291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42565688845327558932406109 15962133316997834599652291)
  ·
    refine ⟨23943199975496751899478437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15962133316997834599652291 23943199975496751899478437)
    ·
      refine ⟨4489349995405640981152207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23943199975496751899478437 4489349995405640981152207)
      ·
        refine ⟨6734024993108461471728311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4489349995405640981152207 6734024993108461471728311)
        ·
          refine ⟨10101037489662692207592467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6734024993108461471728311 10101037489662692207592467)
          ·
            refine ⟨15151556234494038311388701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10101037489662692207592467 15151556234494038311388701)
            ·
              refine ⟨5681833587935264366770763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15151556234494038311388701 5681833587935264366770763)
              ·
                refine ⟨8522750381902896550156145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5681833587935264366770763 8522750381902896550156145)
                ·
                  refine ⟨6392062786427172412617109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8522750381902896550156145 6392062786427172412617109)
                  ·
                    refine ⟨299627943113773706841427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6392062786427172412617109 299627943113773706841427)
                    ·
                      rfl

theorem cell23_1750570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_1750570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750570 prefixEnd_1750570 := by exact prefixLift 1750570
  have htrace : WordTrace (prefixWord ++ tailWord_1750570) baseStart_1750570 baseEnd_1750570 := by
    simpa [prefixWord, tailWord_1750570, baseEnd_1750570] using wordTrace_append hprefix tailTrace_1750570
  have hstable : (prefixWord ++ tailWord_1750570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750570).length < 2 ^ (prefixWord ++ tailWord_1750570).sum := by decide
  have hdescent : baseEnd_1750570 < baseStart_1750570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750577 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 6, 2, 2]
def baseStart_1750577 : Nat := 118140960795 + 1750577 * 2 ^ 59
def prefixEnd_1750577 : Nat := 4983230072969 + 3 ^ 40 * 1750577 * 2
def baseEnd_1750577 : Nat := 898887423705902593136749

theorem tailTrace_1750577 : CollatzResearch.WordTrace tailWord_1750577 prefixEnd_1750577 898887423705902593136749 := by
  unfold tailWord_1750577
  simp only [CollatzResearch.WordTrace]
  refine ⟨63848788578965978594113985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42565859052643985729409323 63848788578965978594113985)
  ·
    refine ⟨47886591434224483945585489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63848788578965978594113985 47886591434224483945585489)
    ·
      refine ⟨35914943575668362959189117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47886591434224483945585489 35914943575668362959189117)
      ·
        refine ⟨13468103840875636109695919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35914943575668362959189117 13468103840875636109695919)
        ·
          refine ⟨20202155761313454164543879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13468103840875636109695919 20202155761313454164543879)
          ·
            refine ⟨30303233641970181246815819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20202155761313454164543879 30303233641970181246815819)
            ·
              refine ⟨45454850462955271870223729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30303233641970181246815819 45454850462955271870223729)
              ·
                refine ⟨34091137847216453902667797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45454850462955271870223729 34091137847216453902667797)
                ·
                  refine ⟨1598022086588271276687553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 34091137847216453902667797 1598022086588271276687553)
                  ·
                    refine ⟨1198516564941203457515665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1598022086588271276687553 1198516564941203457515665)
                    ·
                      refine ⟨898887423705902593136749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1198516564941203457515665 898887423705902593136749)
                      ·
                        rfl

theorem cell23_1750577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_1750577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750577 prefixEnd_1750577 := by exact prefixLift 1750577
  have htrace : WordTrace (prefixWord ++ tailWord_1750577) baseStart_1750577 baseEnd_1750577 := by
    simpa [prefixWord, tailWord_1750577, baseEnd_1750577] using wordTrace_append hprefix tailTrace_1750577
  have hstable : (prefixWord ++ tailWord_1750577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750577).length < 2 ^ (prefixWord ++ tailWord_1750577).sum := by decide
  have hdescent : baseEnd_1750577 < baseStart_1750577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750583 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 9]
def baseStart_1750583 : Nat := 118140960795 + 1750583 * 2 ^ 59
def prefixEnd_1750583 : Nat := 4983230072969 + 3 ^ 40 * 1750583 * 2
def baseEnd_1750583 : Nat := 99876722732203285517969

theorem tailTrace_1750583 : CollatzResearch.WordTrace tailWord_1750583 prefixEnd_1750583 99876722732203285517969 := by
  unfold tailWord_1750583
  simp only [CollatzResearch.WordTrace]
  refine ⟨63849007416944241618832403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42566004944629494412554935 63849007416944241618832403)
  ·
    refine ⟨95773511125416362428248605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63849007416944241618832403 95773511125416362428248605)
    ·
      refine ⟨35915066672031135910593227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95773511125416362428248605 35915066672031135910593227)
      ·
        refine ⟨53872600008046703865889841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35915066672031135910593227 53872600008046703865889841)
        ·
          refine ⟨40404450006035027899417381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53872600008046703865889841 40404450006035027899417381)
          ·
            refine ⟨7575834376131567731140759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40404450006035027899417381 7575834376131567731140759)
            ·
              refine ⟨11363751564197351596711139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7575834376131567731140759 11363751564197351596711139)
              ·
                refine ⟨17045627346296027395066709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11363751564197351596711139 17045627346296027395066709)
                ·
                  refine ⟨99876722732203285517969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17045627346296027395066709 99876722732203285517969)
                  ·
                    rfl

theorem cell23_1750583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 9].length) (baseStart_1750583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750583 prefixEnd_1750583 := by exact prefixLift 1750583
  have htrace : WordTrace (prefixWord ++ tailWord_1750583) baseStart_1750583 baseEnd_1750583 := by
    simpa [prefixWord, tailWord_1750583, baseEnd_1750583] using wordTrace_append hprefix tailTrace_1750583
  have hstable : (prefixWord ++ tailWord_1750583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750583).length < 2 ^ (prefixWord ++ tailWord_1750583).sum := by decide
  have hdescent : baseEnd_1750583 < baseStart_1750583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750598 : List Nat := [6, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2]
def baseStart_1750598 : Nat := 118140960795 + 1750598 * 2 ^ 59
def prefixEnd_1750598 : Nat := 4983230072969 + 3 ^ 40 * 1750598 * 2
def baseEnd_1750598 : Nat := 898898206799647010974153

theorem tailTrace_1750598 : CollatzResearch.WordTrace tailWord_1750598 prefixEnd_1750598 898898206799647010974153 := by
  unfold tailWord_1750598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1995298578496559349394639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42566369674593266120418965 1995298578496559349394639)
  ·
    refine ⟨2992947867744839024091959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1995298578496559349394639 2992947867744839024091959)
    ·
      refine ⟨4489421801617258536137939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2992947867744839024091959 4489421801617258536137939)
      ·
        refine ⟨6734132702425887804206909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4489421801617258536137939 6734132702425887804206909)
        ·
          refine ⟨2525299763409707926577591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6734132702425887804206909 2525299763409707926577591)
          ·
            refine ⟨3787949645114561889866387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2525299763409707926577591 3787949645114561889866387)
            ·
              refine ⟨5681924467671842834799581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3787949645114561889866387 5681924467671842834799581)
              ·
                refine ⟨2130721675376941063049843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5681924467671842834799581 2130721675376941063049843)
                ·
                  refine ⟨3196082513065411594574765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2130721675376941063049843 3196082513065411594574765)
                  ·
                    refine ⟨1198530942399529347965537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3196082513065411594574765 1198530942399529347965537)
                    ·
                      refine ⟨898898206799647010974153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1198530942399529347965537 898898206799647010974153)
                      ·
                        rfl

theorem cell23_1750598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_1750598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750598 prefixEnd_1750598 := by exact prefixLift 1750598
  have htrace : WordTrace (prefixWord ++ tailWord_1750598) baseStart_1750598 baseEnd_1750598 := by
    simpa [prefixWord, tailWord_1750598, baseEnd_1750598] using wordTrace_append hprefix tailTrace_1750598
  have hstable : (prefixWord ++ tailWord_1750598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750598).length < 2 ^ (prefixWord ++ tailWord_1750598).sum := by decide
  have hdescent : baseEnd_1750598 < baseStart_1750598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750664 : List Nat := [2, 1, 3, 5, 1, 1, 1, 2, 2, 5]
def baseStart_1750664 : Nat := 118140960795 + 1750664 * 2 ^ 59
def prefixEnd_1750664 : Nat := 4983230072969 + 3 ^ 40 * 1750664 * 2
def baseEnd_1750664 : Nat := 299644032174281250916283

theorem tailTrace_1750664 : CollatzResearch.WordTrace tailWord_1750664 prefixEnd_1750664 299644032174281250916283 := by
  unfold tailWord_1750664
  simp only [CollatzResearch.WordTrace]
  refine ⟨31925980864825396226265523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42567974486433861635020697 31925980864825396226265523)
  ·
    refine ⟨47888971297238094339398285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31925980864825396226265523 47888971297238094339398285)
    ·
      refine ⟨17958364236464285377274357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47888971297238094339398285 17958364236464285377274357)
      ·
        refine ⟨1683596647168526754119471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17958364236464285377274357 1683596647168526754119471)
        ·
          refine ⟨2525394970752790131179207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1683596647168526754119471 2525394970752790131179207)
          ·
            refine ⟨3788092456129185196768811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2525394970752790131179207 3788092456129185196768811)
            ·
              refine ⟨5682138684193777795153217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3788092456129185196768811 5682138684193777795153217)
              ·
                refine ⟨4261604013145333346364913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5682138684193777795153217 4261604013145333346364913)
                ·
                  refine ⟨3196203009859000009773685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4261604013145333346364913 3196203009859000009773685)
                  ·
                    refine ⟨299644032174281250916283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3196203009859000009773685 299644032174281250916283)
                    ·
                      rfl

theorem cell23_1750664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_1750664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750664 prefixEnd_1750664 := by exact prefixLift 1750664
  have htrace : WordTrace (prefixWord ++ tailWord_1750664) baseStart_1750664 baseEnd_1750664 := by
    simpa [prefixWord, tailWord_1750664, baseEnd_1750664] using wordTrace_append hprefix tailTrace_1750664
  have hstable : (prefixWord ++ tailWord_1750664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750664).length < 2 ^ (prefixWord ++ tailWord_1750664).sum := by decide
  have hdescent : baseEnd_1750664 < baseStart_1750664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750734 : List Nat := [4, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3]
def baseStart_1750734 : Nat := 118140960795 + 1750734 * 2 ^ 59
def prefixEnd_1750734 : Nat := 4983230072969 + 3 ^ 40 * 1750734 * 2
def baseEnd_1750734 : Nat := 898968040168658478873527

theorem tailTrace_1750734 : CollatzResearch.WordTrace tailWord_1750734 prefixEnd_1750734 898968040168658478873527 := by
  unfold tailWord_1750734
  simp only [CollatzResearch.WordTrace]
  refine ⟨7981814354924649300947407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42569676559598129605052837 7981814354924649300947407)
  ·
    refine ⟨11972721532386973951421111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7981814354924649300947407 11972721532386973951421111)
    ·
      refine ⟨17959082298580460927131667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11972721532386973951421111 17959082298580460927131667)
      ·
        refine ⟨26938623447870691390697501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17959082298580460927131667 26938623447870691390697501)
        ·
          refine ⟨10101983792951509271511563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26938623447870691390697501 10101983792951509271511563)
          ·
            refine ⟨15152975689427263907267345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10101983792951509271511563 15152975689427263907267345)
            ·
              refine ⟨11364731767070447930450509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15152975689427263907267345 11364731767070447930450509)
              ·
                refine ⟨4261774412651417973918941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11364731767070447930450509 4261774412651417973918941)
                ·
                  refine ⟨1598165404744281740219603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4261774412651417973918941 1598165404744281740219603)
                  ·
                    refine ⟨2397248107116422610329405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1598165404744281740219603 2397248107116422610329405)
                    ·
                      refine ⟨898968040168658478873527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2397248107116422610329405 898968040168658478873527)
                      ·
                        rfl

theorem cell23_1750734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_1750734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750734 prefixEnd_1750734 := by exact prefixLift 1750734
  have htrace : WordTrace (prefixWord ++ tailWord_1750734) baseStart_1750734 baseEnd_1750734 := by
    simpa [prefixWord, tailWord_1750734, baseEnd_1750734] using wordTrace_append hprefix tailTrace_1750734
  have hstable : (prefixWord ++ tailWord_1750734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750734).length < 2 ^ (prefixWord ++ tailWord_1750734).sum := by decide
  have hdescent : baseEnd_1750734 < baseStart_1750734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750757 : List Nat := [1, 3, 1, 4, 1, 1, 1, 3, 3, 1, 4]
def baseStart_1750757 : Nat := 118140960795 + 1750757 * 2 ^ 59
def prefixEnd_1750757 : Nat := 4983230072969 + 3 ^ 40 * 1750757 * 2
def baseEnd_1750757 : Nat := 898979850223711888885921

theorem tailTrace_1750757 : CollatzResearch.WordTrace tailWord_1750757 prefixEnd_1750757 898979850223711888885921 := by
  unfold tailWord_1750757
  simp only [CollatzResearch.WordTrace]
  refine ⟨63855353718313869335666525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42570235812209246223777683 63855353718313869335666525)
  ·
    refine ⟨23945757644367701000874947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63855353718313869335666525 23945757644367701000874947)
    ·
      refine ⟨35918636466551551501312421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23945757644367701000874947 35918636466551551501312421)
      ·
        refine ⟨6734744337478415906496079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35918636466551551501312421 6734744337478415906496079)
        ·
          refine ⟨10102116506217623859744119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6734744337478415906496079 10102116506217623859744119)
          ·
            refine ⟨15153174759326435789616179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10102116506217623859744119 15153174759326435789616179)
            ·
              refine ⟨22729762138989653684424269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15153174759326435789616179 22729762138989653684424269)
              ·
                refine ⟨8523660802121120131659101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22729762138989653684424269 8523660802121120131659101)
                ·
                  refine ⟨3196372800795420049372163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8523660802121120131659101 3196372800795420049372163)
                  ·
                    refine ⟨4794559201193130074058245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3196372800795420049372163 4794559201193130074058245)
                    ·
                      refine ⟨898979850223711888885921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4794559201193130074058245 898979850223711888885921)
                      ·
                        rfl

theorem cell23_1750757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_1750757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750757 prefixEnd_1750757 := by exact prefixLift 1750757
  have htrace : WordTrace (prefixWord ++ tailWord_1750757) baseStart_1750757 baseEnd_1750757 := by
    simpa [prefixWord, tailWord_1750757, baseEnd_1750757] using wordTrace_append hprefix tailTrace_1750757
  have hstable : (prefixWord ++ tailWord_1750757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750757).length < 2 ^ (prefixWord ++ tailWord_1750757).sum := by decide
  have hdescent : baseEnd_1750757 < baseStart_1750757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750767 : List Nat := [1, 1, 2, 1, 5, 1, 2, 2, 4, 4]
def baseStart_1750767 : Nat := 118140960795 + 1750767 * 2 ^ 59
def prefixEnd_1750767 : Nat := 4983230072969 + 3 ^ 40 * 1750767 * 2
def baseEnd_1750767 : Nat := 299661661676752283253625

theorem tailTrace_1750767 : CollatzResearch.WordTrace tailWord_1750767 prefixEnd_1750767 299661661676752283253625 := by
  unfold tailWord_1750767
  simp only [CollatzResearch.WordTrace]
  refine ⟨63855718448277641043530555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42570478965518427362353703 63855718448277641043530555)
  ·
    refine ⟨95783577672416461565295833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63855718448277641043530555 95783577672416461565295833)
    ·
      refine ⟨71837683254312346173971875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95783577672416461565295833 71837683254312346173971875)
      ·
        refine ⟨107756524881468519260957813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71837683254312346173971875 107756524881468519260957813)
        ·
          refine ⟨10102174207637673680714795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107756524881468519260957813 10102174207637673680714795)
          ·
            refine ⟨15153261311456510521072193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10102174207637673680714795 15153261311456510521072193)
            ·
              refine ⟨11364945983592382890804145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15153261311456510521072193 11364945983592382890804145)
              ·
                refine ⟨8523709487694287168103109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11364945983592382890804145 8523709487694287168103109)
                ·
                  refine ⟨1598195528942678844019333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8523709487694287168103109 1598195528942678844019333)
                  ·
                    refine ⟨299661661676752283253625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1598195528942678844019333 299661661676752283253625)
                    ·
                      rfl

theorem cell23_1750767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 4, 4].length) (baseStart_1750767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750767 prefixEnd_1750767 := by exact prefixLift 1750767
  have htrace : WordTrace (prefixWord ++ tailWord_1750767) baseStart_1750767 baseEnd_1750767 := by
    simpa [prefixWord, tailWord_1750767, baseEnd_1750767] using wordTrace_append hprefix tailTrace_1750767
  have hstable : (prefixWord ++ tailWord_1750767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750767).length < 2 ^ (prefixWord ++ tailWord_1750767).sum := by decide
  have hdescent : baseEnd_1750767 < baseStart_1750767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750780 : List Nat := [2, 2, 2, 1, 3, 1, 12]
def baseStart_1750780 : Nat := 118140960795 + 1750780 * 2 ^ 59
def prefixEnd_1750780 : Nat := 4983230072969 + 3 ^ 40 * 1750780 * 2
def baseEnd_1750780 : Nat := 11098662472577349369115

theorem tailTrace_1750780 : CollatzResearch.WordTrace tailWord_1750780 prefixEnd_1750780 11098662472577349369115 := by
  unfold tailWord_1750780
  simp only [CollatzResearch.WordTrace]
  refine ⟨31928096298615272131876897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42570795064820362842502529 31928096298615272131876897)
  ·
    refine ⟨23946072223961454098907673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31928096298615272131876897 23946072223961454098907673)
    ·
      refine ⟨17959554167971090574180755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23946072223961454098907673 17959554167971090574180755)
      ·
        refine ⟨26939331251956635861271133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17959554167971090574180755 26939331251956635861271133)
        ·
          refine ⟨10102249219483738447976675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26939331251956635861271133 10102249219483738447976675)
          ·
            refine ⟨15153373829225607671965013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10102249219483738447976675 15153373829225607671965013)
            ·
              refine ⟨11098662472577349369115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 15153373829225607671965013 11098662472577349369115)
              ·
                rfl

theorem cell23_1750780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 12].length) (baseStart_1750780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750780 prefixEnd_1750780 := by exact prefixLift 1750780
  have htrace : WordTrace (prefixWord ++ tailWord_1750780) baseStart_1750780 baseEnd_1750780 := by
    simpa [prefixWord, tailWord_1750780, baseEnd_1750780] using wordTrace_append hprefix tailTrace_1750780
  have hstable : (prefixWord ++ tailWord_1750780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750780).length < 2 ^ (prefixWord ++ tailWord_1750780).sum := by decide
  have hdescent : baseEnd_1750780 < baseStart_1750780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750864 : List Nat := [2, 1, 1, 1, 1, 4, 1, 5, 1, 4, 2]
def baseStart_1750864 : Nat := 118140960795 + 1750864 * 2 ^ 59
def prefixEnd_1750864 : Nat := 4983230072969 + 3 ^ 40 * 1750864 * 2
def baseEnd_1750864 : Nat := 899034792653742970247929

theorem tailTrace_1750864 : CollatzResearch.WordTrace tailWord_1750864 prefixEnd_1750864 899034792653742970247929 := by
  unfold tailWord_1750864
  simp only [CollatzResearch.WordTrace]
  refine ⟨31929628164463113304905823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42572837552617484406541097 31929628164463113304905823)
  ·
    refine ⟨47894442246694669957358735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31929628164463113304905823 47894442246694669957358735)
    ·
      refine ⟨71841663370042004936038103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47894442246694669957358735 71841663370042004936038103)
      ·
        refine ⟨107762495055063007404057155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71841663370042004936038103 107762495055063007404057155)
        ·
          refine ⟨161643742582594511106085733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107762495055063007404057155 161643742582594511106085733)
          ·
            refine ⟨30308201734236470832391075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161643742582594511106085733 30308201734236470832391075)
            ·
              refine ⟨45462302601354706248586613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30308201734236470832391075 45462302601354706248586613)
              ·
                refine ⟨4262090868877003710804995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45462302601354706248586613 4262090868877003710804995)
                ·
                  refine ⟨6393136303315505566207493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4262090868877003710804995 6393136303315505566207493)
                  ·
                    refine ⟨1198713056871657293663905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6393136303315505566207493 1198713056871657293663905)
                    ·
                      refine ⟨899034792653742970247929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1198713056871657293663905 899034792653742970247929)
                      ·
                        rfl

theorem cell23_1750864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 1, 4, 2].length) (baseStart_1750864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750864 prefixEnd_1750864 := by exact prefixLift 1750864
  have htrace : WordTrace (prefixWord ++ tailWord_1750864) baseStart_1750864 baseEnd_1750864 := by
    simpa [prefixWord, tailWord_1750864, baseEnd_1750864] using wordTrace_append hprefix tailTrace_1750864
  have hstable : (prefixWord ++ tailWord_1750864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750864).length < 2 ^ (prefixWord ++ tailWord_1750864).sum := by decide
  have hdescent : baseEnd_1750864 < baseStart_1750864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750868 : List Nat := [2, 4, 1, 1, 3, 1, 3, 2, 1, 3, 2]
def baseStart_1750868 : Nat := 118140960795 + 1750868 * 2 ^ 59
def prefixEnd_1750868 : Nat := 4983230072969 + 3 ^ 40 * 1750868 * 2
def baseEnd_1750868 : Nat := 899036846576360954597911

theorem tailTrace_1750868 : CollatzResearch.WordTrace tailWord_1750868 prefixEnd_1750868 899036846576360954597911 := by
  unfold tailWord_1750868
  simp only [CollatzResearch.WordTrace]
  refine ⟨31929701110455867646478629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42572934813941156861971505 31929701110455867646478629)
  ·
    refine ⟨5986818958210475183714743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31929701110455867646478629 5986818958210475183714743)
    ·
      refine ⟨8980228437315712775572115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5986818958210475183714743 8980228437315712775572115)
      ·
        refine ⟨13470342655973569163358173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8980228437315712775572115 13470342655973569163358173)
        ·
          refine ⟨5051378495990088436259315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13470342655973569163358173 5051378495990088436259315)
          ·
            refine ⟨7577067743985132654388973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5051378495990088436259315 7577067743985132654388973)
            ·
              refine ⟨2841400403994424745395865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7577067743985132654388973 2841400403994424745395865)
              ·
                refine ⟨2131050302995818559046899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2841400403994424745395865 2131050302995818559046899)
                ·
                  refine ⟨3196575454493727838570349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2131050302995818559046899 3196575454493727838570349)
                  ·
                    refine ⟨1198715795435147939463881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3196575454493727838570349 1198715795435147939463881)
                    ·
                      refine ⟨899036846576360954597911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1198715795435147939463881 899036846576360954597911)
                      ·
                        rfl

theorem cell23_1750868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_1750868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750868 prefixEnd_1750868 := by exact prefixLift 1750868
  have htrace : WordTrace (prefixWord ++ tailWord_1750868) baseStart_1750868 baseEnd_1750868 := by
    simpa [prefixWord, tailWord_1750868, baseEnd_1750868] using wordTrace_append hprefix tailTrace_1750868
  have hstable : (prefixWord ++ tailWord_1750868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750868).length < 2 ^ (prefixWord ++ tailWord_1750868).sum := by decide
  have hdescent : baseEnd_1750868 < baseStart_1750868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750917 : List Nat := [1, 3, 1, 1, 3, 2, 2, 2, 1, 7]
def baseStart_1750917 : Nat := 118140960795 + 1750917 * 2 ^ 59
def prefixEnd_1750917 : Nat := 4983230072969 + 3 ^ 40 * 1750917 * 2
def baseEnd_1750917 : Nat := 299687335709477087628395

theorem tailTrace_1750917 : CollatzResearch.WordTrace tailWord_1750917 prefixEnd_1750917 299687335709477087628395 := by
  unfold tailWord_1750917
  simp only [CollatzResearch.WordTrace]
  refine ⟨63861189397734216661491005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42574126265156144440994003 63861189397734216661491005)
  ·
    refine ⟨23947946024150331248059127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63861189397734216661491005 23947946024150331248059127)
    ·
      refine ⟨35921919036225496872088691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23947946024150331248059127 35921919036225496872088691)
      ·
        refine ⟨53882878554338245308133037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35921919036225496872088691 53882878554338245308133037)
        ·
          refine ⟨20206079457876841990549889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53882878554338245308133037 20206079457876841990549889)
          ·
            refine ⟨15154559593407631492912417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20206079457876841990549889 15154559593407631492912417)
            ·
              refine ⟨11365919695055723619684313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15154559593407631492912417 11365919695055723619684313)
              ·
                refine ⟨8524439771291792714763235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11365919695055723619684313 8524439771291792714763235)
                ·
                  refine ⟨12786659656937689072144853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8524439771291792714763235 12786659656937689072144853)
                  ·
                    refine ⟨299687335709477087628395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12786659656937689072144853 299687335709477087628395)
                    ·
                      rfl

theorem cell23_1750917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 7].length) (baseStart_1750917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750917 prefixEnd_1750917 := by exact prefixLift 1750917
  have htrace : WordTrace (prefixWord ++ tailWord_1750917) baseStart_1750917 baseEnd_1750917 := by
    simpa [prefixWord, tailWord_1750917, baseEnd_1750917] using wordTrace_append hprefix tailTrace_1750917
  have hstable : (prefixWord ++ tailWord_1750917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750917).length < 2 ^ (prefixWord ++ tailWord_1750917).sum := by decide
  have hdescent : baseEnd_1750917 < baseStart_1750917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750924 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 4, 5, 2]
def baseStart_1750924 : Nat := 118140960795 + 1750924 * 2 ^ 59
def prefixEnd_1750924 : Nat := 4983230072969 + 3 ^ 40 * 1750924 * 2
def baseEnd_1750924 : Nat := 899065601493012735497653

theorem tailTrace_1750924 : CollatzResearch.WordTrace tailWord_1750924 prefixEnd_1750924 899065601493012735497653 := by
  unfold tailWord_1750924
  simp only [CollatzResearch.WordTrace]
  refine ⟨31930722354354428428497913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42574296472472571237997217 31930722354354428428497913)
  ·
    refine ⟨23948041765765821321373435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31930722354354428428497913 23948041765765821321373435)
    ·
      refine ⟨35922062648648731982060153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23948041765765821321373435 35922062648648731982060153)
      ·
        refine ⟨26941546986486548986545115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35922062648648731982060153 26941546986486548986545115)
        ·
          refine ⟨40412320479729823479817673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26941546986486548986545115 40412320479729823479817673)
          ·
            refine ⟨30309240359797367609863255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40412320479729823479817673 30309240359797367609863255)
            ·
              refine ⟨45463860539696051414794883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30309240359797367609863255 45463860539696051414794883)
              ·
                refine ⟨68195790809544077122192325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45463860539696051414794883 68195790809544077122192325)
                ·
                  refine ⟨12786710776789514460411061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68195790809544077122192325 12786710776789514460411061)
                  ·
                    refine ⟨1198754135324016980663537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12786710776789514460411061 1198754135324016980663537)
                    ·
                      refine ⟨899065601493012735497653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1198754135324016980663537 899065601493012735497653)
                      ·
                        rfl

theorem cell23_1750924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 4, 5, 2].length) (baseStart_1750924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750924 prefixEnd_1750924 := by exact prefixLift 1750924
  have htrace : WordTrace (prefixWord ++ tailWord_1750924) baseStart_1750924 baseEnd_1750924 := by
    simpa [prefixWord, tailWord_1750924, baseEnd_1750924] using wordTrace_append hprefix tailTrace_1750924
  have hstable : (prefixWord ++ tailWord_1750924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750924).length < 2 ^ (prefixWord ++ tailWord_1750924).sum := by decide
  have hdescent : baseEnd_1750924 < baseStart_1750924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750967 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 6]
def baseStart_1750967 : Nat := 118140960795 + 1750967 * 2 ^ 59
def prefixEnd_1750967 : Nat := 4983230072969 + 3 ^ 40 * 1750967 * 2
def baseEnd_1750967 : Nat := 899087681161156067259955

theorem tailTrace_1750967 : CollatzResearch.WordTrace tailWord_1750967 prefixEnd_1750967 899087681161156067259955 := by
  unfold tailWord_1750967
  simp only [CollatzResearch.WordTrace]
  refine ⟨63863013047553075200811155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42575342031702050133874103 63863013047553075200811155)
  ·
    refine ⟨95794519571329612801216733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63863013047553075200811155 95794519571329612801216733)
    ·
      refine ⟨35922944839248604800456275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95794519571329612801216733 35922944839248604800456275)
      ·
        refine ⟨53884417258872907200684413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35922944839248604800456275 53884417258872907200684413)
        ·
          refine ⟨20206656472077340200256655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53884417258872907200684413 20206656472077340200256655)
          ·
            refine ⟨30309984708116010300384983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20206656472077340200256655 30309984708116010300384983)
            ·
              refine ⟨45464977062174015450577475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30309984708116010300384983 45464977062174015450577475)
              ·
                refine ⟨68197465593261023175866213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45464977062174015450577475 68197465593261023175866213)
                ·
                  refine ⟨12787024798736441845474915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68197465593261023175866213 12787024798736441845474915)
                  ·
                    refine ⟨19180537198104662768212373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12787024798736441845474915 19180537198104662768212373)
                    ·
                      refine ⟨899087681161156067259955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19180537198104662768212373 899087681161156067259955)
                      ·
                        rfl

theorem cell23_1750967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_1750967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1750967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1750967 prefixEnd_1750967 := by exact prefixLift 1750967
  have htrace : WordTrace (prefixWord ++ tailWord_1750967) baseStart_1750967 baseEnd_1750967 := by
    simpa [prefixWord, tailWord_1750967, baseEnd_1750967] using wordTrace_append hprefix tailTrace_1750967
  have hstable : (prefixWord ++ tailWord_1750967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750967).length < 2 ^ (prefixWord ++ tailWord_1750967).sum := by decide
  have hdescent : baseEnd_1750967 < baseStart_1750967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751015 : List Nat := [1, 1, 5, 2, 4, 1, 1, 1, 3, 4]
def baseStart_1751015 : Nat := 118140960795 + 1751015 * 2 ^ 59
def prefixEnd_1751015 : Nat := 4983230072969 + 3 ^ 40 * 1751015 * 2
def baseEnd_1751015 : Nat := 299704109410857293153245

theorem tailTrace_1751015 : CollatzResearch.WordTrace tailWord_1751015 prefixEnd_1751015 299704109410857293153245 := by
  unfold tailWord_1751015
  simp only [CollatzResearch.WordTrace]
  refine ⟨63864763751379179398558499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42576509167586119599038999 63864763751379179398558499)
  ·
    refine ⟨95797145627068769097837749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63864763751379179398558499 95797145627068769097837749)
    ·
      refine ⟨8980982402537697102922289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95797145627068769097837749 8980982402537697102922289)
      ·
        refine ⟨6735736801903272827191717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8980982402537697102922289 6735736801903272827191717)
        ·
          refine ⟨1262950650356863655098447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6735736801903272827191717 1262950650356863655098447)
          ·
            refine ⟨1894425975535295482647671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1262950650356863655098447 1894425975535295482647671)
            ·
              refine ⟨2841638963302943223971507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1894425975535295482647671 2841638963302943223971507)
              ·
                refine ⟨4262458444954414835957261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2841638963302943223971507 4262458444954414835957261)
                ·
                  refine ⟨1598421916857905563483973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4262458444954414835957261 1598421916857905563483973)
                  ·
                    refine ⟨299704109410857293153245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1598421916857905563483973 299704109410857293153245)
                    ·
                      rfl

theorem cell23_1751015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_1751015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751015 prefixEnd_1751015 := by exact prefixLift 1751015
  have htrace : WordTrace (prefixWord ++ tailWord_1751015) baseStart_1751015 baseEnd_1751015 := by
    simpa [prefixWord, tailWord_1751015, baseEnd_1751015] using wordTrace_append hprefix tailTrace_1751015
  have hstable : (prefixWord ++ tailWord_1751015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751015).length < 2 ^ (prefixWord ++ tailWord_1751015).sum := by decide
  have hdescent : baseEnd_1751015 < baseStart_1751015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751048 : List Nat := [2, 1, 3, 2, 1, 2, 4, 1, 2, 3, 2]
def baseStart_1751048 : Nat := 118140960795 + 1751048 * 2 ^ 59
def prefixEnd_1751048 : Nat := 4983230072969 + 3 ^ 40 * 1751048 * 2
def baseEnd_1751048 : Nat := 899129273094170250347083

theorem tailTrace_1751048 : CollatzResearch.WordTrace tailWord_1751048 prefixEnd_1751048 899129273094170250347083 := by
  unfold tailWord_1751048
  simp only [CollatzResearch.WordTrace]
  refine ⟨31932983680129813017254899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42577311573506417356339865 31932983680129813017254899)
  ·
    refine ⟨47899475520194719525882349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31932983680129813017254899 47899475520194719525882349)
    ·
      refine ⟨17962303320073019822205881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47899475520194719525882349 17962303320073019822205881)
      ·
        refine ⟨13471727490054764866654411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17962303320073019822205881 13471727490054764866654411)
        ·
          refine ⟨20207591235082147299981617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13471727490054764866654411 20207591235082147299981617)
          ·
            refine ⟨15155693426311610474986213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20207591235082147299981617 15155693426311610474986213)
            ·
              refine ⟨2841692517433426964059915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15155693426311610474986213 2841692517433426964059915)
              ·
                refine ⟨4262538776150140446089873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2841692517433426964059915 4262538776150140446089873)
                ·
                  refine ⟨3196904082112605334567405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4262538776150140446089873 3196904082112605334567405)
                  ·
                    refine ⟨1198839030792227000462777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3196904082112605334567405 1198839030792227000462777)
                    ·
                      refine ⟨899129273094170250347083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1198839030792227000462777 899129273094170250347083)
                      ·
                        rfl

theorem cell23_1751048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_1751048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751048 prefixEnd_1751048 := by exact prefixLift 1751048
  have htrace : WordTrace (prefixWord ++ tailWord_1751048) baseStart_1751048 baseEnd_1751048 := by
    simpa [prefixWord, tailWord_1751048, baseEnd_1751048] using wordTrace_append hprefix tailTrace_1751048
  have hstable : (prefixWord ++ tailWord_1751048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751048).length < 2 ^ (prefixWord ++ tailWord_1751048).sum := by decide
  have hdescent : baseEnd_1751048 < baseStart_1751048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751101 : List Nat := [1, 4, 1, 3, 1, 1, 5, 7]
def baseStart_1751101 : Nat := 118140960795 + 1751101 * 2 ^ 59
def prefixEnd_1751101 : Nat := 4983230072969 + 3 ^ 40 * 1751101 * 2
def baseEnd_1751101 : Nat := 33302092132179946036457

theorem tailTrace_1751101 : CollatzResearch.WordTrace tailWord_1751101 prefixEnd_1751101 33302092132179946036457 := by
  unfold tailWord_1751101
  simp only [CollatzResearch.WordTrace]
  refine ⟨63867900429067616086189157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42578600286045077390792771 63867900429067616086189157)
  ·
    refine ⟨11975231330450178016160467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63867900429067616086189157 11975231330450178016160467)
    ·
      refine ⟨17962846995675267024240701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11975231330450178016160467 17962846995675267024240701)
      ·
        refine ⟨6736067623378225134090263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17962846995675267024240701 6736067623378225134090263)
        ·
          refine ⟨10104101435067337701135395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6736067623378225134090263 10104101435067337701135395)
          ·
            refine ⟨15156152152601006551703093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10104101435067337701135395 15156152152601006551703093)
            ·
              refine ⟨1420889264306344364222165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15156152152601006551703093 1420889264306344364222165)
              ·
                refine ⟨33302092132179946036457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1420889264306344364222165 33302092132179946036457)
                ·
                  rfl

theorem cell23_1751101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 7].length) (baseStart_1751101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751101 prefixEnd_1751101 := by exact prefixLift 1751101
  have htrace : WordTrace (prefixWord ++ tailWord_1751101) baseStart_1751101 baseEnd_1751101 := by
    simpa [prefixWord, tailWord_1751101, baseEnd_1751101] using wordTrace_append hprefix tailTrace_1751101
  have hstable : (prefixWord ++ tailWord_1751101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751101).length < 2 ^ (prefixWord ++ tailWord_1751101).sum := by decide
  have hdescent : baseEnd_1751101 < baseStart_1751101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751111 : List Nat := [1, 1, 4, 1, 3, 1, 1, 4, 1, 3, 3]
def baseStart_1751111 : Nat := 118140960795 + 1751111 * 2 ^ 59
def prefixEnd_1751111 : Nat := 4983230072969 + 3 ^ 40 * 1751111 * 2
def baseEnd_1751111 : Nat := 899161622375403503859293

theorem tailTrace_1751111 : CollatzResearch.WordTrace tailWord_1751111 prefixEnd_1751111 899161622375403503859293 := by
  unfold tailWord_1751111
  simp only [CollatzResearch.WordTrace]
  refine ⟨63868265159031387794053187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42578843439354258529368791 63868265159031387794053187)
  ·
    refine ⟨95802397738547081691079781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63868265159031387794053187 95802397738547081691079781)
    ·
      refine ⟨17962949575977577817077459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95802397738547081691079781 17962949575977577817077459)
      ·
        refine ⟨26944424363966366725616189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17962949575977577817077459 26944424363966366725616189)
        ·
          refine ⟨10104159136487387522106071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26944424363966366725616189 10104159136487387522106071)
          ·
            refine ⟨15156238704731081283159107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10104159136487387522106071 15156238704731081283159107)
            ·
              refine ⟨22734358057096621924738661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15156238704731081283159107 22734358057096621924738661)
              ·
                refine ⟨4262692135705616610888499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22734358057096621924738661 4262692135705616610888499)
                ·
                  refine ⟨6394038203558424916332749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4262692135705616610888499 6394038203558424916332749)
                  ·
                    refine ⟨2397764326334409343624781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6394038203558424916332749 2397764326334409343624781)
                    ·
                      refine ⟨899161622375403503859293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2397764326334409343624781 899161622375403503859293)
                      ·
                        rfl

theorem cell23_1751111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_1751111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751111 prefixEnd_1751111 := by exact prefixLift 1751111
  have htrace : WordTrace (prefixWord ++ tailWord_1751111) baseStart_1751111 baseEnd_1751111 := by
    simpa [prefixWord, tailWord_1751111, baseEnd_1751111] using wordTrace_append hprefix tailTrace_1751111
  have hstable : (prefixWord ++ tailWord_1751111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751111).length < 2 ^ (prefixWord ++ tailWord_1751111).sum := by decide
  have hdescent : baseEnd_1751111 < baseStart_1751111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751122 : List Nat := [3, 2, 2, 1, 5, 1, 1, 2, 2, 4]
def baseStart_1751122 : Nat := 118140960795 + 1751122 * 2 ^ 59
def prefixEnd_1751122 : Nat := 4983230072969 + 3 ^ 40 * 1751122 * 2
def baseEnd_1751122 : Nat := 299722423554200986940581

theorem tailTrace_1751122 : CollatzResearch.WordTrace tailWord_1751122 prefixEnd_1751122 299722423554200986940581 := by
  unfold tailWord_1751122
  simp only [CollatzResearch.WordTrace]
  refine ⟨15967166590497884168175905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42579110907994357781802413 15967166590497884168175905)
  ·
    refine ⟨11975374942873413126131929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15967166590497884168175905 11975374942873413126131929)
    ·
      refine ⟨8981531207155059844598947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11975374942873413126131929 8981531207155059844598947)
      ·
        refine ⟨13472296810732589766898421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8981531207155059844598947 13472296810732589766898421)
        ·
          refine ⟨1263027826006180290646727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13472296810732589766898421 1263027826006180290646727)
          ·
            refine ⟨1894541739009270435970091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1263027826006180290646727 1894541739009270435970091)
            ·
              refine ⟨2841812608513905653955137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1894541739009270435970091 2841812608513905653955137)
              ·
                refine ⟨2131359456385429240466353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2841812608513905653955137 2131359456385429240466353)
                ·
                  refine ⟨1598519592289071930349765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2131359456385429240466353 1598519592289071930349765)
                  ·
                    refine ⟨299722423554200986940581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1598519592289071930349765 299722423554200986940581)
                    ·
                      rfl

theorem cell23_1751122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_1751122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751122 prefixEnd_1751122 := by exact prefixLift 1751122
  have htrace : WordTrace (prefixWord ++ tailWord_1751122) baseStart_1751122 baseEnd_1751122 := by
    simpa [prefixWord, tailWord_1751122, baseEnd_1751122] using wordTrace_append hprefix tailTrace_1751122
  have hstable : (prefixWord ++ tailWord_1751122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751122).length < 2 ^ (prefixWord ++ tailWord_1751122).sum := by decide
  have hdescent : baseEnd_1751122 < baseStart_1751122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751128 : List Nat := [2, 1, 2, 2, 1, 5, 1, 1, 4, 1, 3]
def baseStart_1751128 : Nat := 118140960795 + 1751128 * 2 ^ 59
def prefixEnd_1751128 : Nat := 4983230072969 + 3 ^ 40 * 1751128 * 2
def baseEnd_1751128 : Nat := 899170351546529937346715

theorem tailTrace_1751128 : CollatzResearch.WordTrace tailWord_1751128 prefixEnd_1751128 899170351546529937346715 := by
  unfold tailWord_1751128
  simp only [CollatzResearch.WordTrace]
  refine ⟨31934442599984899848711019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42579256799979866464948025 31934442599984899848711019)
  ·
    refine ⟨47901663899977349773066529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31934442599984899848711019 47901663899977349773066529)
    ·
      refine ⟨35926247924983012329799897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47901663899977349773066529 35926247924983012329799897)
      ·
        refine ⟨26944685943737259247349923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35926247924983012329799897 26944685943737259247349923)
        ·
          refine ⟨40417028915605888871024885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26944685943737259247349923 40417028915605888871024885)
          ·
            refine ⟨3789096460838052081658583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40417028915605888871024885 3789096460838052081658583)
            ·
              refine ⟨5683644691257078122487875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3789096460838052081658583 5683644691257078122487875)
              ·
                refine ⟨8525467036885617183731813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5683644691257078122487875 8525467036885617183731813)
                ·
                  refine ⟨1598525069416053221949715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8525467036885617183731813 1598525069416053221949715)
                  ·
                    refine ⟨2397787604124079832924573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1598525069416053221949715 2397787604124079832924573)
                    ·
                      refine ⟨899170351546529937346715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2397787604124079832924573 899170351546529937346715)
                      ·
                        rfl

theorem cell23_1751128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_1751128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751128 prefixEnd_1751128 := by exact prefixLift 1751128
  have htrace : WordTrace (prefixWord ++ tailWord_1751128) baseStart_1751128 baseEnd_1751128 := by
    simpa [prefixWord, tailWord_1751128, baseEnd_1751128] using wordTrace_append hprefix tailTrace_1751128
  have hstable : (prefixWord ++ tailWord_1751128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751128).length < 2 ^ (prefixWord ++ tailWord_1751128).sum := by decide
  have hdescent : baseEnd_1751128 < baseStart_1751128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751145 : List Nat := [1, 2, 1, 1, 1, 5, 5, 1, 2, 1, 3]
def baseStart_1751145 : Nat := 118140960795 + 1751145 * 2 ^ 59
def prefixEnd_1751145 : Nat := 4983230072969 + 3 ^ 40 * 1751145 * 2
def baseEnd_1751145 : Nat := 899179080717656370834137

theorem tailTrace_1751145 : CollatzResearch.WordTrace tailWord_1751145 prefixEnd_1751145 899179080717656370834137 := by
  unfold tailWord_1751145
  simp only [CollatzResearch.WordTrace]
  refine ⟨63869505240908211600790889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42579670160605474400527259 63869505240908211600790889)
  ·
    refine ⟨47902128930681158700593167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63869505240908211600790889 47902128930681158700593167)
    ·
      refine ⟨71853193396021738050889751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47902128930681158700593167 71853193396021738050889751)
      ·
        refine ⟨107779790094032607076334627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71853193396021738050889751 107779790094032607076334627)
        ·
          refine ⟨161669685141048910614501941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107779790094032607076334627 161669685141048910614501941)
          ·
            refine ⟨15156532981973335370109557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 161669685141048910614501941 15156532981973335370109557)
            ·
              refine ⟨1420924967060000190947771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15156532981973335370109557 1420924967060000190947771)
              ·
                refine ⟨2131387450590000286421657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1420924967060000190947771 2131387450590000286421657)
                ·
                  refine ⟨1598540587942500214816243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2131387450590000286421657 1598540587942500214816243)
                  ·
                    refine ⟨2397810881913750322224365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1598540587942500214816243 2397810881913750322224365)
                    ·
                      refine ⟨899179080717656370834137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2397810881913750322224365 899179080717656370834137)
                      ·
                        rfl

theorem cell23_1751145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 2, 1, 3].length) (baseStart_1751145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751145 prefixEnd_1751145 := by exact prefixLift 1751145
  have htrace : WordTrace (prefixWord ++ tailWord_1751145) baseStart_1751145 baseEnd_1751145 := by
    simpa [prefixWord, tailWord_1751145, baseEnd_1751145] using wordTrace_append hprefix tailTrace_1751145
  have hstable : (prefixWord ++ tailWord_1751145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751145).length < 2 ^ (prefixWord ++ tailWord_1751145).sum := by decide
  have hdescent : baseEnd_1751145 < baseStart_1751145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751171 : List Nat := [1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 5]
def baseStart_1751171 : Nat := 118140960795 + 1751171 * 2 ^ 59
def prefixEnd_1751171 : Nat := 4983230072969 + 3 ^ 40 * 1751171 * 2
def baseEnd_1751171 : Nat := 899192431214673269109017

theorem tailTrace_1751171 : CollatzResearch.WordTrace tailWord_1751171 prefixEnd_1751171 899192431214673269109017 := by
  unfold tailWord_1751171
  simp only [CollatzResearch.WordTrace]
  refine ⟨63870453538814018041237367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42580302359209345360824911 63870453538814018041237367)
  ·
    refine ⟨95805680308221027061856051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63870453538814018041237367 95805680308221027061856051)
    ·
      refine ⟨143708520462331540592784077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95805680308221027061856051 143708520462331540592784077)
      ·
        refine ⟨53890695173374327722294029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143708520462331540592784077 53890695173374327722294029)
        ·
          refine ⟨20209010690015372895860261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53890695173374327722294029 20209010690015372895860261)
          ·
            refine ⟨3789189504377882417973799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20209010690015372895860261 3789189504377882417973799)
            ·
              refine ⟨5683784256566823626960699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3789189504377882417973799 5683784256566823626960699)
              ·
                refine ⟨8525676384850235440441049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5683784256566823626960699 8525676384850235440441049)
                ·
                  refine ⟨6394257288637676580330787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8525676384850235440441049 6394257288637676580330787)
                  ·
                    refine ⟨9591385932956514870496181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6394257288637676580330787 9591385932956514870496181)
                    ·
                      refine ⟨899192431214673269109017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9591385932956514870496181 899192431214673269109017)
                      ·
                        rfl

theorem cell23_1751171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_1751171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751171 prefixEnd_1751171 := by exact prefixLift 1751171
  have htrace : WordTrace (prefixWord ++ tailWord_1751171) baseStart_1751171 baseEnd_1751171 := by
    simpa [prefixWord, tailWord_1751171, baseEnd_1751171] using wordTrace_append hprefix tailTrace_1751171
  have hstable : (prefixWord ++ tailWord_1751171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751171).length < 2 ^ (prefixWord ++ tailWord_1751171).sum := by decide
  have hdescent : baseEnd_1751171 < baseStart_1751171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751184 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 7]
def baseStart_1751184 : Nat := 118140960795 + 1751184 * 2 ^ 59
def prefixEnd_1751184 : Nat := 4983230072969 + 3 ^ 40 * 1751184 * 2
def baseEnd_1751184 : Nat := 899199106463181718246457

theorem tailTrace_1751184 : CollatzResearch.WordTrace tailWord_1751184 prefixEnd_1751184 899199106463181718246457 := by
  unfold tailWord_1751184
  simp only [CollatzResearch.WordTrace]
  refine ⟨31935463843883460630730303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42580618458511280840973737 31935463843883460630730303)
  ·
    refine ⟨47903195765825190946095455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31935463843883460630730303 47903195765825190946095455)
    ·
      refine ⟨71854793648737786419143183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47903195765825190946095455 71854793648737786419143183)
      ·
        refine ⟨107782190473106679628714775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71854793648737786419143183 107782190473106679628714775)
        ·
          refine ⟨161673285709660019443072163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107782190473106679628714775 161673285709660019443072163)
          ·
            refine ⟨242509928564490029164608245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161673285709660019443072163 242509928564490029164608245)
            ·
              refine ⟨22735305802920940234182023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 242509928564490029164608245 22735305802920940234182023)
              ·
                refine ⟨34102958704381410351273035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22735305802920940234182023 34102958704381410351273035)
                ·
                  refine ⟨51154438056572115526909553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34102958704381410351273035 51154438056572115526909553)
                  ·
                    refine ⟨38365828542429086645182165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51154438056572115526909553 38365828542429086645182165)
                    ·
                      refine ⟨899199106463181718246457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 38365828542429086645182165 899199106463181718246457)
                      ·
                        rfl

theorem cell23_1751184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 7].length) (baseStart_1751184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751184 prefixEnd_1751184 := by exact prefixLift 1751184
  have htrace : WordTrace (prefixWord ++ tailWord_1751184) baseStart_1751184 baseEnd_1751184 := by
    simpa [prefixWord, tailWord_1751184, baseEnd_1751184] using wordTrace_append hprefix tailTrace_1751184
  have hstable : (prefixWord ++ tailWord_1751184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751184).length < 2 ^ (prefixWord ++ tailWord_1751184).sum := by decide
  have hdescent : baseEnd_1751184 < baseStart_1751184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751190 : List Nat := [5, 3, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_1751190 : Nat := 118140960795 + 1751190 * 2 ^ 59
def prefixEnd_1751190 : Nat := 4983230072969 + 3 ^ 40 * 1751190 * 2
def baseEnd_1751190 : Nat := 299734062449036231590477

theorem tailTrace_1751190 : CollatzResearch.WordTrace tailWord_1751190 prefixEnd_1751190 299734062449036231590477 := by
  unfold tailWord_1751190
  simp only [CollatzResearch.WordTrace]
  refine ⟨3991946657859074017886189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42580764350496789524119349 3991946657859074017886189)
  ·
    refine ⟨1496979996697152756707321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3991946657859074017886189 1496979996697152756707321)
    ·
      refine ⟨1122734997522864567530491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1496979996697152756707321 1122734997522864567530491)
      ·
        refine ⟨1684102496284296851295737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1122734997522864567530491 1684102496284296851295737)
        ·
          refine ⟨1263076872213222638471803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1684102496284296851295737 1263076872213222638471803)
          ·
            refine ⟨1894615308319833957707705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1263076872213222638471803 1894615308319833957707705)
            ·
              refine ⟨1420961481239875468280779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1894615308319833957707705 1420961481239875468280779)
              ·
                refine ⟨2131442221859813202421169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1420961481239875468280779 2131442221859813202421169)
                ·
                  refine ⟨1598581666394859901815877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2131442221859813202421169 1598581666394859901815877)
                  ·
                    refine ⟨299734062449036231590477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1598581666394859901815877 299734062449036231590477)
                    ·
                      rfl

theorem cell23_1751190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_1751190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751190 prefixEnd_1751190 := by exact prefixLift 1751190
  have htrace : WordTrace (prefixWord ++ tailWord_1751190) baseStart_1751190 baseEnd_1751190 := by
    simpa [prefixWord, tailWord_1751190, baseEnd_1751190] using wordTrace_append hprefix tailTrace_1751190
  have hstable : (prefixWord ++ tailWord_1751190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751190).length < 2 ^ (prefixWord ++ tailWord_1751190).sum := by decide
  have hdescent : baseEnd_1751190 < baseStart_1751190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751241 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 4, 1, 4]
def baseStart_1751241 : Nat := 118140960795 + 1751241 * 2 ^ 59
def prefixEnd_1751241 : Nat := 4983230072969 + 3 ^ 40 * 1751241 * 2
def baseEnd_1751241 : Nat := 899228374860487995233695

theorem tailTrace_1751241 : CollatzResearch.WordTrace tailWord_1751241 prefixEnd_1751241 899228374860487995233695 := by
  unfold tailWord_1751241
  simp only [CollatzResearch.WordTrace]
  refine ⟨63873006648560419996285577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42582004432373613330857051 63873006648560419996285577)
  ·
    refine ⟨47904754986420314997214183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63873006648560419996285577 47904754986420314997214183)
    ·
      refine ⟨71857132479630472495821275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47904754986420314997214183 71857132479630472495821275)
      ·
        refine ⟨107785698719445708743731913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71857132479630472495821275 107785698719445708743731913)
        ·
          refine ⟨80839274039584281557798935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107785698719445708743731913 80839274039584281557798935)
          ·
            refine ⟨121258911059376422336698403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80839274039584281557798935 121258911059376422336698403)
            ·
              refine ⟨181888366589064633505047605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121258911059376422336698403 181888366589064633505047605)
              ·
                refine ⟨17052034367724809391098213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181888366589064633505047605 17052034367724809391098213)
                ·
                  refine ⟨3197256443948401760830915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17052034367724809391098213 3197256443948401760830915)
                  ·
                    refine ⟨4795884665922602641246373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3197256443948401760830915 4795884665922602641246373)
                    ·
                      refine ⟨899228374860487995233695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4795884665922602641246373 899228374860487995233695)
                      ·
                        rfl

theorem cell23_1751241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 1, 4].length) (baseStart_1751241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751241 prefixEnd_1751241 := by exact prefixLift 1751241
  have htrace : WordTrace (prefixWord ++ tailWord_1751241) baseStart_1751241 baseEnd_1751241 := by
    simpa [prefixWord, tailWord_1751241, baseEnd_1751241] using wordTrace_append hprefix tailTrace_1751241
  have hstable : (prefixWord ++ tailWord_1751241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751241).length < 2 ^ (prefixWord ++ tailWord_1751241).sum := by decide
  have hdescent : baseEnd_1751241 < baseStart_1751241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751258 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 1, 6, 2]
def baseStart_1751258 : Nat := 118140960795 + 1751258 * 2 ^ 59
def prefixEnd_1751258 : Nat := 4983230072969 + 3 ^ 40 * 1751258 * 2
def baseEnd_1751258 : Nat := 899237104031614428721117

theorem tailTrace_1751258 : CollatzResearch.WordTrace tailWord_1751258 prefixEnd_1751258 899237104031614428721117 := by
  unfold tailWord_1751258
  simp only [CollatzResearch.WordTrace]
  refine ⟨15968406672374707974913607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42582417792999221266436285 15968406672374707974913607)
  ·
    refine ⟨23952610008562061962370411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15968406672374707974913607 23952610008562061962370411)
    ·
      refine ⟨35928915012843092943555617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23952610008562061962370411 35928915012843092943555617)
      ·
        refine ⟨26946686259632319707666713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35928915012843092943555617 26946686259632319707666713)
        ·
          refine ⟨20210014694724239780750035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26946686259632319707666713 20210014694724239780750035)
          ·
            refine ⟨30315022042086359671125053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20210014694724239780750035 30315022042086359671125053)
            ·
              refine ⟨11368133265782384876671895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30315022042086359671125053 11368133265782384876671895)
              ·
                refine ⟨17052199898673577315007843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11368133265782384876671895 17052199898673577315007843)
                ·
                  refine ⟨25578299848010365972511765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17052199898673577315007843 25578299848010365972511765)
                  ·
                    refine ⟨1198982805375485904961489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25578299848010365972511765 1198982805375485904961489)
                    ·
                      refine ⟨899237104031614428721117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1198982805375485904961489 899237104031614428721117)
                      ·
                        rfl

theorem cell23_1751258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 1, 6, 2].length) (baseStart_1751258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751258 prefixEnd_1751258 := by exact prefixLift 1751258
  have htrace : WordTrace (prefixWord ++ tailWord_1751258) baseStart_1751258 baseEnd_1751258 := by
    simpa [prefixWord, tailWord_1751258, baseEnd_1751258] using wordTrace_append hprefix tailTrace_1751258
  have hstable : (prefixWord ++ tailWord_1751258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751258).length < 2 ^ (prefixWord ++ tailWord_1751258).sum := by decide
  have hdescent : baseEnd_1751258 < baseStart_1751258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751291 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 3, 7, 3]
def baseStart_1751291 : Nat := 118140960795 + 1751291 * 2 ^ 59
def prefixEnd_1751291 : Nat := 4983230072969 + 3 ^ 40 * 1751291 * 2
def baseEnd_1751291 : Nat := 899254048893212799608465

theorem tailTrace_1751291 : CollatzResearch.WordTrace tailWord_1751291 prefixEnd_1751291 899254048893212799608465 := by
  unfold tailWord_1751291
  simp only [CollatzResearch.WordTrace]
  refine ⟨63874830298379278535605727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42583220198919519023737151 63874830298379278535605727)
  ·
    refine ⟨95812245447568917803408591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63874830298379278535605727 95812245447568917803408591)
    ·
      refine ⟨143718368171353376705112887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95812245447568917803408591 143718368171353376705112887)
      ·
        refine ⟨215577552257030065057669331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143718368171353376705112887 215577552257030065057669331)
        ·
          refine ⟨323366328385545097586503997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215577552257030065057669331 323366328385545097586503997)
          ·
            refine ⟨121262373144579411594938999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 323366328385545097586503997 121262373144579411594938999)
            ·
              refine ⟨181893559716869117392408499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121262373144579411594938999 181893559716869117392408499)
              ·
                refine ⟨272840339575303676088612749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181893559716869117392408499 272840339575303676088612749)
                ·
                  refine ⟨102315127340738878533229781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 272840339575303676088612749 102315127340738878533229781)
                  ·
                    refine ⟨2398010797048567465622573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 102315127340738878533229781 2398010797048567465622573)
                    ·
                      refine ⟨899254048893212799608465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2398010797048567465622573 899254048893212799608465)
                      ·
                        rfl

theorem cell23_1751291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 7, 3].length) (baseStart_1751291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751291 prefixEnd_1751291 := by exact prefixLift 1751291
  have htrace : WordTrace (prefixWord ++ tailWord_1751291) baseStart_1751291 baseEnd_1751291 := by
    simpa [prefixWord, tailWord_1751291, baseEnd_1751291] using wordTrace_append hprefix tailTrace_1751291
  have hstable : (prefixWord ++ tailWord_1751291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751291).length < 2 ^ (prefixWord ++ tailWord_1751291).sum := by decide
  have hdescent : baseEnd_1751291 < baseStart_1751291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751311 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 5, 5]
def baseStart_1751311 : Nat := 118140960795 + 1751311 * 2 ^ 59
def prefixEnd_1751311 : Nat := 4983230072969 + 3 ^ 40 * 1751311 * 2
def baseEnd_1751311 : Nat := 299754772835434240452791

theorem tailTrace_1751311 : CollatzResearch.WordTrace tailWord_1751311 prefixEnd_1751311 299754772835434240452791 := by
  unfold tailWord_1751311
  simp only [CollatzResearch.WordTrace]
  refine ⟨63875559758306821951333787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42583706505537881300889191 63875559758306821951333787)
  ·
    refine ⟨95813339637460232927000681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63875559758306821951333787 95813339637460232927000681)
    ·
      refine ⟨71860004728095174695250511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95813339637460232927000681 71860004728095174695250511)
      ·
        refine ⟨107790007092142762042875767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71860004728095174695250511 107790007092142762042875767)
        ·
          refine ⟨161685010638214143064313651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107790007092142762042875767 161685010638214143064313651)
          ·
            refine ⟨242527515957321214596470477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161685010638214143064313651 242527515957321214596470477)
            ·
              refine ⟨90947818483995455473676429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242527515957321214596470477 90947818483995455473676429)
              ·
                refine ⟨34105431931498295802628661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90947818483995455473676429 34105431931498295802628661)
                ·
                  refine ⟨3197384243577965231496437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34105431931498295802628661 3197384243577965231496437)
                  ·
                    refine ⟨299754772835434240452791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3197384243577965231496437 299754772835434240452791)
                    ·
                      rfl

theorem cell23_1751311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 5].length) (baseStart_1751311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751311 prefixEnd_1751311 := by exact prefixLift 1751311
  have htrace : WordTrace (prefixWord ++ tailWord_1751311) baseStart_1751311 baseEnd_1751311 := by
    simpa [prefixWord, tailWord_1751311, baseEnd_1751311] using wordTrace_append hprefix tailTrace_1751311
  have hstable : (prefixWord ++ tailWord_1751311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751311).length < 2 ^ (prefixWord ++ tailWord_1751311).sum := by decide
  have hdescent : baseEnd_1751311 < baseStart_1751311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751336 : List Nat := [2, 1, 5, 1, 4, 1, 1, 3, 1, 4]
def baseStart_1751336 : Nat := 118140960795 + 1751336 * 2 ^ 59
def prefixEnd_1751336 : Nat := 4983230072969 + 3 ^ 40 * 1751336 * 2
def baseEnd_1751336 : Nat := 299759051840888374515253

theorem tailTrace_1751336 : CollatzResearch.WordTrace tailWord_1751336 prefixEnd_1751336 299759051840888374515253 := by
  unfold tailWord_1751336
  simp only [CollatzResearch.WordTrace]
  refine ⟨31938235791608125610496931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42584314388810834147329241 31938235791608125610496931)
  ·
    refine ⟨47907353687412188415745397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31938235791608125610496931 47907353687412188415745397)
    ·
      refine ⟨4491314408194892663976131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47907353687412188415745397 4491314408194892663976131)
      ·
        refine ⟨6736971612292338995964197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4491314408194892663976131 6736971612292338995964197)
        ·
          refine ⟨1263182177304813561743287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6736971612292338995964197 1263182177304813561743287)
          ·
            refine ⟨1894773265957220342614931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1263182177304813561743287 1894773265957220342614931)
            ·
              refine ⟨2842159898935830513922397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1894773265957220342614931 2842159898935830513922397)
              ·
                refine ⟨1065809962100936442720899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2842159898935830513922397 1065809962100936442720899)
                ·
                  refine ⟨1598714943151404664081349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1065809962100936442720899 1598714943151404664081349)
                  ·
                    refine ⟨299759051840888374515253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1598714943151404664081349 299759051840888374515253)
                    ·
                      rfl

theorem cell23_1751336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_1751336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751336 prefixEnd_1751336 := by exact prefixLift 1751336
  have htrace : WordTrace (prefixWord ++ tailWord_1751336) baseStart_1751336 baseEnd_1751336 := by
    simpa [prefixWord, tailWord_1751336, baseEnd_1751336] using wordTrace_append hprefix tailTrace_1751336
  have hstable : (prefixWord ++ tailWord_1751336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751336).length < 2 ^ (prefixWord ++ tailWord_1751336).sum := by decide
  have hdescent : baseEnd_1751336 < baseStart_1751336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751359 : List Nat := [1, 1, 2, 2, 4, 1, 5, 2, 1, 1, 3]
def baseStart_1751359 : Nat := 118140960795 + 1751359 * 2 ^ 59
def prefixEnd_1751359 : Nat := 4983230072969 + 3 ^ 40 * 1751359 * 2
def baseEnd_1751359 : Nat := 899288965577718533558153

theorem tailTrace_1751359 : CollatzResearch.WordTrace tailWord_1751359 prefixEnd_1751359 899288965577718533558153 := by
  unfold tailWord_1751359
  simp only [CollatzResearch.WordTrace]
  refine ⟨63877310462132926149081131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42584873641421950766054087 63877310462132926149081131)
  ·
    refine ⟨95815965693199389223621697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63877310462132926149081131 95815965693199389223621697)
    ·
      refine ⟨71861974269899541917716273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95815965693199389223621697 71861974269899541917716273)
      ·
        refine ⟨53896480702424656438287205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71861974269899541917716273 53896480702424656438287205)
        ·
          refine ⟨10105590131704623082178851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53896480702424656438287205 10105590131704623082178851)
          ·
            refine ⟨15158385197556934623268277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10105590131704623082178851 15158385197556934623268277)
            ·
              refine ⟨1421098612270962620931401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15158385197556934623268277 1421098612270962620931401)
              ·
                refine ⟨1065823959203221965698551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1421098612270962620931401 1065823959203221965698551)
                ·
                  refine ⟨1598735938804832948547827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1065823959203221965698551 1598735938804832948547827)
                  ·
                    refine ⟨2398103908207249422821741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1598735938804832948547827 2398103908207249422821741)
                    ·
                      refine ⟨899288965577718533558153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2398103908207249422821741 899288965577718533558153)
                      ·
                        rfl

theorem cell23_1751359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 2, 1, 1, 3].length) (baseStart_1751359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751359 prefixEnd_1751359 := by exact prefixLift 1751359
  have htrace : WordTrace (prefixWord ++ tailWord_1751359) baseStart_1751359 baseEnd_1751359 := by
    simpa [prefixWord, tailWord_1751359, baseEnd_1751359] using wordTrace_append hprefix tailTrace_1751359
  have hstable : (prefixWord ++ tailWord_1751359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751359).length < 2 ^ (prefixWord ++ tailWord_1751359).sum := by decide
  have hdescent : baseEnd_1751359 < baseStart_1751359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751368 : List Nat := [2, 1, 3, 1, 1, 2, 4, 2, 1, 1, 5]
def baseStart_1751368 : Nat := 118140960795 + 1751368 * 2 ^ 59
def prefixEnd_1751368 : Nat := 4983230072969 + 3 ^ 40 * 1751368 * 2
def baseEnd_1751368 : Nat := 899293586903608998345611

theorem tailTrace_1751368 : CollatzResearch.WordTrace tailWord_1751368 prefixEnd_1751368 899293586903608998345611 := by
  unfold tailWord_1751368
  simp only [CollatzResearch.WordTrace]
  refine ⟨31938819359550160343079379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42585092479400213790772505 31938819359550160343079379)
  ·
    refine ⟨47908229039325240514619069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31938819359550160343079379 47908229039325240514619069)
    ·
      refine ⟨17965585889746965192982151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47908229039325240514619069 17965585889746965192982151)
      ·
        refine ⟨26948378834620447789473227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17965585889746965192982151 26948378834620447789473227)
        ·
          refine ⟨40422568251930671684209841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26948378834620447789473227 40422568251930671684209841)
          ·
            refine ⟨30316926188948003763157381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40422568251930671684209841 30316926188948003763157381)
            ·
              refine ⟨5684423660427750705592009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30316926188948003763157381 5684423660427750705592009)
              ·
                refine ⟨4263317745320813029194007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5684423660427750705592009 4263317745320813029194007)
                ·
                  refine ⟨6394976617981219543791011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4263317745320813029194007 6394976617981219543791011)
                  ·
                    refine ⟨9592464926971829315686517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6394976617981219543791011 9592464926971829315686517)
                    ·
                      refine ⟨899293586903608998345611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9592464926971829315686517 899293586903608998345611)
                      ·
                        rfl

theorem cell23_1751368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_1751368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751368 prefixEnd_1751368 := by exact prefixLift 1751368
  have htrace : WordTrace (prefixWord ++ tailWord_1751368) baseStart_1751368 baseEnd_1751368 := by
    simpa [prefixWord, tailWord_1751368, baseEnd_1751368] using wordTrace_append hprefix tailTrace_1751368
  have hstable : (prefixWord ++ tailWord_1751368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751368).length < 2 ^ (prefixWord ++ tailWord_1751368).sum := by decide
  have hdescent : baseEnd_1751368 < baseStart_1751368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751378 : List Nat := [3, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6]
def baseStart_1751378 : Nat := 118140960795 + 1751378 * 2 ^ 59
def prefixEnd_1751378 : Nat := 4983230072969 + 3 ^ 40 * 1751378 * 2
def baseEnd_1751378 : Nat := 899298721710153959220565

theorem tailTrace_1751378 : CollatzResearch.WordTrace tailWord_1751378 prefixEnd_1751378 899298721710153959220565 := by
  unfold tailWord_1751378
  simp only [CollatzResearch.WordTrace]
  refine ⟨15969500862266023098505697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42585335632709394929348525 15969500862266023098505697)
  ·
    refine ⟨11977125646699517323879273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15969500862266023098505697 11977125646699517323879273)
    ·
      refine ⟨8982844235024637992909455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11977125646699517323879273 8982844235024637992909455)
      ·
        refine ⟨13474266352536956989364183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8982844235024637992909455 13474266352536956989364183)
        ·
          refine ⟨20211399528805435484046275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13474266352536956989364183 20211399528805435484046275)
          ·
            refine ⟨30317099293208153226069413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20211399528805435484046275 30317099293208153226069413)
            ·
              refine ⟨5684456117476528729888015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30317099293208153226069413 5684456117476528729888015)
              ·
                refine ⟨8526684176214793094832023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5684456117476528729888015 8526684176214793094832023)
                ·
                  refine ⟨12790026264322189642248035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8526684176214793094832023 12790026264322189642248035)
                  ·
                    refine ⟨19185039396483284463372053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12790026264322189642248035 19185039396483284463372053)
                    ·
                      refine ⟨899298721710153959220565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19185039396483284463372053 899298721710153959220565)
                      ·
                        rfl

theorem cell23_1751378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_1751378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751378 prefixEnd_1751378 := by exact prefixLift 1751378
  have htrace : WordTrace (prefixWord ++ tailWord_1751378) baseStart_1751378 baseEnd_1751378 := by
    simpa [prefixWord, tailWord_1751378, baseEnd_1751378] using wordTrace_append hprefix tailTrace_1751378
  have hstable : (prefixWord ++ tailWord_1751378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751378).length < 2 ^ (prefixWord ++ tailWord_1751378).sum := by decide
  have hdescent : baseEnd_1751378 < baseStart_1751378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751402 : List Nat := [3, 1, 3, 3, 1, 3, 1, 1, 1, 1, 5]
def baseStart_1751402 : Nat := 118140960795 + 1751402 * 2 ^ 59
def prefixEnd_1751402 : Nat := 4983230072969 + 3 ^ 40 * 1751402 * 2
def baseEnd_1751402 : Nat := 899311045245861865320455

theorem tailTrace_1751402 : CollatzResearch.WordTrace tailWord_1751402 prefixEnd_1751402 899311045245861865320455 := by
  unfold tailWord_1751402
  simp only [CollatzResearch.WordTrace]
  refine ⟨15969719700244286123224115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42585919200651429661930973 15969719700244286123224115)
  ·
    refine ⟨23954579550366429184836173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15969719700244286123224115 23954579550366429184836173)
    ·
      refine ⟨8982967331387410944313565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23954579550366429184836173 8982967331387410944313565)
      ·
        refine ⟨3368612749270279104117587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8982967331387410944313565 3368612749270279104117587)
        ·
          refine ⟨5052919123905418656176381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3368612749270279104117587 5052919123905418656176381)
          ·
            refine ⟨1894844671464531996066143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5052919123905418656176381 1894844671464531996066143)
            ·
              refine ⟨2842267007196797994099215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1894844671464531996066143 2842267007196797994099215)
              ·
                refine ⟨4263400510795196991148823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2842267007196797994099215 4263400510795196991148823)
                ·
                  refine ⟨6395100766192795486723235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4263400510795196991148823 6395100766192795486723235)
                  ·
                    refine ⟨9592651149289193230084853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6395100766192795486723235 9592651149289193230084853)
                    ·
                      refine ⟨899311045245861865320455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9592651149289193230084853 899311045245861865320455)
                      ·
                        rfl

theorem cell23_1751402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_1751402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751402 prefixEnd_1751402 := by exact prefixLift 1751402
  have htrace : WordTrace (prefixWord ++ tailWord_1751402) baseStart_1751402 baseEnd_1751402 := by
    simpa [prefixWord, tailWord_1751402, baseEnd_1751402] using wordTrace_append hprefix tailTrace_1751402
  have hstable : (prefixWord ++ tailWord_1751402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751402).length < 2 ^ (prefixWord ++ tailWord_1751402).sum := by decide
  have hdescent : baseEnd_1751402 < baseStart_1751402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751432 : List Nat := [2, 1, 3, 3, 1, 1, 1, 5, 2, 1, 3]
def baseStart_1751432 : Nat := 118140960795 + 1751432 * 2 ^ 59
def prefixEnd_1751432 : Nat := 4983230072969 + 3 ^ 40 * 1751432 * 2
def baseEnd_1751432 : Nat := 899326449665496747945317

theorem tailTrace_1751432 : CollatzResearch.WordTrace tailWord_1751432 prefixEnd_1751432 899326449665496747945317 := by
  unfold tailWord_1751432
  simp only [CollatzResearch.WordTrace]
  refine ⟨31939986495434229808244275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42586648660578973077659033 31939986495434229808244275)
  ·
    refine ⟨47909979743151344712366413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31939986495434229808244275 47909979743151344712366413)
    ·
      refine ⟨17966242403681754267137405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47909979743151344712366413 17966242403681754267137405)
      ·
        refine ⟨6737340901380657850176527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17966242403681754267137405 6737340901380657850176527)
        ·
          refine ⟨10106011352070986775264791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6737340901380657850176527 10106011352070986775264791)
          ·
            refine ⟨15159017028106480162897187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10106011352070986775264791 15159017028106480162897187)
            ·
              refine ⟨22738525542159720244345781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15159017028106480162897187 22738525542159720244345781)
              ·
                refine ⟨2131736769577473772907417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22738525542159720244345781 2131736769577473772907417)
                ·
                  refine ⟨1598802577183105329680563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2131736769577473772907417 1598802577183105329680563)
                  ·
                    refine ⟨2398203865774657994520845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1598802577183105329680563 2398203865774657994520845)
                    ·
                      refine ⟨899326449665496747945317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2398203865774657994520845 899326449665496747945317)
                      ·
                        rfl

theorem cell23_1751432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_1751432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751432 prefixEnd_1751432 := by exact prefixLift 1751432
  have htrace : WordTrace (prefixWord ++ tailWord_1751432) baseStart_1751432 baseEnd_1751432 := by
    simpa [prefixWord, tailWord_1751432, baseEnd_1751432] using wordTrace_append hprefix tailTrace_1751432
  have hstable : (prefixWord ++ tailWord_1751432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751432).length < 2 ^ (prefixWord ++ tailWord_1751432).sum := by decide
  have hdescent : baseEnd_1751432 < baseStart_1751432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751459 : List Nat := [1, 1, 1, 4, 1, 4, 4, 1, 1, 3, 2]
def baseStart_1751459 : Nat := 118140960795 + 1751459 * 2 ^ 59
def prefixEnd_1751459 : Nat := 4983230072969 + 3 ^ 40 * 1751459 * 2
def baseEnd_1751459 : Nat := 899340313643168142307693

theorem tailTrace_1751459 : CollatzResearch.WordTrace tailWord_1751459 prefixEnd_1751459 899340313643168142307693 := by
  unfold tailWord_1751459
  simp only [CollatzResearch.WordTrace]
  refine ⟨63880957761770643227721431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42587305174513762151814287 63880957761770643227721431)
  ·
    refine ⟨95821436642655964841582147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63880957761770643227721431 95821436642655964841582147)
    ·
      refine ⟨143732154963983947262373221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95821436642655964841582147 143732154963983947262373221)
      ·
        refine ⟨26949779055746990111694979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143732154963983947262373221 26949779055746990111694979)
        ·
          refine ⟨40424668583620485167542469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26949779055746990111694979 40424668583620485167542469)
          ·
            refine ⟨7579625359428840968914213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40424668583620485167542469 7579625359428840968914213)
            ·
              refine ⟨1421179754892907681671415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7579625359428840968914213 1421179754892907681671415)
              ·
                refine ⟨2131769632339361522507123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1421179754892907681671415 2131769632339361522507123)
                ·
                  refine ⟨3197654448509042283760685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2131769632339361522507123 3197654448509042283760685)
                  ·
                    refine ⟨1199120418190890856410257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3197654448509042283760685 1199120418190890856410257)
                    ·
                      refine ⟨899340313643168142307693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1199120418190890856410257 899340313643168142307693)
                      ·
                        rfl

theorem cell23_1751459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 1, 3, 2].length) (baseStart_1751459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751459 prefixEnd_1751459 := by exact prefixLift 1751459
  have htrace : WordTrace (prefixWord ++ tailWord_1751459) baseStart_1751459 baseEnd_1751459 := by
    simpa [prefixWord, tailWord_1751459, baseEnd_1751459] using wordTrace_append hprefix tailTrace_1751459
  have hstable : (prefixWord ++ tailWord_1751459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751459).length < 2 ^ (prefixWord ++ tailWord_1751459).sum := by decide
  have hdescent : baseEnd_1751459 < baseStart_1751459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751485 : List Nat := [1, 4, 1, 2, 2, 2, 2, 1, 2, 2, 4]
def baseStart_1751485 : Nat := 118140960795 + 1751485 * 2 ^ 59
def prefixEnd_1751485 : Nat := 4983230072969 + 3 ^ 40 * 1751485 * 2
def baseEnd_1751485 : Nat := 899353664140185040582573

theorem tailTrace_1751485 : CollatzResearch.WordTrace tailWord_1751485 prefixEnd_1751485 899353664140185040582573 := by
  unfold tailWord_1751485
  simp only [CollatzResearch.WordTrace]
  refine ⟨63881906059676449668167909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42587937373117633112111939 63881906059676449668167909)
  ·
    refine ⟨11977857386189334312781483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63881906059676449668167909 11977857386189334312781483)
    ·
      refine ⟨17966786079284001469172225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11977857386189334312781483 17966786079284001469172225)
      ·
        refine ⟨13475089559463001101879169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17966786079284001469172225 13475089559463001101879169)
        ·
          refine ⟨10106317169597250826409377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13475089559463001101879169 10106317169597250826409377)
          ·
            refine ⟨7579737877197938119807033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10106317169597250826409377 7579737877197938119807033)
            ·
              refine ⟨5684803407898453589855275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7579737877197938119807033 5684803407898453589855275)
              ·
                refine ⟨8527205111847680384782913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5684803407898453589855275 8527205111847680384782913)
                ·
                  refine ⟨6395403833885760288587185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8527205111847680384782913 6395403833885760288587185)
                  ·
                    refine ⟨4796552875414320216440389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6395403833885760288587185 4796552875414320216440389)
                    ·
                      refine ⟨899353664140185040582573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4796552875414320216440389 899353664140185040582573)
                      ·
                        rfl

theorem cell23_1751485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_1751485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751485 prefixEnd_1751485 := by exact prefixLift 1751485
  have htrace : WordTrace (prefixWord ++ tailWord_1751485) baseStart_1751485 baseEnd_1751485 := by
    simpa [prefixWord, tailWord_1751485, baseEnd_1751485] using wordTrace_append hprefix tailTrace_1751485
  have hstable : (prefixWord ++ tailWord_1751485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751485).length < 2 ^ (prefixWord ++ tailWord_1751485).sum := by decide
  have hdescent : baseEnd_1751485 < baseStart_1751485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751555 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 5, 4]
def baseStart_1751555 : Nat := 118140960795 + 1751555 * 2 ^ 59
def prefixEnd_1751555 : Nat := 4983230072969 + 3 ^ 40 * 1751555 * 2
def baseEnd_1751555 : Nat := 299796535928666588902417

theorem tailTrace_1751555 : CollatzResearch.WordTrace tailWord_1751555 prefixEnd_1751555 299796535928666588902417 := by
  unfold tailWord_1751555
  simp only [CollatzResearch.WordTrace]
  refine ⟨63884459169422851623216119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42589639446281901082144079 63884459169422851623216119)
  ·
    refine ⟨95826688754134277434824179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63884459169422851623216119 95826688754134277434824179)
    ·
      refine ⟨143740033131201416152236269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95826688754134277434824179 143740033131201416152236269)
      ·
        refine ⟨53902512424200531057088601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143740033131201416152236269 53902512424200531057088601)
        ·
          refine ⟨40426884318150398292816451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53902512424200531057088601 40426884318150398292816451)
          ·
            refine ⟨60640326477225597439224677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40426884318150398292816451 60640326477225597439224677)
            ·
              refine ⟨11370061214479799519854627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60640326477225597439224677 11370061214479799519854627)
              ·
                refine ⟨17055091821719699279781941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11370061214479799519854627 17055091821719699279781941)
                ·
                  refine ⟨1598914858286221807479557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17055091821719699279781941 1598914858286221807479557)
                  ·
                    refine ⟨299796535928666588902417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1598914858286221807479557 299796535928666588902417)
                    ·
                      rfl

theorem cell23_1751555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 5, 4].length) (baseStart_1751555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751555 prefixEnd_1751555 := by exact prefixLift 1751555
  have htrace : WordTrace (prefixWord ++ tailWord_1751555) baseStart_1751555 baseEnd_1751555 := by
    simpa [prefixWord, tailWord_1751555, baseEnd_1751555] using wordTrace_append hprefix tailTrace_1751555
  have hstable : (prefixWord ++ tailWord_1751555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751555).length < 2 ^ (prefixWord ++ tailWord_1751555).sum := by decide
  have hdescent : baseEnd_1751555 < baseStart_1751555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751562 : List Nat := [3, 1, 2, 2, 2, 1, 4, 1, 2, 1, 4]
def baseStart_1751562 : Nat := 118140960795 + 1751562 * 2 ^ 59
def prefixEnd_1751562 : Nat := 4983230072969 + 3 ^ 40 * 1751562 * 2
def baseEnd_1751562 : Nat := 899393202150581239319719

theorem tailTrace_1751562 : CollatzResearch.WordTrace tailWord_1751562 prefixEnd_1751562 899393202150581239319719 := by
  unfold tailWord_1751562
  simp only [CollatzResearch.WordTrace]
  refine ⟨15971178620099372954680235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42589809653598327879147293 15971178620099372954680235)
  ·
    refine ⟨23956767930149059432020353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15971178620099372954680235 23956767930149059432020353)
    ·
      refine ⟨17967575947611794574015265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23956767930149059432020353 17967575947611794574015265)
      ·
        refine ⟨13475681960708845930511449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17967575947611794574015265 13475681960708845930511449)
        ·
          refine ⟨10106761470531634447883587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13475681960708845930511449 10106761470531634447883587)
          ·
            refine ⟨15160142205797451671825381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10106761470531634447883587 15160142205797451671825381)
            ·
              refine ⟨2842526663587022188467259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15160142205797451671825381 2842526663587022188467259)
              ·
                refine ⟨4263789995380533282700889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2842526663587022188467259 4263789995380533282700889)
                ·
                  refine ⟨3197842496535399962025667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4263789995380533282700889 3197842496535399962025667)
                  ·
                    refine ⟨4796763744803099943038501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3197842496535399962025667 4796763744803099943038501)
                    ·
                      refine ⟨899393202150581239319719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4796763744803099943038501 899393202150581239319719)
                      ·
                        rfl

theorem cell23_1751562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_1751562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751562 prefixEnd_1751562 := by exact prefixLift 1751562
  have htrace : WordTrace (prefixWord ++ tailWord_1751562) baseStart_1751562 baseEnd_1751562 := by
    simpa [prefixWord, tailWord_1751562, baseEnd_1751562] using wordTrace_append hprefix tailTrace_1751562
  have hstable : (prefixWord ++ tailWord_1751562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751562).length < 2 ^ (prefixWord ++ tailWord_1751562).sum := by decide
  have hdescent : baseEnd_1751562 < baseStart_1751562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751615 : List Nat := [1, 1, 2, 2, 3, 2, 1, 3, 3, 5]
def baseStart_1751615 : Nat := 118140960795 + 1751615 * 2 ^ 59
def prefixEnd_1751615 : Nat := 4983230072969 + 3 ^ 40 * 1751615 * 2
def baseEnd_1751615 : Nat := 299806805541756510652325

theorem tailTrace_1751615 : CollatzResearch.WordTrace tailWord_1751615 prefixEnd_1751615 299806805541756510652325 := by
  unfold tailWord_1751615
  simp only [CollatzResearch.WordTrace]
  refine ⟨63886647549205481870400299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42591098366136987913600199 63886647549205481870400299)
  ·
    refine ⟨95829971323808222805600449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63886647549205481870400299 95829971323808222805600449)
    ·
      refine ⟨71872478492856167104200337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95829971323808222805600449 71872478492856167104200337)
      ·
        refine ⟨53904358869642125328150253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71872478492856167104200337 53904358869642125328150253)
        ·
          refine ⟨20214134576115796998056345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53904358869642125328150253 20214134576115796998056345)
          ·
            refine ⟨15160600932086847748542259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20214134576115796998056345 15160600932086847748542259)
            ·
              refine ⟨22740901398130271622813389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15160600932086847748542259 22740901398130271622813389)
              ·
                refine ⟨8527838024298851858555021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22740901398130271622813389 8527838024298851858555021)
                ·
                  refine ⟨3197939259112069446958133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8527838024298851858555021 3197939259112069446958133)
                  ·
                    refine ⟨299806805541756510652325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3197939259112069446958133 299806805541756510652325)
                    ·
                      rfl

theorem cell23_1751615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 5].length) (baseStart_1751615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751615 prefixEnd_1751615 := by exact prefixLift 1751615
  have htrace : WordTrace (prefixWord ++ tailWord_1751615) baseStart_1751615 baseEnd_1751615 := by
    simpa [prefixWord, tailWord_1751615, baseEnd_1751615] using wordTrace_append hprefix tailTrace_1751615
  have hstable : (prefixWord ++ tailWord_1751615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751615).length < 2 ^ (prefixWord ++ tailWord_1751615).sum := by decide
  have hdescent : baseEnd_1751615 < baseStart_1751615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751705 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 2, 7]
def baseStart_1751705 : Nat := 118140960795 + 1751705 * 2 ^ 59
def prefixEnd_1751705 : Nat := 4983230072969 + 3 ^ 40 * 1751705 * 2
def baseEnd_1751705 : Nat := 299822209961391393277187

theorem tailTrace_1751705 : CollatzResearch.WordTrace tailWord_1751705 prefixEnd_1751705 299822209961391393277187 := by
  unfold tailWord_1751705
  simp only [CollatzResearch.WordTrace]
  refine ⟨63889930118879427241176569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42593286745919618160784379 63889930118879427241176569)
  ·
    refine ⟨47917447589159570430882427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63889930118879427241176569 47917447589159570430882427)
    ·
      refine ⟨71876171383739355646323641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47917447589159570430882427 71876171383739355646323641)
      ·
        refine ⟨53907128537804516734742731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71876171383739355646323641 53907128537804516734742731)
        ·
          refine ⟨80860692806706775102114097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53907128537804516734742731 80860692806706775102114097)
          ·
            refine ⟨60645519605030081326585573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80860692806706775102114097 60645519605030081326585573)
            ·
              refine ⟨11371034925943140248734795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60645519605030081326585573 11371034925943140248734795)
              ·
                refine ⟨17056552388914710373102193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11371034925943140248734795 17056552388914710373102193)
                ·
                  refine ⟨12792414291686032779826645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17056552388914710373102193 12792414291686032779826645)
                  ·
                    refine ⟨299822209961391393277187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12792414291686032779826645 299822209961391393277187)
                    ·
                      rfl

theorem cell23_1751705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 7].length) (baseStart_1751705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751705 prefixEnd_1751705 := by exact prefixLift 1751705
  have htrace : WordTrace (prefixWord ++ tailWord_1751705) baseStart_1751705 baseEnd_1751705 := by
    simpa [prefixWord, tailWord_1751705, baseEnd_1751705] using wordTrace_append hprefix tailTrace_1751705
  have hstable : (prefixWord ++ tailWord_1751705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751705).length < 2 ^ (prefixWord ++ tailWord_1751705).sum := by decide
  have hdescent : baseEnd_1751705 < baseStart_1751705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751713 : List Nat := [1, 2, 3, 3, 3, 2, 2, 1, 2, 4]
def baseStart_1751713 : Nat := 118140960795 + 1751713 * 2 ^ 59
def prefixEnd_1751713 : Nat := 4983230072969 + 3 ^ 40 * 1751713 * 2
def baseEnd_1751713 : Nat := 299823579243136716177175

theorem tailTrace_1751713 : CollatzResearch.WordTrace tailWord_1751713 prefixEnd_1751713 299823579243136716177175 := by
  unfold tailWord_1751713
  simp only [CollatzResearch.WordTrace]
  refine ⟨63890221902850444607467793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42593481268566963071645195 63890221902850444607467793)
  ·
    refine ⟨47917666427137833455600845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63890221902850444607467793 47917666427137833455600845)
    ·
      refine ⟨17969124910176687545850317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47917666427137833455600845 17969124910176687545850317)
      ·
        refine ⟨6738421841316257829693869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17969124910176687545850317 6738421841316257829693869)
        ·
          refine ⟨2526908190493596686135201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6738421841316257829693869 2526908190493596686135201)
          ·
            refine ⟨1895181142870197514601401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2526908190493596686135201 1895181142870197514601401)
            ·
              refine ⟨1421385857152648135951051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1895181142870197514601401 1421385857152648135951051)
              ·
                refine ⟨2132078785728972203926577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1421385857152648135951051 2132078785728972203926577)
                ·
                  refine ⟨1599059089296729152944933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2132078785728972203926577 1599059089296729152944933)
                  ·
                    refine ⟨299823579243136716177175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1599059089296729152944933 299823579243136716177175)
                    ·
                      rfl

theorem cell23_1751713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_1751713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751713 prefixEnd_1751713 := by exact prefixLift 1751713
  have htrace : WordTrace (prefixWord ++ tailWord_1751713) baseStart_1751713 baseEnd_1751713 := by
    simpa [prefixWord, tailWord_1751713, baseEnd_1751713] using wordTrace_append hprefix tailTrace_1751713
  have hstable : (prefixWord ++ tailWord_1751713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751713).length < 2 ^ (prefixWord ++ tailWord_1751713).sum := by decide
  have hdescent : baseEnd_1751713 < baseStart_1751713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751715 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 5]
def baseStart_1751715 : Nat := 118140960795 + 1751715 * 2 ^ 59
def prefixEnd_1751715 : Nat := 4983230072969 + 3 ^ 40 * 1751715 * 2
def baseEnd_1751715 : Nat := 899471764690719140706515

theorem tailTrace_1751715 : CollatzResearch.WordTrace tailWord_1751715 prefixEnd_1751715 899471764690719140706515 := by
  unfold tailWord_1751715
  simp only [CollatzResearch.WordTrace]
  refine ⟨63890294848843198949040599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42593529899228799299360399 63890294848843198949040599)
  ·
    refine ⟨95835442273264798423560899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63890294848843198949040599 95835442273264798423560899)
    ·
      refine ⟨143753163409897197635341349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95835442273264798423560899 143753163409897197635341349)
      ·
        refine ⟨26953718139355724556626503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143753163409897197635341349 26953718139355724556626503)
        ·
          refine ⟨40430577209033586834939755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26953718139355724556626503 40430577209033586834939755)
          ·
            refine ⟨60645865813550380252409633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40430577209033586834939755 60645865813550380252409633)
            ·
              refine ⟨45484399360162785189307225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60645865813550380252409633 45484399360162785189307225)
              ·
                refine ⟨34113299520122088891980419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45484399360162785189307225 34113299520122088891980419)
                ·
                  refine ⟨51169949280183133337970629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34113299520122088891980419 51169949280183133337970629)
                  ·
                    refine ⟨9594365490034337500869493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51169949280183133337970629 9594365490034337500869493)
                    ·
                      refine ⟨899471764690719140706515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9594365490034337500869493 899471764690719140706515)
                      ·
                        rfl

theorem cell23_1751715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_1751715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751715 prefixEnd_1751715 := by exact prefixLift 1751715
  have htrace : WordTrace (prefixWord ++ tailWord_1751715) baseStart_1751715 baseEnd_1751715 := by
    simpa [prefixWord, tailWord_1751715, baseEnd_1751715] using wordTrace_append hprefix tailTrace_1751715
  have hstable : (prefixWord ++ tailWord_1751715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751715).length < 2 ^ (prefixWord ++ tailWord_1751715).sum := by decide
  have hdescent : baseEnd_1751715 < baseStart_1751715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751755 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 6]
def baseStart_1751755 : Nat := 118140960795 + 1751755 * 2 ^ 59
def prefixEnd_1751755 : Nat := 4983230072969 + 3 ^ 40 * 1751755 * 2
def baseEnd_1751755 : Nat := 899492303916898984206331

theorem tailTrace_1751755 : CollatzResearch.WordTrace tailWord_1751755 prefixEnd_1751755 899492303916898984206331 := by
  unfold tailWord_1751755
  simp only [CollatzResearch.WordTrace]
  refine ⟨63891753768698285780496719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42594502512465523853664479 63891753768698285780496719)
  ·
    refine ⟨95837630653047428670745079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63891753768698285780496719 95837630653047428670745079)
    ·
      refine ⟨143756445979571143006117619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95837630653047428670745079 143756445979571143006117619)
      ·
        refine ⟨215634668969356714509176429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143756445979571143006117619 215634668969356714509176429)
        ·
          refine ⟨80863000863508767940941161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215634668969356714509176429 80863000863508767940941161)
          ·
            refine ⟨60647250647631575955705871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80863000863508767940941161 60647250647631575955705871)
            ·
              refine ⟨90970875971447363933558807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60647250647631575955705871 90970875971447363933558807)
              ·
                refine ⟨136456313957171045900338211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90970875971447363933558807 136456313957171045900338211)
                ·
                  refine ⟨204684470935756568850507317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136456313957171045900338211 204684470935756568850507317)
                  ·
                    refine ⟨19189169150227178329735061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 204684470935756568850507317 19189169150227178329735061)
                    ·
                      refine ⟨899492303916898984206331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19189169150227178329735061 899492303916898984206331)
                      ·
                        rfl

theorem cell23_1751755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 6].length) (baseStart_1751755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751755 prefixEnd_1751755 := by exact prefixLift 1751755
  have htrace : WordTrace (prefixWord ++ tailWord_1751755) baseStart_1751755 baseEnd_1751755 := by
    simpa [prefixWord, tailWord_1751755, baseEnd_1751755] using wordTrace_append hprefix tailTrace_1751755
  have hstable : (prefixWord ++ tailWord_1751755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751755).length < 2 ^ (prefixWord ++ tailWord_1751755).sum := by decide
  have hdescent : baseEnd_1751755 < baseStart_1751755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751792 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 3]
def baseStart_1751792 : Nat := 118140960795 + 1751792 * 2 ^ 59
def prefixEnd_1751792 : Nat := 4983230072969 + 3 ^ 40 * 1751792 * 2
def baseEnd_1751792 : Nat := 899511302701115339443661

theorem tailTrace_1751792 : CollatzResearch.WordTrace tailWord_1751792 prefixEnd_1751792 899511302701115339443661 := by
  unfold tailWord_1751792
  simp only [CollatzResearch.WordTrace]
  refine ⟨31946551634782120549796815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42595402179709494066395753 31946551634782120549796815)
  ·
    refine ⟨47919827452173180824695223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31946551634782120549796815 47919827452173180824695223)
    ·
      refine ⟨71879741178259771237042835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47919827452173180824695223 71879741178259771237042835)
      ·
        refine ⟨107819611767389656855564253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71879741178259771237042835 107819611767389656855564253)
        ·
          refine ⟨40432354412771121320836595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107819611767389656855564253 40432354412771121320836595)
          ·
            refine ⟨60648531619156681981254893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40432354412771121320836595 60648531619156681981254893)
            ·
              refine ⟨22743199357183755742970585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60648531619156681981254893 22743199357183755742970585)
              ·
                refine ⟨17057399517887816807227939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22743199357183755742970585 17057399517887816807227939)
                ·
                  refine ⟨25586099276831725210841909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17057399517887816807227939 25586099276831725210841909)
                  ·
                    refine ⟨2398696807202974238516429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25586099276831725210841909 2398696807202974238516429)
                    ·
                      refine ⟨899511302701115339443661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2398696807202974238516429 899511302701115339443661)
                      ·
                        rfl

theorem cell23_1751792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 3].length) (baseStart_1751792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751792 prefixEnd_1751792 := by exact prefixLift 1751792
  have htrace : WordTrace (prefixWord ++ tailWord_1751792) baseStart_1751792 baseEnd_1751792 := by
    simpa [prefixWord, tailWord_1751792, baseEnd_1751792] using wordTrace_append hprefix tailTrace_1751792
  have hstable : (prefixWord ++ tailWord_1751792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751792).length < 2 ^ (prefixWord ++ tailWord_1751792).sum := by decide
  have hdescent : baseEnd_1751792 < baseStart_1751792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751797 : List Nat := [1, 3, 6, 1, 1, 1, 1, 3, 1, 3, 2]
def baseStart_1751797 : Nat := 118140960795 + 1751797 * 2 ^ 59
def prefixEnd_1751797 : Nat := 4983230072969 + 3 ^ 40 * 1751797 * 2
def baseEnd_1751797 : Nat := 899513870104387819881139

theorem tailTrace_1751797 : CollatzResearch.WordTrace tailWord_1751797 prefixEnd_1751797 899513870104387819881139 := by
  unfold tailWord_1751797
  simp only [CollatzResearch.WordTrace]
  refine ⟨63893285634546126953525645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42595523756364084635683763 63893285634546126953525645)
  ·
    refine ⟨23959982112954797607572117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63893285634546126953525645 23959982112954797607572117)
    ·
      refine ⟨1123124161544756137854943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23959982112954797607572117 1123124161544756137854943)
      ·
        refine ⟨1684686242317134206782415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1123124161544756137854943 1684686242317134206782415)
        ·
          refine ⟨2527029363475701310173623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1684686242317134206782415 2527029363475701310173623)
          ·
            refine ⟨3790544045213551965260435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2527029363475701310173623 3790544045213551965260435)
            ·
              refine ⟨5685816067820327947890653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3790544045213551965260435 5685816067820327947890653)
              ·
                refine ⟨2132181025432622980458995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5685816067820327947890653 2132181025432622980458995)
                ·
                  refine ⟨3198271538148934470688493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2132181025432622980458995 3198271538148934470688493)
                  ·
                    refine ⟨1199351826805850426508185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3198271538148934470688493 1199351826805850426508185)
                    ·
                      refine ⟨899513870104387819881139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1199351826805850426508185 899513870104387819881139)
                      ·
                        rfl

theorem cell23_1751797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_1751797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751797 prefixEnd_1751797 := by exact prefixLift 1751797
  have htrace : WordTrace (prefixWord ++ tailWord_1751797) baseStart_1751797 baseEnd_1751797 := by
    simpa [prefixWord, tailWord_1751797, baseEnd_1751797] using wordTrace_append hprefix tailTrace_1751797
  have hstable : (prefixWord ++ tailWord_1751797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751797).length < 2 ^ (prefixWord ++ tailWord_1751797).sum := by decide
  have hdescent : baseEnd_1751797 < baseStart_1751797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751810 : List Nat := [3, 4, 1, 1, 1, 2, 3, 2, 2, 2, 2]
def baseStart_1751810 : Nat := 118140960795 + 1751810 * 2 ^ 59
def prefixEnd_1751810 : Nat := 4983230072969 + 3 ^ 40 * 1751810 * 2
def baseEnd_1751810 : Nat := 899520545352896269018579

theorem tailTrace_1751810 : CollatzResearch.WordTrace tailWord_1751810 prefixEnd_1751810 899520545352896269018579 := by
  unfold tailWord_1751810
  simp only [CollatzResearch.WordTrace]
  refine ⟨15973439945874757543437221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42595839855666020115832589 15973439945874757543437221)
  ·
    refine ⟨2995019989851517039394479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15973439945874757543437221 2995019989851517039394479)
    ·
      refine ⟨4492529984777275559091719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2995019989851517039394479 4492529984777275559091719)
      ·
        refine ⟨6738794977165913338637579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4492529984777275559091719 6738794977165913338637579)
        ·
          refine ⟨10108192465748870007956369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6738794977165913338637579 10108192465748870007956369)
          ·
            refine ⟨7581144349311652505967277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10108192465748870007956369 7581144349311652505967277)
            ·
              refine ⟨2842929130991869689737729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7581144349311652505967277 2842929130991869689737729)
              ·
                refine ⟨2132196848243902267303297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2842929130991869689737729 2132196848243902267303297)
                ·
                  refine ⟨1599147636182926700477473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2132196848243902267303297 1599147636182926700477473)
                  ·
                    refine ⟨1199360727137195025358105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1599147636182926700477473 1199360727137195025358105)
                    ·
                      refine ⟨899520545352896269018579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1199360727137195025358105 899520545352896269018579)
                      ·
                        rfl

theorem cell23_1751810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_1751810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751810 prefixEnd_1751810 := by exact prefixLift 1751810
  have htrace : WordTrace (prefixWord ++ tailWord_1751810) baseStart_1751810 baseEnd_1751810 := by
    simpa [prefixWord, tailWord_1751810, baseEnd_1751810] using wordTrace_append hprefix tailTrace_1751810
  have hstable : (prefixWord ++ tailWord_1751810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751810).length < 2 ^ (prefixWord ++ tailWord_1751810).sum := by decide
  have hdescent : baseEnd_1751810 < baseStart_1751810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751822 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7]
def baseStart_1751822 : Nat := 118140960795 + 1751822 * 2 ^ 59
def prefixEnd_1751822 : Nat := 4983230072969 + 3 ^ 40 * 1751822 * 2
def baseEnd_1751822 : Nat := 899526707120750222068523

theorem tailTrace_1751822 : CollatzResearch.WordTrace tailWord_1751822 prefixEnd_1751822 899526707120750222068523 := by
  unfold tailWord_1751822
  simp only [CollatzResearch.WordTrace]
  refine ⟨7986774682431944527898215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42596131639637037482123813 7986774682431944527898215)
  ·
    refine ⟨11980162023647916791847323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7986774682431944527898215 11980162023647916791847323)
    ·
      refine ⟨17970243035471875187770985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11980162023647916791847323 17970243035471875187770985)
      ·
        refine ⟨13477682276603906390828239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17970243035471875187770985 13477682276603906390828239)
        ·
          refine ⟨20216523414905859586242359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13477682276603906390828239 20216523414905859586242359)
          ·
            refine ⟨30324785122358789379363539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20216523414905859586242359 30324785122358789379363539)
            ·
              refine ⟨45487177683538184069045309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30324785122358789379363539 45487177683538184069045309)
              ·
                refine ⟨17057691631326819025891991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45487177683538184069045309 17057691631326819025891991)
                ·
                  refine ⟨25586537446990228538837987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17057691631326819025891991 25586537446990228538837987)
                  ·
                    refine ⟨38379806170485342808256981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25586537446990228538837987 38379806170485342808256981)
                    ·
                      refine ⟨899526707120750222068523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 38379806170485342808256981 899526707120750222068523)
                      ·
                        rfl

theorem cell23_1751822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_1751822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751822 prefixEnd_1751822 := by exact prefixLift 1751822
  have htrace : WordTrace (prefixWord ++ tailWord_1751822) baseStart_1751822 baseEnd_1751822 := by
    simpa [prefixWord, tailWord_1751822, baseEnd_1751822] using wordTrace_append hprefix tailTrace_1751822
  have hstable : (prefixWord ++ tailWord_1751822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751822).length < 2 ^ (prefixWord ++ tailWord_1751822).sum := by decide
  have hdescent : baseEnd_1751822 < baseStart_1751822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751850 : List Nat := [3, 1, 4, 3, 1, 2, 1, 3, 5]
def baseStart_1751850 : Nat := 118140960795 + 1751850 * 2 ^ 59
def prefixEnd_1751850 : Nat := 4983230072969 + 3 ^ 40 * 1751850 * 2
def baseEnd_1751850 : Nat := 99949009397675123613155

theorem tailTrace_1751850 : CollatzResearch.WordTrace tailWord_1751850 prefixEnd_1751850 99949009397675123613155 := by
  unfold tailWord_1751850
  simp only [CollatzResearch.WordTrace]
  refine ⟨15973804675838529251301251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42596812468902744670136669 15973804675838529251301251)
  ·
    refine ⟨23960707013757793876951877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15973804675838529251301251 23960707013757793876951877)
    ·
      refine ⟨4492632565079586351928477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23960707013757793876951877 4492632565079586351928477)
      ·
        refine ⟨1684737211904844881973179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4492632565079586351928477 1684737211904844881973179)
        ·
          refine ⟨2527105817857267322959769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1684737211904844881973179 2527105817857267322959769)
          ·
            refine ⟨1895329363392950492219827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2527105817857267322959769 1895329363392950492219827)
            ·
              refine ⟨2842994045089425738329741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1895329363392950492219827 2842994045089425738329741)
              ·
                refine ⟨1066122766908534651873653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2842994045089425738329741 1066122766908534651873653)
                ·
                  refine ⟨99949009397675123613155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1066122766908534651873653 99949009397675123613155)
                  ·
                    rfl

theorem cell23_1751850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 3, 5].length) (baseStart_1751850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751850 prefixEnd_1751850 := by exact prefixLift 1751850
  have htrace : WordTrace (prefixWord ++ tailWord_1751850) baseStart_1751850 baseEnd_1751850 := by
    simpa [prefixWord, tailWord_1751850, baseEnd_1751850] using wordTrace_append hprefix tailTrace_1751850
  have hstable : (prefixWord ++ tailWord_1751850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751850).length < 2 ^ (prefixWord ++ tailWord_1751850).sum := by decide
  have hdescent : baseEnd_1751850 < baseStart_1751850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751866 : List Nat := [3, 1, 1, 1, 6, 1, 1, 2, 2, 1, 4]
def baseStart_1751866 : Nat := 118140960795 + 1751866 * 2 ^ 59
def prefixEnd_1751866 : Nat := 4983230072969 + 3 ^ 40 * 1751866 * 2
def baseEnd_1751866 : Nat := 899549300269548049918321

theorem tailTrace_1751866 : CollatzResearch.WordTrace tailWord_1751866 prefixEnd_1751866 899549300269548049918321 := by
  unfold tailWord_1751866
  simp only [CollatzResearch.WordTrace]
  refine ⟨15973950567824037934446863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42597201514197434491858301 15973950567824037934446863)
  ·
    refine ⟨23960925851736056901670295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15973950567824037934446863 23960925851736056901670295)
    ·
      refine ⟨35941388777604085352505443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23960925851736056901670295 35941388777604085352505443)
      ·
        refine ⟨53912083166406128028758165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35941388777604085352505443 53912083166406128028758165)
        ·
          refine ⟨2527128898425287251348039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53912083166406128028758165 2527128898425287251348039)
          ·
            refine ⟨3790693347637930877022059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2527128898425287251348039 3790693347637930877022059)
            ·
              refine ⟨5686040021456896315533089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3790693347637930877022059 5686040021456896315533089)
              ·
                refine ⟨4264530016092672236649817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5686040021456896315533089 4264530016092672236649817)
                ·
                  refine ⟨3198397512069504177487363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4264530016092672236649817 3198397512069504177487363)
                  ·
                    refine ⟨4797596268104256266231045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3198397512069504177487363 4797596268104256266231045)
                    ·
                      refine ⟨899549300269548049918321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4797596268104256266231045 899549300269548049918321)
                      ·
                        rfl

theorem cell23_1751866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 2, 1, 4].length) (baseStart_1751866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751866 prefixEnd_1751866 := by exact prefixLift 1751866
  have htrace : WordTrace (prefixWord ++ tailWord_1751866) baseStart_1751866 baseEnd_1751866 := by
    simpa [prefixWord, tailWord_1751866, baseEnd_1751866] using wordTrace_append hprefix tailTrace_1751866
  have hstable : (prefixWord ++ tailWord_1751866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751866).length < 2 ^ (prefixWord ++ tailWord_1751866).sum := by decide
  have hdescent : baseEnd_1751866 < baseStart_1751866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751919 : List Nat := [1, 1, 2, 1, 3, 1, 1, 7, 1, 5]
def baseStart_1751919 : Nat := 118140960795 + 1751919 * 2 ^ 59
def prefixEnd_1751919 : Nat := 4983230072969 + 3 ^ 40 * 1751919 * 2
def baseEnd_1751919 : Nat := 299858838248078780851859

theorem tailTrace_1751919 : CollatzResearch.WordTrace tailWord_1751919 prefixEnd_1751919 299858838248078780851859 := by
  unfold tailWord_1751919
  simp only [CollatzResearch.WordTrace]
  refine ⟨63897735340104141789466811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42598490226736094526311207 63897735340104141789466811)
  ·
    refine ⟨95846603010156212684200217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63897735340104141789466811 95846603010156212684200217)
    ·
      refine ⟨71884952257617159513150163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95846603010156212684200217 71884952257617159513150163)
      ·
        refine ⟨107827428386425739269725245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71884952257617159513150163 107827428386425739269725245)
        ·
          refine ⟨40435285644909652226146967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107827428386425739269725245 40435285644909652226146967)
          ·
            refine ⟨60652928467364478339220451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40435285644909652226146967 60652928467364478339220451)
            ·
              refine ⟨90979392701046717508830677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60652928467364478339220451 90979392701046717508830677)
              ·
                refine ⟨2132329516430782441613219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 90979392701046717508830677 2132329516430782441613219)
                ·
                  refine ⟨3198494274646173662419829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2132329516430782441613219 3198494274646173662419829)
                  ·
                    refine ⟨299858838248078780851859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3198494274646173662419829 299858838248078780851859)
                    ·
                      rfl

theorem cell23_1751919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 5].length) (baseStart_1751919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751919 prefixEnd_1751919 := by exact prefixLift 1751919
  have htrace : WordTrace (prefixWord ++ tailWord_1751919) baseStart_1751919 baseEnd_1751919 := by
    simpa [prefixWord, tailWord_1751919, baseEnd_1751919] using wordTrace_append hprefix tailTrace_1751919
  have hstable : (prefixWord ++ tailWord_1751919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751919).length < 2 ^ (prefixWord ++ tailWord_1751919).sum := by decide
  have hdescent : baseEnd_1751919 < baseStart_1751919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751939 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 4]
def baseStart_1751939 : Nat := 118140960795 + 1751939 * 2 ^ 59
def prefixEnd_1751939 : Nat := 4983230072969 + 3 ^ 40 * 1751939 * 2
def baseEnd_1751939 : Nat := 899586784357326264305485

theorem tailTrace_1751939 : CollatzResearch.WordTrace tailWord_1751939 prefixEnd_1751939 899586784357326264305485 := by
  unfold tailWord_1751939
  simp only [CollatzResearch.WordTrace]
  refine ⟨63898464800031685205194871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42598976533354456803463247 63898464800031685205194871)
  ·
    refine ⟨95847697200047527807792307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63898464800031685205194871 95847697200047527807792307)
    ·
      refine ⟨143771545800071291711688461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95847697200047527807792307 143771545800071291711688461)
      ·
        refine ⟨53914329675026734391883173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143771545800071291711688461 53914329675026734391883173)
        ·
          refine ⟨10108936814067512698478095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53914329675026734391883173 10108936814067512698478095)
          ·
            refine ⟨15163405221101269047717143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10108936814067512698478095 15163405221101269047717143)
            ·
              refine ⟨22745107831651903571575715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15163405221101269047717143 22745107831651903571575715)
              ·
                refine ⟨34117661747477855357363573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22745107831651903571575715 34117661747477855357363573)
                ·
                  refine ⟨3198530788826048939752835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34117661747477855357363573 3198530788826048939752835)
                  ·
                    refine ⟨4797796183239073409629253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3198530788826048939752835 4797796183239073409629253)
                    ·
                      refine ⟨899586784357326264305485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4797796183239073409629253 899586784357326264305485)
                      ·
                        rfl

theorem cell23_1751939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_1751939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751939 prefixEnd_1751939 := by exact prefixLift 1751939
  have htrace : WordTrace (prefixWord ++ tailWord_1751939) baseStart_1751939 baseEnd_1751939 := by
    simpa [prefixWord, tailWord_1751939, baseEnd_1751939] using wordTrace_append hprefix tailTrace_1751939
  have hstable : (prefixWord ++ tailWord_1751939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751939).length < 2 ^ (prefixWord ++ tailWord_1751939).sum := by decide
  have hdescent : baseEnd_1751939 < baseStart_1751939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751956 : List Nat := [2, 4, 2, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_1751956 : Nat := 118140960795 + 1751956 * 2 ^ 59
def prefixEnd_1751956 : Nat := 4983230072969 + 3 ^ 40 * 1751956 * 2
def baseEnd_1751956 : Nat := 899595513528452697792907

theorem tailTrace_1751956 : CollatzResearch.WordTrace tailWord_1751956 prefixEnd_1751956 899595513528452697792907 := by
  unfold tailWord_1751956
  simp only [CollatzResearch.WordTrace]
  refine ⟨31949542420485048554281861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42599389893980064739042481 31949542420485048554281861)
  ·
    refine ⟨5990539203840946603927849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31949542420485048554281861 5990539203840946603927849)
    ·
      refine ⟨4492904402880709952945887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5990539203840946603927849 4492904402880709952945887)
      ·
        refine ⟨6739356604321064929418831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4492904402880709952945887 6739356604321064929418831)
        ·
          refine ⟨10109034906481597394128247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6739356604321064929418831 10109034906481597394128247)
          ·
            refine ⟨15163552359722396091192371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10109034906481597394128247 15163552359722396091192371)
            ·
              refine ⟨22745328539583594136788557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15163552359722396091192371 22745328539583594136788557)
              ·
                refine ⟨8529498202343847801295709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22745328539583594136788557 8529498202343847801295709)
                ·
                  refine ⟨3198561825878942925485891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8529498202343847801295709 3198561825878942925485891)
                  ·
                    refine ⟨4797842738818414388228837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3198561825878942925485891 4797842738818414388228837)
                    ·
                      refine ⟨899595513528452697792907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4797842738818414388228837 899595513528452697792907)
                      ·
                        rfl

theorem cell23_1751956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_1751956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751956 prefixEnd_1751956 := by exact prefixLift 1751956
  have htrace : WordTrace (prefixWord ++ tailWord_1751956) baseStart_1751956 baseEnd_1751956 := by
    simpa [prefixWord, tailWord_1751956, baseEnd_1751956] using wordTrace_append hprefix tailTrace_1751956
  have hstable : (prefixWord ++ tailWord_1751956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751956).length < 2 ^ (prefixWord ++ tailWord_1751956).sum := by decide
  have hdescent : baseEnd_1751956 < baseStart_1751956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751970 : List Nat := [3, 3, 1, 2, 2, 3, 2, 1, 1, 5]
def baseStart_1751970 : Nat := 118140960795 + 1751970 * 2 ^ 59
def prefixEnd_1751970 : Nat := 4983230072969 + 3 ^ 40 * 1751970 * 2
def baseEnd_1751970 : Nat := 299867567419205214339281

theorem tailTrace_1751970 : CollatzResearch.WordTrace tailWord_1751970 prefixEnd_1751970 299867567419205214339281 := by
  unfold tailWord_1751970
  simp only [CollatzResearch.WordTrace]
  refine ⟨15974898865729844374893341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42599730308612918333048909 15974898865729844374893341)
  ·
    refine ⟨5990587074648691640585003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15974898865729844374893341 5990587074648691640585003)
    ·
      refine ⟨8985880611973037460877505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5990587074648691640585003 8985880611973037460877505)
      ·
        refine ⟨6739410458979778095658129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8985880611973037460877505 6739410458979778095658129)
        ·
          refine ⟨5054557844234833571743597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6739410458979778095658129 5054557844234833571743597)
          ·
            refine ⟨1895459191588062589403849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5054557844234833571743597 1895459191588062589403849)
            ·
              refine ⟨1421594393691046942052887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1895459191588062589403849 1421594393691046942052887)
              ·
                refine ⟨2132391590536570413079331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1421594393691046942052887 2132391590536570413079331)
                ·
                  refine ⟨3198587385804855619618997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2132391590536570413079331 3198587385804855619618997)
                  ·
                    refine ⟨299867567419205214339281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3198587385804855619618997 299867567419205214339281)
                    ·
                      rfl

theorem cell23_1751970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_1751970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1751970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1751970 prefixEnd_1751970 := by exact prefixLift 1751970
  have htrace : WordTrace (prefixWord ++ tailWord_1751970) baseStart_1751970 baseEnd_1751970 := by
    simpa [prefixWord, tailWord_1751970, baseEnd_1751970] using wordTrace_append hprefix tailTrace_1751970
  have hstable : (prefixWord ++ tailWord_1751970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751970).length < 2 ^ (prefixWord ++ tailWord_1751970).sum := by decide
  have hdescent : baseEnd_1751970 < baseStart_1751970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752059 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 4]
def baseStart_1752059 : Nat := 118140960795 + 1752059 * 2 ^ 59
def prefixEnd_1752059 : Nat := 4983230072969 + 3 ^ 40 * 1752059 * 2
def baseEnd_1752059 : Nat := 899648402035865794804933

theorem tailTrace_1752059 : CollatzResearch.WordTrace tailWord_1752059 prefixEnd_1752059 899648402035865794804933 := by
  unfold tailWord_1752059
  simp only [CollatzResearch.WordTrace]
  refine ⟨63902841559596945699563231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42601894373064630466375487 63902841559596945699563231)
  ·
    refine ⟨95854262339395418549344847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63902841559596945699563231 95854262339395418549344847)
    ·
      refine ⟨143781393509093127824017271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95854262339395418549344847 143781393509093127824017271)
      ·
        refine ⟨215672090263639691736025907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143781393509093127824017271 215672090263639691736025907)
        ·
          refine ⟨323508135395459537604038861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215672090263639691736025907 323508135395459537604038861)
          ·
            refine ⟨121315550773297326601514573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 323508135395459537604038861 121315550773297326601514573)
            ·
              refine ⟨45493331539986497475567965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121315550773297326601514573 45493331539986497475567965)
              ·
                refine ⟨17059999327494936553337987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45493331539986497475567965 17059999327494936553337987)
                ·
                  refine ⟨25589998991242404830006981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17059999327494936553337987 25589998991242404830006981)
                  ·
                    refine ⟨4798124810857950905626309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25589998991242404830006981 4798124810857950905626309)
                    ·
                      refine ⟨899648402035865794804933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4798124810857950905626309 899648402035865794804933)
                      ·
                        rfl

theorem cell23_1752059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 4].length) (baseStart_1752059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752059 prefixEnd_1752059 := by exact prefixLift 1752059
  have htrace : WordTrace (prefixWord ++ tailWord_1752059) baseStart_1752059 baseEnd_1752059 := by
    simpa [prefixWord, tailWord_1752059, baseEnd_1752059] using wordTrace_append hprefix tailTrace_1752059
  have hstable : (prefixWord ++ tailWord_1752059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752059).length < 2 ^ (prefixWord ++ tailWord_1752059).sum := by decide
  have hdescent : baseEnd_1752059 < baseStart_1752059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752069 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 9]
def baseStart_1752069 : Nat := 118140960795 + 1752069 * 2 ^ 59
def prefixEnd_1752069 : Nat := 4983230072969 + 3 ^ 40 * 1752069 * 2
def baseEnd_1752069 : Nat := 99961504093601195075543

theorem tailTrace_1752069 : CollatzResearch.WordTrace tailWord_1752069 prefixEnd_1752069 99961504093601195075543 := by
  unfold tailWord_1752069
  simp only [CollatzResearch.WordTrace]
  refine ⟨63903206289560717407427261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42602137526373811604951507 63903206289560717407427261)
  ·
    refine ⟨23963702358585269027785223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63903206289560717407427261 23963702358585269027785223)
    ·
      refine ⟨35945553537877903541677835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23963702358585269027785223 35945553537877903541677835)
      ·
        refine ⟨53918330306816855312516753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35945553537877903541677835 53918330306816855312516753)
        ·
          refine ⟨40438747730112641484387565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53918330306816855312516753 40438747730112641484387565)
          ·
            refine ⟨15164530398792240556645337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40438747730112641484387565 15164530398792240556645337)
            ·
              refine ⟨11373397799094180417484003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15164530398792240556645337 11373397799094180417484003)
              ·
                refine ⟨17060096698641270626226005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11373397799094180417484003 17060096698641270626226005)
                ·
                  refine ⟨99961504093601195075543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17060096698641270626226005 99961504093601195075543)
                  ·
                    rfl

theorem cell23_1752069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 9].length) (baseStart_1752069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752069 prefixEnd_1752069 := by exact prefixLift 1752069
  have htrace : WordTrace (prefixWord ++ tailWord_1752069) baseStart_1752069 baseEnd_1752069 := by
    simpa [prefixWord, tailWord_1752069, baseEnd_1752069] using wordTrace_append hprefix tailTrace_1752069
  have hstable : (prefixWord ++ tailWord_1752069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752069).length < 2 ^ (prefixWord ++ tailWord_1752069).sum := by decide
  have hdescent : baseEnd_1752069 < baseStart_1752069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752097 : List Nat := [1, 2, 3, 2, 3, 2, 2, 2, 2, 2, 2]
def baseStart_1752097 : Nat := 118140960795 + 1752097 * 2 ^ 59
def prefixEnd_1752097 : Nat := 4983230072969 + 3 ^ 40 * 1752097 * 2
def baseEnd_1752097 : Nat := 899667914300736646129759

theorem tailTrace_1752097 : CollatzResearch.WordTrace tailWord_1752097 prefixEnd_1752097 899667914300736646129759 := by
  unfold tailWord_1752097
  simp only [CollatzResearch.WordTrace]
  refine ⟨63904227533459278189446545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42602818355639518792964363 63904227533459278189446545)
  ·
    refine ⟨47928170650094458642084909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63904227533459278189446545 47928170650094458642084909)
    ·
      refine ⟨17973063993785421990781841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47928170650094458642084909 17973063993785421990781841)
      ·
        refine ⟨13479797995339066493086381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17973063993785421990781841 13479797995339066493086381)
        ·
          refine ⟨5054924248252149934907393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13479797995339066493086381 5054924248252149934907393)
          ·
            refine ⟨3791193186189112451180545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5054924248252149934907393 3791193186189112451180545)
            ·
              refine ⟨2843394889641834338385409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3791193186189112451180545 2843394889641834338385409)
              ·
                refine ⟨2132546167231375753789057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2843394889641834338385409 2132546167231375753789057)
                ·
                  refine ⟨1599409625423531815341793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2132546167231375753789057 1599409625423531815341793)
                  ·
                    refine ⟨1199557219067648861506345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1599409625423531815341793 1199557219067648861506345)
                    ·
                      refine ⟨899667914300736646129759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1199557219067648861506345 899667914300736646129759)
                      ·
                        rfl

theorem cell23_1752097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_1752097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752097 prefixEnd_1752097 := by exact prefixLift 1752097
  have htrace : WordTrace (prefixWord ++ tailWord_1752097) baseStart_1752097 baseEnd_1752097 := by
    simpa [prefixWord, tailWord_1752097, baseEnd_1752097] using wordTrace_append hprefix tailTrace_1752097
  have hstable : (prefixWord ++ tailWord_1752097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752097).length < 2 ^ (prefixWord ++ tailWord_1752097).sum := by decide
  have hdescent : baseEnd_1752097 < baseStart_1752097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752136 : List Nat := [2, 1, 3, 1, 1, 1, 5, 1, 1, 3, 4]
def baseStart_1752136 : Nat := 118140960795 + 1752136 * 2 ^ 59
def prefixEnd_1752136 : Nat := 4983230072969 + 3 ^ 40 * 1752136 * 2
def baseEnd_1752136 : Nat := 899687940046261993542079

theorem tailTrace_1752136 : CollatzResearch.WordTrace tailWord_1752136 prefixEnd_1752136 899687940046261993542079 := by
  unfold tailWord_1752136
  simp only [CollatzResearch.WordTrace]
  refine ⟨31952824990158993925058131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42603766653545325233410841 31952824990158993925058131)
  ·
    refine ⟨47929237485238490887587197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31952824990158993925058131 47929237485238490887587197)
    ·
      refine ⟨17973464056964434082845199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47929237485238490887587197 17973464056964434082845199)
      ·
        refine ⟨26960196085446651124267799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17973464056964434082845199 26960196085446651124267799)
        ·
          refine ⟨40440294128169976686401699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26960196085446651124267799 40440294128169976686401699)
          ·
            refine ⟨60660441192254965029602549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40440294128169976686401699 60660441192254965029602549)
            ·
              refine ⟨5686916361773902971525239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60660441192254965029602549 5686916361773902971525239)
              ·
                refine ⟨8530374542660854457287859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5686916361773902971525239 8530374542660854457287859)
                ·
                  refine ⟨12795561813991281685931789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8530374542660854457287859 12795561813991281685931789)
                  ·
                    refine ⟨4798335680246730632224421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12795561813991281685931789 4798335680246730632224421)
                    ·
                      refine ⟨899687940046261993542079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4798335680246730632224421 899687940046261993542079)
                      ·
                        rfl

theorem cell23_1752136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_1752136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752136 prefixEnd_1752136 := by exact prefixLift 1752136
  have htrace : WordTrace (prefixWord ++ tailWord_1752136) baseStart_1752136 baseEnd_1752136 := by
    simpa [prefixWord, tailWord_1752136, baseEnd_1752136] using wordTrace_append hprefix tailTrace_1752136
  have hstable : (prefixWord ++ tailWord_1752136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752136).length < 2 ^ (prefixWord ++ tailWord_1752136).sum := by decide
  have hdescent : baseEnd_1752136 < baseStart_1752136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752139 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 9]
def baseStart_1752139 : Nat := 118140960795 + 1752139 * 2 ^ 59
def prefixEnd_1752139 : Nat := 4983230072969 + 3 ^ 40 * 1752139 * 2
def baseEnd_1752139 : Nat := 899689480488225481804565

theorem tailTrace_1752139 : CollatzResearch.WordTrace tailWord_1752139 prefixEnd_1752139 899689480488225481804565 := by
  unfold tailWord_1752139
  simp only [CollatzResearch.WordTrace]
  refine ⟨63905759399307119362475471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42603839599538079574983647 63905759399307119362475471)
  ·
    refine ⟨95858639098960679043713207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63905759399307119362475471 95858639098960679043713207)
    ·
      refine ⟨143787958648441018565569811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95858639098960679043713207 143787958648441018565569811)
      ·
        refine ⟨215681937972661527848354717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143787958648441018565569811 215681937972661527848354717)
        ·
          refine ⟨80880726739748072943133019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215681937972661527848354717 80880726739748072943133019)
          ·
            refine ⟨121321090109622109414699529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80880726739748072943133019 121321090109622109414699529)
            ·
              refine ⟨90990817582216582061024647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121321090109622109414699529 90990817582216582061024647)
              ·
                refine ⟨136486226373324873091536971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90990817582216582061024647 136486226373324873091536971)
                ·
                  refine ⟨204729339559987309637305457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136486226373324873091536971 204729339559987309637305457)
                  ·
                    refine ⟨153547004669990482227979093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 204729339559987309637305457 153547004669990482227979093)
                    ·
                      refine ⟨899689480488225481804565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 153547004669990482227979093 899689480488225481804565)
                      ·
                        rfl

theorem cell23_1752139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 9].length) (baseStart_1752139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752139 prefixEnd_1752139 := by exact prefixLift 1752139
  have htrace : WordTrace (prefixWord ++ tailWord_1752139) baseStart_1752139 baseEnd_1752139 := by
    simpa [prefixWord, tailWord_1752139, baseEnd_1752139] using wordTrace_append hprefix tailTrace_1752139
  have hstable : (prefixWord ++ tailWord_1752139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752139).length < 2 ^ (prefixWord ++ tailWord_1752139).sum := by decide
  have hdescent : baseEnd_1752139 < baseStart_1752139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752170 : List Nat := [3, 1, 3, 2, 2, 1, 2, 1, 2, 4, 2]
def baseStart_1752170 : Nat := 118140960795 + 1752170 * 2 ^ 59
def prefixEnd_1752170 : Nat := 4983230072969 + 3 ^ 40 * 1752170 * 2
def baseEnd_1752170 : Nat := 899705398388514860516923

theorem tailTrace_1752170 : CollatzResearch.WordTrace tailWord_1752170 prefixEnd_1752170 899705398388514860516923 := by
  unfold tailWord_1752170
  simp only [CollatzResearch.WordTrace]
  refine ⟨15976722515548702914213491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42604593374796541104569309 15976722515548702914213491)
  ·
    refine ⟨23965083773323054371320237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15976722515548702914213491 23965083773323054371320237)
    ·
      refine ⟨8986906414996145389245089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23965083773323054371320237 8986906414996145389245089)
      ·
        refine ⟨6740179811247109041933817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8986906414996145389245089 6740179811247109041933817)
        ·
          refine ⟨5055134858435331781450363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6740179811247109041933817 5055134858435331781450363)
          ·
            refine ⟨7582702287652997672175545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5055134858435331781450363 7582702287652997672175545)
            ·
              refine ⟨5687026715739748254131659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7582702287652997672175545 5687026715739748254131659)
              ·
                refine ⟨8530540073609622381197489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5687026715739748254131659 8530540073609622381197489)
                ·
                  refine ⟨6397905055207216785898117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8530540073609622381197489 6397905055207216785898117)
                  ·
                    refine ⟨1199607197851353147355897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6397905055207216785898117 1199607197851353147355897)
                    ·
                      refine ⟨899705398388514860516923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1199607197851353147355897 899705398388514860516923)
                      ·
                        rfl

theorem cell23_1752170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_1752170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752170 prefixEnd_1752170 := by exact prefixLift 1752170
  have htrace : WordTrace (prefixWord ++ tailWord_1752170) baseStart_1752170 baseEnd_1752170 := by
    simpa [prefixWord, tailWord_1752170, baseEnd_1752170] using wordTrace_append hprefix tailTrace_1752170
  have hstable : (prefixWord ++ tailWord_1752170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752170).length < 2 ^ (prefixWord ++ tailWord_1752170).sum := by decide
  have hdescent : baseEnd_1752170 < baseStart_1752170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752173 : List Nat := [1, 5, 1, 1, 2, 2, 1, 2, 1, 4, 3]
def baseStart_1752173 : Nat := 118140960795 + 1752173 * 2 ^ 59
def prefixEnd_1752173 : Nat := 4983230072969 + 3 ^ 40 * 1752173 * 2
def baseEnd_1752173 : Nat := 899706938830478348779409

theorem tailTrace_1752173 : CollatzResearch.WordTrace tailWord_1752173 prefixEnd_1752173 899706938830478348779409 := by
  unfold tailWord_1752173
  simp only [CollatzResearch.WordTrace]
  refine ⟨63906999481183943169213173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42604666320789295446142115 63906999481183943169213173)
  ·
    refine ⟨5991281201360994672113735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63906999481183943169213173 5991281201360994672113735)
    ·
      refine ⟨8986921802041492008170603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5991281201360994672113735 8986921802041492008170603)
      ·
        refine ⟨13480382703062238012255905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8986921802041492008170603 13480382703062238012255905)
        ·
          refine ⟨10110287027296678509191929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13480382703062238012255905 10110287027296678509191929)
          ·
            refine ⟨7582715270472508881893947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10110287027296678509191929 7582715270472508881893947)
            ·
              refine ⟨11374072905708763322840921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7582715270472508881893947 11374072905708763322840921)
              ·
                refine ⟨8530554679281572492130691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11374072905708763322840921 8530554679281572492130691)
                ·
                  refine ⟨12795832018922358738196037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8530554679281572492130691 12795832018922358738196037)
                  ·
                    refine ⟨2399218503547942263411757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12795832018922358738196037 2399218503547942263411757)
                    ·
                      refine ⟨899706938830478348779409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2399218503547942263411757 899706938830478348779409)
                      ·
                        rfl

theorem cell23_1752173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_1752173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752173 prefixEnd_1752173 := by exact prefixLift 1752173
  have htrace : WordTrace (prefixWord ++ tailWord_1752173) baseStart_1752173 baseEnd_1752173 := by
    simpa [prefixWord, tailWord_1752173, baseEnd_1752173] using wordTrace_append hprefix tailTrace_1752173
  have hstable : (prefixWord ++ tailWord_1752173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752173).length < 2 ^ (prefixWord ++ tailWord_1752173).sum := by decide
  have hdescent : baseEnd_1752173 < baseStart_1752173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752203 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 5, 1, 3]
def baseStart_1752203 : Nat := 118140960795 + 1752203 * 2 ^ 59
def prefixEnd_1752203 : Nat := 4983230072969 + 3 ^ 40 * 1752203 * 2
def baseEnd_1752203 : Nat := 899722343250113231404271

theorem tailTrace_1752203 : CollatzResearch.WordTrace tailWord_1752203 prefixEnd_1752203 899722343250113231404271 := by
  unfold tailWord_1752203
  simp only [CollatzResearch.WordTrace]
  refine ⟨63908093671075258292805263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42605395780716838861870175 63908093671075258292805263)
  ·
    refine ⟨95862140506612887439207895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63908093671075258292805263 95862140506612887439207895)
    ·
      refine ⟨143793210759919331158811843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95862140506612887439207895 143793210759919331158811843)
      ·
        refine ⟨215689816139878996738217765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143793210759919331158811843 215689816139878996738217765)
        ·
          refine ⟨40441840526227311888415831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215689816139878996738217765 40441840526227311888415831)
          ·
            refine ⟨60662760789340967832623747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40441840526227311888415831 60662760789340967832623747)
            ·
              refine ⟨90994141184011451748935621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60662760789340967832623747 90994141184011451748935621)
              ·
                refine ⟨17061401472002147202925429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90994141184011451748935621 17061401472002147202925429)
                ·
                  refine ⟨1599506388000201300274259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17061401472002147202925429 1599506388000201300274259)
                  ·
                    refine ⟨2399259582000301950411389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1599506388000201300274259 2399259582000301950411389)
                    ·
                      refine ⟨899722343250113231404271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2399259582000301950411389 899722343250113231404271)
                      ·
                        rfl

theorem cell23_1752203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 5, 1, 3].length) (baseStart_1752203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752203 prefixEnd_1752203 := by exact prefixLift 1752203
  have htrace : WordTrace (prefixWord ++ tailWord_1752203) baseStart_1752203 baseEnd_1752203 := by
    simpa [prefixWord, tailWord_1752203, baseEnd_1752203] using wordTrace_append hprefix tailTrace_1752203
  have hstable : (prefixWord ++ tailWord_1752203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752203).length < 2 ^ (prefixWord ++ tailWord_1752203).sum := by decide
  have hdescent : baseEnd_1752203 < baseStart_1752203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752213 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 3, 5, 2]
def baseStart_1752213 : Nat := 118140960795 + 1752213 * 2 ^ 59
def prefixEnd_1752213 : Nat := 4983230072969 + 3 ^ 40 * 1752213 * 2
def baseEnd_1752213 : Nat := 899727478056658192279225

theorem tailTrace_1752213 : CollatzResearch.WordTrace tailWord_1752213 prefixEnd_1752213 899727478056658192279225 := by
  unfold tailWord_1752213
  simp only [CollatzResearch.WordTrace]
  refine ⟨63908458401039030000669293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42605638934026020000446195 63908458401039030000669293)
  ·
    refine ⟨23965671900389636250250985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63908458401039030000669293 23965671900389636250250985)
    ·
      refine ⟨17974253925292227187688239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23965671900389636250250985 17974253925292227187688239)
      ·
        refine ⟨26961380887938340781532359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17974253925292227187688239 26961380887938340781532359)
        ·
          refine ⟨40442071331907511172298539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26961380887938340781532359 40442071331907511172298539)
          ·
            refine ⟨60663106997861266758447809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40442071331907511172298539 60663106997861266758447809)
            ·
              refine ⟨45497330248395950068835857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60663106997861266758447809 45497330248395950068835857)
              ·
                refine ⟨34122997686296962551626893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45497330248395950068835857 34122997686296962551626893)
                ·
                  refine ⟨12796124132361360956860085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34122997686296962551626893 12796124132361360956860085)
                  ·
                    refine ⟨1199636637408877589705633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12796124132361360956860085 1199636637408877589705633)
                    ·
                      refine ⟨899727478056658192279225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1199636637408877589705633 899727478056658192279225)
                      ·
                        rfl

theorem cell23_1752213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 5, 2].length) (baseStart_1752213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752213 prefixEnd_1752213 := by exact prefixLift 1752213
  have htrace : WordTrace (prefixWord ++ tailWord_1752213) baseStart_1752213 baseEnd_1752213 := by
    simpa [prefixWord, tailWord_1752213, baseEnd_1752213] using wordTrace_append hprefix tailTrace_1752213
  have hstable : (prefixWord ++ tailWord_1752213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752213).length < 2 ^ (prefixWord ++ tailWord_1752213).sum := by decide
  have hdescent : baseEnd_1752213 < baseStart_1752213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752243 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 2, 6, 2]
def baseStart_1752243 : Nat := 118140960795 + 1752243 * 2 ^ 59
def prefixEnd_1752243 : Nat := 4983230072969 + 3 ^ 40 * 1752243 * 2
def baseEnd_1752243 : Nat := 899742882476293074904087

theorem tailTrace_1752243 : CollatzResearch.WordTrace tailWord_1752243 prefixEnd_1752243 899742882476293074904087 := by
  unfold tailWord_1752243
  simp only [CollatzResearch.WordTrace]
  refine ⟨63909552590930345124261383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42606368393953563416174255 63909552590930345124261383)
  ·
    refine ⟨95864328886395517686392075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63909552590930345124261383 95864328886395517686392075)
    ·
      refine ⟨143796493329593276529588113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95864328886395517686392075 143796493329593276529588113)
      ·
        refine ⟨107847369997194957397191085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143796493329593276529588113 107847369997194957397191085)
        ·
          refine ⟨40442763748948109023946657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107847369997194957397191085 40442763748948109023946657)
          ·
            refine ⟨30332072811711081767959993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40442763748948109023946657 30332072811711081767959993)
            ·
              refine ⟨22749054608783311325969995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30332072811711081767959993 22749054608783311325969995)
              ·
                refine ⟨34123581913174966988954993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22749054608783311325969995 34123581913174966988954993)
                ·
                  refine ⟨25592686434881225241716245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34123581913174966988954993 25592686434881225241716245)
                  ·
                    refine ⟨1199657176635057433205449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25592686434881225241716245 1199657176635057433205449)
                    ·
                      refine ⟨899742882476293074904087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1199657176635057433205449 899742882476293074904087)
                      ·
                        rfl

theorem cell23_1752243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 6, 2].length) (baseStart_1752243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752243 prefixEnd_1752243 := by exact prefixLift 1752243
  have htrace : WordTrace (prefixWord ++ tailWord_1752243) baseStart_1752243 baseEnd_1752243 := by
    simpa [prefixWord, tailWord_1752243, baseEnd_1752243] using wordTrace_append hprefix tailTrace_1752243
  have hstable : (prefixWord ++ tailWord_1752243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752243).length < 2 ^ (prefixWord ++ tailWord_1752243).sum := by decide
  have hdescent : baseEnd_1752243 < baseStart_1752243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752253 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 6, 4]
def baseStart_1752253 : Nat := 118140960795 + 1752253 * 2 ^ 59
def prefixEnd_1752253 : Nat := 4983230072969 + 3 ^ 40 * 1752253 * 2
def baseEnd_1752253 : Nat := 299916005760946011926347

theorem tailTrace_1752253 : CollatzResearch.WordTrace tailWord_1752253 prefixEnd_1752253 299916005760946011926347 := by
  unfold tailWord_1752253
  simp only [CollatzResearch.WordTrace]
  refine ⟨63909917320894116832125413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42606611547262744554750275 63909917320894116832125413)
  ·
    refine ⟨11983109497667646906023515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63909917320894116832125413 11983109497667646906023515)
    ·
      refine ⟨17974664246501470359035273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11983109497667646906023515 17974664246501470359035273)
      ·
        refine ⟨13480998184876102769276455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17974664246501470359035273 13480998184876102769276455)
        ·
          refine ⟨20221497277314154153914683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13480998184876102769276455 20221497277314154153914683)
          ·
            refine ⟨30332245915971231230872025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20221497277314154153914683 30332245915971231230872025)
            ·
              refine ⟨22749184436978423423154019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30332245915971231230872025 22749184436978423423154019)
              ·
                refine ⟨34123776655467635134731029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22749184436978423423154019 34123776655467635134731029)
                ·
                  refine ⟨1599552030725045396940517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 34123776655467635134731029 1599552030725045396940517)
                  ·
                    refine ⟨299916005760946011926347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1599552030725045396940517 299916005760946011926347)
                    ·
                      rfl

theorem cell23_1752253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_1752253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752253 prefixEnd_1752253 := by exact prefixLift 1752253
  have htrace : WordTrace (prefixWord ++ tailWord_1752253) baseStart_1752253 baseEnd_1752253 := by
    simpa [prefixWord, tailWord_1752253, baseEnd_1752253] using wordTrace_append hprefix tailTrace_1752253
  have hstable : (prefixWord ++ tailWord_1752253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752253).length < 2 ^ (prefixWord ++ tailWord_1752253).sum := by decide
  have hdescent : baseEnd_1752253 < baseStart_1752253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752266 : List Nat := [3, 1, 2, 1, 3, 13]
def baseStart_1752266 : Nat := 118140960795 + 1752266 * 2 ^ 59
def prefixEnd_1752266 : Nat := 4983230072969 + 3 ^ 40 * 1752266 * 2
def baseEnd_1752266 : Nat := 3702694207947927921467

theorem tailTrace_1752266 : CollatzResearch.WordTrace tailWord_1752266 prefixEnd_1752266 3702694207947927921467 := by
  unfold tailWord_1752266
  simp only [CollatzResearch.WordTrace]
  refine ⟨15977597867461755013087163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42606927646564680034899101 15977597867461755013087163)
  ·
    refine ⟨23966396801192632519630745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15977597867461755013087163 23966396801192632519630745)
    ·
      refine ⟨17974797600894474389723059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23966396801192632519630745 17974797600894474389723059)
      ·
        refine ⟨26962196401341711584584589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17974797600894474389723059 26962196401341711584584589)
        ·
          refine ⟨10110823650503141844219221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26962196401341711584584589 10110823650503141844219221)
          ·
            refine ⟨3702694207947927921467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 10110823650503141844219221 3702694207947927921467)
            ·
              rfl

theorem cell23_1752266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 13].length) (baseStart_1752266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752266 prefixEnd_1752266 := by exact prefixLift 1752266
  have htrace : WordTrace (prefixWord ++ tailWord_1752266) baseStart_1752266 baseEnd_1752266 := by
    simpa [prefixWord, tailWord_1752266, baseEnd_1752266] using wordTrace_append hprefix tailTrace_1752266
  have hstable : (prefixWord ++ tailWord_1752266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752266).length < 2 ^ (prefixWord ++ tailWord_1752266).sum := by decide
  have hdescent : baseEnd_1752266 < baseStart_1752266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752308 : List Nat := [2, 6, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_1752308 : Nat := 118140960795 + 1752308 * 2 ^ 59
def prefixEnd_1752308 : Nat := 4983230072969 + 3 ^ 40 * 1752308 * 2
def baseEnd_1752308 : Nat := 299925419572945106863763

theorem tailTrace_1752308 : CollatzResearch.WordTrace tailWord_1752308 prefixEnd_1752308 299925419572945106863763 := by
  unfold tailWord_1752308
  simp only [CollatzResearch.WordTrace]
  refine ⟨31955961667847430612688789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42607948890463240816918385 31955961667847430612688789)
  ·
    refine ⟨1497935703180348309969787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31955961667847430612688789 1497935703180348309969787)
    ·
      refine ⟨2246903554770522464954681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1497935703180348309969787 2246903554770522464954681)
      ·
        refine ⟨1685177666077891848716011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2246903554770522464954681 1685177666077891848716011)
        ·
          refine ⟨2527766499116837773074017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1685177666077891848716011 2527766499116837773074017)
          ·
            refine ⟨1895824874337628329805513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2527766499116837773074017 1895824874337628329805513)
            ·
              refine ⟨1421868655753221247354135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1895824874337628329805513 1421868655753221247354135)
              ·
                refine ⟨2132802983629831871031203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1421868655753221247354135 2132802983629831871031203)
                ·
                  refine ⟨3199204475444747806546805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2132802983629831871031203 3199204475444747806546805)
                  ·
                    refine ⟨299925419572945106863763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3199204475444747806546805 299925419572945106863763)
                    ·
                      rfl

theorem cell23_1752308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_1752308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752308 prefixEnd_1752308 := by exact prefixLift 1752308
  have htrace : WordTrace (prefixWord ++ tailWord_1752308) baseStart_1752308 baseEnd_1752308 := by
    simpa [prefixWord, tailWord_1752308, baseEnd_1752308] using wordTrace_append hprefix tailTrace_1752308
  have hstable : (prefixWord ++ tailWord_1752308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752308).length < 2 ^ (prefixWord ++ tailWord_1752308).sum := by decide
  have hdescent : baseEnd_1752308 < baseStart_1752308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752343 : List Nat := [1, 1, 3, 4, 1, 1, 1, 3, 2, 6]
def baseStart_1752343 : Nat := 118140960795 + 1752343 * 2 ^ 59
def prefixEnd_1752343 : Nat := 4983230072969 + 3 ^ 40 * 1752343 * 2
def baseEnd_1752343 : Nat := 299931410180580894551209

theorem tailTrace_1752343 : CollatzResearch.WordTrace tailWord_1752343 prefixEnd_1752343 299931410180580894551209 := by
  unfold tailWord_1752343
  simp only [CollatzResearch.WordTrace]
  refine ⟨63913199890568062202901683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42608799927045374801934455 63913199890568062202901683)
  ·
    refine ⟨95869799835852093304352525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63913199890568062202901683 95869799835852093304352525)
    ·
      refine ⟨35951174938444534989132197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95869799835852093304352525 35951174938444534989132197)
      ·
        refine ⟨6740845300958350310462287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35951174938444534989132197 6740845300958350310462287)
        ·
          refine ⟨10111267951437525465693431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6740845300958350310462287 10111267951437525465693431)
          ·
            refine ⟨15166901927156288198540147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10111267951437525465693431 15166901927156288198540147)
            ·
              refine ⟨22750352890734432297810221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15166901927156288198540147 22750352890734432297810221)
              ·
                refine ⟨8531382334025412111678833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22750352890734432297810221 8531382334025412111678833)
                ·
                  refine ⟨6398536750519059083759125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8531382334025412111678833 6398536750519059083759125)
                  ·
                    refine ⟨299931410180580894551209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6398536750519059083759125 299931410180580894551209)
                    ·
                      rfl

theorem cell23_1752343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 6].length) (baseStart_1752343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752343 prefixEnd_1752343 := by exact prefixLift 1752343
  have htrace : WordTrace (prefixWord ++ tailWord_1752343) baseStart_1752343 baseEnd_1752343 := by
    simpa [prefixWord, tailWord_1752343, baseEnd_1752343] using wordTrace_append hprefix tailTrace_1752343
  have hstable : (prefixWord ++ tailWord_1752343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752343).length < 2 ^ (prefixWord ++ tailWord_1752343).sum := by decide
  have hdescent : baseEnd_1752343 < baseStart_1752343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752344 : List Nat := [2, 1, 2, 3, 1, 4, 3, 1, 2, 1, 3]
def baseStart_1752344 : Nat := 118140960795 + 1752344 * 2 ^ 59
def prefixEnd_1752344 : Nat := 4983230072969 + 3 ^ 40 * 1752344 * 2
def baseEnd_1752344 : Nat := 899794744022397179741123

theorem tailTrace_1752344 : CollatzResearch.WordTrace tailWord_1752344 prefixEnd_1752344 899794744022397179741123 := by
  unfold tailWord_1752344
  simp only [CollatzResearch.WordTrace]
  refine ⟨31956618181782219686844043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42608824242376292915792057 31956618181782219686844043)
  ·
    refine ⟨47934927272673329530266065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31956618181782219686844043 47934927272673329530266065)
    ·
      refine ⟨35951195454504997147699549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47934927272673329530266065 35951195454504997147699549)
      ·
        refine ⟨13481698295439373930387331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35951195454504997147699549 13481698295439373930387331)
        ·
          refine ⟨20222547443159060895580997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13481698295439373930387331 20222547443159060895580997)
          ·
            refine ⟨3791727645592323917921437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20222547443159060895580997 3791727645592323917921437)
            ·
              refine ⟨1421897867097121469220539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3791727645592323917921437 1421897867097121469220539)
              ·
                refine ⟨2132846800645682203830809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1421897867097121469220539 2132846800645682203830809)
                ·
                  refine ⟨1599635100484261652873107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2132846800645682203830809 1599635100484261652873107)
                  ·
                    refine ⟨2399452650726392479309661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1599635100484261652873107 2399452650726392479309661)
                    ·
                      refine ⟨899794744022397179741123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2399452650726392479309661 899794744022397179741123)
                      ·
                        rfl

theorem cell23_1752344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_1752344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752344 prefixEnd_1752344 := by exact prefixLift 1752344
  have htrace : WordTrace (prefixWord ++ tailWord_1752344) baseStart_1752344 baseEnd_1752344 := by
    simpa [prefixWord, tailWord_1752344, baseEnd_1752344] using wordTrace_append hprefix tailTrace_1752344
  have hstable : (prefixWord ++ tailWord_1752344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752344).length < 2 ^ (prefixWord ++ tailWord_1752344).sum := by decide
  have hdescent : baseEnd_1752344 < baseStart_1752344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752353 : List Nat := [1, 2, 3, 2, 1, 1, 1, 4, 2, 1, 5]
def baseStart_1752353 : Nat := 118140960795 + 1752353 * 2 ^ 59
def prefixEnd_1752353 : Nat := 4983230072969 + 3 ^ 40 * 1752353 * 2
def baseEnd_1752353 : Nat := 899799365348287644528581

theorem tailTrace_1752353 : CollatzResearch.WordTrace tailWord_1752353 prefixEnd_1752353 899799365348287644528581 := by
  unfold tailWord_1752353
  simp only [CollatzResearch.WordTrace]
  refine ⟨63913564620531833910765713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42609043080354555940510475 63913564620531833910765713)
  ·
    refine ⟨47935173465398875433074285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63913564620531833910765713 47935173465398875433074285)
    ·
      refine ⟨17975690049524578287402857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47935173465398875433074285 17975690049524578287402857)
      ·
        refine ⟨13481767537143433715552143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17975690049524578287402857 13481767537143433715552143)
        ·
          refine ⟨20222651305715150573328215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13481767537143433715552143 20222651305715150573328215)
          ·
            refine ⟨30333976958572725859992323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20222651305715150573328215 30333976958572725859992323)
            ·
              refine ⟨45500965437859088789988485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30333976958572725859992323 45500965437859088789988485)
              ·
                refine ⟨8531431019598579148122841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45500965437859088789988485 8531431019598579148122841)
                ·
                  refine ⟨6398573264698934361092131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8531431019598579148122841 6398573264698934361092131)
                  ·
                    refine ⟨9597859897048401541638197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6398573264698934361092131 9597859897048401541638197)
                    ·
                      refine ⟨899799365348287644528581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9597859897048401541638197 899799365348287644528581)
                      ·
                        rfl

theorem cell23_1752353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_1752353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752353 prefixEnd_1752353 := by exact prefixLift 1752353
  have htrace : WordTrace (prefixWord ++ tailWord_1752353) baseStart_1752353 baseEnd_1752353 := by
    simpa [prefixWord, tailWord_1752353, baseEnd_1752353] using wordTrace_append hprefix tailTrace_1752353
  have hstable : (prefixWord ++ tailWord_1752353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752353).length < 2 ^ (prefixWord ++ tailWord_1752353).sum := by decide
  have hdescent : baseEnd_1752353 < baseStart_1752353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752370 : List Nat := [3, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5]
def baseStart_1752370 : Nat := 118140960795 + 1752370 * 2 ^ 59
def prefixEnd_1752370 : Nat := 4983230072969 + 3 ^ 40 * 1752370 * 2
def baseEnd_1752370 : Nat := 899808094519414078016003

theorem tailTrace_1752370 : CollatzResearch.WordTrace tailWord_1752370 prefixEnd_1752370 899808094519414078016003 := by
  unfold tailWord_1752370
  simp only [CollatzResearch.WordTrace]
  refine ⟨15978546165367561453533641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42609456440980163876089709 15978546165367561453533641)
  ·
    refine ⟨11983909624025671090150231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15978546165367561453533641 11983909624025671090150231)
    ·
      refine ⟨17975864436038506635225347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11983909624025671090150231 17975864436038506635225347)
      ·
        refine ⟨26963796654057759952838021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17975864436038506635225347 26963796654057759952838021)
        ·
          refine ⟨5055711872635829991157129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26963796654057759952838021 5055711872635829991157129)
          ·
            refine ⟨3791783904476872493367847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5055711872635829991157129 3791783904476872493367847)
            ·
              refine ⟨5687675856715308740051771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3791783904476872493367847 5687675856715308740051771)
              ·
                refine ⟨8531513785072963110077657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5687675856715308740051771 8531513785072963110077657)
                ·
                  refine ⟨6398635338804722332558243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8531513785072963110077657 6398635338804722332558243)
                  ·
                    refine ⟨9597953008207083498837365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6398635338804722332558243 9597953008207083498837365)
                    ·
                      refine ⟨899808094519414078016003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9597953008207083498837365 899808094519414078016003)
                      ·
                        rfl

theorem cell23_1752370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_1752370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752370 prefixEnd_1752370 := by exact prefixLift 1752370
  have htrace : WordTrace (prefixWord ++ tailWord_1752370) baseStart_1752370 baseEnd_1752370 := by
    simpa [prefixWord, tailWord_1752370, baseEnd_1752370] using wordTrace_append hprefix tailTrace_1752370
  have hstable : (prefixWord ++ tailWord_1752370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752370).length < 2 ^ (prefixWord ++ tailWord_1752370).sum := by decide
  have hdescent : baseEnd_1752370 < baseStart_1752370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752403 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 4, 5]
def baseStart_1752403 : Nat := 118140960795 + 1752403 * 2 ^ 59
def prefixEnd_1752403 : Nat := 4983230072969 + 3 ^ 40 * 1752403 * 2
def baseEnd_1752403 : Nat := 299941679793670816301117

theorem tailTrace_1752403 : CollatzResearch.WordTrace tailWord_1752403 prefixEnd_1752403 299941679793670816301117 := by
  unfold tailWord_1752403
  simp only [CollatzResearch.WordTrace]
  refine ⟨63915388270350692450085863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42610258846900461633390575 63915388270350692450085863)
  ·
    refine ⟨95873082405526038675128795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63915388270350692450085863 95873082405526038675128795)
    ·
      refine ⟨143809623608289058012693193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95873082405526038675128795 143809623608289058012693193)
      ·
        refine ⟨107857217706216793509519895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143809623608289058012693193 107857217706216793509519895)
        ·
          refine ⟨161785826559325190264279843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107857217706216793509519895 161785826559325190264279843)
          ·
            refine ⟨242678739838987785396419765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161785826559325190264279843 242678739838987785396419765)
            ·
              refine ⟨22751131859905104880914353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 242678739838987785396419765 22751131859905104880914353)
              ·
                refine ⟨17063348894928828660685765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22751131859905104880914353 17063348894928828660685765)
                ·
                  refine ⟨3199377917799155373878581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17063348894928828660685765 3199377917799155373878581)
                  ·
                    refine ⟨299941679793670816301117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3199377917799155373878581 299941679793670816301117)
                    ·
                      rfl

theorem cell23_1752403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 5].length) (baseStart_1752403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752403 prefixEnd_1752403 := by exact prefixLift 1752403
  have htrace : WordTrace (prefixWord ++ tailWord_1752403) baseStart_1752403 baseEnd_1752403 := by
    simpa [prefixWord, tailWord_1752403, baseEnd_1752403] using wordTrace_append hprefix tailTrace_1752403
  have hstable : (prefixWord ++ tailWord_1752403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752403).length < 2 ^ (prefixWord ++ tailWord_1752403).sum := by decide
  have hdescent : baseEnd_1752403 < baseStart_1752403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752420 : List Nat := [2, 3, 1, 1, 3, 2, 1, 3, 2, 5]
def baseStart_1752420 : Nat := 118140960795 + 1752420 * 2 ^ 59
def prefixEnd_1752420 : Nat := 4983230072969 + 3 ^ 40 * 1752420 * 2
def baseEnd_1752420 : Nat := 299944589517379627463591

theorem tailTrace_1752420 : CollatzResearch.WordTrace tailWord_1752420 prefixEnd_1752420 299944589517379627463591 := by
  unfold tailWord_1752420
  simp only [CollatzResearch.WordTrace]
  refine ⟨31958004155644552176727357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42610672207526069568969809 31958004155644552176727357)
  ·
    refine ⟨11984251558366707066272759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31958004155644552176727357 11984251558366707066272759)
    ·
      refine ⟨17976377337550060599409139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11984251558366707066272759 17976377337550060599409139)
      ·
        refine ⟨26964566006325090899113709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17976377337550060599409139 26964566006325090899113709)
        ·
          refine ⟨10111712252371909087167641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26964566006325090899113709 10111712252371909087167641)
          ·
            refine ⟨7583784189278931815375731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10111712252371909087167641 7583784189278931815375731)
            ·
              refine ⟨11375676283918397723063597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7583784189278931815375731 11375676283918397723063597)
              ·
                refine ⟨4265878606469399146148849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11375676283918397723063597 4265878606469399146148849)
                ·
                  refine ⟨3199408954852049359611637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4265878606469399146148849 3199408954852049359611637)
                  ·
                    refine ⟨299944589517379627463591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3199408954852049359611637 299944589517379627463591)
                    ·
                      rfl

theorem cell23_1752420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_1752420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752420 prefixEnd_1752420 := by exact prefixLift 1752420
  have htrace : WordTrace (prefixWord ++ tailWord_1752420) baseStart_1752420 baseEnd_1752420 := by
    simpa [prefixWord, tailWord_1752420, baseEnd_1752420] using wordTrace_append hprefix tailTrace_1752420
  have hstable : (prefixWord ++ tailWord_1752420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752420).length < 2 ^ (prefixWord ++ tailWord_1752420).sum := by decide
  have hdescent : baseEnd_1752420 < baseStart_1752420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752440 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 5, 6, 2]
def baseStart_1752440 : Nat := 118140960795 + 1752440 * 2 ^ 59
def prefixEnd_1752440 : Nat := 4983230072969 + 3 ^ 40 * 1752440 * 2
def baseEnd_1752440 : Nat := 899844038165228804140681

theorem tailTrace_1752440 : CollatzResearch.WordTrace tailWord_1752440 prefixEnd_1752440 899844038165228804140681 := by
  unfold tailWord_1752440
  simp only [CollatzResearch.WordTrace]
  refine ⟨31958368885608323884591387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42611158514144431846121849 31958368885608323884591387)
  ·
    refine ⟨47937553328412485826887081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31958368885608323884591387 47937553328412485826887081)
    ·
      refine ⟨35953164996309364370165311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47937553328412485826887081 35953164996309364370165311)
      ·
        refine ⟨53929747494464046555247967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35953164996309364370165311 53929747494464046555247967)
        ·
          refine ⟨80894621241696069832871951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53929747494464046555247967 80894621241696069832871951)
          ·
            refine ⟨121341931862544104749307927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80894621241696069832871951 121341931862544104749307927)
            ·
              refine ⟨182012897793816157123961891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121341931862544104749307927 182012897793816157123961891)
              ·
                refine ⟨273019346690724235685942837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182012897793816157123961891 273019346690724235685942837)
                ·
                  refine ⟨25595563752255397095557141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 273019346690724235685942837 25595563752255397095557141)
                  ·
                    refine ⟨1199792050886971738854241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25595563752255397095557141 1199792050886971738854241)
                    ·
                      refine ⟨899844038165228804140681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1199792050886971738854241 899844038165228804140681)
                      ·
                        rfl

theorem cell23_1752440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 5, 6, 2].length) (baseStart_1752440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752440 prefixEnd_1752440 := by exact prefixLift 1752440
  have htrace : WordTrace (prefixWord ++ tailWord_1752440) baseStart_1752440 baseEnd_1752440 := by
    simpa [prefixWord, tailWord_1752440, baseEnd_1752440] using wordTrace_append hprefix tailTrace_1752440
  have hstable : (prefixWord ++ tailWord_1752440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752440).length < 2 ^ (prefixWord ++ tailWord_1752440).sum := by decide
  have hdescent : baseEnd_1752440 < baseStart_1752440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752443 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 5]
def baseStart_1752443 : Nat := 118140960795 + 1752443 * 2 ^ 59
def prefixEnd_1752443 : Nat := 4983230072969 + 3 ^ 40 * 1752443 * 2
def baseEnd_1752443 : Nat := 899845578607192292403167

theorem tailTrace_1752443 : CollatzResearch.WordTrace tailWord_1752443 prefixEnd_1752443 899845578607192292403167 := by
  unfold tailWord_1752443
  simp only [CollatzResearch.WordTrace]
  refine ⟨63916847190205779281541983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42611231460137186187694655 63916847190205779281541983)
  ·
    refine ⟨95875270785308668922312975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63916847190205779281541983 95875270785308668922312975)
    ·
      refine ⟨143812906177963003383469463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95875270785308668922312975 143812906177963003383469463)
      ·
        refine ⟨215719359266944505075204195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143812906177963003383469463 215719359266944505075204195)
        ·
          refine ⟨323579038900416757612806293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215719359266944505075204195 323579038900416757612806293)
          ·
            refine ⟨15167767448457035513100295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 323579038900416757612806293 15167767448457035513100295)
            ·
              refine ⟨22751651172685553269650443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15167767448457035513100295 22751651172685553269650443)
              ·
                refine ⟨34127476759028329904475665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22751651172685553269650443 34127476759028329904475665)
                ·
                  refine ⟨25595607569271247428356749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34127476759028329904475665 25595607569271247428356749)
                  ·
                    refine ⟨9598352838476717785633781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25595607569271247428356749 9598352838476717785633781)
                    ·
                      refine ⟨899845578607192292403167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9598352838476717785633781 899845578607192292403167)
                      ·
                        rfl

theorem cell23_1752443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 5].length) (baseStart_1752443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752443 prefixEnd_1752443 := by exact prefixLift 1752443
  have htrace : WordTrace (prefixWord ++ tailWord_1752443) baseStart_1752443 baseEnd_1752443 := by
    simpa [prefixWord, tailWord_1752443, baseEnd_1752443] using wordTrace_append hprefix tailTrace_1752443
  have hstable : (prefixWord ++ tailWord_1752443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752443).length < 2 ^ (prefixWord ++ tailWord_1752443).sum := by decide
  have hdescent : baseEnd_1752443 < baseStart_1752443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752460 : List Nat := [2, 2, 1, 2, 1, 3, 2, 2, 1, 4, 3]
def baseStart_1752460 : Nat := 118140960795 + 1752460 * 2 ^ 59
def prefixEnd_1752460 : Nat := 4983230072969 + 3 ^ 40 * 1752460 * 2
def baseEnd_1752460 : Nat := 899854307778318725890589

theorem tailTrace_1752460 : CollatzResearch.WordTrace tailWord_1752460 prefixEnd_1752460 899854307778318725890589 := by
  unfold tailWord_1752460
  simp only [CollatzResearch.WordTrace]
  refine ⟨31958733615572095592455417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42611644820762794123273889 31958733615572095592455417)
  ·
    refine ⟨23969050211679071694341563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31958733615572095592455417 23969050211679071694341563)
    ·
      refine ⟨35953575317518607541512345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23969050211679071694341563 35953575317518607541512345)
      ·
        refine ⟨26965181488138955656134259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35953575317518607541512345 26965181488138955656134259)
        ·
          refine ⟨40447772232208433484201389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26965181488138955656134259 40447772232208433484201389)
          ·
            refine ⟨15167914587078162556575521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40447772232208433484201389 15167914587078162556575521)
            ·
              refine ⟨11375935940308621917431641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15167914587078162556575521 11375935940308621917431641)
              ·
                refine ⟨8531951955231466438073731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11375935940308621917431641 8531951955231466438073731)
                ·
                  refine ⟨12797927932847199657110597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8531951955231466438073731 12797927932847199657110597)
                  ·
                    refine ⟨2399611487408849935708237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12797927932847199657110597 2399611487408849935708237)
                    ·
                      refine ⟨899854307778318725890589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2399611487408849935708237 899854307778318725890589)
                      ·
                        rfl

theorem cell23_1752460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_1752460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752460 prefixEnd_1752460 := by exact prefixLift 1752460
  have htrace : WordTrace (prefixWord ++ tailWord_1752460) baseStart_1752460 baseEnd_1752460 := by
    simpa [prefixWord, tailWord_1752460, baseEnd_1752460] using wordTrace_append hprefix tailTrace_1752460
  have hstable : (prefixWord ++ tailWord_1752460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752460).length < 2 ^ (prefixWord ++ tailWord_1752460).sum := by decide
  have hdescent : baseEnd_1752460 < baseStart_1752460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752477 : List Nat := [1, 4, 2, 1, 3, 2, 1, 1, 1, 4, 3]
def baseStart_1752477 : Nat := 118140960795 + 1752477 * 2 ^ 59
def prefixEnd_1752477 : Nat := 4983230072969 + 3 ^ 40 * 1752477 * 2
def baseEnd_1752477 : Nat := 899863036949445159378011

theorem tailTrace_1752477 : CollatzResearch.WordTrace tailWord_1752477 prefixEnd_1752477 899863036949445159378011 := by
  unfold tailWord_1752477
  simp only [CollatzResearch.WordTrace]
  refine ⟨63918087272082603088279685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42612058181388402058853123 63918087272082603088279685)
  ·
    refine ⟨11984641363515488079052441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63918087272082603088279685 11984641363515488079052441)
    ·
      refine ⟨8988481022636616059289331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11984641363515488079052441 8988481022636616059289331)
      ·
        refine ⟨13482721533954924088933997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8988481022636616059289331 13482721533954924088933997)
        ·
          refine ⟨5056020575233096533350249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13482721533954924088933997 5056020575233096533350249)
          ·
            refine ⟨3792015431424822400012687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5056020575233096533350249 3792015431424822400012687)
            ·
              refine ⟨5688023147137233600019031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3792015431424822400012687 5688023147137233600019031)
              ·
                refine ⟨8532034720705850400028547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5688023147137233600019031 8532034720705850400028547)
                ·
                  refine ⟨12798052081058775600042821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8532034720705850400028547 12798052081058775600042821)
                  ·
                    refine ⟨2399634765198520425008029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12798052081058775600042821 2399634765198520425008029)
                    ·
                      refine ⟨899863036949445159378011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2399634765198520425008029 899863036949445159378011)
                      ·
                        rfl

theorem cell23_1752477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_1752477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752477 prefixEnd_1752477 := by exact prefixLift 1752477
  have htrace : WordTrace (prefixWord ++ tailWord_1752477) baseStart_1752477 baseEnd_1752477 := by
    simpa [prefixWord, tailWord_1752477, baseEnd_1752477] using wordTrace_append hprefix tailTrace_1752477
  have hstable : (prefixWord ++ tailWord_1752477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752477).length < 2 ^ (prefixWord ++ tailWord_1752477).sum := by decide
  have hdescent : baseEnd_1752477 < baseStart_1752477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752524 : List Nat := [2, 2, 1, 4, 2, 1, 2, 2, 3, 1, 3]
def baseStart_1752524 : Nat := 118140960795 + 1752524 * 2 ^ 59
def prefixEnd_1752524 : Nat := 4983230072969 + 3 ^ 40 * 1752524 * 2
def baseEnd_1752524 : Nat := 899887170540206475490295

theorem tailTrace_1752524 : CollatzResearch.WordTrace tailWord_1752524 prefixEnd_1752524 899887170540206475490295 := by
  unfold tailWord_1752524
  simp only [CollatzResearch.WordTrace]
  refine ⟨31959900751456165057620313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42613201001941553410160417 31959900751456165057620313)
  ·
    refine ⟨23969925563592123793215235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31959900751456165057620313 23969925563592123793215235)
    ·
      refine ⟨35954888345388185689822853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23969925563592123793215235 35954888345388185689822853)
      ·
        refine ⟨6741541564760284816841785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35954888345388185689822853 6741541564760284816841785)
        ·
          refine ⟨5056156173570213612631339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6741541564760284816841785 5056156173570213612631339)
          ·
            refine ⟨7584234260355320418947009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5056156173570213612631339 7584234260355320418947009)
            ·
              refine ⟨5688175695266490314210257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7584234260355320418947009 5688175695266490314210257)
              ·
                refine ⟨4266131771449867735657693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5688175695266490314210257 4266131771449867735657693)
                ·
                  refine ⟨1599799414293700400871635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4266131771449867735657693 1599799414293700400871635)
                  ·
                    refine ⟨2399699121440550601307453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1599799414293700400871635 2399699121440550601307453)
                    ·
                      refine ⟨899887170540206475490295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2399699121440550601307453 899887170540206475490295)
                      ·
                        rfl

theorem cell23_1752524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_1752524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752524 prefixEnd_1752524 := by exact prefixLift 1752524
  have htrace : WordTrace (prefixWord ++ tailWord_1752524) baseStart_1752524 baseEnd_1752524 := by
    simpa [prefixWord, tailWord_1752524, baseEnd_1752524] using wordTrace_append hprefix tailTrace_1752524
  have hstable : (prefixWord ++ tailWord_1752524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752524).length < 2 ^ (prefixWord ++ tailWord_1752524).sum := by decide
  have hdescent : baseEnd_1752524 < baseStart_1752524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752558 : List Nat := [4, 1, 2, 1, 2, 1, 5, 2, 1, 1, 3]
def baseStart_1752558 : Nat := 118140960795 + 1752558 * 2 ^ 59
def prefixEnd_1752558 : Nat := 4983230072969 + 3 ^ 40 * 1752558 * 2
def baseEnd_1752558 : Nat := 899904628882459342465139

theorem tailTrace_1752558 : CollatzResearch.WordTrace tailWord_1752558 prefixEnd_1752558 899904628882459342465139 := by
  unfold tailWord_1752558
  simp only [CollatzResearch.WordTrace]
  refine ⟨7990130198098644240247291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42614027723192769281318885 7990130198098644240247291)
  ·
    refine ⟨11985195297147966360370937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7990130198098644240247291 11985195297147966360370937)
    ·
      refine ⟨8988896472860974770278203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11985195297147966360370937 8988896472860974770278203)
      ·
        refine ⟨13483344709291462155417305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8988896472860974770278203 13483344709291462155417305)
        ·
          refine ⟨10112508531968596616562979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13483344709291462155417305 10112508531968596616562979)
          ·
            refine ⟨15168762797952894924844469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10112508531968596616562979 15168762797952894924844469)
            ·
              refine ⟨1422071512308083899204169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15168762797952894924844469 1422071512308083899204169)
              ·
                refine ⟨1066553634231062924403127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1422071512308083899204169 1066553634231062924403127)
                ·
                  refine ⟨1599830451346594386604691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1066553634231062924403127 1599830451346594386604691)
                  ·
                    refine ⟨2399745677019891579907037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1599830451346594386604691 2399745677019891579907037)
                    ·
                      refine ⟨899904628882459342465139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2399745677019891579907037 899904628882459342465139)
                      ·
                        rfl

theorem cell23_1752558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_1752558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752558 prefixEnd_1752558 := by exact prefixLift 1752558
  have htrace : WordTrace (prefixWord ++ tailWord_1752558) baseStart_1752558 baseEnd_1752558 := by
    simpa [prefixWord, tailWord_1752558, baseEnd_1752558] using wordTrace_append hprefix tailTrace_1752558
  have hstable : (prefixWord ++ tailWord_1752558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752558).length < 2 ^ (prefixWord ++ tailWord_1752558).sum := by decide
  have hdescent : baseEnd_1752558 < baseStart_1752558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752560 : List Nat := [2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 6]
def baseStart_1752560 : Nat := 118140960795 + 1752560 * 2 ^ 59
def prefixEnd_1752560 : Nat := 4983230072969 + 3 ^ 40 * 1752560 * 2
def baseEnd_1752560 : Nat := 899905655843768334640129

theorem tailTrace_1752560 : CollatzResearch.WordTrace tailWord_1752560 prefixEnd_1752560 899905655843768334640129 := by
  unfold tailWord_1752560
  simp only [CollatzResearch.WordTrace]
  refine ⟨31960557265390954131775567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42614076353854605509034089 31960557265390954131775567)
  ·
    refine ⟨47940835898086431197663351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31960557265390954131775567 47940835898086431197663351)
    ·
      refine ⟨71911253847129646796495027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47940835898086431197663351 71911253847129646796495027)
      ·
        refine ⟨107866880770694470194742541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71911253847129646796495027 107866880770694470194742541)
        ·
          refine ⟨40450080289010426323028453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107866880770694470194742541 40450080289010426323028453)
          ·
            refine ⟨7584390054189454935567835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40450080289010426323028453 7584390054189454935567835)
            ·
              refine ⟨11376585081284182403351753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7584390054189454935567835 11376585081284182403351753)
              ·
                refine ⟨8532438810963136802513815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11376585081284182403351753 8532438810963136802513815)
                ·
                  refine ⟨12798658216444705203770723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8532438810963136802513815 12798658216444705203770723)
                  ·
                    refine ⟨19197987324667057805656085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12798658216444705203770723 19197987324667057805656085)
                    ·
                      refine ⟨899905655843768334640129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19197987324667057805656085 899905655843768334640129)
                      ·
                        rfl

theorem cell23_1752560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 6].length) (baseStart_1752560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752560 prefixEnd_1752560 := by exact prefixLift 1752560
  have htrace : WordTrace (prefixWord ++ tailWord_1752560) baseStart_1752560 baseEnd_1752560 := by
    simpa [prefixWord, tailWord_1752560, baseEnd_1752560] using wordTrace_append hprefix tailTrace_1752560
  have hstable : (prefixWord ++ tailWord_1752560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752560).length < 2 ^ (prefixWord ++ tailWord_1752560).sum := by decide
  have hdescent : baseEnd_1752560 < baseStart_1752560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752570 : List Nat := [3, 1, 1, 1, 1, 2, 6, 8]
def baseStart_1752570 : Nat := 118140960795 + 1752570 * 2 ^ 59
def prefixEnd_1752570 : Nat := 4983230072969 + 3 ^ 40 * 1752570 * 2
def baseEnd_1752570 : Nat := 33330029283344936870929

theorem tailTrace_1752570 : CollatzResearch.WordTrace tailWord_1752570 prefixEnd_1752570 33330029283344936870929 := by
  unfold tailWord_1752570
  simp only [CollatzResearch.WordTrace]
  refine ⟨15980369815186419992853791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42614319507163786647610109 15980369815186419992853791)
  ·
    refine ⟨23970554722779629989280687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15980369815186419992853791 23970554722779629989280687)
    ·
      refine ⟨35955832084169444983921031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23970554722779629989280687 35955832084169444983921031)
      ·
        refine ⟨53933748126254167475881547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35955832084169444983921031 53933748126254167475881547)
        ·
          refine ⟨80900622189381251213822321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53933748126254167475881547 80900622189381251213822321)
          ·
            refine ⟨60675466642035938410366741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80900622189381251213822321 60675466642035938410366741)
            ·
              refine ⟨2844162498845434612985941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60675466642035938410366741 2844162498845434612985941)
              ·
                refine ⟨33330029283344936870929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2844162498845434612985941 33330029283344936870929)
                ·
                  rfl

theorem cell23_1752570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 8].length) (baseStart_1752570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752570 prefixEnd_1752570 := by exact prefixLift 1752570
  have htrace : WordTrace (prefixWord ++ tailWord_1752570) baseStart_1752570 baseEnd_1752570 := by
    simpa [prefixWord, tailWord_1752570, baseEnd_1752570] using wordTrace_append hprefix tailTrace_1752570
  have hstable : (prefixWord ++ tailWord_1752570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752570).length < 2 ^ (prefixWord ++ tailWord_1752570).sum := by decide
  have hdescent : baseEnd_1752570 < baseStart_1752570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752584 : List Nat := [2, 1, 3, 2, 1, 1, 5, 2, 1, 2, 3]
def baseStart_1752584 : Nat := 118140960795 + 1752584 * 2 ^ 59
def prefixEnd_1752584 : Nat := 4983230072969 + 3 ^ 40 * 1752584 * 2
def baseEnd_1752584 : Nat := 899917979379476240740019

theorem tailTrace_1752584 : CollatzResearch.WordTrace tailWord_1752584 prefixEnd_1752584 899917979379476240740019 := by
  unfold tailWord_1752584
  simp only [CollatzResearch.WordTrace]
  refine ⟨31960994941347480181212403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42614659921796640241616537 31960994941347480181212403)
  ·
    refine ⟨47941492412021220271818605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31960994941347480181212403 47941492412021220271818605)
    ·
      refine ⟨17978059654507957601931977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47941492412021220271818605 17978059654507957601931977)
      ·
        refine ⟨13483544740880968201448983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17978059654507957601931977 13483544740880968201448983)
        ·
          refine ⟨20225317111321452302173475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13483544740880968201448983 20225317111321452302173475)
          ·
            refine ⟨30337975666982178453260213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20225317111321452302173475 30337975666982178453260213)
            ·
              refine ⟨2844185218779579229993145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30337975666982178453260213 2844185218779579229993145)
              ·
                refine ⟨2133138914084684422494859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2844185218779579229993145 2133138914084684422494859)
                ·
                  refine ⟨3199708371127026633742289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2133138914084684422494859 3199708371127026633742289)
                  ·
                    refine ⟨2399781278345269975306717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3199708371127026633742289 2399781278345269975306717)
                    ·
                      refine ⟨899917979379476240740019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2399781278345269975306717 899917979379476240740019)
                      ·
                        rfl

theorem cell23_1752584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_1752584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752584 prefixEnd_1752584 := by exact prefixLift 1752584
  have htrace : WordTrace (prefixWord ++ tailWord_1752584) baseStart_1752584 baseEnd_1752584 := by
    simpa [prefixWord, tailWord_1752584, baseEnd_1752584] using wordTrace_append hprefix tailTrace_1752584
  have hstable : (prefixWord ++ tailWord_1752584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752584).length < 2 ^ (prefixWord ++ tailWord_1752584).sum := by decide
  have hdescent : baseEnd_1752584 < baseStart_1752584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752597 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 3, 3, 3]
def baseStart_1752597 : Nat := 118140960795 + 1752597 * 2 ^ 59
def prefixEnd_1752597 : Nat := 4983230072969 + 3 ^ 40 * 1752597 * 2
def baseEnd_1752597 : Nat := 899924654627984689877459

theorem tailTrace_1752597 : CollatzResearch.WordTrace tailWord_1752597 prefixEnd_1752597 899924654627984689877459 := by
  unfold tailWord_1752597
  simp only [CollatzResearch.WordTrace]
  refine ⟨63922464031647863582648045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42614976021098575721765363 63922464031647863582648045)
  ·
    refine ⟨23970924011867948843493017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63922464031647863582648045 23970924011867948843493017)
    ·
      refine ⟨17978193008900961632619763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23970924011867948843493017 17978193008900961632619763)
      ·
        refine ⟨26967289513351442448929645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17978193008900961632619763 26967289513351442448929645)
        ·
          refine ⟨10112733567506790918348617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26967289513351442448929645 10112733567506790918348617)
          ·
            refine ⟨7584550175630093188761463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10112733567506790918348617 7584550175630093188761463)
            ·
              refine ⟨11376825263445139783142195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7584550175630093188761463 11376825263445139783142195)
              ·
                refine ⟨17065237895167709674713293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11376825263445139783142195 17065237895167709674713293)
                ·
                  refine ⟨6399464210687891128017485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17065237895167709674713293 6399464210687891128017485)
                  ·
                    refine ⟨2399799079007959173006557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6399464210687891128017485 2399799079007959173006557)
                    ·
                      refine ⟨899924654627984689877459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2399799079007959173006557 899924654627984689877459)
                      ·
                        rfl

theorem cell23_1752597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_1752597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752597 prefixEnd_1752597 := by exact prefixLift 1752597
  have htrace : WordTrace (prefixWord ++ tailWord_1752597) baseStart_1752597 baseEnd_1752597 := by
    simpa [prefixWord, tailWord_1752597, baseEnd_1752597] using wordTrace_append hprefix tailTrace_1752597
  have hstable : (prefixWord ++ tailWord_1752597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752597).length < 2 ^ (prefixWord ++ tailWord_1752597).sum := by decide
  have hdescent : baseEnd_1752597 < baseStart_1752597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752641 : List Nat := [1, 2, 5, 1, 1, 1, 2, 4, 1, 3, 2]
def baseStart_1752641 : Nat := 118140960795 + 1752641 * 2 ^ 59
def prefixEnd_1752641 : Nat := 4983230072969 + 3 ^ 40 * 1752641 * 2
def baseEnd_1752641 : Nat := 899947247776782517727257

theorem tailTrace_1752641 : CollatzResearch.WordTrace tailWord_1752641 prefixEnd_1752641 899947247776782517727257 := by
  unfold tailWord_1752641
  simp only [CollatzResearch.WordTrace]
  refine ⟨63924068843488459097249777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42616045895658972731499851 63924068843488459097249777)
  ·
    refine ⟨47943051632616344322937333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63924068843488459097249777 47943051632616344322937333)
    ·
      refine ⟨4494661090557782280275375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47943051632616344322937333 4494661090557782280275375)
      ·
        refine ⟨6741991635836673420413063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4494661090557782280275375 6741991635836673420413063)
        ·
          refine ⟨10112987453755010130619595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6741991635836673420413063 10112987453755010130619595)
          ·
            refine ⟨15169481180632515195929393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10112987453755010130619595 15169481180632515195929393)
            ·
              refine ⟨11377110885474386396947045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15169481180632515195929393 11377110885474386396947045)
              ·
                refine ⟨2133208291026447449427571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11377110885474386396947045 2133208291026447449427571)
                ·
                  refine ⟨3199812436539671174141357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2133208291026447449427571 3199812436539671174141357)
                  ·
                    refine ⟨1199929663702376690303009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3199812436539671174141357 1199929663702376690303009)
                    ·
                      refine ⟨899947247776782517727257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1199929663702376690303009 899947247776782517727257)
                      ·
                        rfl

theorem cell23_1752641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_1752641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752641 prefixEnd_1752641 := by exact prefixLift 1752641
  have htrace : WordTrace (prefixWord ++ tailWord_1752641) baseStart_1752641 baseEnd_1752641 := by
    simpa [prefixWord, tailWord_1752641, baseEnd_1752641] using wordTrace_append hprefix tailTrace_1752641
  have hstable : (prefixWord ++ tailWord_1752641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752641).length < 2 ^ (prefixWord ++ tailWord_1752641).sum := by decide
  have hdescent : baseEnd_1752641 < baseStart_1752641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752658 : List Nat := [3, 2, 2, 1, 2, 2, 4, 1, 1, 3, 2]
def baseStart_1752658 : Nat := 118140960795 + 1752658 * 2 ^ 59
def prefixEnd_1752658 : Nat := 4983230072969 + 3 ^ 40 * 1752658 * 2
def baseEnd_1752658 : Nat := 899955976947908951214679

theorem tailTrace_1752658 : CollatzResearch.WordTrace tailWord_1752658 prefixEnd_1752658 899955976947908951214679 := by
  unfold tailWord_1752658
  simp only [CollatzResearch.WordTrace]
  refine ⟨15981172221106717750154657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42616459256284580667079085 15981172221106717750154657)
  ·
    refine ⟨11985879165830038312615993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15981172221106717750154657 11985879165830038312615993)
    ·
      refine ⟨8989409374372528734461995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11985879165830038312615993 8989409374372528734461995)
      ·
        refine ⟨13484114061558793101692993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8989409374372528734461995 13484114061558793101692993)
        ·
          refine ⟨10113085546169094826269745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13484114061558793101692993 10113085546169094826269745)
          ·
            refine ⟨7584814159626821119702309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10113085546169094826269745 7584814159626821119702309)
            ·
              refine ⟨1422152654930028959944183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7584814159626821119702309 1422152654930028959944183)
              ·
                refine ⟨2133228982395043439916275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1422152654930028959944183 2133228982395043439916275)
                ·
                  refine ⟨3199843473592565159874413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2133228982395043439916275 3199843473592565159874413)
                  ·
                    refine ⟨1199941302597211934952905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3199843473592565159874413 1199941302597211934952905)
                    ·
                      refine ⟨899955976947908951214679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1199941302597211934952905 899955976947908951214679)
                      ·
                        rfl

theorem cell23_1752658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_1752658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752658 prefixEnd_1752658 := by exact prefixLift 1752658
  have htrace : WordTrace (prefixWord ++ tailWord_1752658) baseStart_1752658 baseEnd_1752658 := by
    simpa [prefixWord, tailWord_1752658, baseEnd_1752658] using wordTrace_append hprefix tailTrace_1752658
  have hstable : (prefixWord ++ tailWord_1752658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752658).length < 2 ^ (prefixWord ++ tailWord_1752658).sum := by decide
  have hdescent : baseEnd_1752658 < baseStart_1752658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752677 : List Nat := [1, 3, 1, 3, 3, 1, 1, 3, 7]
def baseStart_1752677 : Nat := 118140960795 + 1752677 * 2 ^ 59
def prefixEnd_1752677 : Nat := 4983230072969 + 3 ^ 40 * 1752677 * 2
def baseEnd_1752677 : Nat := 99996192564482708541899

theorem tailTrace_1752677 : CollatzResearch.WordTrace tailWord_1752677 prefixEnd_1752677 99996192564482708541899 := by
  unfold tailWord_1752677
  simp only [CollatzResearch.WordTrace]
  refine ⟨63925381871358037245560285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42616921247572024830373523 63925381871358037245560285)
  ·
    refine ⟨23972018201759263967085107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63925381871358037245560285 23972018201759263967085107)
    ·
      refine ⟨35958027302638895950627661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23972018201759263967085107 35958027302638895950627661)
      ·
        refine ⟨13484260238489585981485373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35958027302638895950627661 13484260238489585981485373)
        ·
          refine ⟨5056597589433594743057015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13484260238489585981485373 5056597589433594743057015)
          ·
            refine ⟨7584896384150392114585523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5056597589433594743057015 7584896384150392114585523)
            ·
              refine ⟨11377344576225588171878285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7584896384150392114585523 11377344576225588171878285)
              ·
                refine ⟨4266504216084595564454357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11377344576225588171878285 4266504216084595564454357)
                ·
                  refine ⟨99996192564482708541899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4266504216084595564454357 99996192564482708541899)
                  ·
                    rfl

theorem cell23_1752677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 7].length) (baseStart_1752677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752677 prefixEnd_1752677 := by exact prefixLift 1752677
  have htrace : WordTrace (prefixWord ++ tailWord_1752677) baseStart_1752677 baseEnd_1752677 := by
    simpa [prefixWord, tailWord_1752677, baseEnd_1752677] using wordTrace_append hprefix tailTrace_1752677
  have hstable : (prefixWord ++ tailWord_1752677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752677).length < 2 ^ (prefixWord ++ tailWord_1752677).sum := by decide
  have hdescent : baseEnd_1752677 < baseStart_1752677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752694 : List Nat := [5, 1, 1, 2, 2, 1, 2, 2, 7]
def baseStart_1752694 : Nat := 118140960795 + 1752694 * 2 ^ 59
def prefixEnd_1752694 : Nat := 4983230072969 + 3 ^ 40 * 1752694 * 2
def baseEnd_1752694 : Nat := 99997162472385645596057

theorem tailTrace_1752694 : CollatzResearch.WordTrace tailWord_1752694 prefixEnd_1752694 99997162472385645596057 := by
  unfold tailWord_1752694
  simp only [CollatzResearch.WordTrace]
  refine ⟨3995375119518528071808071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42617334608197632765952757 3995375119518528071808071)
  ·
    refine ⟨5993062679277792107712107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3995375119518528071808071 5993062679277792107712107)
    ·
      refine ⟨8989594018916688161568161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5993062679277792107712107 8989594018916688161568161)
      ·
        refine ⟨6742195514187516121176121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8989594018916688161568161 6742195514187516121176121)
        ·
          refine ⟨5056646635640637090882091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6742195514187516121176121 5056646635640637090882091)
          ·
            refine ⟨7584969953460955636323137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5056646635640637090882091 7584969953460955636323137)
            ·
              refine ⟨5688727465095716727242353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7584969953460955636323137 5688727465095716727242353)
              ·
                refine ⟨4266545598821787545431765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5688727465095716727242353 4266545598821787545431765)
                ·
                  refine ⟨99997162472385645596057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4266545598821787545431765 99997162472385645596057)
                  ·
                    rfl

theorem cell23_1752694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_1752694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752694 prefixEnd_1752694 := by exact prefixLift 1752694
  have htrace : WordTrace (prefixWord ++ tailWord_1752694) baseStart_1752694 baseEnd_1752694 := by
    simpa [prefixWord, tailWord_1752694, baseEnd_1752694] using wordTrace_append hprefix tailTrace_1752694
  have hstable : (prefixWord ++ tailWord_1752694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752694).length < 2 ^ (prefixWord ++ tailWord_1752694).sum := by decide
  have hdescent : baseEnd_1752694 < baseStart_1752694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752707 : List Nat := [1, 1, 1, 3, 3, 1, 1, 5, 2, 5]
def baseStart_1752707 : Nat := 118140960795 + 1752707 * 2 ^ 59
def prefixEnd_1752707 : Nat := 4983230072969 + 3 ^ 40 * 1752707 * 2
def baseEnd_1752707 : Nat := 299993712499993086500651

theorem tailTrace_1752707 : CollatzResearch.WordTrace tailWord_1752707 prefixEnd_1752707 299993712499993086500651 := by
  unfold tailWord_1752707
  simp only [CollatzResearch.WordTrace]
  refine ⟨63926476061249352369152375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42617650707499568246101583 63926476061249352369152375)
  ·
    refine ⟨95889714091874028553728563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63926476061249352369152375 95889714091874028553728563)
    ·
      refine ⟨143834571137811042830592845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95889714091874028553728563 143834571137811042830592845)
      ·
        refine ⟨53937964176679141061472317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143834571137811042830592845 53937964176679141061472317)
        ·
          refine ⟨20226736566254677898052119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53937964176679141061472317 20226736566254677898052119)
          ·
            refine ⟨30340104849382016847078179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20226736566254677898052119 30340104849382016847078179)
            ·
              refine ⟨45510157274073025270617269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30340104849382016847078179 45510157274073025270617269)
              ·
                refine ⟨4266577244444346119120369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45510157274073025270617269 4266577244444346119120369)
                ·
                  refine ⟨3199932933333259589340277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4266577244444346119120369 3199932933333259589340277)
                  ·
                    refine ⟨299993712499993086500651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3199932933333259589340277 299993712499993086500651)
                    ·
                      rfl

theorem cell23_1752707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 5].length) (baseStart_1752707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752707 prefixEnd_1752707 := by exact prefixLift 1752707
  have htrace : WordTrace (prefixWord ++ tailWord_1752707) baseStart_1752707 baseEnd_1752707 := by
    simpa [prefixWord, tailWord_1752707, baseEnd_1752707] using wordTrace_append hprefix tailTrace_1752707
  have hstable : (prefixWord ++ tailWord_1752707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752707).length < 2 ^ (prefixWord ++ tailWord_1752707).sum := by decide
  have hdescent : baseEnd_1752707 < baseStart_1752707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752711 : List Nat := [1, 1, 4, 2, 1, 5, 1, 3, 5]
def baseStart_1752711 : Nat := 118140960795 + 1752711 * 2 ^ 59
def prefixEnd_1752711 : Nat := 4983230072969 + 3 ^ 40 * 1752711 * 2
def baseEnd_1752711 : Nat := 99998132380288582650215

theorem tailTrace_1752711 : CollatzResearch.WordTrace tailWord_1752711 prefixEnd_1752711 99998132380288582650215 := by
  unfold tailWord_1752711
  simp only [CollatzResearch.WordTrace]
  refine ⟨63926621953234861052297987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42617747968823240701531991 63926621953234861052297987)
  ·
    refine ⟨95889932929852291578446981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63926621953234861052297987 95889932929852291578446981)
    ·
      refine ⟨17979362424347304670958809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95889932929852291578446981 17979362424347304670958809)
      ·
        refine ⟨13484521818260478503219107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17979362424347304670958809 13484521818260478503219107)
        ·
          refine ⟨20226782727390717754828661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13484521818260478503219107 20226782727390717754828661)
          ·
            refine ⟨1896260880692879789515187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20226782727390717754828661 1896260880692879789515187)
            ·
              refine ⟨2844391321039319684272781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1896260880692879789515187 2844391321039319684272781)
              ·
                refine ⟨1066646745389744881602293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2844391321039319684272781 1066646745389744881602293)
                ·
                  refine ⟨99998132380288582650215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1066646745389744881602293 99998132380288582650215)
                  ·
                    rfl

theorem cell23_1752711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 3, 5].length) (baseStart_1752711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752711 prefixEnd_1752711 := by exact prefixLift 1752711
  have htrace : WordTrace (prefixWord ++ tailWord_1752711) baseStart_1752711 baseEnd_1752711 := by
    simpa [prefixWord, tailWord_1752711, baseEnd_1752711] using wordTrace_append hprefix tailTrace_1752711
  have hstable : (prefixWord ++ tailWord_1752711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752711).length < 2 ^ (prefixWord ++ tailWord_1752711).sum := by decide
  have hdescent : baseEnd_1752711 < baseStart_1752711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752734 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_1752734 : Nat := 118140960795 + 1752734 * 2 ^ 59
def prefixEnd_1752734 : Nat := 4983230072969 + 3 ^ 40 * 1752734 * 2
def baseEnd_1752734 : Nat := 899995001477650653864329

theorem tailTrace_1752734 : CollatzResearch.WordTrace tailWord_1752734 prefixEnd_1752734 899995001477650653864329 := by
  unfold tailWord_1752734
  simp only [CollatzResearch.WordTrace]
  refine ⟨7990932604018941997548157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42618307221434357320256837 7990932604018941997548157)
  ·
    refine ⟨2996599726507103249080559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7990932604018941997548157 2996599726507103249080559)
    ·
      refine ⟨4494899589760654873620839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2996599726507103249080559 4494899589760654873620839)
      ·
        refine ⟨6742349384640982310431259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4494899589760654873620839 6742349384640982310431259)
        ·
          refine ⟨10113524076961473465646889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6742349384640982310431259 10113524076961473465646889)
          ·
            refine ⟨7585143057721105099235167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10113524076961473465646889 7585143057721105099235167)
            ·
              refine ⟨11377714586581657648852751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7585143057721105099235167 11377714586581657648852751)
              ·
                refine ⟨17066571879872486473279127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11377714586581657648852751 17066571879872486473279127)
                ·
                  refine ⟨25599857819808729709918691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17066571879872486473279127 25599857819808729709918691)
                  ·
                    refine ⟨38399786729713094564878037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25599857819808729709918691 38399786729713094564878037)
                    ·
                      refine ⟨899995001477650653864329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 38399786729713094564878037 899995001477650653864329)
                      ·
                        rfl

theorem cell23_1752734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_1752734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752734 prefixEnd_1752734 := by exact prefixLift 1752734
  have htrace : WordTrace (prefixWord ++ tailWord_1752734) baseStart_1752734 baseEnd_1752734 := by
    simpa [prefixWord, tailWord_1752734, baseEnd_1752734] using wordTrace_append hprefix tailTrace_1752734
  have hstable : (prefixWord ++ tailWord_1752734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752734).length < 2 ^ (prefixWord ++ tailWord_1752734).sum := by decide
  have hdescent : baseEnd_1752734 < baseStart_1752734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752754 : List Nat := [3, 2, 1, 1, 1, 2, 2, 4, 3, 4]
def baseStart_1752754 : Nat := 118140960795 + 1752754 * 2 ^ 59
def prefixEnd_1752754 : Nat := 4983230072969 + 3 ^ 40 * 1752754 * 2
def baseEnd_1752754 : Nat := 300001757030246858538079

theorem tailTrace_1752754 : CollatzResearch.WordTrace tailWord_1752754 prefixEnd_1752754 300001757030246858538079 := by
  unfold tailWord_1752754
  simp only [CollatzResearch.WordTrace]
  refine ⟨15982047573019769849028329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42618793528052719597408877 15982047573019769849028329)
  ·
    refine ⟨11986535679764827386771247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15982047573019769849028329 11986535679764827386771247)
    ·
      refine ⟨17979803519647241080156871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11986535679764827386771247 17979803519647241080156871)
      ·
        refine ⟨26969705279470861620235307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17979803519647241080156871 26969705279470861620235307)
        ·
          refine ⟨40454557919206292430352961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26969705279470861620235307 40454557919206292430352961)
          ·
            refine ⟨30340918439404719322764721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40454557919206292430352961 30340918439404719322764721)
            ·
              refine ⟨22755688829553539492073541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30340918439404719322764721 22755688829553539492073541)
              ·
                refine ⟨4266691655541288654763789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22755688829553539492073541 4266691655541288654763789)
                ·
                  refine ⟨1600009370827983245536421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4266691655541288654763789 1600009370827983245536421)
                  ·
                    refine ⟨300001757030246858538079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1600009370827983245536421 300001757030246858538079)
                    ·
                      rfl

theorem cell23_1752754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_1752754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752754 prefixEnd_1752754 := by exact prefixLift 1752754
  have htrace : WordTrace (prefixWord ++ tailWord_1752754) baseStart_1752754 baseEnd_1752754 := by
    simpa [prefixWord, tailWord_1752754, baseEnd_1752754] using wordTrace_append hprefix tailTrace_1752754
  have hstable : (prefixWord ++ tailWord_1752754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752754).length < 2 ^ (prefixWord ++ tailWord_1752754).sum := by decide
  have hdescent : baseEnd_1752754 < baseStart_1752754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752758 : List Nat := [5, 1, 3, 1, 1, 2, 2, 1, 2, 5]
def baseStart_1752758 : Nat := 118140960795 + 1752758 * 2 ^ 59
def prefixEnd_1752758 : Nat := 4983230072969 + 3 ^ 40 * 1752758 * 2
def baseEnd_1752758 : Nat := 300002441671119519988073

theorem tailTrace_1752758 : CollatzResearch.WordTrace tailWord_1752758 prefixEnd_1752758 300002441671119519988073 := by
  unfold tailWord_1752758
  simp only [CollatzResearch.WordTrace]
  refine ⟨3995521011504036754953683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42618890789376392052839285 3995521011504036754953683)
  ·
    refine ⟨5993281517256055132430525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3995521011504036754953683 5993281517256055132430525)
    ·
      refine ⟨2247480568971020674661447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5993281517256055132430525 2247480568971020674661447)
      ·
        refine ⟨3371220853456531011992171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2247480568971020674661447 3371220853456531011992171)
        ·
          refine ⟨5056831280184796517988257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3371220853456531011992171 5056831280184796517988257)
          ·
            refine ⟨3792623460138597388491193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5056831280184796517988257 3792623460138597388491193)
            ·
              refine ⟨2844467595103948041368395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3792623460138597388491193 2844467595103948041368395)
              ·
                refine ⟨4266701392655922062052593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2844467595103948041368395 4266701392655922062052593)
                ·
                  refine ⟨3200026044491941546539445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4266701392655922062052593 3200026044491941546539445)
                  ·
                    refine ⟨300002441671119519988073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3200026044491941546539445 300002441671119519988073)
                    ·
                      rfl

theorem cell23_1752758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_1752758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752758 prefixEnd_1752758 := by exact prefixLift 1752758
  have htrace : WordTrace (prefixWord ++ tailWord_1752758) baseStart_1752758 baseEnd_1752758 := by
    simpa [prefixWord, tailWord_1752758, baseEnd_1752758] using wordTrace_append hprefix tailTrace_1752758
  have hstable : (prefixWord ++ tailWord_1752758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752758).length < 2 ^ (prefixWord ++ tailWord_1752758).sum := by decide
  have hdescent : baseEnd_1752758 < baseStart_1752758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752814 : List Nat := [4, 1, 2, 1, 1, 2, 1, 3, 3, 5]
def baseStart_1752814 : Nat := 118140960795 + 1752814 * 2 ^ 59
def prefixEnd_1752814 : Nat := 4983230072969 + 3 ^ 40 * 1752814 * 2
def baseEnd_1752814 : Nat := 300012026643336780287987

theorem tailTrace_1752814 : CollatzResearch.WordTrace tailWord_1752814 prefixEnd_1752814 300012026643336780287987 := by
  unfold tailWord_1752814
  simp only [CollatzResearch.WordTrace]
  refine ⟨7991297333982713705412187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42620252447907806428864997 7991297333982713705412187)
  ·
    refine ⟨11986946000974070558118281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7991297333982713705412187 11986946000974070558118281)
    ·
      refine ⟨8990209500730552918588711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11986946000974070558118281 8990209500730552918588711)
      ·
        refine ⟨13485314251095829377883067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8990209500730552918588711 13485314251095829377883067)
        ·
          refine ⟨20227971376643744066824601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13485314251095829377883067 20227971376643744066824601)
          ·
            refine ⟨15170978532482808050118451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20227971376643744066824601 15170978532482808050118451)
            ·
              refine ⟨22756467798724212075177677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15170978532482808050118451 22756467798724212075177677)
              ·
                refine ⟨8533675424521579528191629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22756467798724212075177677 8533675424521579528191629)
                ·
                  refine ⟨3200128284195592323071861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8533675424521579528191629 3200128284195592323071861)
                  ·
                    refine ⟨300012026643336780287987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3200128284195592323071861 300012026643336780287987)
                    ·
                      rfl

theorem cell23_1752814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_1752814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752814 prefixEnd_1752814 := by exact prefixLift 1752814
  have htrace : WordTrace (prefixWord ++ tailWord_1752814) baseStart_1752814 baseEnd_1752814 := by
    simpa [prefixWord, tailWord_1752814, baseEnd_1752814] using wordTrace_append hprefix tailTrace_1752814
  have hstable : (prefixWord ++ tailWord_1752814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752814).length < 2 ^ (prefixWord ++ tailWord_1752814).sum := by decide
  have hdescent : baseEnd_1752814 < baseStart_1752814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752827 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 3, 6]
def baseStart_1752827 : Nat := 118140960795 + 1752827 * 2 ^ 59
def prefixEnd_1752827 : Nat := 4983230072969 + 3 ^ 40 * 1752827 * 2
def baseEnd_1752827 : Nat := 300014251726172930000467

theorem tailTrace_1752827 : CollatzResearch.WordTrace tailWord_1752827 prefixEnd_1752827 300014251726172930000467 := by
  unfold tailWord_1752827
  simp only [CollatzResearch.WordTrace]
  refine ⟨63930852820814612863520735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42620568547209741909013823 63930852820814612863520735)
  ·
    refine ⟨95896279231221919295281103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63930852820814612863520735 95896279231221919295281103)
    ·
      refine ⟨143844418846832878942921655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95896279231221919295281103 143844418846832878942921655)
      ·
        refine ⟨215766628270249318414382483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143844418846832878942921655 215766628270249318414382483)
        ·
          refine ⟨323649942405373977621573725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215766628270249318414382483 323649942405373977621573725)
          ·
            refine ⟨121368728402015241608090147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 323649942405373977621573725 121368728402015241608090147)
            ·
              refine ⟨182053092603022862412135221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121368728402015241608090147 182053092603022862412135221)
              ·
                refine ⟨17067477431533393351137677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 182053092603022862412135221 17067477431533393351137677)
                ·
                  refine ⟨6400304036825022506676629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17067477431533393351137677 6400304036825022506676629)
                  ·
                    refine ⟨300014251726172930000467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6400304036825022506676629 300014251726172930000467)
                    ·
                      rfl

theorem cell23_1752827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 6].length) (baseStart_1752827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752827 prefixEnd_1752827 := by exact prefixLift 1752827
  have htrace : WordTrace (prefixWord ++ tailWord_1752827) baseStart_1752827 baseEnd_1752827 := by
    simpa [prefixWord, tailWord_1752827, baseEnd_1752827] using wordTrace_append hprefix tailTrace_1752827
  have hstable : (prefixWord ++ tailWord_1752827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752827).length < 2 ^ (prefixWord ++ tailWord_1752827).sum := by decide
  have hdescent : baseEnd_1752827 < baseStart_1752827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752831 : List Nat := [1, 1, 2, 2, 1, 3, 6, 1, 1, 5]
def baseStart_1752831 : Nat := 118140960795 + 1752831 * 2 ^ 59
def prefixEnd_1752831 : Nat := 4983230072969 + 3 ^ 40 * 1752831 * 2
def baseEnd_1752831 : Nat := 300014936367045591450461

theorem tailTrace_1752831 : CollatzResearch.WordTrace tailWord_1752831 prefixEnd_1752831 300014936367045591450461 := by
  unfold tailWord_1752831
  simp only [CollatzResearch.WordTrace]
  refine ⟨63930998712800121546666347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42620665808533414364444231 63930998712800121546666347)
  ·
    refine ⟨95896498069200182319999521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63930998712800121546666347 95896498069200182319999521)
    ·
      refine ⟨71922373551900136739999641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95896498069200182319999521 71922373551900136739999641)
      ·
        refine ⟨53941780163925102554999731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71922373551900136739999641 53941780163925102554999731)
        ·
          refine ⟨80912670245887653832499597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53941780163925102554999731 80912670245887653832499597)
          ·
            refine ⟨30342251342207870187187349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80912670245887653832499597 30342251342207870187187349)
            ·
              refine ⟨1422293031665993915024407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30342251342207870187187349 1422293031665993915024407)
              ·
                refine ⟨2133439547498990872536611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1422293031665993915024407 2133439547498990872536611)
                ·
                  refine ⟨3200159321248486308804917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2133439547498990872536611 3200159321248486308804917)
                  ·
                    refine ⟨300014936367045591450461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3200159321248486308804917 300014936367045591450461)
                    ·
                      rfl

theorem cell23_1752831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 1, 5].length) (baseStart_1752831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752831 prefixEnd_1752831 := by exact prefixLift 1752831
  have htrace : WordTrace (prefixWord ++ tailWord_1752831) baseStart_1752831 baseEnd_1752831 := by
    simpa [prefixWord, tailWord_1752831, baseEnd_1752831] using wordTrace_append hprefix tailTrace_1752831
  have hstable : (prefixWord ++ tailWord_1752831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752831).length < 2 ^ (prefixWord ++ tailWord_1752831).sum := by decide
  have hdescent : baseEnd_1752831 < baseStart_1752831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752852 : List Nat := [2, 4, 4, 1, 1, 1, 3, 1, 6]
def baseStart_1752852 : Nat := 118140960795 + 1752852 * 2 ^ 59
def prefixEnd_1752852 : Nat := 4983230072969 + 3 ^ 40 * 1752852 * 2
def baseEnd_1752852 : Nat := 100006176910542354687643

theorem tailTrace_1752852 : CollatzResearch.WordTrace tailWord_1752852 prefixEnd_1752852 100006176910542354687643 := by
  unfold tailWord_1752852
  simp only [CollatzResearch.WordTrace]
  refine ⟨31965882322862021066590405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42621176430482694755453873 31965882322862021066590405)
  ·
    refine ⟨5993602935536628949985701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31965882322862021066590405 5993602935536628949985701)
    ·
      refine ⟨1123800550413117928122319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5993602935536628949985701 1123800550413117928122319)
      ·
        refine ⟨1685700825619676892183479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1123800550413117928122319 1685700825619676892183479)
        ·
          refine ⟨2528551238429515338275219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1685700825619676892183479 2528551238429515338275219)
          ·
            refine ⟨3792826857644273007412829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2528551238429515338275219 3792826857644273007412829)
            ·
              refine ⟨1422310071616602377779811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3792826857644273007412829 1422310071616602377779811)
              ·
                refine ⟨2133465107424903566669717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1422310071616602377779811 2133465107424903566669717)
                ·
                  refine ⟨100006176910542354687643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2133465107424903566669717 100006176910542354687643)
                  ·
                    rfl

theorem cell23_1752852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_1752852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752852 prefixEnd_1752852 := by exact prefixLift 1752852
  have htrace : WordTrace (prefixWord ++ tailWord_1752852) baseStart_1752852 baseEnd_1752852 := by
    simpa [prefixWord, tailWord_1752852, baseEnd_1752852] using wordTrace_append hprefix tailTrace_1752852
  have hstable : (prefixWord ++ tailWord_1752852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752852).length < 2 ^ (prefixWord ++ tailWord_1752852).sum := by decide
  have hdescent : baseEnd_1752852 < baseStart_1752852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752864 : List Nat := [2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 6]
def baseStart_1752864 : Nat := 118140960795 + 1752864 * 2 ^ 59
def prefixEnd_1752864 : Nat := 4983230072969 + 3 ^ 40 * 1752864 * 2
def baseEnd_1752864 : Nat := 900061753962735145238731

theorem tailTrace_1752864 : CollatzResearch.WordTrace tailWord_1752864 prefixEnd_1752864 900061753962735145238731 := by
  unfold tailWord_1752864
  simp only [CollatzResearch.WordTrace]
  refine ⟨31966101160840284091308823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42621468214453712121745097 31966101160840284091308823)
  ·
    refine ⟨47949151741260426136963235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31966101160840284091308823 47949151741260426136963235)
    ·
      refine ⟨71923727611890639205444853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47949151741260426136963235 71923727611890639205444853)
      ·
        refine ⟨6742849463614747425510455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71923727611890639205444853 6742849463614747425510455)
        ·
          refine ⟨10114274195422121138265683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6742849463614747425510455 10114274195422121138265683)
          ·
            refine ⟨15171411293133181707398525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10114274195422121138265683 15171411293133181707398525)
            ·
              refine ⟨5689279234924943140274447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15171411293133181707398525 5689279234924943140274447)
              ·
                refine ⟨8533918852387414710411671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5689279234924943140274447 8533918852387414710411671)
                ·
                  refine ⟨12800878278581122065617507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8533918852387414710411671 12800878278581122065617507)
                  ·
                    refine ⟨19201317417871683098426261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12800878278581122065617507 19201317417871683098426261)
                    ·
                      refine ⟨900061753962735145238731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19201317417871683098426261 900061753962735145238731)
                      ·
                        rfl

theorem cell23_1752864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_1752864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752864 prefixEnd_1752864 := by exact prefixLift 1752864
  have htrace : WordTrace (prefixWord ++ tailWord_1752864) baseStart_1752864 baseEnd_1752864 := by
    simpa [prefixWord, tailWord_1752864, baseEnd_1752864] using wordTrace_append hprefix tailTrace_1752864
  have hstable : (prefixWord ++ tailWord_1752864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752864).length < 2 ^ (prefixWord ++ tailWord_1752864).sum := by decide
  have hdescent : baseEnd_1752864 < baseStart_1752864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752868 : List Nat := [2, 3, 1, 3, 2, 2, 2, 2, 1, 1, 4]
def baseStart_1752868 : Nat := 118140960795 + 1752868 * 2 ^ 59
def prefixEnd_1752868 : Nat := 4983230072969 + 3 ^ 40 * 1752868 * 2
def baseEnd_1752868 : Nat := 900063807885353129588713

theorem tailTrace_1752868 : CollatzResearch.WordTrace tailWord_1752868 prefixEnd_1752868 900063807885353129588713 := by
  unfold tailWord_1752868
  simp only [CollatzResearch.WordTrace]
  refine ⟨31966174106833038432881629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42621565475777384577175505 31966174106833038432881629)
  ·
    refine ⟨11987315290062389412330611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31966174106833038432881629 11987315290062389412330611)
    ·
      refine ⟨17980972935093584118495917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11987315290062389412330611 17980972935093584118495917)
      ·
        refine ⟨6742864850660094044435969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17980972935093584118495917 6742864850660094044435969)
        ·
          refine ⟨5057148637995070533326977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6742864850660094044435969 5057148637995070533326977)
          ·
            refine ⟨3792861478496302899995233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5057148637995070533326977 3792861478496302899995233)
            ·
              refine ⟨2844646108872227174996425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3792861478496302899995233 2844646108872227174996425)
              ·
                refine ⟨2133484581654170381247319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2844646108872227174996425 2133484581654170381247319)
                ·
                  refine ⟨3200226872481255571870979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2133484581654170381247319 3200226872481255571870979)
                  ·
                    refine ⟨4800340308721883357806469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3200226872481255571870979 4800340308721883357806469)
                    ·
                      refine ⟨900063807885353129588713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4800340308721883357806469 900063807885353129588713)
                      ·
                        rfl

theorem cell23_1752868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_1752868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752868 prefixEnd_1752868 := by exact prefixLift 1752868
  have htrace : WordTrace (prefixWord ++ tailWord_1752868) baseStart_1752868 baseEnd_1752868 := by
    simpa [prefixWord, tailWord_1752868, baseEnd_1752868] using wordTrace_append hprefix tailTrace_1752868
  have hstable : (prefixWord ++ tailWord_1752868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752868).length < 2 ^ (prefixWord ++ tailWord_1752868).sum := by decide
  have hdescent : baseEnd_1752868 < baseStart_1752868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752901 : List Nat := [1, 3, 1, 1, 1, 2, 3, 3, 4, 1, 3]
def baseStart_1752901 : Nat := 118140960795 + 1752901 * 2 ^ 59
def prefixEnd_1752901 : Nat := 4983230072969 + 3 ^ 40 * 1752901 * 2
def baseEnd_1752901 : Nat := 900080752746951500476061

theorem tailTrace_1752901 : CollatzResearch.WordTrace tailWord_1752901 prefixEnd_1752901 900080752746951500476061 := by
  unfold tailWord_1752901
  simp only [CollatzResearch.WordTrace]
  refine ⟨63933551822546523501714557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42622367881697682334476371 63933551822546523501714557)
  ·
    refine ⟨23975081933454946313142959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63933551822546523501714557 23975081933454946313142959)
    ·
      refine ⟨35962622900182419469714439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23975081933454946313142959 35962622900182419469714439)
      ·
        refine ⟨53943934350273629204571659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35962622900182419469714439 53943934350273629204571659)
        ·
          refine ⟨80915901525410443806857489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53943934350273629204571659 80915901525410443806857489)
          ·
            refine ⟨60686926144057832855143117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80915901525410443806857489 60686926144057832855143117)
            ·
              refine ⟨22757597304021687320678669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60686926144057832855143117 22757597304021687320678669)
              ·
                refine ⟨8534098989008132745254501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22757597304021687320678669 8534098989008132745254501)
                ·
                  refine ⟨1600143560439024889735219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8534098989008132745254501 1600143560439024889735219)
                  ·
                    refine ⟨2400215340658537334602829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1600143560439024889735219 2400215340658537334602829)
                    ·
                      refine ⟨900080752746951500476061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2400215340658537334602829 900080752746951500476061)
                      ·
                        rfl

theorem cell23_1752901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 4, 1, 3].length) (baseStart_1752901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752901 prefixEnd_1752901 := by exact prefixLift 1752901
  have htrace : WordTrace (prefixWord ++ tailWord_1752901) baseStart_1752901 baseEnd_1752901 := by
    simpa [prefixWord, tailWord_1752901, baseEnd_1752901] using wordTrace_append hprefix tailTrace_1752901
  have hstable : (prefixWord ++ tailWord_1752901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752901).length < 2 ^ (prefixWord ++ tailWord_1752901).sum := by decide
  have hdescent : baseEnd_1752901 < baseStart_1752901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752928 : List Nat := [2, 1, 1, 3, 3, 3, 1, 1, 3, 3, 2]
def baseStart_1752928 : Nat := 118140960795 + 1752928 * 2 ^ 59
def prefixEnd_1752928 : Nat := 4983230072969 + 3 ^ 40 * 1752928 * 2
def baseEnd_1752928 : Nat := 900094616724622894838437

theorem tailTrace_1752928 : CollatzResearch.WordTrace tailWord_1752928 prefixEnd_1752928 900094616724622894838437 := by
  unfold tailWord_1752928
  simp only [CollatzResearch.WordTrace]
  refine ⟨31967268296724353556473719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42623024395632471408631625 31967268296724353556473719)
  ·
    refine ⟨47950902445086530334710579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31967268296724353556473719 47950902445086530334710579)
    ·
      refine ⟨71926353667629795502065869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47950902445086530334710579 71926353667629795502065869)
      ·
        refine ⟨26972382625361173313274701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71926353667629795502065869 26972382625361173313274701)
        ·
          refine ⟨10114643484510439992478013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26972382625361173313274701 10114643484510439992478013)
          ·
            refine ⟨3792991306691414997179255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10114643484510439992478013 3792991306691414997179255)
            ·
              refine ⟨5689486960037122495768883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3792991306691414997179255 5689486960037122495768883)
              ·
                refine ⟨8534230440055683743653325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5689486960037122495768883 8534230440055683743653325)
                ·
                  refine ⟨3200336415020881403869997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8534230440055683743653325 3200336415020881403869997)
                  ·
                    refine ⟨1200126155632830526451249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3200336415020881403869997 1200126155632830526451249)
                    ·
                      refine ⟨900094616724622894838437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1200126155632830526451249 900094616724622894838437)
                      ·
                        rfl

theorem cell23_1752928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 3, 3, 2].length) (baseStart_1752928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752928 prefixEnd_1752928 := by exact prefixLift 1752928
  have htrace : WordTrace (prefixWord ++ tailWord_1752928) baseStart_1752928 baseEnd_1752928 := by
    simpa [prefixWord, tailWord_1752928, baseEnd_1752928] using wordTrace_append hprefix tailTrace_1752928
  have hstable : (prefixWord ++ tailWord_1752928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752928).length < 2 ^ (prefixWord ++ tailWord_1752928).sum := by decide
  have hdescent : baseEnd_1752928 < baseStart_1752928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752945 : List Nat := [1, 2, 2, 2, 1, 3, 5, 1, 1, 3, 2]
def baseStart_1752945 : Nat := 118140960795 + 1752945 * 2 ^ 59
def prefixEnd_1752945 : Nat := 4983230072969 + 3 ^ 40 * 1752945 * 2
def baseEnd_1752945 : Nat := 900103345895749328325859

theorem tailTrace_1752945 : CollatzResearch.WordTrace tailWord_1752945 prefixEnd_1752945 900103345895749328325859 := by
  unfold tailWord_1752945
  simp only [CollatzResearch.WordTrace]
  refine ⟨63935156634387119016316289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42623437756258079344210859 63935156634387119016316289)
  ·
    refine ⟨47951367475790339262237217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63935156634387119016316289 47951367475790339262237217)
    ·
      refine ⟨35963525606842754446677913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47951367475790339262237217 35963525606842754446677913)
      ·
        refine ⟨26972644205132065835008435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35963525606842754446677913 26972644205132065835008435)
        ·
          refine ⟨40458966307698098752512653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26972644205132065835008435 40458966307698098752512653)
          ·
            refine ⟨15172112365386787032192245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40458966307698098752512653 15172112365386787032192245)
            ·
              refine ⟨1422385534255011284268023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15172112365386787032192245 1422385534255011284268023)
              ·
                refine ⟨2133578301382516926402035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1422385534255011284268023 2133578301382516926402035)
                ·
                  refine ⟨3200367452073775389603053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2133578301382516926402035 3200367452073775389603053)
                  ·
                    refine ⟨1200137794527665771101145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3200367452073775389603053 1200137794527665771101145)
                    ·
                      refine ⟨900103345895749328325859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1200137794527665771101145 900103345895749328325859)
                      ·
                        rfl

theorem cell23_1752945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 1, 3, 2].length) (baseStart_1752945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752945 prefixEnd_1752945 := by exact prefixLift 1752945
  have htrace : WordTrace (prefixWord ++ tailWord_1752945) baseStart_1752945 baseEnd_1752945 := by
    simpa [prefixWord, tailWord_1752945, baseEnd_1752945] using wordTrace_append hprefix tailTrace_1752945
  have hstable : (prefixWord ++ tailWord_1752945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752945).length < 2 ^ (prefixWord ++ tailWord_1752945).sum := by decide
  have hdescent : baseEnd_1752945 < baseStart_1752945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752958 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_1752958 : Nat := 118140960795 + 1752958 * 2 ^ 59
def prefixEnd_1752958 : Nat := 4983230072969 + 3 ^ 40 * 1752958 * 2
def baseEnd_1752958 : Nat := 900110021144257777463299

theorem tailTrace_1752958 : CollatzResearch.WordTrace tailWord_1752958 prefixEnd_1752958 900110021144257777463299 := by
  unfold tailWord_1752958
  simp only [CollatzResearch.WordTrace]
  refine ⟨7991953847917502779567441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42623753855560014824359685 7991953847917502779567441)
  ·
    refine ⟨5993965385938127084675581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7991953847917502779567441 5993965385938127084675581)
    ·
      refine ⟨2247737019726797656753343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5993965385938127084675581 2247737019726797656753343)
      ·
        refine ⟨3371605529590196485130015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2247737019726797656753343 3371605529590196485130015)
        ·
          refine ⟨5057408294385294727695023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3371605529590196485130015 5057408294385294727695023)
          ·
            refine ⟨7586112441577942091542535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5057408294385294727695023 7586112441577942091542535)
            ·
              refine ⟨11379168662366913137313803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7586112441577942091542535 11379168662366913137313803)
              ·
                refine ⟨17068752993550369705970705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11379168662366913137313803 17068752993550369705970705)
                ·
                  refine ⟨12801564745162777279478029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17068752993550369705970705 12801564745162777279478029)
                  ·
                    refine ⟨4800586779436041479804261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12801564745162777279478029 4800586779436041479804261)
                    ·
                      refine ⟨900110021144257777463299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4800586779436041479804261 900110021144257777463299)
                      ·
                        rfl

theorem cell23_1752958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_1752958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1752958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1752958 prefixEnd_1752958 := by exact prefixLift 1752958
  have htrace : WordTrace (prefixWord ++ tailWord_1752958) baseStart_1752958 baseEnd_1752958 := by
    simpa [prefixWord, tailWord_1752958, baseEnd_1752958] using wordTrace_append hprefix tailTrace_1752958
  have hstable : (prefixWord ++ tailWord_1752958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752958).length < 2 ^ (prefixWord ++ tailWord_1752958).sum := by decide
  have hdescent : baseEnd_1752958 < baseStart_1752958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753001 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 1, 7, 2]
def baseStart_1753001 : Nat := 118140960795 + 1753001 * 2 ^ 59
def prefixEnd_1753001 : Nat := 4983230072969 + 3 ^ 40 * 1753001 * 2
def baseEnd_1753001 : Nat := 900132100812401109225601

theorem tailTrace_1753001 : CollatzResearch.WordTrace tailWord_1753001 prefixEnd_1753001 900132100812401109225601 := by
  unfold tailWord_1753001
  simp only [CollatzResearch.WordTrace]
  refine ⟨63937199122184240580354857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42624799414789493720236571 63937199122184240580354857)
  ·
    refine ⟨47952899341638180435266143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63937199122184240580354857 47952899341638180435266143)
    ·
      refine ⟨71929349012457270652899215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47952899341638180435266143 71929349012457270652899215)
      ·
        refine ⟨107894023518685905979348823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71929349012457270652899215 107894023518685905979348823)
        ·
          refine ⟨161841035278028858969023235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107894023518685905979348823 161841035278028858969023235)
          ·
            refine ⟨242761552917043288453534853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161841035278028858969023235 242761552917043288453534853)
            ·
              refine ⟨45517791171945616585037785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 242761552917043288453534853 45517791171945616585037785)
              ·
                refine ⟨34138343378959212438778339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45517791171945616585037785 34138343378959212438778339)
                ·
                  refine ⟨51207515068438818658167509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34138343378959212438778339 51207515068438818658167509)
                  ·
                    refine ⟨1200176134416534812300801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51207515068438818658167509 1200176134416534812300801)
                    ·
                      refine ⟨900132100812401109225601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1200176134416534812300801 900132100812401109225601)
                      ·
                        rfl

theorem cell23_1753001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 7, 2].length) (baseStart_1753001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753001 prefixEnd_1753001 := by exact prefixLift 1753001
  have htrace : WordTrace (prefixWord ++ tailWord_1753001) baseStart_1753001 baseEnd_1753001 := by
    simpa [prefixWord, tailWord_1753001, baseEnd_1753001] using wordTrace_append hprefix tailTrace_1753001
  have hstable : (prefixWord ++ tailWord_1753001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753001).length < 2 ^ (prefixWord ++ tailWord_1753001).sum := by decide
  have hdescent : baseEnd_1753001 < baseStart_1753001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753041 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 5, 4]
def baseStart_1753041 : Nat := 118140960795 + 1753041 * 2 ^ 59
def prefixEnd_1753041 : Nat := 4983230072969 + 3 ^ 40 * 1753041 * 2
def baseEnd_1753041 : Nat := 300050880012860317575139

theorem tailTrace_1753041 : CollatzResearch.WordTrace tailWord_1753041 prefixEnd_1753041 300050880012860317575139 := by
  unfold tailWord_1753041
  simp only [CollatzResearch.WordTrace]
  refine ⟨63938658042039327411810977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42625772028026218274540651 63938658042039327411810977)
  ·
    refine ⟨47953993531529495558858233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63938658042039327411810977 47953993531529495558858233)
    ·
      refine ⟨35965495148647121669143675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47953993531529495558858233 35965495148647121669143675)
      ·
        refine ⟨53948242722970682503715513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35965495148647121669143675 53948242722970682503715513)
        ·
          refine ⟨40461182042228011877786635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53948242722970682503715513 40461182042228011877786635)
          ·
            refine ⟨60691773063342017816679953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40461182042228011877786635 60691773063342017816679953)
            ·
              refine ⟨45518829797506513362509965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60691773063342017816679953 45518829797506513362509965)
              ·
                refine ⟨17069561174064942510941237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45518829797506513362509965 17069561174064942510941237)
                ·
                  refine ⟨1600271360068588360400741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17069561174064942510941237 1600271360068588360400741)
                  ·
                    refine ⟨300050880012860317575139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1600271360068588360400741 300050880012860317575139)
                    ·
                      rfl

theorem cell23_1753041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 5, 4].length) (baseStart_1753041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753041 prefixEnd_1753041 := by exact prefixLift 1753041
  have htrace : WordTrace (prefixWord ++ tailWord_1753041) baseStart_1753041 baseEnd_1753041 := by
    simpa [prefixWord, tailWord_1753041, baseEnd_1753041] using wordTrace_append hprefix tailTrace_1753041
  have hstable : (prefixWord ++ tailWord_1753041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753041).length < 2 ^ (prefixWord ++ tailWord_1753041).sum := by decide
  have hdescent : baseEnd_1753041 < baseStart_1753041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753071 : List Nat := [1, 1, 2, 1, 4, 2, 2, 4, 6]
def baseStart_1753071 : Nat := 118140960795 + 1753071 * 2 ^ 59
def prefixEnd_1753071 : Nat := 4983230072969 + 3 ^ 40 * 1753071 * 2
def baseEnd_1753071 : Nat := 100018671606468426150031

theorem tailTrace_1753071 : CollatzResearch.WordTrace tailWord_1753071 prefixEnd_1753071 100018671606468426150031 := by
  unfold tailWord_1753071
  simp only [CollatzResearch.WordTrace]
  refine ⟨63939752231930642535403067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42626501487953761690268711 63939752231930642535403067)
  ·
    refine ⟨95909628347895963803104601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63939752231930642535403067 95909628347895963803104601)
    ·
      refine ⟨71932221260921972852328451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95909628347895963803104601 71932221260921972852328451)
      ·
        refine ⟨107898331891382959278492677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71932221260921972852328451 107898331891382959278492677)
        ·
          refine ⟨20230937229634304864717377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107898331891382959278492677 20230937229634304864717377)
          ·
            refine ⟨15173202922225728648538033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20230937229634304864717377 15173202922225728648538033)
            ·
              refine ⟨11379902191669296486403525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15173202922225728648538033 11379902191669296486403525)
              ·
                refine ⟨2133731660937993091200661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11379902191669296486403525 2133731660937993091200661)
                ·
                  refine ⟨100018671606468426150031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2133731660937993091200661 100018671606468426150031)
                  ·
                    rfl

theorem cell23_1753071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 6].length) (baseStart_1753071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753071 prefixEnd_1753071 := by exact prefixLift 1753071
  have htrace : WordTrace (prefixWord ++ tailWord_1753071) baseStart_1753071 baseEnd_1753071 := by
    simpa [prefixWord, tailWord_1753071, baseEnd_1753071] using wordTrace_append hprefix tailTrace_1753071
  have hstable : (prefixWord ++ tailWord_1753071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753071).length < 2 ^ (prefixWord ++ tailWord_1753071).sum := by decide
  have hdescent : baseEnd_1753071 < baseStart_1753071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753125 : List Nat := [1, 3, 1, 2, 2, 3, 2, 2, 2, 3, 2]
def baseStart_1753125 : Nat := 118140960795 + 1753125 * 2 ^ 59
def prefixEnd_1753125 : Nat := 4983230072969 + 3 ^ 40 * 1753125 * 2
def baseEnd_1753125 : Nat := 900195772413558624075031

theorem tailTrace_1753125 : CollatzResearch.WordTrace tailWord_1753125 prefixEnd_1753125 900195772413558624075031 := by
  unfold tailWord_1753125
  simp only [CollatzResearch.WordTrace]
  refine ⟨63941721773735009757868829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42627814515823339838579219 63941721773735009757868829)
  ·
    refine ⟨23978145665150628659200811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63941721773735009757868829 23978145665150628659200811)
    ·
      refine ⟨35967218497725942988801217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23978145665150628659200811 35967218497725942988801217)
      ·
        refine ⟨26975413873294457241600913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35967218497725942988801217 26975413873294457241600913)
        ·
          refine ⟨20231560404970842931200685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26975413873294457241600913 20231560404970842931200685)
          ·
            refine ⟨7586835151864066099200257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20231560404970842931200685 7586835151864066099200257)
            ·
              refine ⟨5690126363898049574400193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7586835151864066099200257 5690126363898049574400193)
              ·
                refine ⟨4267594772923537180800145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5690126363898049574400193 4267594772923537180800145)
                ·
                  refine ⟨3200696079692652885600109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4267594772923537180800145 3200696079692652885600109)
                  ·
                    refine ⟨1200261029884744832100041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3200696079692652885600109 1200261029884744832100041)
                    ·
                      refine ⟨900195772413558624075031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1200261029884744832100041 900195772413558624075031)
                      ·
                        rfl

theorem cell23_1753125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 3, 2].length) (baseStart_1753125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753125 prefixEnd_1753125 := by exact prefixLift 1753125
  have htrace : WordTrace (prefixWord ++ tailWord_1753125) baseStart_1753125 baseEnd_1753125 := by
    simpa [prefixWord, tailWord_1753125, baseEnd_1753125] using wordTrace_append hprefix tailTrace_1753125
  have hstable : (prefixWord ++ tailWord_1753125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753125).length < 2 ^ (prefixWord ++ tailWord_1753125).sum := by decide
  have hdescent : baseEnd_1753125 < baseStart_1753125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753138 : List Nat := [3, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4]
def baseStart_1753138 : Nat := 118140960795 + 1753138 * 2 ^ 59
def prefixEnd_1753138 : Nat := 4983230072969 + 3 ^ 40 * 1753138 * 2
def baseEnd_1753138 : Nat := 900202447662067073212471

theorem tailTrace_1753138 : CollatzResearch.WordTrace tailWord_1753138 prefixEnd_1753138 900202447662067073212471 := by
  unfold tailWord_1753138
  simp only [CollatzResearch.WordTrace]
  refine ⟨15985548980671978244523017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42628130615125275318728045 15985548980671978244523017)
  ·
    refine ⟨11989161735503983683392263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15985548980671978244523017 11989161735503983683392263)
    ·
      refine ⟨17983742603255975525088395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11989161735503983683392263 17983742603255975525088395)
      ·
        refine ⟨26975613904883963287632593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17983742603255975525088395 26975613904883963287632593)
        ·
          refine ⟨20231710428662972465724445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26975613904883963287632593 20231710428662972465724445)
          ·
            refine ⟨7586891410748614674646667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20231710428662972465724445 7586891410748614674646667)
            ·
              refine ⟨11380337116122922011970001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7586891410748614674646667 11380337116122922011970001)
              ·
                refine ⟨8535252837092191508977501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11380337116122922011970001 8535252837092191508977501)
                ·
                  refine ⟨3200719813909571815866563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8535252837092191508977501 3200719813909571815866563)
                  ·
                    refine ⟨4801079720864357723799845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3200719813909571815866563 4801079720864357723799845)
                    ·
                      refine ⟨900202447662067073212471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4801079720864357723799845 900202447662067073212471)
                      ·
                        rfl

theorem cell23_1753138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_1753138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753138 prefixEnd_1753138 := by exact prefixLift 1753138
  have htrace : WordTrace (prefixWord ++ tailWord_1753138) baseStart_1753138 baseEnd_1753138 := by
    simpa [prefixWord, tailWord_1753138, baseEnd_1753138] using wordTrace_append hprefix tailTrace_1753138
  have hstable : (prefixWord ++ tailWord_1753138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753138).length < 2 ^ (prefixWord ++ tailWord_1753138).sum := by decide
  have hdescent : baseEnd_1753138 < baseStart_1753138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753148 : List Nat := [2, 2, 2, 2, 2, 1, 4, 1, 1, 6]
def baseStart_1753148 : Nat := 118140960795 + 1753148 * 2 ^ 59
def prefixEnd_1753148 : Nat := 4983230072969 + 3 ^ 40 * 1753148 * 2
def baseEnd_1753148 : Nat := 300069194156204011362475

theorem tailTrace_1753148 : CollatzResearch.WordTrace tailWord_1753148 prefixEnd_1753148 300069194156204011362475 := by
  unfold tailWord_1753148
  simp only [CollatzResearch.WordTrace]
  refine ⟨31971280326325842342978049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42628373768434456457304065 31971280326325842342978049)
  ·
    refine ⟨23978460244744381757233537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31971280326325842342978049 23978460244744381757233537)
    ·
      refine ⟨17983845183558286317925153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23978460244744381757233537 17983845183558286317925153)
      ·
        refine ⟨13487883887668714738443865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17983845183558286317925153 13487883887668714738443865)
        ·
          refine ⟨10115912915751536053832899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13487883887668714738443865 10115912915751536053832899)
          ·
            refine ⟨15173869373627304080749349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10115912915751536053832899 15173869373627304080749349)
            ·
              refine ⟨2845100507555119515140503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15173869373627304080749349 2845100507555119515140503)
              ·
                refine ⟨4267650761332679272710755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2845100507555119515140503 4267650761332679272710755)
                ·
                  refine ⟨6401476141999018909066133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4267650761332679272710755 6401476141999018909066133)
                  ·
                    refine ⟨300069194156204011362475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6401476141999018909066133 300069194156204011362475)
                    ·
                      rfl

theorem cell23_1753148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_1753148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753148 prefixEnd_1753148 := by exact prefixLift 1753148
  have htrace : WordTrace (prefixWord ++ tailWord_1753148) baseStart_1753148 baseEnd_1753148 := by
    simpa [prefixWord, tailWord_1753148, baseEnd_1753148] using wordTrace_append hprefix tailTrace_1753148
  have hstable : (prefixWord ++ tailWord_1753148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753148).length < 2 ^ (prefixWord ++ tailWord_1753148).sum := by decide
  have hdescent : baseEnd_1753148 < baseStart_1753148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753151 : List Nat := [1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 6]
def baseStart_1753151 : Nat := 118140960795 + 1753151 * 2 ^ 59
def prefixEnd_1753151 : Nat := 4983230072969 + 3 ^ 40 * 1753151 * 2
def baseEnd_1753151 : Nat := 900209122910575522349911

theorem tailTrace_1753151 : CollatzResearch.WordTrace tailWord_1753151 prefixEnd_1753151 900209122910575522349911 := by
  unfold tailWord_1753151
  simp only [CollatzResearch.WordTrace]
  refine ⟨63942670071640816198315307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42628446714427210798876871 63942670071640816198315307)
  ·
    refine ⟨95914005107461224297472961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63942670071640816198315307 95914005107461224297472961)
    ·
      refine ⟨71935503830595918223104721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95914005107461224297472961 71935503830595918223104721)
      ·
        refine ⟨53951627872946938667328541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71935503830595918223104721 53951627872946938667328541)
        ·
          refine ⟨20231860452355102000248203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53951627872946938667328541 20231860452355102000248203)
          ·
            refine ⟨30347790678532653000372305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20231860452355102000248203 30347790678532653000372305)
            ·
              refine ⟨22760843008899489750279229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30347790678532653000372305 22760843008899489750279229)
              ·
                refine ⟨8535316128337308656354711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22760843008899489750279229 8535316128337308656354711)
                ·
                  refine ⟨12802974192505962984532067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8535316128337308656354711 12802974192505962984532067)
                  ·
                    refine ⟨19204461288758944476798101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12802974192505962984532067 19204461288758944476798101)
                    ·
                      refine ⟨900209122910575522349911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19204461288758944476798101 900209122910575522349911)
                      ·
                        rfl

theorem cell23_1753151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_1753151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753151 prefixEnd_1753151 := by exact prefixLift 1753151
  have htrace : WordTrace (prefixWord ++ tailWord_1753151) baseStart_1753151 baseEnd_1753151 := by
    simpa [prefixWord, tailWord_1753151, baseEnd_1753151] using wordTrace_append hprefix tailTrace_1753151
  have hstable : (prefixWord ++ tailWord_1753151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753151).length < 2 ^ (prefixWord ++ tailWord_1753151).sum := by decide
  have hdescent : baseEnd_1753151 < baseStart_1753151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753165 : List Nat := [1, 6, 1, 1, 1, 1, 2, 2, 4, 4]
def baseStart_1753165 : Nat := 118140960795 + 1753165 * 2 ^ 59
def prefixEnd_1753165 : Nat := 4983230072969 + 3 ^ 40 * 1753165 * 2
def baseEnd_1753165 : Nat := 300072103879912822524949

theorem tailTrace_1753165 : CollatzResearch.WordTrace tailWord_1753165 prefixEnd_1753165 300072103879912822524949 := by
  unfold tailWord_1753165
  simp only [CollatzResearch.WordTrace]
  refine ⟨63943180693590096589324949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42628787129060064392883299 63943180693590096589324949)
  ·
    refine ⟨2997336595012035777624607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63943180693590096589324949 2997336595012035777624607)
    ·
      refine ⟨4496004892518053666436911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2997336595012035777624607 4496004892518053666436911)
      ·
        refine ⟨6744007338777080499655367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4496004892518053666436911 6744007338777080499655367)
        ·
          refine ⟨10116011008165620749483051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6744007338777080499655367 10116011008165620749483051)
          ·
            refine ⟨15174016512248431124224577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10116011008165620749483051 15174016512248431124224577)
            ·
              refine ⟨11380512384186323343168433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15174016512248431124224577 11380512384186323343168433)
              ·
                refine ⟨8535384288139742507376325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11380512384186323343168433 8535384288139742507376325)
                ·
                  refine ⟨1600384554026201720133061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8535384288139742507376325 1600384554026201720133061)
                  ·
                    refine ⟨300072103879912822524949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1600384554026201720133061 300072103879912822524949)
                    ·
                      rfl

theorem cell23_1753165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_1753165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753165 prefixEnd_1753165 := by exact prefixLift 1753165
  have htrace : WordTrace (prefixWord ++ tailWord_1753165) baseStart_1753165 baseEnd_1753165 := by
    simpa [prefixWord, tailWord_1753165, baseEnd_1753165] using wordTrace_append hprefix tailTrace_1753165
  have hstable : (prefixWord ++ tailWord_1753165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753165).length < 2 ^ (prefixWord ++ tailWord_1753165).sum := by decide
  have hdescent : baseEnd_1753165 < baseStart_1753165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753188 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 3, 3, 3]
def baseStart_1753188 : Nat := 118140960795 + 1753188 * 2 ^ 59
def prefixEnd_1753188 : Nat := 4983230072969 + 3 ^ 40 * 1753188 * 2
def baseEnd_1753188 : Nat := 900228121694791877587241

theorem tailTrace_1753188 : CollatzResearch.WordTrace tailWord_1753188 prefixEnd_1753188 900228121694791877587241 := by
  unfold tailWord_1753188
  simp only [CollatzResearch.WordTrace]
  refine ⟨31972009786253385758706109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42629346381671181011608145 31972009786253385758706109)
  ·
    refine ⟨11989503669845019659514791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31972009786253385758706109 11989503669845019659514791)
    ·
      refine ⟨17984255504767529489272187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11989503669845019659514791 17984255504767529489272187)
      ·
        refine ⟨26976383257151294233908281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17984255504767529489272187 26976383257151294233908281)
        ·
          refine ⟨20232287442863470675431211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26976383257151294233908281 20232287442863470675431211)
          ·
            refine ⟨30348431164295206013146817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20232287442863470675431211 30348431164295206013146817)
            ·
              refine ⟨22761323373221404509860113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30348431164295206013146817 22761323373221404509860113)
              ·
                refine ⟨17070992529916053382395085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22761323373221404509860113 17070992529916053382395085)
                ·
                  refine ⟨6401622198718520018398157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17070992529916053382395085 6401622198718520018398157)
                  ·
                    refine ⟨2400608324519445006899309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6401622198718520018398157 2400608324519445006899309)
                    ·
                      refine ⟨900228121694791877587241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2400608324519445006899309 900228121694791877587241)
                      ·
                        rfl

theorem cell23_1753188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_1753188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753188 prefixEnd_1753188 := by exact prefixLift 1753188
  have htrace : WordTrace (prefixWord ++ tailWord_1753188) baseStart_1753188 baseEnd_1753188 := by
    simpa [prefixWord, tailWord_1753188, baseEnd_1753188] using wordTrace_append hprefix tailTrace_1753188
  have hstable : (prefixWord ++ tailWord_1753188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753188).length < 2 ^ (prefixWord ++ tailWord_1753188).sum := by decide
  have hdescent : baseEnd_1753188 < baseStart_1753188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753189 : List Nat := [1, 3, 1, 3, 2, 2, 2, 4, 1, 2, 2]
def baseStart_1753189 : Nat := 118140960795 + 1753189 * 2 ^ 59
def prefixEnd_1753189 : Nat := 4983230072969 + 3 ^ 40 * 1753189 * 2
def baseEnd_1753189 : Nat := 900228635175446373674737

theorem tailTrace_1753189 : CollatzResearch.WordTrace tailWord_1753189 prefixEnd_1753189 900228635175446373674737 := by
  unfold tailWord_1753189
  simp only [CollatzResearch.WordTrace]
  refine ⟨63944056045503148688198621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42629370697002099125465747 63944056045503148688198621)
  ·
    refine ⟨23979021017063680758074483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63944056045503148688198621 23979021017063680758074483)
    ·
      refine ⟨35968531525595521137111725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23979021017063680758074483 35968531525595521137111725)
      ·
        refine ⟨13488199322098320426416897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35968531525595521137111725 13488199322098320426416897)
        ·
          refine ⟨10116149491573740319812673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13488199322098320426416897 10116149491573740319812673)
          ·
            refine ⟨7587112118680305239859505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10116149491573740319812673 7587112118680305239859505)
            ·
              refine ⟨5690334089010228929894629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7587112118680305239859505 5690334089010228929894629)
              ·
                refine ⟨1066937641689417924355243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5690334089010228929894629 1066937641689417924355243)
                ·
                  refine ⟨1600406462534126886532865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1066937641689417924355243 1600406462534126886532865)
                  ·
                    refine ⟨1200304846900595164899649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1600406462534126886532865 1200304846900595164899649)
                    ·
                      refine ⟨900228635175446373674737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1200304846900595164899649 900228635175446373674737)
                      ·
                        rfl

theorem cell23_1753189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_1753189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753189 prefixEnd_1753189 := by exact prefixLift 1753189
  have htrace : WordTrace (prefixWord ++ tailWord_1753189) baseStart_1753189 baseEnd_1753189 := by
    simpa [prefixWord, tailWord_1753189, baseEnd_1753189] using wordTrace_append hprefix tailTrace_1753189
  have hstable : (prefixWord ++ tailWord_1753189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753189).length < 2 ^ (prefixWord ++ tailWord_1753189).sum := by decide
  have hdescent : baseEnd_1753189 < baseStart_1753189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753305 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 2, 5, 2]
def baseStart_1753305 : Nat := 118140960795 + 1753305 * 2 ^ 59
def prefixEnd_1753305 : Nat := 4983230072969 + 3 ^ 40 * 1753305 * 2
def baseEnd_1753305 : Nat := 900288198931367919824203

theorem tailTrace_1753305 : CollatzResearch.WordTrace tailWord_1753305 prefixEnd_1753305 900288198931367919824203 := by
  unfold tailWord_1753305
  simp only [CollatzResearch.WordTrace]
  refine ⟨63948286913082900499421369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42632191275388600332947579 63948286913082900499421369)
  ·
    refine ⟨47961215184812175374566027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63948286913082900499421369 47961215184812175374566027)
    ·
      refine ⟨71941822777218263061849041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47961215184812175374566027 71941822777218263061849041)
      ·
        refine ⟨53956367082913697296386781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71941822777218263061849041 53956367082913697296386781)
        ·
          refine ⟨20233637656092636486145043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53956367082913697296386781 20233637656092636486145043)
          ·
            refine ⟨30350456484138954729217565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20233637656092636486145043 30350456484138954729217565)
            ·
              refine ⟨11381421181552108023456587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30350456484138954729217565 11381421181552108023456587)
              ·
                refine ⟨17072131772328162035184881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11381421181552108023456587 17072131772328162035184881)
                ·
                  refine ⟨12804098829246121526388661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17072131772328162035184881 12804098829246121526388661)
                  ·
                    refine ⟨1200384265241823893098937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12804098829246121526388661 1200384265241823893098937)
                    ·
                      refine ⟨900288198931367919824203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1200384265241823893098937 900288198931367919824203)
                      ·
                        rfl

theorem cell23_1753305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 5, 2].length) (baseStart_1753305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753305 prefixEnd_1753305 := by exact prefixLift 1753305
  have htrace : WordTrace (prefixWord ++ tailWord_1753305) baseStart_1753305 baseEnd_1753305 := by
    simpa [prefixWord, tailWord_1753305, baseEnd_1753305] using wordTrace_append hprefix tailTrace_1753305
  have hstable : (prefixWord ++ tailWord_1753305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753305).length < 2 ^ (prefixWord ++ tailWord_1753305).sum := by decide
  have hdescent : baseEnd_1753305 < baseStart_1753305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753335 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 6, 4, 2]
def baseStart_1753335 : Nat := 118140960795 + 1753335 * 2 ^ 59
def prefixEnd_1753335 : Nat := 4983230072969 + 3 ^ 40 * 1753335 * 2
def baseEnd_1753335 : Nat := 900303603351002802449065

theorem tailTrace_1753335 : CollatzResearch.WordTrace tailWord_1753335 prefixEnd_1753335 900303603351002802449065 := by
  unfold tailWord_1753335
  simp only [CollatzResearch.WordTrace]
  refine ⟨63949381102974215623013459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42632920735316143748675639 63949381102974215623013459)
  ·
    refine ⟨95924071654461323434520189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63949381102974215623013459 95924071654461323434520189)
    ·
      refine ⟨35971526870422996287945071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95924071654461323434520189 35971526870422996287945071)
      ·
        refine ⟨53957290305634494431917607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35971526870422996287945071 53957290305634494431917607)
        ·
          refine ⟨80935935458451741647876411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53957290305634494431917607 80935935458451741647876411)
          ·
            refine ⟨121403903187677612471814617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80935935458451741647876411 121403903187677612471814617)
            ·
              refine ⟨91052927390758209353860963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121403903187677612471814617 91052927390758209353860963)
              ·
                refine ⟨136579391086137314030791445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91052927390758209353860963 136579391086137314030791445)
                ·
                  refine ⟨6402158957162686595193349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 136579391086137314030791445 6402158957162686595193349)
                  ·
                    refine ⟨1200404804468003736598753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6402158957162686595193349 1200404804468003736598753)
                    ·
                      refine ⟨900303603351002802449065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1200404804468003736598753 900303603351002802449065)
                      ·
                        rfl

theorem cell23_1753335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 4, 2].length) (baseStart_1753335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753335 prefixEnd_1753335 := by exact prefixLift 1753335
  have htrace : WordTrace (prefixWord ++ tailWord_1753335) baseStart_1753335 baseEnd_1753335 := by
    simpa [prefixWord, tailWord_1753335, baseEnd_1753335] using wordTrace_append hprefix tailTrace_1753335
  have hstable : (prefixWord ++ tailWord_1753335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753335).length < 2 ^ (prefixWord ++ tailWord_1753335).sum := by decide
  have hdescent : baseEnd_1753335 < baseStart_1753335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753345 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 5, 4]
def baseStart_1753345 : Nat := 118140960795 + 1753345 * 2 ^ 59
def prefixEnd_1753345 : Nat := 4983230072969 + 3 ^ 40 * 1753345 * 2
def baseEnd_1753345 : Nat := 300102912719182587774673

theorem tailTrace_1753345 : CollatzResearch.WordTrace tailWord_1753345 prefixEnd_1753345 300102912719182587774673 := by
  unfold tailWord_1753345
  simp only [CollatzResearch.WordTrace]
  refine ⟨63949745832937987330877489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42633163888625324887251659 63949745832937987330877489)
  ·
    refine ⟨47962309374703490498158117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63949745832937987330877489 47962309374703490498158117)
    ·
      refine ⟨8992933007756904468404647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47962309374703490498158117 8992933007756904468404647)
      ·
        refine ⟨13489399511635356702606971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8992933007756904468404647 13489399511635356702606971)
        ·
          refine ⟨20234099267453035053910457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13489399511635356702606971 20234099267453035053910457)
          ·
            refine ⟨15175574450589776290432843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20234099267453035053910457 15175574450589776290432843)
            ·
              refine ⟨22763361675884664435649265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15175574450589776290432843 22763361675884664435649265)
              ·
                refine ⟨17072521256913498326736949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22763361675884664435649265 17072521256913498326736949)
                ·
                  refine ⟨1600548867835640468131589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17072521256913498326736949 1600548867835640468131589)
                  ·
                    refine ⟨300102912719182587774673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1600548867835640468131589 300102912719182587774673)
                    ·
                      rfl

theorem cell23_1753345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_1753345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753345 prefixEnd_1753345 := by exact prefixLift 1753345
  have htrace : WordTrace (prefixWord ++ tailWord_1753345) baseStart_1753345 baseEnd_1753345 := by
    simpa [prefixWord, tailWord_1753345, baseEnd_1753345] using wordTrace_append hprefix tailTrace_1753345
  have hstable : (prefixWord ++ tailWord_1753345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753345).length < 2 ^ (prefixWord ++ tailWord_1753345).sum := by decide
  have hdescent : baseEnd_1753345 < baseStart_1753345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753352 : List Nat := [2, 1, 3, 2, 3, 1, 1, 2, 2, 4, 2]
def baseStart_1753352 : Nat := 118140960795 + 1753352 * 2 ^ 59
def prefixEnd_1753352 : Nat := 4983230072969 + 3 ^ 40 * 1753352 * 2
def baseEnd_1753352 : Nat := 900312332522129235936487

theorem tailTrace_1753352 : CollatzResearch.WordTrace tailWord_1753352 prefixEnd_1753352 900312332522129235936487 := by
  unfold tailWord_1753352
  simp only [CollatzResearch.WordTrace]
  refine ⟨31975000571956313763191155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42633334095941751684254873 31975000571956313763191155)
  ·
    refine ⟨47962500857934470644786733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31975000571956313763191155 47962500857934470644786733)
    ·
      refine ⟨17985937821725426491795025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47962500857934470644786733 17985937821725426491795025)
      ·
        refine ⟨13489453366294069868846269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17985937821725426491795025 13489453366294069868846269)
        ·
          refine ⟨5058545012360276200817351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13489453366294069868846269 5058545012360276200817351)
          ·
            refine ⟨7587817518540414301226027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5058545012360276200817351 7587817518540414301226027)
            ·
              refine ⟨11381726277810621451839041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7587817518540414301226027 11381726277810621451839041)
              ·
                refine ⟨8536294708357966088879281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11381726277810621451839041 8536294708357966088879281)
                ·
                  refine ⟨6402221031268474566659461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8536294708357966088879281 6402221031268474566659461)
                  ·
                    refine ⟨1200416443362838981248649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6402221031268474566659461 1200416443362838981248649)
                    ·
                      refine ⟨900312332522129235936487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1200416443362838981248649 900312332522129235936487)
                      ·
                        rfl

theorem cell23_1753352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_1753352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753352 prefixEnd_1753352 := by exact prefixLift 1753352
  have htrace : WordTrace (prefixWord ++ tailWord_1753352) baseStart_1753352 baseEnd_1753352 := by
    simpa [prefixWord, tailWord_1753352, baseEnd_1753352] using wordTrace_append hprefix tailTrace_1753352
  have hstable : (prefixWord ++ tailWord_1753352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753352).length < 2 ^ (prefixWord ++ tailWord_1753352).sum := by decide
  have hdescent : baseEnd_1753352 < baseStart_1753352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753355 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 4, 2, 3]
def baseStart_1753355 : Nat := 118140960795 + 1753355 * 2 ^ 59
def prefixEnd_1753355 : Nat := 4983230072969 + 3 ^ 40 * 1753355 * 2
def baseEnd_1753355 : Nat := 900313872964092724198973

theorem tailTrace_1753355 : CollatzResearch.WordTrace tailWord_1753355 prefixEnd_1753355 900313872964092724198973 := by
  unfold tailWord_1753355
  simp only [CollatzResearch.WordTrace]
  refine ⟨63950110562901759038741519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42633407041934506025827679 63950110562901759038741519)
  ·
    refine ⟨95925165844352638558112279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63950110562901759038741519 95925165844352638558112279)
    ·
      refine ⟨143887748766528957837168419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95925165844352638558112279 143887748766528957837168419)
      ·
        refine ⟨215831623149793436755752629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143887748766528957837168419 215831623149793436755752629)
        ·
          refine ⟨20234214670293134695851809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 215831623149793436755752629 20234214670293134695851809)
          ·
            refine ⟨15175661002719851021888857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20234214670293134695851809 15175661002719851021888857)
            ·
              refine ⟨11381745752039888266416643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15175661002719851021888857 11381745752039888266416643)
              ·
                refine ⟨17072618628059832399624965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11381745752039888266416643 17072618628059832399624965)
                ·
                  refine ⟨3201115992761218574929681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17072618628059832399624965 3201115992761218574929681)
                  ·
                    refine ⟨2400836994570913931197261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3201115992761218574929681 2400836994570913931197261)
                    ·
                      refine ⟨900313872964092724198973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2400836994570913931197261 900313872964092724198973)
                      ·
                        rfl

theorem cell23_1753355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 2, 3].length) (baseStart_1753355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753355 prefixEnd_1753355 := by exact prefixLift 1753355
  have htrace : WordTrace (prefixWord ++ tailWord_1753355) baseStart_1753355 baseEnd_1753355 := by
    simpa [prefixWord, tailWord_1753355, baseEnd_1753355] using wordTrace_append hprefix tailTrace_1753355
  have hstable : (prefixWord ++ tailWord_1753355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753355).length < 2 ^ (prefixWord ++ tailWord_1753355).sum := by decide
  have hdescent : baseEnd_1753355 < baseStart_1753355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753396 : List Nat := [2, 5, 1, 1, 1, 2, 3, 3, 1, 4]
def baseStart_1753396 : Nat := 118140960795 + 1753396 * 2 ^ 59
def prefixEnd_1753396 : Nat := 4983230072969 + 3 ^ 40 * 1753396 * 2
def baseEnd_1753396 : Nat := 300111641890309021262095

theorem tailTrace_1753396 : CollatzResearch.WordTrace tailWord_1753396 prefixEnd_1753396 300111641890309021262095 := by
  unfold tailWord_1753396
  simp only [CollatzResearch.WordTrace]
  refine ⟨31975802977876611520492021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42634403970502148693989361 31975802977876611520492021)
  ·
    refine ⟨2997731529175932330046127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31975802977876611520492021 2997731529175932330046127)
    ·
      refine ⟨4496597293763898495069191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2997731529175932330046127 4496597293763898495069191)
      ·
        refine ⟨6744895940645847742603787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4496597293763898495069191 6744895940645847742603787)
        ·
          refine ⟨10117343910968771613905681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6744895940645847742603787 10117343910968771613905681)
          ·
            refine ⟨7588007933226578710429261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10117343910968771613905681 7588007933226578710429261)
            ·
              refine ⟨2845502974959967016410973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7588007933226578710429261 2845502974959967016410973)
              ·
                refine ⟨1067063615609987631154115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2845502974959967016410973 1067063615609987631154115)
                ·
                  refine ⟨1600595423414981446731173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1067063615609987631154115 1600595423414981446731173)
                  ·
                    refine ⟨300111641890309021262095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1600595423414981446731173 300111641890309021262095)
                    ·
                      rfl

theorem cell23_1753396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_1753396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753396 prefixEnd_1753396 := by exact prefixLift 1753396
  have htrace : WordTrace (prefixWord ++ tailWord_1753396) baseStart_1753396 baseEnd_1753396 := by
    simpa [prefixWord, tailWord_1753396, baseEnd_1753396] using wordTrace_append hprefix tailTrace_1753396
  have hstable : (prefixWord ++ tailWord_1753396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753396).length < 2 ^ (prefixWord ++ tailWord_1753396).sum := by decide
  have hdescent : baseEnd_1753396 < baseStart_1753396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753452 : List Nat := [2, 2, 1, 1, 6, 1, 1, 2, 1, 6]
def baseStart_1753452 : Nat := 118140960795 + 1753452 * 2 ^ 59
def prefixEnd_1753452 : Nat := 4983230072969 + 3 ^ 40 * 1753452 * 2
def baseEnd_1753452 : Nat := 300121226862526281562009

theorem tailTrace_1753452 : CollatzResearch.WordTrace tailWord_1753452 prefixEnd_1753452 300121226862526281562009 := by
  unfold tailWord_1753452
  simp only [CollatzResearch.WordTrace]
  refine ⟨31976824221775172302511305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42635765629033563070015073 31976824221775172302511305)
  ·
    refine ⟨23982618166331379226883479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31976824221775172302511305 23982618166331379226883479)
    ·
      refine ⟨35973927249497068840325219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23982618166331379226883479 35973927249497068840325219)
      ·
        refine ⟨53960890874245603260487829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35973927249497068840325219 53960890874245603260487829)
        ·
          refine ⟨2529416759730262652835367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53960890874245603260487829 2529416759730262652835367)
          ·
            refine ⟨3794125139595393979253051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2529416759730262652835367 3794125139595393979253051)
            ·
              refine ⟨5691187709393090968879577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3794125139595393979253051 5691187709393090968879577)
              ·
                refine ⟨4268390782044818226659683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5691187709393090968879577 4268390782044818226659683)
                ·
                  refine ⟨6402586173067227339989525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4268390782044818226659683 6402586173067227339989525)
                  ·
                    refine ⟨300121226862526281562009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6402586173067227339989525 300121226862526281562009)
                    ·
                      rfl

theorem cell23_1753452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 6].length) (baseStart_1753452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753452 prefixEnd_1753452 := by exact prefixLift 1753452
  have htrace : WordTrace (prefixWord ++ tailWord_1753452) baseStart_1753452 baseEnd_1753452 := by
    simpa [prefixWord, tailWord_1753452, baseEnd_1753452] using wordTrace_append hprefix tailTrace_1753452
  have hstable : (prefixWord ++ tailWord_1753452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753452).length < 2 ^ (prefixWord ++ tailWord_1753452).sum := by decide
  have hdescent : baseEnd_1753452 < baseStart_1753452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753469 : List Nat := [1, 4, 1, 1, 2, 4, 2, 2, 2, 4]
def baseStart_1753469 : Nat := 118140960795 + 1753469 * 2 ^ 59
def prefixEnd_1753469 : Nat := 4983230072969 + 3 ^ 40 * 1753469 * 2
def baseEnd_1753469 : Nat := 300124136586235092724483

theorem tailTrace_1753469 : CollatzResearch.WordTrace tailWord_1753469 prefixEnd_1753469 300124136586235092724483 := by
  unfold tailWord_1753469
  simp only [CollatzResearch.WordTrace]
  refine ⟨63954268484488756508391461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42636178989659171005594307 63954268484488756508391461)
  ·
    refine ⟨11991425340841641845323399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63954268484488756508391461 11991425340841641845323399)
    ·
      refine ⟨17987138011262462767985099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11991425340841641845323399 17987138011262462767985099)
      ·
        refine ⟨26980707016893694151977649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17987138011262462767985099 26980707016893694151977649)
        ·
          refine ⟨20235530262670270613983237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26980707016893694151977649 20235530262670270613983237)
          ·
            refine ⟨3794161924250675740121857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20235530262670270613983237 3794161924250675740121857)
            ·
              refine ⟨2845621443188006805091393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3794161924250675740121857 2845621443188006805091393)
              ·
                refine ⟨2134216082391005103818545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2845621443188006805091393 2134216082391005103818545)
                ·
                  refine ⟨1600662061793253827863909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2134216082391005103818545 1600662061793253827863909)
                  ·
                    refine ⟨300124136586235092724483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1600662061793253827863909 300124136586235092724483)
                    ·
                      rfl

theorem cell23_1753469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_1753469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753469 prefixEnd_1753469 := by exact prefixLift 1753469
  have htrace : WordTrace (prefixWord ++ tailWord_1753469) baseStart_1753469 baseEnd_1753469 := by
    simpa [prefixWord, tailWord_1753469, baseEnd_1753469] using wordTrace_append hprefix tailTrace_1753469
  have hstable : (prefixWord ++ tailWord_1753469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753469).length < 2 ^ (prefixWord ++ tailWord_1753469).sum := by decide
  have hdescent : baseEnd_1753469 < baseStart_1753469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753535 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 5]
def baseStart_1753535 : Nat := 118140960795 + 1753535 * 2 ^ 59
def prefixEnd_1753535 : Nat := 4983230072969 + 3 ^ 40 * 1753535 * 2
def baseEnd_1753535 : Nat := 900406299481902019948145

theorem tailTrace_1753535 : CollatzResearch.WordTrace tailWord_1753535 prefixEnd_1753535 900406299481902019948145 := by
  unfold tailWord_1753535
  simp only [CollatzResearch.WordTrace]
  refine ⟨63956675702249649780294059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42637783801499766520196039 63956675702249649780294059)
  ·
    refine ⟨95935013553374474670441089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63956675702249649780294059 95935013553374474670441089)
    ·
      refine ⟨71951260165030856002830817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95935013553374474670441089 71951260165030856002830817)
      ·
        refine ⟨53963445123773142002123113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71951260165030856002830817 53963445123773142002123113)
        ·
          refine ⟨40472583842829856501592335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53963445123773142002123113 40472583842829856501592335)
          ·
            refine ⟨60708875764244784752388503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40472583842829856501592335 60708875764244784752388503)
            ·
              refine ⟨91063313646367177128582755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60708875764244784752388503 91063313646367177128582755)
              ·
                refine ⟨136594970469550765692874133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91063313646367177128582755 136594970469550765692874133)
                ·
                  refine ⟨6402889240760192141853475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 136594970469550765692874133 6402889240760192141853475)
                  ·
                    refine ⟨9604333861140288212780213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6402889240760192141853475 9604333861140288212780213)
                    ·
                      refine ⟨900406299481902019948145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9604333861140288212780213 900406299481902019948145)
                      ·
                        rfl

theorem cell23_1753535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_1753535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753535 prefixEnd_1753535 := by exact prefixLift 1753535
  have htrace : WordTrace (prefixWord ++ tailWord_1753535) baseStart_1753535 baseEnd_1753535 := by
    simpa [prefixWord, tailWord_1753535, baseEnd_1753535] using wordTrace_append hprefix tailTrace_1753535
  have hstable : (prefixWord ++ tailWord_1753535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753535).length < 2 ^ (prefixWord ++ tailWord_1753535).sum := by decide
  have hdescent : baseEnd_1753535 < baseStart_1753535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753615 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 1, 10]
def baseStart_1753615 : Nat := 118140960795 + 1753615 * 2 ^ 59
def prefixEnd_1753615 : Nat := 4983230072969 + 3 ^ 40 * 1753615 * 2
def baseEnd_1753615 : Nat := 300149125978087235649259

theorem tailTrace_1753615 : CollatzResearch.WordTrace tailWord_1753615 prefixEnd_1753615 300149125978087235649259 := by
  unfold tailWord_1753615
  simp only [CollatzResearch.WordTrace]
  refine ⟨63959593541959823443206299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42639729027973215628804199 63959593541959823443206299)
  ·
    refine ⟨95939390312939735164809449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63959593541959823443206299 95939390312939735164809449)
    ·
      refine ⟨71954542734704801373607087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95939390312939735164809449 71954542734704801373607087)
      ·
        refine ⟨107931814102057202060410631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71954542734704801373607087 107931814102057202060410631)
        ·
          refine ⟨161897721153085803090615947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107931814102057202060410631 161897721153085803090615947)
          ·
            refine ⟨242846581729628704635923921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161897721153085803090615947 242846581729628704635923921)
            ·
              refine ⟨182134936297221528476942941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242846581729628704635923921 182134936297221528476942941)
              ·
                refine ⟨68300601111458073178853603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182134936297221528476942941 68300601111458073178853603)
                ·
                  refine ⟨102450901667187109768280405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68300601111458073178853603 102450901667187109768280405)
                  ·
                    refine ⟨300149125978087235649259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 102450901667187109768280405 300149125978087235649259)
                    ·
                      rfl

theorem cell23_1753615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 10].length) (baseStart_1753615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753615 prefixEnd_1753615 := by exact prefixLift 1753615
  have htrace : WordTrace (prefixWord ++ tailWord_1753615) baseStart_1753615 baseEnd_1753615 := by
    simpa [prefixWord, tailWord_1753615, baseEnd_1753615] using wordTrace_append hprefix tailTrace_1753615
  have hstable : (prefixWord ++ tailWord_1753615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753615).length < 2 ^ (prefixWord ++ tailWord_1753615).sum := by decide
  have hdescent : baseEnd_1753615 < baseStart_1753615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753749 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 7, 2, 3]
def baseStart_1753749 : Nat := 118140960795 + 1753749 * 2 ^ 59
def prefixEnd_1753749 : Nat := 4983230072969 + 3 ^ 40 * 1753749 * 2
def baseEnd_1753749 : Nat := 900516184341964182672161

theorem tailTrace_1753749 : CollatzResearch.WordTrace tailWord_1753749 prefixEnd_1753749 900516184341964182672161 := by
  unfold tailWord_1753749
  simp only [CollatzResearch.WordTrace]
  refine ⟨63964480923474364328584301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42642987282316242885722867 63964480923474364328584301)
  ·
    refine ⟨23986680346302886623219113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63964480923474364328584301 23986680346302886623219113)
    ·
      refine ⟨17990010259727164967414335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23986680346302886623219113 17990010259727164967414335)
      ·
        refine ⟨26985015389590747451121503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17990010259727164967414335 26985015389590747451121503)
        ·
          refine ⟨40477523084386121176682255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26985015389590747451121503 40477523084386121176682255)
          ·
            refine ⟨60716284626579181765023383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40477523084386121176682255 60716284626579181765023383)
            ·
              refine ⟨91074426939868772647535075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60716284626579181765023383 91074426939868772647535075)
              ·
                refine ⟨136611640409803158971302613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91074426939868772647535075 136611640409803158971302613)
                ·
                  refine ⟨3201835322104761538389905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 136611640409803158971302613 3201835322104761538389905)
                  ·
                    refine ⟨2401376491578571153792429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3201835322104761538389905 2401376491578571153792429)
                    ·
                      refine ⟨900516184341964182672161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2401376491578571153792429 900516184341964182672161)
                      ·
                        rfl

theorem cell23_1753749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_1753749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753749 prefixEnd_1753749 := by exact prefixLift 1753749
  have htrace : WordTrace (prefixWord ++ tailWord_1753749) baseStart_1753749 baseEnd_1753749 := by
    simpa [prefixWord, tailWord_1753749, baseEnd_1753749] using wordTrace_append hprefix tailTrace_1753749
  have hstable : (prefixWord ++ tailWord_1753749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753749).length < 2 ^ (prefixWord ++ tailWord_1753749).sum := by decide
  have hdescent : baseEnd_1753749 < baseStart_1753749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753756 : List Nat := [2, 2, 3, 2, 2, 1, 2, 1, 4, 4]
def baseStart_1753756 : Nat := 118140960795 + 1753756 * 2 ^ 59
def prefixEnd_1753756 : Nat := 4983230072969 + 3 ^ 40 * 1753756 * 2
def baseEnd_1753756 : Nat := 300173259568848551761543

theorem tailTrace_1753756 : CollatzResearch.WordTrace tailWord_1753756 prefixEnd_1753756 300173259568848551761543 := by
  unfold tailWord_1753756
  simp only [CollatzResearch.WordTrace]
  refine ⟨31982368117224502262044561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42643157489632669682726081 31982368117224502262044561)
  ·
    refine ⟨23986776087918376696533421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31982368117224502262044561 23986776087918376696533421)
    ·
      refine ⟨8995041032969391261200033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23986776087918376696533421 8995041032969391261200033)
      ·
        refine ⟨6746280774727043445900025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8995041032969391261200033 6746280774727043445900025)
        ·
          refine ⟨5059710581045282584425019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6746280774727043445900025 5059710581045282584425019)
          ·
            refine ⟨7589565871567923876637529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5059710581045282584425019 7589565871567923876637529)
            ·
              refine ⟨5692174403675942907478147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7589565871567923876637529 5692174403675942907478147)
              ·
                refine ⟨8538261605513914361217221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5692174403675942907478147 8538261605513914361217221)
                ·
                  refine ⟨1600924051033858942728229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8538261605513914361217221 1600924051033858942728229)
                  ·
                    refine ⟨300173259568848551761543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1600924051033858942728229 300173259568848551761543)
                    ·
                      rfl

theorem cell23_1753756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_1753756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753756 prefixEnd_1753756 := by exact prefixLift 1753756
  have htrace : WordTrace (prefixWord ++ tailWord_1753756) baseStart_1753756 baseEnd_1753756 := by
    simpa [prefixWord, tailWord_1753756, baseEnd_1753756] using wordTrace_append hprefix tailTrace_1753756
  have hstable : (prefixWord ++ tailWord_1753756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753756).length < 2 ^ (prefixWord ++ tailWord_1753756).sum := by decide
  have hdescent : baseEnd_1753756 < baseStart_1753756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753773 : List Nat := [1, 5, 2, 1, 1, 3, 1, 3, 2, 4]
def baseStart_1753773 : Nat := 118140960795 + 1753773 * 2 ^ 59
def prefixEnd_1753773 : Nat := 4983230072969 + 3 ^ 40 * 1753773 * 2
def baseEnd_1753773 : Nat := 300176169292557362924017

theorem tailTrace_1753773 : CollatzResearch.WordTrace tailWord_1753773 prefixEnd_1753773 300176169292557362924017 := by
  unfold tailWord_1753773
  simp only [CollatzResearch.WordTrace]
  refine ⟨63965356275387416427457973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42643570850258277618305315 63965356275387416427457973)
  ·
    refine ⟨5996752150817570290074185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63965356275387416427457973 5996752150817570290074185)
    ·
      refine ⟨4497564113113177717555639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5996752150817570290074185 4497564113113177717555639)
      ·
        refine ⟨6746346169669766576333459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4497564113113177717555639 6746346169669766576333459)
        ·
          refine ⟨10119519254504649864500189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6746346169669766576333459 10119519254504649864500189)
          ·
            refine ⟨3794819720439243699187571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10119519254504649864500189 3794819720439243699187571)
            ·
              refine ⟨5692229580658865548781357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3794819720439243699187571 5692229580658865548781357)
              ·
                refine ⟨2134586092747074580793009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5692229580658865548781357 2134586092747074580793009)
                ·
                  refine ⟨1600939569560305935594757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2134586092747074580793009 1600939569560305935594757)
                  ·
                    refine ⟨300176169292557362924017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1600939569560305935594757 300176169292557362924017)
                    ·
                      rfl

theorem cell23_1753773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_1753773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753773 prefixEnd_1753773 := by exact prefixLift 1753773
  have htrace : WordTrace (prefixWord ++ tailWord_1753773) baseStart_1753773 baseEnd_1753773 := by
    simpa [prefixWord, tailWord_1753773, baseEnd_1753773] using wordTrace_append hprefix tailTrace_1753773
  have hstable : (prefixWord ++ tailWord_1753773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753773).length < 2 ^ (prefixWord ++ tailWord_1753773).sum := by decide
  have hdescent : baseEnd_1753773 < baseStart_1753773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753796 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 3, 3, 3]
def baseStart_1753796 : Nat := 118140960795 + 1753796 * 2 ^ 59
def prefixEnd_1753796 : Nat := 4983230072969 + 3 ^ 40 * 1753796 * 2
def baseEnd_1753796 : Nat := 900540317932725498784445

theorem tailTrace_1753796 : CollatzResearch.WordTrace tailWord_1753796 prefixEnd_1753796 900540317932725498784445 := by
  unfold tailWord_1753796
  simp only [CollatzResearch.WordTrace]
  refine ⟨31983097577152045677772621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42644130102869394237030161 31983097577152045677772621)
  ·
    refine ⟨11993661591432017129164733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31983097577152045677772621 11993661591432017129164733)
    ·
      refine ⟨4497623096787006423436775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11993661591432017129164733 4497623096787006423436775)
      ·
        refine ⟨6746434645180509635155163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4497623096787006423436775 6746434645180509635155163)
        ·
          refine ⟨10119651967770764452732745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6746434645180509635155163 10119651967770764452732745)
          ·
            refine ⟨7589738975828073339549559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10119651967770764452732745 7589738975828073339549559)
            ·
              refine ⟨11384608463742110009324339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7589738975828073339549559 11384608463742110009324339)
              ·
                refine ⟨17076912695613165013986509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11384608463742110009324339 17076912695613165013986509)
                ·
                  refine ⟨6403842260854936880244941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17076912695613165013986509 6403842260854936880244941)
                  ·
                    refine ⟨2401440847820601330091853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6403842260854936880244941 2401440847820601330091853)
                    ·
                      refine ⟨900540317932725498784445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2401440847820601330091853 900540317932725498784445)
                      ·
                        rfl

theorem cell23_1753796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_1753796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753796 prefixEnd_1753796 := by exact prefixLift 1753796
  have htrace : WordTrace (prefixWord ++ tailWord_1753796) baseStart_1753796 baseEnd_1753796 := by
    simpa [prefixWord, tailWord_1753796, baseEnd_1753796] using wordTrace_append hprefix tailTrace_1753796
  have hstable : (prefixWord ++ tailWord_1753796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753796).length < 2 ^ (prefixWord ++ tailWord_1753796).sum := by decide
  have hdescent : baseEnd_1753796 < baseStart_1753796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753829 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 1, 8]
def baseStart_1753829 : Nat := 118140960795 + 1753829 * 2 ^ 59
def prefixEnd_1753829 : Nat := 4983230072969 + 3 ^ 40 * 1753829 * 2
def baseEnd_1753829 : Nat := 300185754264774623223931

theorem tailTrace_1753829 : CollatzResearch.WordTrace tailWord_1753829 prefixEnd_1753829 300185754264774623223931 := by
  unfold tailWord_1753829
  simp only [CollatzResearch.WordTrace]
  refine ⟨63967398763184537991496541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42644932508789691994331027 63967398763184537991496541)
  ·
    refine ⟨23987774536194201746811203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63967398763184537991496541 23987774536194201746811203)
    ·
      refine ⟨35981661804291302620216805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23987774536194201746811203 35981661804291302620216805)
      ·
        refine ⟨6746561588304619241290651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35981661804291302620216805 6746561588304619241290651)
        ·
          refine ⟨10119842382456928861935977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6746561588304619241290651 10119842382456928861935977)
          ·
            refine ⟨7589881786842696646451983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10119842382456928861935977 7589881786842696646451983)
            ·
              refine ⟨11384822680264044969677975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7589881786842696646451983 11384822680264044969677975)
              ·
                refine ⟨17077234020396067454516963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11384822680264044969677975 17077234020396067454516963)
                ·
                  refine ⟨25615851030594101181775445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17077234020396067454516963 25615851030594101181775445)
                  ·
                    refine ⟨300185754264774623223931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25615851030594101181775445 300185754264774623223931)
                    ·
                      rfl

theorem cell23_1753829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 8].length) (baseStart_1753829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753829 prefixEnd_1753829 := by exact prefixLift 1753829
  have htrace : WordTrace (prefixWord ++ tailWord_1753829) baseStart_1753829 baseEnd_1753829 := by
    simpa [prefixWord, tailWord_1753829, baseEnd_1753829] using wordTrace_append hprefix tailTrace_1753829
  have hstable : (prefixWord ++ tailWord_1753829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753829).length < 2 ^ (prefixWord ++ tailWord_1753829).sum := by decide
  have hdescent : baseEnd_1753829 < baseStart_1753829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753853 : List Nat := [1, 4, 1, 1, 1, 1, 4, 2, 4, 2, 2]
def baseStart_1753853 : Nat := 118140960795 + 1753853 * 2 ^ 59
def prefixEnd_1753853 : Nat := 4983230072969 + 3 ^ 40 * 1753853 * 2
def baseEnd_1753853 : Nat := 900569586330031775771683

theorem tailTrace_1753853 : CollatzResearch.WordTrace tailWord_1753853 prefixEnd_1753853 900569586330031775771683 := by
  unfold tailWord_1753853
  simp only [CollatzResearch.WordTrace]
  refine ⟨63968274115097590090370213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42645516076731726726913475 63968274115097590090370213)
  ·
    refine ⟨11994051396580798141944415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63968274115097590090370213 11994051396580798141944415)
    ·
      refine ⟨17991077094871197212916623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11994051396580798141944415 17991077094871197212916623)
      ·
        refine ⟨26986615642306795819374935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17991077094871197212916623 26986615642306795819374935)
        ·
          refine ⟨40479923463460193729062403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26986615642306795819374935 40479923463460193729062403)
          ·
            refine ⟨60719885195190290593593605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40479923463460193729062403 60719885195190290593593605)
            ·
              refine ⟨11384978474098179486298801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60719885195190290593593605 11384978474098179486298801)
              ·
                refine ⟨8538733855573634614724101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11384978474098179486298801 8538733855573634614724101)
                ·
                  refine ⟨1601012597920056490260769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8538733855573634614724101 1601012597920056490260769)
                  ·
                    refine ⟨1200759448440042367695577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1601012597920056490260769 1200759448440042367695577)
                    ·
                      refine ⟨900569586330031775771683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1200759448440042367695577 900569586330031775771683)
                      ·
                        rfl

theorem cell23_1753853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 4, 2, 2].length) (baseStart_1753853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753853 prefixEnd_1753853 := by exact prefixLift 1753853
  have htrace : WordTrace (prefixWord ++ tailWord_1753853) baseStart_1753853 baseEnd_1753853 := by
    simpa [prefixWord, tailWord_1753853, baseEnd_1753853] using wordTrace_append hprefix tailTrace_1753853
  have hstable : (prefixWord ++ tailWord_1753853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753853).length < 2 ^ (prefixWord ++ tailWord_1753853).sum := by decide
  have hdescent : baseEnd_1753853 < baseStart_1753853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753887 : List Nat := [1, 1, 2, 4, 2, 3, 3, 1, 2, 2, 2]
def baseStart_1753887 : Nat := 118140960795 + 1753887 * 2 ^ 59
def prefixEnd_1753887 : Nat := 4983230072969 + 3 ^ 40 * 1753887 * 2
def baseEnd_1753887 : Nat := 900587044672284642746527

theorem tailTrace_1753887 : CollatzResearch.WordTrace tailWord_1753887 prefixEnd_1753887 900587044672284642746527 := by
  unfold tailWord_1753887
  simp only [CollatzResearch.WordTrace]
  refine ⟨63969514196974413897107915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42646342797982942598071943 63969514196974413897107915)
  ·
    refine ⟨95954271295461620845661873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63969514196974413897107915 95954271295461620845661873)
    ·
      refine ⟨71965703471596215634246405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95954271295461620845661873 71965703471596215634246405)
      ·
        refine ⟨13493569400924290431421201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71965703471596215634246405 13493569400924290431421201)
        ·
          refine ⟨10120177050693217823565901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13493569400924290431421201 10120177050693217823565901)
          ·
            refine ⟨3795066394009956683837213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10120177050693217823565901 3795066394009956683837213)
            ·
              refine ⟨1423149897753733756438955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3795066394009956683837213 1423149897753733756438955)
              ·
                refine ⟨2134724846630600634658433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1423149897753733756438955 2134724846630600634658433)
                ·
                  refine ⟨1601043634972950475993825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2134724846630600634658433 1601043634972950475993825)
                  ·
                    refine ⟨1200782726229712856995369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1601043634972950475993825 1200782726229712856995369)
                    ·
                      refine ⟨900587044672284642746527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1200782726229712856995369 900587044672284642746527)
                      ·
                        rfl

theorem cell23_1753887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_1753887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753887 prefixEnd_1753887 := by exact prefixLift 1753887
  have htrace : WordTrace (prefixWord ++ tailWord_1753887) baseStart_1753887 baseEnd_1753887 := by
    simpa [prefixWord, tailWord_1753887, baseEnd_1753887] using wordTrace_append hprefix tailTrace_1753887
  have hstable : (prefixWord ++ tailWord_1753887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753887).length < 2 ^ (prefixWord ++ tailWord_1753887).sum := by decide
  have hdescent : baseEnd_1753887 < baseStart_1753887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753889 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 3, 7]
def baseStart_1753889 : Nat := 118140960795 + 1753889 * 2 ^ 59
def prefixEnd_1753889 : Nat := 4983230072969 + 3 ^ 40 * 1753889 * 2
def baseEnd_1753889 : Nat := 300196023877864544973839

theorem tailTrace_1753889 : CollatzResearch.WordTrace tailWord_1753889 prefixEnd_1753889 300196023877864544973839 := by
  unfold tailWord_1753889
  simp only [CollatzResearch.WordTrace]
  refine ⟨63969587142967168238680721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42646391428644778825787147 63969587142967168238680721)
  ·
    refine ⟨47977190357225376179010541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63969587142967168238680721 47977190357225376179010541)
    ·
      refine ⟨17991446383959516067128953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47977190357225376179010541 17991446383959516067128953)
      ·
        refine ⟨13493584787969637050346715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17991446383959516067128953 13493584787969637050346715)
        ·
          refine ⟨20240377181954455575520073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13493584787969637050346715 20240377181954455575520073)
          ·
            refine ⟨15180282886465841681640055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20240377181954455575520073 15180282886465841681640055)
            ·
              refine ⟨22770424329698762522460083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15180282886465841681640055 22770424329698762522460083)
              ·
                refine ⟨34155636494548143783690125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22770424329698762522460083 34155636494548143783690125)
                ·
                  refine ⟨12808363685455553918883797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34155636494548143783690125 12808363685455553918883797)
                  ·
                    refine ⟨300196023877864544973839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12808363685455553918883797 300196023877864544973839)
                    ·
                      rfl

theorem cell23_1753889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_1753889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753889 prefixEnd_1753889 := by exact prefixLift 1753889
  have htrace : WordTrace (prefixWord ++ tailWord_1753889) baseStart_1753889 baseEnd_1753889 := by
    simpa [prefixWord, tailWord_1753889, baseEnd_1753889] using wordTrace_append hprefix tailTrace_1753889
  have hstable : (prefixWord ++ tailWord_1753889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753889).length < 2 ^ (prefixWord ++ tailWord_1753889).sum := by decide
  have hdescent : baseEnd_1753889 < baseStart_1753889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753906 : List Nat := [3, 2, 1, 1, 3, 1, 2, 3, 2, 5]
def baseStart_1753906 : Nat := 118140960795 + 1753906 * 2 ^ 59
def prefixEnd_1753906 : Nat := 4983230072969 + 3 ^ 40 * 1753906 * 2
def baseEnd_1753906 : Nat := 300198933601573356136313

theorem tailTrace_1753906 : CollatzResearch.WordTrace tailWord_1753906 prefixEnd_1753906 300198933601573356136313 := by
  unfold tailWord_1753906
  simp only [CollatzResearch.WordTrace]
  refine ⟨15992551795976395035512393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42646804789270386761366381 15992551795976395035512393)
  ·
    refine ⟨11994413846982296276634295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15992551795976395035512393 11994413846982296276634295)
    ·
      refine ⟨17991620770473444414951443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11994413846982296276634295 17991620770473444414951443)
      ·
        refine ⟨26987431155710166622427165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17991620770473444414951443 26987431155710166622427165)
        ·
          refine ⟨10120286683391312483410187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26987431155710166622427165 10120286683391312483410187)
          ·
            refine ⟨15180430025086968725115281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10120286683391312483410187 15180430025086968725115281)
            ·
              refine ⟨11385322518815226543836461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15180430025086968725115281 11385322518815226543836461)
              ·
                refine ⟨4269495944555709953938673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11385322518815226543836461 4269495944555709953938673)
                ·
                  refine ⟨3202121958416782465454005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4269495944555709953938673 3202121958416782465454005)
                  ·
                    refine ⟨300198933601573356136313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3202121958416782465454005 300198933601573356136313)
                    ·
                      rfl

theorem cell23_1753906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_1753906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753906 prefixEnd_1753906 := by exact prefixLift 1753906
  have htrace : WordTrace (prefixWord ++ tailWord_1753906) baseStart_1753906 baseEnd_1753906 := by
    simpa [prefixWord, tailWord_1753906, baseEnd_1753906] using wordTrace_append hprefix tailTrace_1753906
  have hstable : (prefixWord ++ tailWord_1753906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753906).length < 2 ^ (prefixWord ++ tailWord_1753906).sum := by decide
  have hdescent : baseEnd_1753906 < baseStart_1753906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753939 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 6]
def baseStart_1753939 : Nat := 118140960795 + 1753939 * 2 ^ 59
def prefixEnd_1753939 : Nat := 4983230072969 + 3 ^ 40 * 1753939 * 2
def baseEnd_1753939 : Nat := 900613745666318439296287

theorem tailTrace_1753939 : CollatzResearch.WordTrace tailWord_1753939 prefixEnd_1753939 900613745666318439296287 := by
  unfold tailWord_1753939
  simp only [CollatzResearch.WordTrace]
  refine ⟨63971410792786026778000871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42647607195190684518667247 63971410792786026778000871)
  ·
    refine ⟨95957116189179040167001307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63971410792786026778000871 95957116189179040167001307)
    ·
      refine ⟨143935674283768560250501961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95957116189179040167001307 143935674283768560250501961)
      ·
        refine ⟨107951755712826420187876471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143935674283768560250501961 107951755712826420187876471)
        ·
          refine ⟨161927633569239630281814707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107951755712826420187876471 161927633569239630281814707)
          ·
            refine ⟨242891450353859445422722061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161927633569239630281814707 242891450353859445422722061)
            ·
              refine ⟨91084293882697292033520773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242891450353859445422722061 91084293882697292033520773)
              ·
                refine ⟨17078305103005742256285145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91084293882697292033520773 17078305103005742256285145)
                ·
                  refine ⟨12808728827254306692213859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17078305103005742256285145 12808728827254306692213859)
                  ·
                    refine ⟨19213093240881460038320789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12808728827254306692213859 19213093240881460038320789)
                    ·
                      refine ⟨900613745666318439296287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19213093240881460038320789 900613745666318439296287)
                      ·
                        rfl

theorem cell23_1753939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 6].length) (baseStart_1753939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753939 prefixEnd_1753939 := by exact prefixLift 1753939
  have htrace : WordTrace (prefixWord ++ tailWord_1753939) baseStart_1753939 baseEnd_1753939 := by
    simpa [prefixWord, tailWord_1753939, baseEnd_1753939] using wordTrace_append hprefix tailTrace_1753939
  have hstable : (prefixWord ++ tailWord_1753939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753939).length < 2 ^ (prefixWord ++ tailWord_1753939).sum := by decide
  have hdescent : baseEnd_1753939 < baseStart_1753939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753996 : List Nat := [2, 2, 1, 2, 1, 2, 3, 2, 3, 5]
def baseStart_1753996 : Nat := 118140960795 + 1753996 * 2 ^ 59
def prefixEnd_1753996 : Nat := 4983230072969 + 3 ^ 40 * 1753996 * 2
def baseEnd_1753996 : Nat := 300214338021208238761175

theorem tailTrace_1753996 : CollatzResearch.WordTrace tailWord_1753996 prefixEnd_1753996 300214338021208238761175 := by
  unfold tailWord_1753996
  simp only [CollatzResearch.WordTrace]
  refine ⟨31986744876789762756412921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42648993169053017008550561 31986744876789762756412921)
  ·
    refine ⟨23990058657592322067309691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31986744876789762756412921 23990058657592322067309691)
    ·
      refine ⟨35985087986388483100964537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23990058657592322067309691 35985087986388483100964537)
      ·
        refine ⟨26988815989791362325723403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35985087986388483100964537 26988815989791362325723403)
        ·
          refine ⟨40483223984687043488585105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26988815989791362325723403 40483223984687043488585105)
          ·
            refine ⟨30362417988515282616438829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40483223984687043488585105 30362417988515282616438829)
            ·
              refine ⟨11385906745693230981164561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30362417988515282616438829 11385906745693230981164561)
              ·
                refine ⟨8539430059269923235873421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11385906745693230981164561 8539430059269923235873421)
                ·
                  refine ⟨3202286272226221213452533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8539430059269923235873421 3202286272226221213452533)
                  ·
                    refine ⟨300214338021208238761175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3202286272226221213452533 300214338021208238761175)
                    ·
                      rfl

theorem cell23_1753996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 3, 5].length) (baseStart_1753996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1753996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1753996 prefixEnd_1753996 := by exact prefixLift 1753996
  have htrace : WordTrace (prefixWord ++ tailWord_1753996) baseStart_1753996 baseEnd_1753996 := by
    simpa [prefixWord, tailWord_1753996, baseEnd_1753996] using wordTrace_append hprefix tailTrace_1753996
  have hstable : (prefixWord ++ tailWord_1753996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753996).length < 2 ^ (prefixWord ++ tailWord_1753996).sum := by decide
  have hdescent : baseEnd_1753996 < baseStart_1753996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754013 : List Nat := [1, 4, 2, 1, 2, 1, 2, 4, 1, 5]
def baseStart_1754013 : Nat := 118140960795 + 1754013 * 2 ^ 59
def prefixEnd_1754013 : Nat := 4983230072969 + 3 ^ 40 * 1754013 * 2
def baseEnd_1754013 : Nat := 300217247744917049923649

theorem tailTrace_1754013 : CollatzResearch.WordTrace tailWord_1754013 prefixEnd_1754013 300217247744917049923649 := by
  unfold tailWord_1754013
  simp only [CollatzResearch.WordTrace]
  refine ⟨63974109794517937416194693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42649406529678624944129795 63974109794517937416194693)
  ·
    refine ⟨11995145586472113265536505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63974109794517937416194693 11995145586472113265536505)
    ·
      refine ⟨8996359189854084949152379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11995145586472113265536505 8996359189854084949152379)
      ·
        refine ⟨13494538784781127423728569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8996359189854084949152379 13494538784781127423728569)
        ·
          refine ⟨10120904088585845567796427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13494538784781127423728569 10120904088585845567796427)
          ·
            refine ⟨15181356132878768351694641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10120904088585845567796427 15181356132878768351694641)
            ·
              refine ⟨11386017099659076263770981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15181356132878768351694641 11386017099659076263770981)
              ·
                refine ⟨2134878206186076799457059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11386017099659076263770981 2134878206186076799457059)
                ·
                  refine ⟨3202317309279115199185589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2134878206186076799457059 3202317309279115199185589)
                  ·
                    refine ⟨300217247744917049923649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3202317309279115199185589 300217247744917049923649)
                    ·
                      rfl

theorem cell23_1754013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_1754013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754013 prefixEnd_1754013 := by exact prefixLift 1754013
  have htrace : WordTrace (prefixWord ++ tailWord_1754013) baseStart_1754013 baseEnd_1754013 := by
    simpa [prefixWord, tailWord_1754013, baseEnd_1754013] using wordTrace_append hprefix tailTrace_1754013
  have hstable : (prefixWord ++ tailWord_1754013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754013).length < 2 ^ (prefixWord ++ tailWord_1754013).sum := by decide
  have hdescent : baseEnd_1754013 < baseStart_1754013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754063 : List Nat := [1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 4]
def baseStart_1754063 : Nat := 118140960795 + 1754063 * 2 ^ 59
def prefixEnd_1754063 : Nat := 4983230072969 + 3 ^ 40 * 1754063 * 2
def baseEnd_1754063 : Nat := 900677417267475954145717

theorem tailTrace_1754063 : CollatzResearch.WordTrace tailWord_1754063 prefixEnd_1754063 900677417267475954145717 := by
  unfold tailWord_1754063
  simp only [CollatzResearch.WordTrace]
  refine ⟨63975933444336795955514843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42650622296224530637009895 63975933444336795955514843)
  ·
    refine ⟨95963900166505193933272265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63975933444336795955514843 95963900166505193933272265)
    ·
      refine ⟨71972925124878895449954199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95963900166505193933272265 71972925124878895449954199)
      ·
        refine ⟨107959387687318343174931299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71972925124878895449954199 107959387687318343174931299)
        ·
          refine ⟨161939081530977514762396949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107959387687318343174931299 161939081530977514762396949)
          ·
            refine ⟨7590894446764571004487357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 161939081530977514762396949 7590894446764571004487357)
            ·
              refine ⟨2846585417536714126682759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7590894446764571004487357 2846585417536714126682759)
              ·
                refine ⟨4269878126305071190024139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2846585417536714126682759 4269878126305071190024139)
                ·
                  refine ⟨6404817189457606785036209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4269878126305071190024139 6404817189457606785036209)
                  ·
                    refine ⟨4803612892093205088777157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6404817189457606785036209 4803612892093205088777157)
                    ·
                      refine ⟨900677417267475954145717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4803612892093205088777157 900677417267475954145717)
                      ·
                        rfl

theorem cell23_1754063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 4].length) (baseStart_1754063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754063 prefixEnd_1754063 := by exact prefixLift 1754063
  have htrace : WordTrace (prefixWord ++ tailWord_1754063) baseStart_1754063 baseEnd_1754063 := by
    simpa [prefixWord, tailWord_1754063, baseEnd_1754063] using wordTrace_append hprefix tailTrace_1754063
  have hstable : (prefixWord ++ tailWord_1754063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754063).length < 2 ^ (prefixWord ++ tailWord_1754063).sum := by decide
  have hdescent : baseEnd_1754063 < baseStart_1754063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754073 : List Nat := [1, 2, 1, 2, 5, 1, 4, 7]
def baseStart_1754073 : Nat := 118140960795 + 1754073 * 2 ^ 59
def prefixEnd_1754073 : Nat := 4983230072969 + 3 ^ 40 * 1754073 * 2
def baseEnd_1754073 : Nat := 33358613039778552408173

theorem tailTrace_1754073 : CollatzResearch.WordTrace tailWord_1754073 prefixEnd_1754073 33358613039778552408173 := by
  unfold tailWord_1754073
  simp only [CollatzResearch.WordTrace]
  refine ⟨63976298174300567663378873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42650865449533711775585915 63976298174300567663378873)
  ·
    refine ⟨47982223630725425747534155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63976298174300567663378873 47982223630725425747534155)
    ·
      refine ⟨71973335446088138621301233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47982223630725425747534155 71973335446088138621301233)
      ·
        refine ⟨53980001584566103965975925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71973335446088138621301233 53980001584566103965975925)
        ·
          refine ⟨5060625148553072246810243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53980001584566103965975925 5060625148553072246810243)
          ·
            refine ⟨7590937722829608370215365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5060625148553072246810243 7590937722829608370215365)
            ·
              refine ⟨1423300823030551569415381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7590937722829608370215365 1423300823030551569415381)
              ·
                refine ⟨33358613039778552408173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1423300823030551569415381 33358613039778552408173)
                ·
                  rfl

theorem cell23_1754073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 7].length) (baseStart_1754073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754073 prefixEnd_1754073 := by exact prefixLift 1754073
  have htrace : WordTrace (prefixWord ++ tailWord_1754073) baseStart_1754073 baseEnd_1754073 := by
    simpa [prefixWord, tailWord_1754073, baseEnd_1754073] using wordTrace_append hprefix tailTrace_1754073
  have hstable : (prefixWord ++ tailWord_1754073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754073).length < 2 ^ (prefixWord ++ tailWord_1754073).sum := by decide
  have hdescent : baseEnd_1754073 < baseStart_1754073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754083 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 3, 3, 3]
def baseStart_1754083 : Nat := 118140960795 + 1754083 * 2 ^ 59
def prefixEnd_1754083 : Nat := 4983230072969 + 3 ^ 40 * 1754083 * 2
def baseEnd_1754083 : Nat := 900687686880565875895625

theorem tailTrace_1754083 : CollatzResearch.WordTrace tailWord_1754083 prefixEnd_1754083 900687686880565875895625 := by
  unfold tailWord_1754083
  simp only [CollatzResearch.WordTrace]
  refine ⟨63976662904264339371242903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42651108602842892914161935 63976662904264339371242903)
  ·
    refine ⟨95964994356396509056864355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63976662904264339371242903 95964994356396509056864355)
    ·
      refine ⟨143947491534594763585296533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95964994356396509056864355 143947491534594763585296533)
      ·
        refine ⟨6747538665684129543060775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 143947491534594763585296533 6747538665684129543060775)
        ·
          refine ⟨10121307998526194314591163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6747538665684129543060775 10121307998526194314591163)
          ·
            refine ⟨15181961997789291471886745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10121307998526194314591163 15181961997789291471886745)
            ·
              refine ⟨11386471498341968603915059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15181961997789291471886745 11386471498341968603915059)
              ·
                refine ⟨17079707247512952905872589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11386471498341968603915059 17079707247512952905872589)
                ·
                  refine ⟨6404890217817357339702221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17079707247512952905872589 6404890217817357339702221)
                  ·
                    refine ⟨2401833831681509002388333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6404890217817357339702221 2401833831681509002388333)
                    ·
                      refine ⟨900687686880565875895625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2401833831681509002388333 900687686880565875895625)
                      ·
                        rfl

theorem cell23_1754083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_1754083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754083 prefixEnd_1754083 := by exact prefixLift 1754083
  have htrace : WordTrace (prefixWord ++ tailWord_1754083) baseStart_1754083 baseEnd_1754083 := by
    simpa [prefixWord, tailWord_1754083, baseEnd_1754083] using wordTrace_append hprefix tailTrace_1754083
  have hstable : (prefixWord ++ tailWord_1754083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754083).length < 2 ^ (prefixWord ++ tailWord_1754083).sum := by decide
  have hdescent : baseEnd_1754083 < baseStart_1754083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754096 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 5]
def baseStart_1754096 : Nat := 118140960795 + 1754096 * 2 ^ 59
def prefixEnd_1754096 : Nat := 4983230072969 + 3 ^ 40 * 1754096 * 2
def baseEnd_1754096 : Nat := 900694362129074325033065

theorem tailTrace_1754096 : CollatzResearch.WordTrace tailWord_1754096 prefixEnd_1754096 900694362129074325033065 := by
  unfold tailWord_1754096
  simp only [CollatzResearch.WordTrace]
  refine ⟨31988568526608621295733071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42651424702144828394310761 31988568526608621295733071)
  ·
    refine ⟨47982852789912931943599607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31988568526608621295733071 47982852789912931943599607)
    ·
      refine ⟨71974279184869397915399411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47982852789912931943599607 71974279184869397915399411)
      ·
        refine ⟨107961418777304096873099117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71974279184869397915399411 107961418777304096873099117)
        ·
          refine ⟨40485532041489036327412169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107961418777304096873099117 40485532041489036327412169)
          ·
            refine ⟨30364149031116777245559127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40485532041489036327412169 30364149031116777245559127)
            ·
              refine ⟨45546223546675165868338691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30364149031116777245559127 45546223546675165868338691)
              ·
                refine ⟨68319335320012748802508037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45546223546675165868338691 68319335320012748802508037)
                ·
                  refine ⟨12809875372502390400470257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68319335320012748802508037 12809875372502390400470257)
                  ·
                    refine ⟨9607406529376792800352693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12809875372502390400470257 9607406529376792800352693)
                    ·
                      refine ⟨900694362129074325033065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9607406529376792800352693 900694362129074325033065)
                      ·
                        rfl

theorem cell23_1754096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 5].length) (baseStart_1754096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754096 prefixEnd_1754096 := by exact prefixLift 1754096
  have htrace : WordTrace (prefixWord ++ tailWord_1754096) baseStart_1754096 baseEnd_1754096 := by
    simpa [prefixWord, tailWord_1754096, baseEnd_1754096] using wordTrace_append hprefix tailTrace_1754096
  have hstable : (prefixWord ++ tailWord_1754096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754096).length < 2 ^ (prefixWord ++ tailWord_1754096).sum := by decide
  have hdescent : baseEnd_1754096 < baseStart_1754096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754143 : List Nat := [1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 5]
def baseStart_1754143 : Nat := 118140960795 + 1754143 * 2 ^ 59
def prefixEnd_1754143 : Nat := 4983230072969 + 3 ^ 40 * 1754143 * 2
def baseEnd_1754143 : Nat := 900718495719835641145349

theorem tailTrace_1754143 : CollatzResearch.WordTrace tailWord_1754143 prefixEnd_1754143 900718495719835641145349 := by
  unfold tailWord_1754143
  simp only [CollatzResearch.WordTrace]
  refine ⟨63978851284046969618427083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42652567522697979745618055 63978851284046969618427083)
  ·
    refine ⟨95968276926070454427640625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63978851284046969618427083 95968276926070454427640625)
    ·
      refine ⟨71976207694552840820730469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95968276926070454427640625 71976207694552840820730469)
      ·
        refine ⟨13495538942728657653886963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71976207694552840820730469 13495538942728657653886963)
        ·
          refine ⟨20243308414092986480830445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13495538942728657653886963 20243308414092986480830445)
          ·
            refine ⟨7591240655284869930311417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20243308414092986480830445 7591240655284869930311417)
            ·
              refine ⟨5693430491463652447733563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7591240655284869930311417 5693430491463652447733563)
              ·
                refine ⟨8540145737195478671600345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5693430491463652447733563 8540145737195478671600345)
                ·
                  refine ⟨6405109302896609003700259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8540145737195478671600345 6405109302896609003700259)
                  ·
                    refine ⟨9607663954344913505550389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6405109302896609003700259 9607663954344913505550389)
                    ·
                      refine ⟨900718495719835641145349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9607663954344913505550389 900718495719835641145349)
                      ·
                        rfl

theorem cell23_1754143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_1754143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754143 prefixEnd_1754143 := by exact prefixLift 1754143
  have htrace : WordTrace (prefixWord ++ tailWord_1754143) baseStart_1754143 baseEnd_1754143 := by
    simpa [prefixWord, tailWord_1754143, baseEnd_1754143] using wordTrace_append hprefix tailTrace_1754143
  have hstable : (prefixWord ++ tailWord_1754143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754143).length < 2 ^ (prefixWord ++ tailWord_1754143).sum := by decide
  have hdescent : baseEnd_1754143 < baseStart_1754143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754174 : List Nat := [4, 2, 1, 3, 1, 2, 2, 1, 1, 4, 2]
def baseStart_1754174 : Nat := 118140960795 + 1754174 * 2 ^ 59
def prefixEnd_1754174 : Nat := 4983230072969 + 3 ^ 40 * 1754174 * 2
def baseEnd_1754174 : Nat := 900734413620125019857707

theorem tailTrace_1754174 : CollatzResearch.WordTrace tailWord_1754174 prefixEnd_1754174 900734413620125019857707 := by
  unfold tailWord_1754174
  simp only [CollatzResearch.WordTrace]
  refine ⟨7997497743366832739100697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42653321297956441275203717 7997497743366832739100697)
  ·
    refine ⟨5998123307525124554325523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7997497743366832739100697 5998123307525124554325523)
    ·
      refine ⟨8997184961287686831488285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5998123307525124554325523 8997184961287686831488285)
      ·
        refine ⟨3373944360482882561808107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8997184961287686831488285 3373944360482882561808107)
        ·
          refine ⟨5060916540724323842712161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3373944360482882561808107 5060916540724323842712161)
          ·
            refine ⟨3795687405543242882034121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5060916540724323842712161 3795687405543242882034121)
            ·
              refine ⟨2846765554157432161525591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3795687405543242882034121 2846765554157432161525591)
              ·
                refine ⟨4270148331236148242288387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2846765554157432161525591 4270148331236148242288387)
                ·
                  refine ⟨6405222496854222363432581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4270148331236148242288387 6405222496854222363432581)
                  ·
                    refine ⟨1200979218160166693143609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6405222496854222363432581 1200979218160166693143609)
                    ·
                      refine ⟨900734413620125019857707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1200979218160166693143609 900734413620125019857707)
                      ·
                        rfl

theorem cell23_1754174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_1754174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754174 prefixEnd_1754174 := by exact prefixLift 1754174
  have htrace : WordTrace (prefixWord ++ tailWord_1754174) baseStart_1754174 baseEnd_1754174 := by
    simpa [prefixWord, tailWord_1754174, baseEnd_1754174] using wordTrace_append hprefix tailTrace_1754174
  have hstable : (prefixWord ++ tailWord_1754174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754174).length < 2 ^ (prefixWord ++ tailWord_1754174).sum := by decide
  have hdescent : baseEnd_1754174 < baseStart_1754174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754230 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4]
def baseStart_1754230 : Nat := 118140960795 + 1754230 * 2 ^ 59
def prefixEnd_1754230 : Nat := 4983230072969 + 3 ^ 40 * 1754230 * 2
def baseEnd_1754230 : Nat := 900763168536776800757449

theorem tailTrace_1754230 : CollatzResearch.WordTrace tailWord_1754230 prefixEnd_1754230 900763168536776800757449 := by
  unfold tailWord_1754230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3998876527170736467302759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42654682956487855651229429 3998876527170736467302759)
  ·
    refine ⟨5998314790756104700954139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3998876527170736467302759 5998314790756104700954139)
    ·
      refine ⟨8997472186134157051431209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5998314790756104700954139 8997472186134157051431209)
      ·
        refine ⟨6748104139600617788573407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8997472186134157051431209 6748104139600617788573407)
        ·
          refine ⟨10122156209400926682860111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6748104139600617788573407 10122156209400926682860111)
          ·
            refine ⟨15183234314101390024290167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10122156209400926682860111 15183234314101390024290167)
            ·
              refine ⟨22774851471152085036435251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15183234314101390024290167 22774851471152085036435251)
              ·
                refine ⟨34162277206728127554652877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22774851471152085036435251 34162277206728127554652877)
                ·
                  refine ⟨12810853952523047832994829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34162277206728127554652877 12810853952523047832994829)
                  ·
                    refine ⟨4804070232196142937373061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12810853952523047832994829 4804070232196142937373061)
                    ·
                      refine ⟨900763168536776800757449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4804070232196142937373061 900763168536776800757449)
                      ·
                        rfl

theorem cell23_1754230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_1754230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754230 prefixEnd_1754230 := by exact prefixLift 1754230
  have htrace : WordTrace (prefixWord ++ tailWord_1754230) baseStart_1754230 baseEnd_1754230 := by
    simpa [prefixWord, tailWord_1754230, baseEnd_1754230] using wordTrace_append hprefix tailTrace_1754230
  have hstable : (prefixWord ++ tailWord_1754230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754230).length < 2 ^ (prefixWord ++ tailWord_1754230).sum := by decide
  have hdescent : baseEnd_1754230 < baseStart_1754230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754240 : List Nat := [2, 1, 1, 2, 1, 3, 4, 2, 3, 4]
def baseStart_1754240 : Nat := 118140960795 + 1754240 * 2 ^ 59
def prefixEnd_1754240 : Nat := 4983230072969 + 3 ^ 40 * 1754240 * 2
def baseEnd_1754240 : Nat := 300256101114440587210801

theorem tailTrace_1754240 : CollatzResearch.WordTrace tailWord_1754240 prefixEnd_1754240 300256101114440587210801 := by
  unfold tailWord_1754240
  simp only [CollatzResearch.WordTrace]
  refine ⟨31991194582347777592354087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42654926109797036789805449 31991194582347777592354087)
  ·
    refine ⟨47986791873521666388531131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31991194582347777592354087 47986791873521666388531131)
    ·
      refine ⟨71980187810282499582796697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47986791873521666388531131 71980187810282499582796697)
      ·
        refine ⟨53985140857711874687097523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71980187810282499582796697 53985140857711874687097523)
        ·
          refine ⟨80977711286567812030646285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53985140857711874687097523 80977711286567812030646285)
          ·
            refine ⟨30366641732462929511492357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80977711286567812030646285 30366641732462929511492357)
            ·
              refine ⟨5693745324836799283404817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30366641732462929511492357 5693745324836799283404817)
              ·
                refine ⟨4270308993627599462553613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5693745324836799283404817 4270308993627599462553613)
                ·
                  refine ⟨1601365872610349798457605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4270308993627599462553613 1601365872610349798457605)
                  ·
                    refine ⟨300256101114440587210801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1601365872610349798457605 300256101114440587210801)
                    ·
                      rfl

theorem cell23_1754240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 3, 4].length) (baseStart_1754240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754240 prefixEnd_1754240 := by exact prefixLift 1754240
  have htrace : WordTrace (prefixWord ++ tailWord_1754240) baseStart_1754240 baseEnd_1754240 := by
    simpa [prefixWord, tailWord_1754240, baseEnd_1754240] using wordTrace_append hprefix tailTrace_1754240
  have hstable : (prefixWord ++ tailWord_1754240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754240).length < 2 ^ (prefixWord ++ tailWord_1754240).sum := by decide
  have hdescent : baseEnd_1754240 < baseStart_1754240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754243 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 4]
def baseStart_1754243 : Nat := 118140960795 + 1754243 * 2 ^ 59
def prefixEnd_1754243 : Nat := 4983230072969 + 3 ^ 40 * 1754243 * 2
def baseEnd_1754243 : Nat := 900769843785285249894889

theorem tailTrace_1754243 : CollatzResearch.WordTrace tailWord_1754243 prefixEnd_1754243 900769843785285249894889 := by
  unfold tailWord_1754243
  simp only [CollatzResearch.WordTrace]
  refine ⟨63982498583684686697067383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42654999055789791131378255 63982498583684686697067383)
  ·
    refine ⟨95973747875527030045601075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63982498583684686697067383 95973747875527030045601075)
    ·
      refine ⟨143960621813290545068401613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95973747875527030045601075 143960621813290545068401613)
      ·
        refine ⟨53985233179983954400650605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143960621813290545068401613 53985233179983954400650605)
        ·
          refine ⟨20244462442493982900243977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53985233179983954400650605 20244462442493982900243977)
          ·
            refine ⟨15183346831870487175182983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20244462442493982900243977 15183346831870487175182983)
            ·
              refine ⟨22775020247805730762774475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15183346831870487175182983 22775020247805730762774475)
              ·
                refine ⟨34162530371708596144161713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22775020247805730762774475 34162530371708596144161713)
                ·
                  refine ⟨25621897778781447108121285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34162530371708596144161713 25621897778781447108121285)
                  ·
                    refine ⟨4804105833521521332772741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25621897778781447108121285 4804105833521521332772741)
                    ·
                      refine ⟨900769843785285249894889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4804105833521521332772741 900769843785285249894889)
                      ·
                        rfl

theorem cell23_1754243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_1754243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754243 prefixEnd_1754243 := by exact prefixLift 1754243
  have htrace : WordTrace (prefixWord ++ tailWord_1754243) baseStart_1754243 baseEnd_1754243 := by
    simpa [prefixWord, tailWord_1754243, baseEnd_1754243] using wordTrace_append hprefix tailTrace_1754243
  have hstable : (prefixWord ++ tailWord_1754243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754243).length < 2 ^ (prefixWord ++ tailWord_1754243).sum := by decide
  have hdescent : baseEnd_1754243 < baseStart_1754243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754250 : List Nat := [3, 1, 2, 3, 1, 1, 1, 3, 1, 4, 3]
def baseStart_1754250 : Nat := 118140960795 + 1754250 * 2 ^ 59
def prefixEnd_1754250 : Nat := 4983230072969 + 3 ^ 40 * 1754250 * 2
def baseEnd_1754250 : Nat := 900773438149866722507357

theorem tailTrace_1754250 : CollatzResearch.WordTrace tailWord_1754250 prefixEnd_1754250 900773438149866722507357 := by
  unfold tailWord_1754250
  simp only [CollatzResearch.WordTrace]
  refine ⟨15995688473664831723143051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42655169263106217928381469 15995688473664831723143051)
  ·
    refine ⟨23993532710497247584714577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15995688473664831723143051 23993532710497247584714577)
    ·
      refine ⟨17995149532872935688535933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23993532710497247584714577 17995149532872935688535933)
      ·
        refine ⟨6748181074827350883200975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17995149532872935688535933 6748181074827350883200975)
        ·
          refine ⟨10122271612241026324801463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6748181074827350883200975 10122271612241026324801463)
          ·
            refine ⟨15183407418361539487202195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10122271612241026324801463 15183407418361539487202195)
            ·
              refine ⟨22775111127542309230803293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15183407418361539487202195 22775111127542309230803293)
              ·
                refine ⟨8540666672828365961551235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22775111127542309230803293 8540666672828365961551235)
                ·
                  refine ⟨12811000009242548942326853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8540666672828365961551235 12811000009242548942326853)
                  ·
                    refine ⟨2402062501732977926686285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12811000009242548942326853 2402062501732977926686285)
                    ·
                      refine ⟨900773438149866722507357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2402062501732977926686285 900773438149866722507357)
                      ·
                        rfl

theorem cell23_1754250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_1754250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754250 prefixEnd_1754250 := by exact prefixLift 1754250
  have htrace : WordTrace (prefixWord ++ tailWord_1754250) baseStart_1754250 baseEnd_1754250 := by
    simpa [prefixWord, tailWord_1754250, baseEnd_1754250] using wordTrace_append hprefix tailTrace_1754250
  have hstable : (prefixWord ++ tailWord_1754250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754250).length < 2 ^ (prefixWord ++ tailWord_1754250).sum := by decide
  have hdescent : baseEnd_1754250 < baseStart_1754250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754340 : List Nat := [2, 3, 1, 1, 1, 2, 2, 4, 1, 1, 5]
def baseStart_1754340 : Nat := 118140960795 + 1754340 * 2 ^ 59
def prefixEnd_1754340 : Nat := 4983230072969 + 3 ^ 40 * 1754340 * 2
def baseEnd_1754340 : Nat := 900819651408771370381943

theorem tailTrace_1754340 : CollatzResearch.WordTrace tailWord_1754340 prefixEnd_1754340 900819651408771370381943 := by
  unfold tailWord_1754340
  simp only [CollatzResearch.WordTrace]
  refine ⟨31993018232166636131674237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42657357642888848175565649 31993018232166636131674237)
  ·
    refine ⟨11997381837062488549377839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31993018232166636131674237 11997381837062488549377839)
    ·
      refine ⟨17996072755593732824066759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11997381837062488549377839 17996072755593732824066759)
      ·
        refine ⟨26994109133390599236100139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17996072755593732824066759 26994109133390599236100139)
        ·
          refine ⟨40491163700085898854150209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26994109133390599236100139 40491163700085898854150209)
          ·
            refine ⟨30368372775064424140612657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40491163700085898854150209 30368372775064424140612657)
            ·
              refine ⟨22776279581298318105459493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30368372775064424140612657 22776279581298318105459493)
              ·
                refine ⟨4270552421493434644773655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22776279581298318105459493 4270552421493434644773655)
                ·
                  refine ⟨6405828632240151967160483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4270552421493434644773655 6405828632240151967160483)
                  ·
                    refine ⟨9608742948360227950740725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6405828632240151967160483 9608742948360227950740725)
                    ·
                      refine ⟨900819651408771370381943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9608742948360227950740725 900819651408771370381943)
                      ·
                        rfl

theorem cell23_1754340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_1754340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754340 prefixEnd_1754340 := by exact prefixLift 1754340
  have htrace : WordTrace (prefixWord ++ tailWord_1754340) baseStart_1754340 baseEnd_1754340 := by
    simpa [prefixWord, tailWord_1754340, baseEnd_1754340] using wordTrace_append hprefix tailTrace_1754340
  have hstable : (prefixWord ++ tailWord_1754340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754340).length < 2 ^ (prefixWord ++ tailWord_1754340).sum := by decide
  have hdescent : baseEnd_1754340 < baseStart_1754340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754347 : List Nat := [1, 1, 1, 1, 2, 6, 2, 3, 2, 4]
def baseStart_1754347 : Nat := 118140960795 + 1754347 * 2 ^ 59
def prefixEnd_1754347 : Nat := 4983230072969 + 3 ^ 40 * 1754347 * 2
def baseEnd_1754347 : Nat := 300274415257784280998137

theorem tailTrace_1754347 : CollatzResearch.WordTrace tailWord_1754347 prefixEnd_1754347 300274415257784280998137 := by
  unfold tailWord_1754347
  simp only [CollatzResearch.WordTrace]
  refine ⟨63986291775307912458853295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42657527850205274972568863 63986291775307912458853295)
  ·
    refine ⟨95979437662961868688279943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63986291775307912458853295 95979437662961868688279943)
    ·
      refine ⟨143969156494442803032419915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95979437662961868688279943 143969156494442803032419915)
      ·
        refine ⟨215953734741664204548629873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143969156494442803032419915 215953734741664204548629873)
        ·
          refine ⟨161965301056248153411472405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215953734741664204548629873 161965301056248153411472405)
          ·
            refine ⟨7592123487011632191162769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 161965301056248153411472405 7592123487011632191162769)
            ·
              refine ⟨5694092615258724143372077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7592123487011632191162769 5694092615258724143372077)
              ·
                refine ⟨2135284730722021553764529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5694092615258724143372077 2135284730722021553764529)
                ·
                  refine ⟨1601463548041516165323397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2135284730722021553764529 1601463548041516165323397)
                  ·
                    refine ⟨300274415257784280998137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1601463548041516165323397 300274415257784280998137)
                    ·
                      rfl

theorem cell23_1754347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 2, 4].length) (baseStart_1754347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754347 prefixEnd_1754347 := by exact prefixLift 1754347
  have htrace : WordTrace (prefixWord ++ tailWord_1754347) baseStart_1754347 baseEnd_1754347 := by
    simpa [prefixWord, tailWord_1754347, baseEnd_1754347] using wordTrace_append hprefix tailTrace_1754347
  have hstable : (prefixWord ++ tailWord_1754347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754347).length < 2 ^ (prefixWord ++ tailWord_1754347).sum := by decide
  have hdescent : baseEnd_1754347 < baseStart_1754347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754350 : List Nat := [4, 1, 2, 1, 1, 1, 2, 3, 1, 1, 6]
def baseStart_1754350 : Nat := 118140960795 + 1754350 * 2 ^ 59
def prefixEnd_1754350 : Nat := 4983230072969 + 3 ^ 40 * 1754350 * 2
def baseEnd_1754350 : Nat := 900824786215316331256897

theorem tailTrace_1754350 : CollatzResearch.WordTrace tailWord_1754350 prefixEnd_1754350 900824786215316331256897 := by
  unfold tailWord_1754350
  simp only [CollatzResearch.WordTrace]
  refine ⟨7998300149287130496401563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42657600796198029314141669 7998300149287130496401563)
  ·
    refine ⟨11997450223930695744602345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7998300149287130496401563 11997450223930695744602345)
    ·
      refine ⟨8998087667948021808451759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11997450223930695744602345 8998087667948021808451759)
      ·
        refine ⟨13497131501922032712677639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8998087667948021808451759 13497131501922032712677639)
        ·
          refine ⟨20245697252883049069016459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13497131501922032712677639 20245697252883049069016459)
          ·
            refine ⟨30368545879324573603524689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20245697252883049069016459 30368545879324573603524689)
            ·
              refine ⟨22776409409493430202643517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30368545879324573603524689 22776409409493430202643517)
              ·
                refine ⟨8541153528560036325991319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22776409409493430202643517 8541153528560036325991319)
                ·
                  refine ⟨12811730292840054488986979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8541153528560036325991319 12811730292840054488986979)
                  ·
                    refine ⟨19217595439260081733480469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12811730292840054488986979 19217595439260081733480469)
                    ·
                      refine ⟨900824786215316331256897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19217595439260081733480469 900824786215316331256897)
                      ·
                        rfl

theorem cell23_1754350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_1754350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754350 prefixEnd_1754350 := by exact prefixLift 1754350
  have htrace : WordTrace (prefixWord ++ tailWord_1754350) baseStart_1754350 baseEnd_1754350 := by
    simpa [prefixWord, tailWord_1754350, baseEnd_1754350] using wordTrace_append hprefix tailTrace_1754350
  have hstable : (prefixWord ++ tailWord_1754350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754350).length < 2 ^ (prefixWord ++ tailWord_1754350).sum := by decide
  have hdescent : baseEnd_1754350 < baseStart_1754350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754371 : List Nat := [1, 1, 1, 3, 2, 4, 1, 5, 1, 2, 2]
def baseStart_1754371 : Nat := 118140960795 + 1754371 * 2 ^ 59
def prefixEnd_1754371 : Nat := 4983230072969 + 3 ^ 40 * 1754371 * 2
def baseEnd_1754371 : Nat := 900835569309060749094301

theorem tailTrace_1754371 : CollatzResearch.WordTrace tailWord_1754371 prefixEnd_1754371 900835569309060749094301 := by
  unfold tailWord_1754371
  simp only [CollatzResearch.WordTrace]
  refine ⟨63987167127220964557726967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42658111418147309705151311 63987167127220964557726967)
  ·
    refine ⟨95980750690831446836590451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63987167127220964557726967 95980750690831446836590451)
    ·
      refine ⟨143971126036247170254885677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95980750690831446836590451 143971126036247170254885677)
      ·
        refine ⟨53989172263592688845582129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143971126036247170254885677 53989172263592688845582129)
        ·
          refine ⟨40491879197694516634186597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53989172263592688845582129 40491879197694516634186597)
          ·
            refine ⟨7592227349567721868909987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40491879197694516634186597 7592227349567721868909987)
            ·
              refine ⟨11388341024351582803364981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7592227349567721868909987 11388341024351582803364981)
              ·
                refine ⟨1067656971032960887815467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11388341024351582803364981 1067656971032960887815467)
                ·
                  refine ⟨1601485456549441331723201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1067656971032960887815467 1601485456549441331723201)
                  ·
                    refine ⟨1201114092412080998792401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1601485456549441331723201 1201114092412080998792401)
                    ·
                      refine ⟨900835569309060749094301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1201114092412080998792401 900835569309060749094301)
                      ·
                        rfl

theorem cell23_1754371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 5, 1, 2, 2].length) (baseStart_1754371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754371 prefixEnd_1754371 := by exact prefixLift 1754371
  have htrace : WordTrace (prefixWord ++ tailWord_1754371) baseStart_1754371 baseEnd_1754371 := by
    simpa [prefixWord, tailWord_1754371, baseEnd_1754371] using wordTrace_append hprefix tailTrace_1754371
  have hstable : (prefixWord ++ tailWord_1754371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754371).length < 2 ^ (prefixWord ++ tailWord_1754371).sum := by decide
  have hdescent : baseEnd_1754371 < baseStart_1754371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754398 : List Nat := [4, 3, 2, 1, 3, 1, 1, 1, 1, 6]
def baseStart_1754398 : Nat := 118140960795 + 1754398 * 2 ^ 59
def prefixEnd_1754398 : Nat := 4983230072969 + 3 ^ 40 * 1754398 * 2
def baseEnd_1754398 : Nat := 300283144428910714485559

theorem tailTrace_1754398 : CollatzResearch.WordTrace tailWord_1754398 prefixEnd_1754398 300283144428910714485559 := by
  unfold tailWord_1754398
  simp only [CollatzResearch.WordTrace]
  refine ⟨7998518987265393521119981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42658767932082098779306565 7998518987265393521119981)
  ·
    refine ⟨2999444620224522570419993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7998518987265393521119981 2999444620224522570419993)
    ·
      refine ⟨2249583465168391927814995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2999444620224522570419993 2249583465168391927814995)
      ·
        refine ⟨3374375197752587891722493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2249583465168391927814995 3374375197752587891722493)
        ·
          refine ⟨1265390699157220459395935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3374375197752587891722493 1265390699157220459395935)
          ·
            refine ⟨1898086048735830689093903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1265390699157220459395935 1898086048735830689093903)
            ·
              refine ⟨2847129073103746033640855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1898086048735830689093903 2847129073103746033640855)
              ·
                refine ⟨4270693609655619050461283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2847129073103746033640855 4270693609655619050461283)
                ·
                  refine ⟨6406040414483428575691925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4270693609655619050461283 6406040414483428575691925)
                  ·
                    refine ⟨300283144428910714485559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6406040414483428575691925 300283144428910714485559)
                    ·
                      rfl

theorem cell23_1754398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_1754398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754398 prefixEnd_1754398 := by exact prefixLift 1754398
  have htrace : WordTrace (prefixWord ++ tailWord_1754398) baseStart_1754398 baseEnd_1754398 := by
    simpa [prefixWord, tailWord_1754398, baseEnd_1754398] using wordTrace_append hprefix tailTrace_1754398
  have hstable : (prefixWord ++ tailWord_1754398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754398).length < 2 ^ (prefixWord ++ tailWord_1754398).sum := by decide
  have hdescent : baseEnd_1754398 < baseStart_1754398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754478 : List Nat := [4, 1, 2, 4, 1, 1, 1, 2, 1, 4, 2]
def baseStart_1754478 : Nat := 118140960795 + 1754478 * 2 ^ 59
def prefixEnd_1754478 : Nat := 4983230072969 + 3 ^ 40 * 1754478 * 2
def baseEnd_1754478 : Nat := 900890511739091830456309

theorem tailTrace_1754478 : CollatzResearch.WordTrace tailWord_1754478 prefixEnd_1754478 900890511739091830456309 := by
  unfold tailWord_1754478
  simp only [CollatzResearch.WordTrace]
  refine ⟨7998883717229165228984011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42660713158555547887914725 7998883717229165228984011)
  ·
    refine ⟨11998325575843747843476017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7998883717229165228984011 11998325575843747843476017)
    ·
      refine ⟨8998744181882810882607013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11998325575843747843476017 8998744181882810882607013)
      ·
        refine ⟨1687264534103027040488815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8998744181882810882607013 1687264534103027040488815)
        ·
          refine ⟨2530896801154540560733223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1687264534103027040488815 2530896801154540560733223)
          ·
            refine ⟨3796345201731810841099835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2530896801154540560733223 3796345201731810841099835)
            ·
              refine ⟨5694517802597716261649753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3796345201731810841099835 5694517802597716261649753)
              ·
                refine ⟨4270888351948287196237315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5694517802597716261649753 4270888351948287196237315)
                ·
                  refine ⟨6406332527922430794355973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4270888351948287196237315 6406332527922430794355973)
                  ·
                    refine ⟨1201187348985455773941745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6406332527922430794355973 1201187348985455773941745)
                    ·
                      refine ⟨900890511739091830456309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1201187348985455773941745 900890511739091830456309)
                      ·
                        rfl

theorem cell23_1754478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_1754478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754478 prefixEnd_1754478 := by exact prefixLift 1754478
  have htrace : WordTrace (prefixWord ++ tailWord_1754478) baseStart_1754478 baseEnd_1754478 := by
    simpa [prefixWord, tailWord_1754478, baseEnd_1754478] using wordTrace_append hprefix tailTrace_1754478
  have hstable : (prefixWord ++ tailWord_1754478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754478).length < 2 ^ (prefixWord ++ tailWord_1754478).sum := by decide
  have hdescent : baseEnd_1754478 < baseStart_1754478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754490 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 3, 1, 7]
def baseStart_1754490 : Nat := 118140960795 + 1754490 * 2 ^ 59
def prefixEnd_1754490 : Nat := 4983230072969 + 3 ^ 40 * 1754490 * 2
def baseEnd_1754490 : Nat := 900896673506945783506253

theorem tailTrace_1754490 : CollatzResearch.WordTrace tailWord_1754490 prefixEnd_1754490 900896673506945783506253 := by
  unfold tailWord_1754490
  simp only [CollatzResearch.WordTrace]
  refine ⟨15997876853447461970327231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42661004942526565254205949 15997876853447461970327231)
  ·
    refine ⟨23996815280171192955490847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15997876853447461970327231 23996815280171192955490847)
    ·
      refine ⟨35995222920256789433236271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23996815280171192955490847 35995222920256789433236271)
      ·
        refine ⟨53992834380385184149854407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35995222920256789433236271 53992834380385184149854407)
        ·
          refine ⟨80989251570577776224781611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53992834380385184149854407 80989251570577776224781611)
          ·
            refine ⟨121483877355866664337172417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80989251570577776224781611 121483877355866664337172417)
            ·
              refine ⟨91112908016899998252879313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121483877355866664337172417 91112908016899998252879313)
              ·
                refine ⟨68334681012674998689659485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91112908016899998252879313 68334681012674998689659485)
                ·
                  refine ⟨25625505379753124508622307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68334681012674998689659485 25625505379753124508622307)
                  ·
                    refine ⟨38438258069629686762933461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25625505379753124508622307 38438258069629686762933461)
                    ·
                      refine ⟨900896673506945783506253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 38438258069629686762933461 900896673506945783506253)
                      ·
                        rfl

theorem cell23_1754490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_1754490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754490 prefixEnd_1754490 := by exact prefixLift 1754490
  have htrace : WordTrace (prefixWord ++ tailWord_1754490) baseStart_1754490 baseEnd_1754490 := by
    simpa [prefixWord, tailWord_1754490, baseEnd_1754490] using wordTrace_append hprefix tailTrace_1754490
  have hstable : (prefixWord ++ tailWord_1754490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754490).length < 2 ^ (prefixWord ++ tailWord_1754490).sum := by decide
  have hdescent : baseEnd_1754490 < baseStart_1754490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754504 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 2, 5, 2]
def baseStart_1754504 : Nat := 118140960795 + 1754504 * 2 ^ 59
def prefixEnd_1754504 : Nat := 4983230072969 + 3 ^ 40 * 1754504 * 2
def baseEnd_1754504 : Nat := 900903862236108728731189

theorem tailTrace_1754504 : CollatzResearch.WordTrace tailWord_1754504 prefixEnd_1754504 900903862236108728731189 := by
  unfold tailWord_1754504
  simp only [CollatzResearch.WordTrace]
  refine ⟨31996009017869564136159283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42661345357159418848212377 31996009017869564136159283)
  ·
    refine ⟨47994013526804346204238925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31996009017869564136159283 47994013526804346204238925)
    ·
      refine ⟨17997755072551629826589597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47994013526804346204238925 17997755072551629826589597)
      ·
        refine ⟨6749158152206861184971099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17997755072551629826589597 6749158152206861184971099)
        ·
          refine ⟨10123737228310291777456649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6749158152206861184971099 10123737228310291777456649)
          ·
            refine ⟨7592802921232718833092487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10123737228310291777456649 7592802921232718833092487)
            ·
              refine ⟨11389204381849078249638731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7592802921232718833092487 11389204381849078249638731)
              ·
                refine ⟨17083806572773617374458097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11389204381849078249638731 17083806572773617374458097)
                ·
                  refine ⟨12812854929580213030843573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17083806572773617374458097 12812854929580213030843573)
                  ·
                    refine ⟨1201205149648144971641585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12812854929580213030843573 1201205149648144971641585)
                    ·
                      refine ⟨900903862236108728731189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1201205149648144971641585 900903862236108728731189)
                      ·
                        rfl

theorem cell23_1754504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_1754504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754504 prefixEnd_1754504 := by exact prefixLift 1754504
  have htrace : WordTrace (prefixWord ++ tailWord_1754504) baseStart_1754504 baseEnd_1754504 := by
    simpa [prefixWord, tailWord_1754504, baseEnd_1754504] using wordTrace_append hprefix tailTrace_1754504
  have hstable : (prefixWord ++ tailWord_1754504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754504).length < 2 ^ (prefixWord ++ tailWord_1754504).sum := by decide
  have hdescent : baseEnd_1754504 < baseStart_1754504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754517 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 4, 1, 4]
def baseStart_1754517 : Nat := 118140960795 + 1754517 * 2 ^ 59
def prefixEnd_1754517 : Nat := 4983230072969 + 3 ^ 40 * 1754517 * 2
def baseEnd_1754517 : Nat := 900910537484617177868629

theorem tailTrace_1754517 : CollatzResearch.WordTrace tailWord_1754517 prefixEnd_1754517 900910537484617177868629 := by
  unfold tailWord_1754517
  simp only [CollatzResearch.WordTrace]
  refine ⟨63992492184692031492541805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42661661456461354328361203 63992492184692031492541805)
  ·
    refine ⟨23997184569259511809703177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63992492184692031492541805 23997184569259511809703177)
    ·
      refine ⟨17997888426944633857277383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23997184569259511809703177 17997888426944633857277383)
      ·
        refine ⟨26996832640416950785916075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17997888426944633857277383 26996832640416950785916075)
        ·
          refine ⟨40495248960625426178874113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26996832640416950785916075 40495248960625426178874113)
          ·
            refine ⟨30371436720469069634155585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40495248960625426178874113 30371436720469069634155585)
            ·
              refine ⟨22778577540351802225616689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30371436720469069634155585 22778577540351802225616689)
              ·
                refine ⟨17083933155263851669212517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22778577540351802225616689 17083933155263851669212517)
                ·
                  refine ⟨3203237466611972187977347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17083933155263851669212517 3203237466611972187977347)
                  ·
                    refine ⟨4804856199917958281966021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3203237466611972187977347 4804856199917958281966021)
                    ·
                      refine ⟨900910537484617177868629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4804856199917958281966021 900910537484617177868629)
                      ·
                        rfl

theorem cell23_1754517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_1754517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754517 prefixEnd_1754517 := by exact prefixLift 1754517
  have htrace : WordTrace (prefixWord ++ tailWord_1754517) baseStart_1754517 baseEnd_1754517 := by
    simpa [prefixWord, tailWord_1754517, baseEnd_1754517] using wordTrace_append hprefix tailTrace_1754517
  have hstable : (prefixWord ++ tailWord_1754517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754517).length < 2 ^ (prefixWord ++ tailWord_1754517).sum := by decide
  have hdescent : baseEnd_1754517 < baseStart_1754517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754557 : List Nat := [1, 4, 1, 2, 2, 1, 3, 1, 8]
def baseStart_1754557 : Nat := 118140960795 + 1754557 * 2 ^ 59
def prefixEnd_1754557 : Nat := 4983230072969 + 3 ^ 40 * 1754557 * 2
def baseEnd_1754557 : Nat := 100103452967866335707605

theorem tailTrace_1754557 : CollatzResearch.WordTrace tailWord_1754557 prefixEnd_1754557 100103452967866335707605 := by
  unfold tailWord_1754557
  simp only [CollatzResearch.WordTrace]
  refine ⟨63993951104547118323997925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42662634069698078882665283 63993951104547118323997925)
  ·
    refine ⟨11998865832102584685749611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63993951104547118323997925 11998865832102584685749611)
    ·
      refine ⟨17998298748153877028624417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11998865832102584685749611 17998298748153877028624417)
      ·
        refine ⟨13498724061115407771468313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17998298748153877028624417 13498724061115407771468313)
        ·
          refine ⟨10124043045836555828601235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13498724061115407771468313 10124043045836555828601235)
          ·
            refine ⟨15186064568754833742901853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10124043045836555828601235 15186064568754833742901853)
            ·
              refine ⟨5694774213283062653588195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15186064568754833742901853 5694774213283062653588195)
              ·
                refine ⟨8542161319924593980382293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5694774213283062653588195 8542161319924593980382293)
                ·
                  refine ⟨100103452967866335707605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8542161319924593980382293 100103452967866335707605)
                  ·
                    rfl

theorem cell23_1754557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 8].length) (baseStart_1754557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754557 prefixEnd_1754557 := by exact prefixLift 1754557
  have htrace : WordTrace (prefixWord ++ tailWord_1754557) baseStart_1754557 baseEnd_1754557 := by
    simpa [prefixWord, tailWord_1754557, baseEnd_1754557] using wordTrace_append hprefix tailTrace_1754557
  have hstable : (prefixWord ++ tailWord_1754557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754557).length < 2 ^ (prefixWord ++ tailWord_1754557).sum := by decide
  have hdescent : baseEnd_1754557 < baseStart_1754557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754627 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 5]
def baseStart_1754627 : Nat := 118140960795 + 1754627 * 2 ^ 59
def prefixEnd_1754627 : Nat := 4983230072969 + 3 ^ 40 * 1754627 * 2
def baseEnd_1754627 : Nat := 900967020356611747493123

theorem tailTrace_1754627 : CollatzResearch.WordTrace tailWord_1754627 prefixEnd_1754627 900967020356611747493123 := by
  unfold tailWord_1754627
  simp only [CollatzResearch.WordTrace]
  refine ⟨63996504214293520279046135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42664336142862346852697423 63996504214293520279046135)
  ·
    refine ⟨95994756321440280418569203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63996504214293520279046135 95994756321440280418569203)
    ·
      refine ⟨143992134482160420627853805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95994756321440280418569203 143992134482160420627853805)
      ·
        refine ⟨53997050430810157735445177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143992134482160420627853805 53997050430810157735445177)
        ·
          refine ⟨40497787823107618301583883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53997050430810157735445177 40497787823107618301583883)
          ·
            refine ⟨60746681734661427452375825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40497787823107618301583883 60746681734661427452375825)
            ·
              refine ⟨45560011300996070589281869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60746681734661427452375825 45560011300996070589281869)
              ·
                refine ⟨17085004237873526470980701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45560011300996070589281869 17085004237873526470980701)
                ·
                  refine ⟨6406876589202572426617763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17085004237873526470980701 6406876589202572426617763)
                  ·
                    refine ⟨9610314883803858639926645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6406876589202572426617763 9610314883803858639926645)
                    ·
                      refine ⟨900967020356611747493123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9610314883803858639926645 900967020356611747493123)
                      ·
                        rfl

theorem cell23_1754627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_1754627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754627 prefixEnd_1754627 := by exact prefixLift 1754627
  have htrace : WordTrace (prefixWord ++ tailWord_1754627) baseStart_1754627 baseEnd_1754627 := by
    simpa [prefixWord, tailWord_1754627, baseEnd_1754627] using wordTrace_append hprefix tailTrace_1754627
  have hstable : (prefixWord ++ tailWord_1754627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754627).length < 2 ^ (prefixWord ++ tailWord_1754627).sum := by decide
  have hdescent : baseEnd_1754627 < baseStart_1754627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754638 : List Nat := [4, 1, 1, 2, 4, 2, 1, 2, 1, 5]
def baseStart_1754638 : Nat := 118140960795 + 1754638 * 2 ^ 59
def prefixEnd_1754638 : Nat := 4983230072969 + 3 ^ 40 * 1754638 * 2
def baseEnd_1754638 : Nat := 300324222881270401485191

theorem tailTrace_1754638 : CollatzResearch.WordTrace tailWord_1754638 prefixEnd_1754638 300324222881270401485191 := by
  unfold tailWord_1754638
  simp only [CollatzResearch.WordTrace]
  refine ⟨7999613177156708644712071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42664603611502446105131045 7999613177156708644712071)
  ·
    refine ⟨11999419765735062967068107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7999613177156708644712071 11999419765735062967068107)
    ·
      refine ⟨17999129648602594450602161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11999419765735062967068107 17999129648602594450602161)
      ·
        refine ⟨13499347236451945837951621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17999129648602594450602161 13499347236451945837951621)
        ·
          refine ⟨2531127606834739844615929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13499347236451945837951621 2531127606834739844615929)
          ·
            refine ⟨1898345705126054883461947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2531127606834739844615929 1898345705126054883461947)
            ·
              refine ⟨2847518557689082325192921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1898345705126054883461947 2847518557689082325192921)
              ·
                refine ⟨2135638918266811743894691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2847518557689082325192921 2135638918266811743894691)
                ·
                  refine ⟨3203458377400217615842037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2135638918266811743894691 3203458377400217615842037)
                  ·
                    refine ⟨300324222881270401485191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3203458377400217615842037 300324222881270401485191)
                    ·
                      rfl

theorem cell23_1754638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_1754638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754638 prefixEnd_1754638 := by exact prefixLift 1754638
  have htrace : WordTrace (prefixWord ++ tailWord_1754638) baseStart_1754638 baseEnd_1754638 := by
    simpa [prefixWord, tailWord_1754638, baseEnd_1754638] using wordTrace_append hprefix tailTrace_1754638
  have hstable : (prefixWord ++ tailWord_1754638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754638).length < 2 ^ (prefixWord ++ tailWord_1754638).sum := by decide
  have hdescent : baseEnd_1754638 < baseStart_1754638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754641 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 5, 2, 2]
def baseStart_1754641 : Nat := 118140960795 + 1754641 * 2 ^ 59
def prefixEnd_1754641 : Nat := 4983230072969 + 3 ^ 40 * 1754641 * 2
def baseEnd_1754641 : Nat := 900974209085774692718059

theorem tailTrace_1754641 : CollatzResearch.WordTrace tailWord_1754641 prefixEnd_1754641 900974209085774692718059 := by
  unfold tailWord_1754641
  simp only [CollatzResearch.WordTrace]
  refine ⟨63997014836242800670055777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42664676557495200446703851 63997014836242800670055777)
  ·
    refine ⟨47997761127182100502541833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63997014836242800670055777 47997761127182100502541833)
    ·
      refine ⟨35998320845386575376906375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47997761127182100502541833 35998320845386575376906375)
      ·
        refine ⟨53997481268079863065359563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35998320845386575376906375 53997481268079863065359563)
        ·
          refine ⟨80996221902119794598039345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53997481268079863065359563 80996221902119794598039345)
          ·
            refine ⟨60747166426589845948529509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80996221902119794598039345 60747166426589845948529509)
            ·
              refine ⟨11390093704985596115349283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60747166426589845948529509 11390093704985596115349283)
              ·
                refine ⟨17085140557478394173023925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11390093704985596115349283 17085140557478394173023925)
                ·
                  refine ⟨1601731927263599453720993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17085140557478394173023925 1601731927263599453720993)
                  ·
                    refine ⟨1201298945447699590290745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1601731927263599453720993 1201298945447699590290745)
                    ·
                      refine ⟨900974209085774692718059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1201298945447699590290745 900974209085774692718059)
                      ·
                        rfl

theorem cell23_1754641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5, 2, 2].length) (baseStart_1754641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754641 prefixEnd_1754641 := by exact prefixLift 1754641
  have htrace : WordTrace (prefixWord ++ tailWord_1754641) baseStart_1754641 baseEnd_1754641 := by
    simpa [prefixWord, tailWord_1754641, baseEnd_1754641] using wordTrace_append hprefix tailTrace_1754641
  have hstable : (prefixWord ++ tailWord_1754641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754641).length < 2 ^ (prefixWord ++ tailWord_1754641).sum := by decide
  have hdescent : baseEnd_1754641 < baseStart_1754641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754664 : List Nat := [2, 1, 5, 2, 2, 11]
def baseStart_1754664 : Nat := 118140960795 + 1754664 * 2 ^ 59
def prefixEnd_1754664 : Nat := 4983230072969 + 3 ^ 40 * 1754664 * 2
def baseEnd_1754664 : Nat := 3707761395641267912471

theorem tailTrace_1754664 : CollatzResearch.WordTrace tailWord_1754664 prefixEnd_1754664 3707761395641267912471 := by
  unfold tailWord_1754664
  simp only [CollatzResearch.WordTrace]
  refine ⟨31998926857579737799071523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42665235810106317065428697 31998926857579737799071523)
  ·
    refine ⟨47998390286369606698607285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31998926857579737799071523 47998390286369606698607285)
    ·
      refine ⟨4499849089347150627994433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47998390286369606698607285 4499849089347150627994433)
      ·
        refine ⟨3374886817010362970995825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4499849089347150627994433 3374886817010362970995825)
        ·
          refine ⟨2531165112757772228246869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3374886817010362970995825 2531165112757772228246869)
          ·
            refine ⟨3707761395641267912471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2531165112757772228246869 3707761395641267912471)
            ·
              rfl

theorem cell23_1754664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 11].length) (baseStart_1754664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754664 prefixEnd_1754664 := by exact prefixLift 1754664
  have htrace : WordTrace (prefixWord ++ tailWord_1754664) baseStart_1754664 baseEnd_1754664 := by
    simpa [prefixWord, tailWord_1754664, baseEnd_1754664] using wordTrace_append hprefix tailTrace_1754664
  have hstable : (prefixWord ++ tailWord_1754664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754664).length < 2 ^ (prefixWord ++ tailWord_1754664).sum := by decide
  have hdescent : baseEnd_1754664 < baseStart_1754664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754674 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3]
def baseStart_1754674 : Nat := 118140960795 + 1754674 * 2 ^ 59
def prefixEnd_1754674 : Nat := 4983230072969 + 3 ^ 40 * 1754674 * 2
def baseEnd_1754674 : Nat := 900991153947373063605407

theorem tailTrace_1754674 : CollatzResearch.WordTrace tailWord_1754674 prefixEnd_1754674 900991153947373063605407 := by
  unfold tailWord_1754674
  simp only [CollatzResearch.WordTrace]
  refine ⟨15999554611280811826501769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42665478963415498204004717 15999554611280811826501769)
  ·
    refine ⟨11999665958460608869876327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15999554611280811826501769 11999665958460608869876327)
    ·
      refine ⟨17999498937690913304814491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11999665958460608869876327 17999498937690913304814491)
      ·
        refine ⟨26999248406536369957221737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17999498937690913304814491 26999248406536369957221737)
        ·
          refine ⟨20249436304902277467916303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26999248406536369957221737 20249436304902277467916303)
          ·
            refine ⟨30374154457353416201874455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20249436304902277467916303 30374154457353416201874455)
            ·
              refine ⟨45561231686030124302811683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30374154457353416201874455 45561231686030124302811683)
              ·
                refine ⟨68341847529045186454217525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45561231686030124302811683 68341847529045186454217525)
                ·
                  refine ⟨6407048205847986230082893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68341847529045186454217525 6407048205847986230082893)
                  ·
                    refine ⟨2402643077192994836281085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6407048205847986230082893 2402643077192994836281085)
                    ·
                      refine ⟨900991153947373063605407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2402643077192994836281085 900991153947373063605407)
                      ·
                        rfl

theorem cell23_1754674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_1754674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754674 prefixEnd_1754674 := by exact prefixLift 1754674
  have htrace : WordTrace (prefixWord ++ tailWord_1754674) baseStart_1754674 baseEnd_1754674 := by
    simpa [prefixWord, tailWord_1754674, baseEnd_1754674] using wordTrace_append hprefix tailTrace_1754674
  have hstable : (prefixWord ++ tailWord_1754674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754674).length < 2 ^ (prefixWord ++ tailWord_1754674).sum := by decide
  have hdescent : baseEnd_1754674 < baseStart_1754674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754675 : List Nat := [1, 1, 1, 2, 4, 4, 1, 4, 1, 2, 2]
def baseStart_1754675 : Nat := 118140960795 + 1754675 * 2 ^ 59
def prefixEnd_1754675 : Nat := 4983230072969 + 3 ^ 40 * 1754675 * 2
def baseEnd_1754675 : Nat := 900991667428027559692903

theorem tailTrace_1754675 : CollatzResearch.WordTrace tailWord_1754675 prefixEnd_1754675 900991667428027559692903 := by
  unfold tailWord_1754675
  simp only [CollatzResearch.WordTrace]
  refine ⟨63998254918119624476793479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42665503278746416317862319 63998254918119624476793479)
  ·
    refine ⟨95997382377179436715190219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63998254918119624476793479 95997382377179436715190219)
    ·
      refine ⟨143996073565769155072785329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95997382377179436715190219 143996073565769155072785329)
      ·
        refine ⟨107997055174326866304588997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143996073565769155072785329 107997055174326866304588997)
        ·
          refine ⟨20249447845186287432110437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107997055174326866304588997 20249447845186287432110437)
          ·
            refine ⟨3796771470972428893520707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20249447845186287432110437 3796771470972428893520707)
            ·
              refine ⟨5695157206458643340281061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3796771470972428893520707 5695157206458643340281061)
              ·
                refine ⟨1067841976210995626302699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5695157206458643340281061 1067841976210995626302699)
                ·
                  refine ⟨1601762964316493439454049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1067841976210995626302699 1601762964316493439454049)
                  ·
                    refine ⟨1201322223237370079590537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1601762964316493439454049 1201322223237370079590537)
                    ·
                      refine ⟨900991667428027559692903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1201322223237370079590537 900991667428027559692903)
                      ·
                        rfl

theorem cell23_1754675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 4, 1, 2, 2].length) (baseStart_1754675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754675 prefixEnd_1754675 := by exact prefixLift 1754675
  have htrace : WordTrace (prefixWord ++ tailWord_1754675) baseStart_1754675 baseEnd_1754675 := by
    simpa [prefixWord, tailWord_1754675, baseEnd_1754675] using wordTrace_append hprefix tailTrace_1754675
  have hstable : (prefixWord ++ tailWord_1754675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754675).length < 2 ^ (prefixWord ++ tailWord_1754675).sum := by decide
  have hdescent : baseEnd_1754675 < baseStart_1754675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754724 : List Nat := [2, 3, 1, 1, 2, 3, 1, 2, 2, 6]
def baseStart_1754724 : Nat := 118140960795 + 1754724 * 2 ^ 59
def prefixEnd_1754724 : Nat := 4983230072969 + 3 ^ 40 * 1754724 * 2
def baseEnd_1754724 : Nat := 300338942660032622660059

theorem tailTrace_1754724 : CollatzResearch.WordTrace tailWord_1754724 prefixEnd_1754724 300338942660032622660059 := by
  unfold tailWord_1754724
  simp only [CollatzResearch.WordTrace]
  refine ⟨32000021047471052922663613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42666694729961403896884817 32000021047471052922663613)
  ·
    refine ⟨12000007892801644845998855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32000021047471052922663613 12000007892801644845998855)
    ·
      refine ⟨18000011839202467268998283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12000007892801644845998855 18000011839202467268998283)
      ·
        refine ⟨27000017758803700903497425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18000011839202467268998283 27000017758803700903497425)
        ·
          refine ⟨20250013319102775677623069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27000017758803700903497425 20250013319102775677623069)
          ·
            refine ⟨7593754994663540879108651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20250013319102775677623069 7593754994663540879108651)
            ·
              refine ⟨11390632491995311318662977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7593754994663540879108651 11390632491995311318662977)
              ·
                refine ⟨8542974368996483488997233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11390632491995311318662977 8542974368996483488997233)
                ·
                  refine ⟨6407230776747362616747925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8542974368996483488997233 6407230776747362616747925)
                  ·
                    refine ⟨300338942660032622660059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6407230776747362616747925 300338942660032622660059)
                    ·
                      rfl

theorem cell23_1754724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_1754724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754724 prefixEnd_1754724 := by exact prefixLift 1754724
  have htrace : WordTrace (prefixWord ++ tailWord_1754724) baseStart_1754724 baseEnd_1754724 := by
    simpa [prefixWord, tailWord_1754724, baseEnd_1754724] using wordTrace_append hprefix tailTrace_1754724
  have hstable : (prefixWord ++ tailWord_1754724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754724).length < 2 ^ (prefixWord ++ tailWord_1754724).sum := by decide
  have hdescent : baseEnd_1754724 < baseStart_1754724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754725 : List Nat := [1, 3, 1, 3, 3, 3, 1, 2, 2, 1, 3]
def baseStart_1754725 : Nat := 118140960795 + 1754725 * 2 ^ 59
def prefixEnd_1754725 : Nat := 4983230072969 + 3 ^ 40 * 1754725 * 2
def baseEnd_1754725 : Nat := 901017341460752364067673

theorem tailTrace_1754725 : CollatzResearch.WordTrace tailWord_1754725 prefixEnd_1754725 901017341460752364067673 := by
  unfold tailWord_1754725
  simp only [CollatzResearch.WordTrace]
  refine ⟨64000078567938483016113629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42666719045292322010742419 64000078567938483016113629)
  ·
    refine ⟨24000029462976931131042611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64000078567938483016113629 24000029462976931131042611)
    ·
      refine ⟨36000044194465396696563917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24000029462976931131042611 36000044194465396696563917)
      ·
        refine ⟨13500016572924523761211469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36000044194465396696563917 13500016572924523761211469)
        ·
          refine ⟨5062506214846696410454301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13500016572924523761211469 5062506214846696410454301)
          ·
            refine ⟨1898439830567511153920363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5062506214846696410454301 1898439830567511153920363)
            ·
              refine ⟨2847659745851266730880545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1898439830567511153920363 2847659745851266730880545)
              ·
                refine ⟨2135744809388450048160409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2847659745851266730880545 2135744809388450048160409)
                ·
                  refine ⟨1601808607041337536120307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2135744809388450048160409 1601808607041337536120307)
                  ·
                    refine ⟨2402712910562006304180461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1601808607041337536120307 2402712910562006304180461)
                    ·
                      refine ⟨901017341460752364067673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2402712910562006304180461 901017341460752364067673)
                      ·
                        rfl

theorem cell23_1754725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_1754725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754725 prefixEnd_1754725 := by exact prefixLift 1754725
  have htrace : WordTrace (prefixWord ++ tailWord_1754725) baseStart_1754725 baseEnd_1754725 := by
    simpa [prefixWord, tailWord_1754725, baseEnd_1754725] using wordTrace_append hprefix tailTrace_1754725
  have hstable : (prefixWord ++ tailWord_1754725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754725).length < 2 ^ (prefixWord ++ tailWord_1754725).sum := by decide
  have hdescent : baseEnd_1754725 < baseStart_1754725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754741 : List Nat := [1, 3, 4, 2, 1, 1, 2, 1, 2, 6]
def baseStart_1754741 : Nat := 118140960795 + 1754741 * 2 ^ 59
def prefixEnd_1754741 : Nat := 4983230072969 + 3 ^ 40 * 1754741 * 2
def baseEnd_1754741 : Nat := 300341852383741433822533

theorem tailTrace_1754741 : CollatzResearch.WordTrace tailWord_1754741 prefixEnd_1754741 300341852383741433822533 := by
  unfold tailWord_1754741
  simp only [CollatzResearch.WordTrace]
  refine ⟨64000662135880517748696077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42667108090587011832464051 64000662135880517748696077)
  ·
    refine ⟨24000248300955194155761029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64000662135880517748696077 24000248300955194155761029)
    ·
      refine ⟨4500046556429098904205193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24000248300955194155761029 4500046556429098904205193)
      ·
        refine ⟨3375034917321824178153895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4500046556429098904205193 3375034917321824178153895)
        ·
          refine ⟨5062552375982736267230843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3375034917321824178153895 5062552375982736267230843)
          ·
            refine ⟨7593828563974104400846265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5062552375982736267230843 7593828563974104400846265)
            ·
              refine ⟨5695371422980578300634699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7593828563974104400846265 5695371422980578300634699)
              ·
                refine ⟨8543057134470867450952049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5695371422980578300634699 8543057134470867450952049)
                ·
                  refine ⟨6407292850853150588214037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8543057134470867450952049 6407292850853150588214037)
                  ·
                    refine ⟨300341852383741433822533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6407292850853150588214037 300341852383741433822533)
                    ·
                      rfl

theorem cell23_1754741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_1754741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754741 prefixEnd_1754741 := by exact prefixLift 1754741
  have htrace : WordTrace (prefixWord ++ tailWord_1754741) baseStart_1754741 baseEnd_1754741 := by
    simpa [prefixWord, tailWord_1754741, baseEnd_1754741] using wordTrace_append hprefix tailTrace_1754741
  have hstable : (prefixWord ++ tailWord_1754741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754741).length < 2 ^ (prefixWord ++ tailWord_1754741).sum := by decide
  have hdescent : baseEnd_1754741 < baseStart_1754741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754742 : List Nat := [5, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3]
def baseStart_1754742 : Nat := 118140960795 + 1754742 * 2 ^ 59
def prefixEnd_1754742 : Nat := 4983230072969 + 3 ^ 40 * 1754742 * 2
def baseEnd_1754742 : Nat := 901026070631878797555095

theorem tailTrace_1754742 : CollatzResearch.WordTrace tailWord_1754742 prefixEnd_1754742 901026070631878797555095 := by
  unfold tailWord_1754742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4000043663054805932467655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42667132405917929946321653 4000043663054805932467655)
  ·
    refine ⟨6000065494582208898701483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4000043663054805932467655 6000065494582208898701483)
    ·
      refine ⟨9000098241873313348052225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6000065494582208898701483 9000098241873313348052225)
      ·
        refine ⟨6750073681404985011039169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9000098241873313348052225 6750073681404985011039169)
        ·
          refine ⟨5062555261053738758279377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6750073681404985011039169 5062555261053738758279377)
          ·
            refine ⟨3796916445790304068709533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5062555261053738758279377 3796916445790304068709533)
            ·
              refine ⟨1423843667171364025766075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3796916445790304068709533 1423843667171364025766075)
              ·
                refine ⟨2135765500757046038649113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1423843667171364025766075 2135765500757046038649113)
                ·
                  refine ⟨1601824125567784528986835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2135765500757046038649113 1601824125567784528986835)
                  ·
                    refine ⟨2402736188351676793480253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1601824125567784528986835 2402736188351676793480253)
                    ·
                      refine ⟨901026070631878797555095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2402736188351676793480253 901026070631878797555095)
                      ·
                        rfl

theorem cell23_1754742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_1754742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754742 prefixEnd_1754742 := by exact prefixLift 1754742
  have htrace : WordTrace (prefixWord ++ tailWord_1754742) baseStart_1754742 baseEnd_1754742 := by
    simpa [prefixWord, tailWord_1754742, baseEnd_1754742] using wordTrace_append hprefix tailTrace_1754742
  have hstable : (prefixWord ++ tailWord_1754742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754742).length < 2 ^ (prefixWord ++ tailWord_1754742).sum := by decide
  have hdescent : baseEnd_1754742 < baseStart_1754742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754821 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 1, 6, 2]
def baseStart_1754821 : Nat := 118140960795 + 1754821 * 2 ^ 59
def prefixEnd_1754821 : Nat := 4983230072969 + 3 ^ 40 * 1754821 * 2
def baseEnd_1754821 : Nat := 901066635603583988467231

theorem tailTrace_1754821 : CollatzResearch.WordTrace tailWord_1754821 prefixEnd_1754821 901066635603583988467231 := by
  unfold tailWord_1754821
  simp only [CollatzResearch.WordTrace]
  refine ⟨64003579975590691411608317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42669053317060460941072211 64003579975590691411608317)
  ·
    refine ⟨24001342490846509279353119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64003579975590691411608317 24001342490846509279353119)
    ·
      refine ⟨36002013736269763919029679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24001342490846509279353119 36002013736269763919029679)
      ·
        refine ⟨54003020604404645878544519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36002013736269763919029679 54003020604404645878544519)
        ·
          refine ⟨81004530906606968817816779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54003020604404645878544519 81004530906606968817816779)
          ·
            refine ⟨121506796359910453226725169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81004530906606968817816779 121506796359910453226725169)
            ·
              refine ⟨91130097269932839920043877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121506796359910453226725169 91130097269932839920043877)
              ·
                refine ⟨17086893238112407485008227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91130097269932839920043877 17086893238112407485008227)
                ·
                  refine ⟨25630339857168611227512341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17086893238112407485008227 25630339857168611227512341)
                  ·
                    refine ⟨1201422180804778651289641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25630339857168611227512341 1201422180804778651289641)
                    ·
                      refine ⟨901066635603583988467231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1201422180804778651289641 901066635603583988467231)
                      ·
                        rfl

theorem cell23_1754821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 6, 2].length) (baseStart_1754821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754821 prefixEnd_1754821 := by exact prefixLift 1754821
  have htrace : WordTrace (prefixWord ++ tailWord_1754821) baseStart_1754821 baseEnd_1754821 := by
    simpa [prefixWord, tailWord_1754821, baseEnd_1754821] using wordTrace_append hprefix tailTrace_1754821
  have hstable : (prefixWord ++ tailWord_1754821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754821).length < 2 ^ (prefixWord ++ tailWord_1754821).sum := by decide
  have hdescent : baseEnd_1754821 < baseStart_1754821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754864 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 6]
def baseStart_1754864 : Nat := 118140960795 + 1754864 * 2 ^ 59
def prefixEnd_1754864 : Nat := 4983230072969 + 3 ^ 40 * 1754864 * 2
def baseEnd_1754864 : Nat := 901088715271727320229533

theorem tailTrace_1754864 : CollatzResearch.WordTrace tailWord_1754864 prefixEnd_1754864 901088715271727320229533 := by
  unfold tailWord_1754864
  simp only [CollatzResearch.WordTrace]
  refine ⟨32002574157217454877711823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42670098876289939836949097 32002574157217454877711823)
  ·
    refine ⟨48003861235826182316567735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32002574157217454877711823 48003861235826182316567735)
    ·
      refine ⟨72005791853739273474851603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48003861235826182316567735 72005791853739273474851603)
      ·
        refine ⟨108008687780608910212277405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72005791853739273474851603 108008687780608910212277405)
        ·
          refine ⟨40503257917728341329604027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108008687780608910212277405 40503257917728341329604027)
          ·
            refine ⟨60754886876592511994406041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40503257917728341329604027 60754886876592511994406041)
            ·
              refine ⟨45566165157444383995804531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60754886876592511994406041 45566165157444383995804531)
              ·
                refine ⟨68349247736166575993706797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45566165157444383995804531 68349247736166575993706797)
                ·
                  refine ⟨25630967901062465997640049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68349247736166575993706797 25630967901062465997640049)
                  ·
                    refine ⟨19223225925796849498230037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25630967901062465997640049 19223225925796849498230037)
                    ·
                      refine ⟨901088715271727320229533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19223225925796849498230037 901088715271727320229533)
                      ·
                        rfl

theorem cell23_1754864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 6].length) (baseStart_1754864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754864 prefixEnd_1754864 := by exact prefixLift 1754864
  have htrace : WordTrace (prefixWord ++ tailWord_1754864) baseStart_1754864 baseEnd_1754864 := by
    simpa [prefixWord, tailWord_1754864, baseEnd_1754864] using wordTrace_append hprefix tailTrace_1754864
  have hstable : (prefixWord ++ tailWord_1754864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754864).length < 2 ^ (prefixWord ++ tailWord_1754864).sum := by decide
  have hdescent : baseEnd_1754864 < baseStart_1754864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754882 : List Nat := [3, 4, 1, 1, 1, 1, 4, 3, 1, 4]
def baseStart_1754882 : Nat := 118140960795 + 1754882 * 2 ^ 59
def prefixEnd_1754882 : Nat := 4983230072969 + 3 ^ 40 * 1754882 * 2
def baseEnd_1754882 : Nat := 300365985974502749934817

theorem tailTrace_1754882 : CollatzResearch.WordTrace tailWord_1754882 prefixEnd_1754882 300365985974502749934817 := by
  unfold tailWord_1754882
  simp only [CollatzResearch.WordTrace]
  refine ⟨16001451207092424707394725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42670536552246465886385933 16001451207092424707394725)
  ·
    refine ⟨3000272101329829632636511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16001451207092424707394725 3000272101329829632636511)
    ·
      refine ⟨4500408151994744448954767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3000272101329829632636511 4500408151994744448954767)
      ·
        refine ⟨6750612227992116673432151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4500408151994744448954767 6750612227992116673432151)
        ·
          refine ⟨10125918341988175010148227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6750612227992116673432151 10125918341988175010148227)
          ·
            refine ⟨15188877512982262515222341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10125918341988175010148227 15188877512982262515222341)
            ·
              refine ⟨2847914533684174221604189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15188877512982262515222341 2847914533684174221604189)
              ·
                refine ⟨1067967950131565333101571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2847914533684174221604189 1067967950131565333101571)
                ·
                  refine ⟨1601951925197347999652357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1067967950131565333101571 1601951925197347999652357)
                  ·
                    refine ⟨300365985974502749934817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1601951925197347999652357 300365985974502749934817)
                    ·
                      rfl

theorem cell23_1754882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_1754882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754882 prefixEnd_1754882 := by exact prefixLift 1754882
  have htrace : WordTrace (prefixWord ++ tailWord_1754882) baseStart_1754882 baseEnd_1754882 := by
    simpa [prefixWord, tailWord_1754882, baseEnd_1754882] using wordTrace_append hprefix tailTrace_1754882
  have hstable : (prefixWord ++ tailWord_1754882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754882).length < 2 ^ (prefixWord ++ tailWord_1754882).sum := by decide
  have hdescent : baseEnd_1754882 < baseStart_1754882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754888 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 5, 1, 3]
def baseStart_1754888 : Nat := 118140960795 + 1754888 * 2 ^ 59
def prefixEnd_1754888 : Nat := 4983230072969 + 3 ^ 40 * 1754888 * 2
def baseEnd_1754888 : Nat := 901101038807435226329423

theorem tailTrace_1754888 : CollatzResearch.WordTrace tailWord_1754888 prefixEnd_1754888 901101038807435226329423 := by
  unfold tailWord_1754888
  simp only [CollatzResearch.WordTrace]
  refine ⟨32003011833173980927148659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42670682444231974569531545 32003011833173980927148659)
  ·
    refine ⟨48004517749760971390722989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32003011833173980927148659 48004517749760971390722989)
    ·
      refine ⟨18001694156160364271521121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48004517749760971390722989 18001694156160364271521121)
      ·
        refine ⟨13501270617120273203640841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18001694156160364271521121 13501270617120273203640841)
        ·
          refine ⟨10125952962840204902730631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13501270617120273203640841 10125952962840204902730631)
          ·
            refine ⟨15188929444260307354095947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10125952962840204902730631 15188929444260307354095947)
            ·
              refine ⟨22783394166390461031143921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15188929444260307354095947 22783394166390461031143921)
              ·
                refine ⟨17087545624792845773357941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22783394166390461031143921 17087545624792845773357941)
                ·
                  refine ⟨1601957402324329291252307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17087545624792845773357941 1601957402324329291252307)
                  ·
                    refine ⟨2402936103486493936878461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1601957402324329291252307 2402936103486493936878461)
                    ·
                      refine ⟨901101038807435226329423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2402936103486493936878461 901101038807435226329423)
                      ·
                        rfl

theorem cell23_1754888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_1754888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754888 prefixEnd_1754888 := by exact prefixLift 1754888
  have htrace : WordTrace (prefixWord ++ tailWord_1754888) baseStart_1754888 baseEnd_1754888 := by
    simpa [prefixWord, tailWord_1754888, baseEnd_1754888] using wordTrace_append hprefix tailTrace_1754888
  have hstable : (prefixWord ++ tailWord_1754888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754888).length < 2 ^ (prefixWord ++ tailWord_1754888).sum := by decide
  have hdescent : baseEnd_1754888 < baseStart_1754888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754898 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_1754898 : Nat := 118140960795 + 1754898 * 2 ^ 59
def prefixEnd_1754898 : Nat := 4983230072969 + 3 ^ 40 * 1754898 * 2
def baseEnd_1754898 : Nat := 901106173613980187204377

theorem tailTrace_1754898 : CollatzResearch.WordTrace tailWord_1754898 prefixEnd_1754898 901106173613980187204377 := by
  unfold tailWord_1754898
  simp only [CollatzResearch.WordTrace]
  refine ⟨16001597099077933390540337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42670925597541155708107565 16001597099077933390540337)
  ·
    refine ⟨12001197824308450042905253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16001597099077933390540337 12001197824308450042905253)
    ·
      refine ⟨2250224592057834383044735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12001197824308450042905253 2250224592057834383044735)
      ·
        refine ⟨3375336888086751574567103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2250224592057834383044735 3375336888086751574567103)
        ·
          refine ⟨5063005332130127361850655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3375336888086751574567103 5063005332130127361850655)
          ·
            refine ⟨7594507998195191042775983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5063005332130127361850655 7594507998195191042775983)
            ·
              refine ⟨11391761997292786564163975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7594507998195191042775983 11391761997292786564163975)
              ·
                refine ⟨17087642995939179846245963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11391761997292786564163975 17087642995939179846245963)
                ·
                  refine ⟨25631464493908769769368945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17087642995939179846245963 25631464493908769769368945)
                  ·
                    refine ⟨19223598370431577327026709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25631464493908769769368945 19223598370431577327026709)
                    ·
                      refine ⟨901106173613980187204377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19223598370431577327026709 901106173613980187204377)
                      ·
                        rfl

theorem cell23_1754898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_1754898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754898 prefixEnd_1754898 := by exact prefixLift 1754898
  have htrace : WordTrace (prefixWord ++ tailWord_1754898) baseStart_1754898 baseEnd_1754898 := by
    simpa [prefixWord, tailWord_1754898, baseEnd_1754898] using wordTrace_append hprefix tailTrace_1754898
  have hstable : (prefixWord ++ tailWord_1754898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754898).length < 2 ^ (prefixWord ++ tailWord_1754898).sum := by decide
  have hdescent : baseEnd_1754898 < baseStart_1754898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754921 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 8, 4]
def baseStart_1754921 : Nat := 118140960795 + 1754921 * 2 ^ 59
def prefixEnd_1754921 : Nat := 4983230072969 + 3 ^ 40 * 1754921 * 2
def baseEnd_1754921 : Nat := 300372661223011199072257

theorem tailTrace_1754921 : CollatzResearch.WordTrace tailWord_1754921 prefixEnd_1754921 300372661223011199072257 := by
  unfold tailWord_1754921
  simp only [CollatzResearch.WordTrace]
  refine ⟨64007227275228408490248617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42671484850152272326832411 64007227275228408490248617)
  ·
    refine ⟨48005420456421306367686463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64007227275228408490248617 48005420456421306367686463)
    ·
      refine ⟨72008130684631959551529695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48005420456421306367686463 72008130684631959551529695)
      ·
        refine ⟨108012196026947939327294543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72008130684631959551529695 108012196026947939327294543)
        ·
          refine ⟨162018294040421908990941815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108012196026947939327294543 162018294040421908990941815)
          ·
            refine ⟨243027441060632863486412723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162018294040421908990941815 243027441060632863486412723)
            ·
              refine ⟨364541161590949295229619085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243027441060632863486412723 364541161590949295229619085)
              ·
                refine ⟨136702935596605985711107157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 364541161590949295229619085 136702935596605985711107157)
                ·
                  refine ⟨1601987526522726395052037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 136702935596605985711107157 1601987526522726395052037)
                  ·
                    refine ⟨300372661223011199072257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1601987526522726395052037 300372661223011199072257)
                    ·
                      rfl

theorem cell23_1754921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 8, 4].length) (baseStart_1754921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754921 prefixEnd_1754921 := by exact prefixLift 1754921
  have htrace : WordTrace (prefixWord ++ tailWord_1754921) baseStart_1754921 baseEnd_1754921 := by
    simpa [prefixWord, tailWord_1754921, baseEnd_1754921] using wordTrace_append hprefix tailTrace_1754921
  have hstable : (prefixWord ++ tailWord_1754921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754921).length < 2 ^ (prefixWord ++ tailWord_1754921).sum := by decide
  have hdescent : baseEnd_1754921 < baseStart_1754921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754938 : List Nat := [3, 1, 1, 1, 5, 1, 1, 2, 4, 4]
def baseStart_1754938 : Nat := 118140960795 + 1754938 * 2 ^ 59
def prefixEnd_1754938 : Nat := 4983230072969 + 3 ^ 40 * 1754938 * 2
def baseEnd_1754938 : Nat := 300375570946720010234731

theorem tailTrace_1754938 : CollatzResearch.WordTrace tailWord_1754938 prefixEnd_1754938 300375570946720010234731 := by
  unfold tailWord_1754938
  simp only [CollatzResearch.WordTrace]
  refine ⟨16001961829041705098404367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42671898210777880262411645 16001961829041705098404367)
  ·
    refine ⟨24002942743562557647606551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16001961829041705098404367 24002942743562557647606551)
    ·
      refine ⟨36004414115343836471409827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24002942743562557647606551 36004414115343836471409827)
      ·
        refine ⟨54006621173015754707114741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36004414115343836471409827 54006621173015754707114741)
        ·
          refine ⟨5063120734970227003792007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54006621173015754707114741 5063120734970227003792007)
          ·
            refine ⟨7594681102455340505688011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5063120734970227003792007 7594681102455340505688011)
            ·
              refine ⟨11392021653683010758532017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7594681102455340505688011 11392021653683010758532017)
              ·
                refine ⟨8544016240262258068899013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11392021653683010758532017 8544016240262258068899013)
                ·
                  refine ⟨1602003045049173387918565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8544016240262258068899013 1602003045049173387918565)
                  ·
                    refine ⟨300375570946720010234731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1602003045049173387918565 300375570946720010234731)
                    ·
                      rfl

theorem cell23_1754938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 4, 4].length) (baseStart_1754938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754938 prefixEnd_1754938 := by exact prefixLift 1754938
  have htrace : WordTrace (prefixWord ++ tailWord_1754938) baseStart_1754938 baseEnd_1754938 := by
    simpa [prefixWord, tailWord_1754938, baseEnd_1754938] using wordTrace_append hprefix tailTrace_1754938
  have hstable : (prefixWord ++ tailWord_1754938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754938).length < 2 ^ (prefixWord ++ tailWord_1754938).sum := by decide
  have hdescent : baseEnd_1754938 < baseStart_1754938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754962 : List Nat := [3, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2]
def baseStart_1754962 : Nat := 118140960795 + 1754962 * 2 ^ 59
def prefixEnd_1754962 : Nat := 4983230072969 + 3 ^ 40 * 1754962 * 2
def baseEnd_1754962 : Nat := 901139036375867936804083

theorem tailTrace_1754962 : CollatzResearch.WordTrace tailWord_1754962 prefixEnd_1754962 901139036375867936804083 := by
  unfold tailWord_1754962
  simp only [CollatzResearch.WordTrace]
  refine ⟨16002180667019968123122785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42672481778719914994994093 16002180667019968123122785)
  ·
    refine ⟨12001635500264976092342089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16002180667019968123122785 12001635500264976092342089)
    ·
      refine ⟨9001226625198732069256567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12001635500264976092342089 9001226625198732069256567)
      ·
        refine ⟨13501839937798098103884851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9001226625198732069256567 13501839937798098103884851)
        ·
          refine ⟨20252759906697147155827277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13501839937798098103884851 20252759906697147155827277)
          ·
            refine ⟨7594784965011430183435229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20252759906697147155827277 7594784965011430183435229)
            ·
              refine ⟨2848044361879286318788211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7594784965011430183435229 2848044361879286318788211)
              ·
                refine ⟨4272066542818929478182317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2848044361879286318788211 4272066542818929478182317)
                ·
                  refine ⟨1602024953557098554318369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4272066542818929478182317 1602024953557098554318369)
                  ·
                    refine ⟨1201518715167823915738777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1602024953557098554318369 1201518715167823915738777)
                    ·
                      refine ⟨901139036375867936804083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1201518715167823915738777 901139036375867936804083)
                      ·
                        rfl

theorem cell23_1754962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_1754962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754962 prefixEnd_1754962 := by exact prefixLift 1754962
  have htrace : WordTrace (prefixWord ++ tailWord_1754962) baseStart_1754962 baseEnd_1754962 := by
    simpa [prefixWord, tailWord_1754962, baseEnd_1754962] using wordTrace_append hprefix tailTrace_1754962
  have hstable : (prefixWord ++ tailWord_1754962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754962).length < 2 ^ (prefixWord ++ tailWord_1754962).sum := by decide
  have hdescent : baseEnd_1754962 < baseStart_1754962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754972 : List Nat := [2, 2, 4, 2, 2, 1, 1, 3, 2, 4]
def baseStart_1754972 : Nat := 118140960795 + 1754972 * 2 ^ 59
def prefixEnd_1754972 : Nat := 4983230072969 + 3 ^ 40 * 1754972 * 2
def baseEnd_1754972 : Nat := 300381390394137632559679

theorem tailTrace_1754972 : CollatzResearch.WordTrace tailWord_1754972 prefixEnd_1754972 300381390394137632559679 := by
  unfold tailWord_1754972
  simp only [CollatzResearch.WordTrace]
  refine ⟨32004543699021822100177585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42672724932029096133570113 32004543699021822100177585)
  ·
    refine ⟨24003407774266366575133189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32004543699021822100177585 24003407774266366575133189)
    ·
      refine ⟨4500638957674943732837473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24003407774266366575133189 4500638957674943732837473)
      ·
        refine ⟨3375479218256207799628105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4500638957674943732837473 3375479218256207799628105)
        ·
          refine ⟨2531609413692155849721079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3375479218256207799628105 2531609413692155849721079)
          ·
            refine ⟨3797414120538233774581619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2531609413692155849721079 3797414120538233774581619)
            ·
              refine ⟨5696121180807350661872429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3797414120538233774581619 5696121180807350661872429)
              ·
                refine ⟨2136045442802756498202161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5696121180807350661872429 2136045442802756498202161)
                ·
                  refine ⟨1602034082102067373651621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2136045442802756498202161 1602034082102067373651621)
                  ·
                    refine ⟨300381390394137632559679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1602034082102067373651621 300381390394137632559679)
                    ·
                      rfl

theorem cell23_1754972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_1754972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1754972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1754972 prefixEnd_1754972 := by exact prefixLift 1754972
  have htrace : WordTrace (prefixWord ++ tailWord_1754972) baseStart_1754972 baseEnd_1754972 := by
    simpa [prefixWord, tailWord_1754972, baseEnd_1754972] using wordTrace_append hprefix tailTrace_1754972
  have hstable : (prefixWord ++ tailWord_1754972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754972).length < 2 ^ (prefixWord ++ tailWord_1754972).sum := by decide
  have hdescent : baseEnd_1754972 < baseStart_1754972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755028 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 1, 8]
def baseStart_1755028 : Nat := 118140960795 + 1755028 * 2 ^ 59
def prefixEnd_1755028 : Nat := 4983230072969 + 3 ^ 40 * 1755028 * 2
def baseEnd_1755028 : Nat := 300390975366354892859593

theorem tailTrace_1755028 : CollatzResearch.WordTrace tailWord_1755028 prefixEnd_1755028 300390975366354892859593 := by
  unfold tailWord_1755028
  simp only [CollatzResearch.WordTrace]
  refine ⟨32005564942920382882196869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42674086590560510509595825 32005564942920382882196869)
  ·
    refine ⟨6001043426797571790411913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32005564942920382882196869 6001043426797571790411913)
    ·
      refine ⟨4500782570098178842808935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6001043426797571790411913 4500782570098178842808935)
      ·
        refine ⟨6751173855147268264213403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4500782570098178842808935 6751173855147268264213403)
        ·
          refine ⟨10126760782720902396320105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6751173855147268264213403 10126760782720902396320105)
          ·
            refine ⟨7595070587040676797240079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10126760782720902396320105 7595070587040676797240079)
            ·
              refine ⟨11392605880561015195860119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7595070587040676797240079 11392605880561015195860119)
              ·
                refine ⟨17088908820841522793790179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11392605880561015195860119 17088908820841522793790179)
                ·
                  refine ⟨25633363231262284190685269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17088908820841522793790179 25633363231262284190685269)
                  ·
                    refine ⟨300390975366354892859593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25633363231262284190685269 300390975366354892859593)
                    ·
                      rfl

theorem cell23_1755028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_1755028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755028 prefixEnd_1755028 := by exact prefixLift 1755028
  have htrace : WordTrace (prefixWord ++ tailWord_1755028) baseStart_1755028 baseEnd_1755028 := by
    simpa [prefixWord, tailWord_1755028, baseEnd_1755028] using wordTrace_append hprefix tailTrace_1755028
  have hstable : (prefixWord ++ tailWord_1755028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755028).length < 2 ^ (prefixWord ++ tailWord_1755028).sum := by decide
  have hdescent : baseEnd_1755028 < baseStart_1755028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755069 : List Nat := [1, 4, 1, 2, 3, 1, 3, 2, 2, 2, 2]
def baseStart_1755069 : Nat := 118140960795 + 1755069 * 2 ^ 59
def prefixEnd_1755069 : Nat := 4983230072969 + 3 ^ 40 * 1755069 * 2
def baseEnd_1755069 : Nat := 901193978805899018166091

theorem tailTrace_1755069 : CollatzResearch.WordTrace tailWord_1755069 prefixEnd_1755069 901193978805899018166091 := by
  unfold tailWord_1755069
  simp only [CollatzResearch.WordTrace]
  refine ⟨64012625278692229766636261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42675083519128153177757507 64012625278692229766636261)
  ·
    refine ⟨12002367239754793081244299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64012625278692229766636261 12002367239754793081244299)
    ·
      refine ⟨18003550859632189621866449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12002367239754793081244299 18003550859632189621866449)
      ·
        refine ⟨13502663144724142216399837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18003550859632189621866449 13502663144724142216399837)
        ·
          refine ⟨5063498679271553331149939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13502663144724142216399837 5063498679271553331149939)
          ·
            refine ⟨7595248018907329996724909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5063498679271553331149939 7595248018907329996724909)
            ·
              refine ⟨2848218007090248748771841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7595248018907329996724909 2848218007090248748771841)
              ·
                refine ⟨2136163505317686561578881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2848218007090248748771841 2136163505317686561578881)
                ·
                  refine ⟨1602122628988264921184161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2136163505317686561578881 1602122628988264921184161)
                  ·
                    refine ⟨1201591971741198690888121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1602122628988264921184161 1201591971741198690888121)
                    ·
                      refine ⟨901193978805899018166091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1201591971741198690888121 901193978805899018166091)
                      ·
                        rfl

theorem cell23_1755069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_1755069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755069 prefixEnd_1755069 := by exact prefixLift 1755069
  have htrace : WordTrace (prefixWord ++ tailWord_1755069) baseStart_1755069 baseEnd_1755069 := by
    simpa [prefixWord, tailWord_1755069, baseEnd_1755069] using wordTrace_append hprefix tailTrace_1755069
  have hstable : (prefixWord ++ tailWord_1755069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755069).length < 2 ^ (prefixWord ++ tailWord_1755069).sum := by decide
  have hdescent : baseEnd_1755069 < baseStart_1755069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755108 : List Nat := [2, 3, 1, 1, 1, 1, 3, 3, 1, 3, 4]
def baseStart_1755108 : Nat := 118140960795 + 1755108 * 2 ^ 59
def prefixEnd_1755108 : Nat := 4983230072969 + 3 ^ 40 * 1755108 * 2
def baseEnd_1755108 : Nat := 901214004551424365578411

theorem tailTrace_1755108 : CollatzResearch.WordTrace tailWord_1755108 prefixEnd_1755108 901214004551424365578411 := by
  unfold tailWord_1755108
  simp only [CollatzResearch.WordTrace]
  refine ⟨32007023862775469713652989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42676031817033959618203985 32007023862775469713652989)
  ·
    refine ⟨12002633948540801142619871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32007023862775469713652989 12002633948540801142619871)
    ·
      refine ⟨18003950922811201713929807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12002633948540801142619871 18003950922811201713929807)
      ·
        refine ⟨27005926384216802570894711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18003950922811201713929807 27005926384216802570894711)
        ·
          refine ⟨40508889576325203856342067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27005926384216802570894711 40508889576325203856342067)
          ·
            refine ⟨60763334364487805784513101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40508889576325203856342067 60763334364487805784513101)
            ·
              refine ⟨22786250386682927169192413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60763334364487805784513101 22786250386682927169192413)
              ·
                refine ⟨8544843895006097688447155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22786250386682927169192413 8544843895006097688447155)
                ·
                  refine ⟨12817265842509146532670733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8544843895006097688447155 12817265842509146532670733)
                  ·
                    refine ⟨4806474690940929949751525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12817265842509146532670733 4806474690940929949751525)
                    ·
                      refine ⟨901214004551424365578411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4806474690940929949751525 901214004551424365578411)
                      ·
                        rfl

theorem cell23_1755108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_1755108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755108 prefixEnd_1755108 := by exact prefixLift 1755108
  have htrace : WordTrace (prefixWord ++ tailWord_1755108) baseStart_1755108 baseEnd_1755108 := by
    simpa [prefixWord, tailWord_1755108, baseEnd_1755108] using wordTrace_append hprefix tailTrace_1755108
  have hstable : (prefixWord ++ tailWord_1755108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755108).length < 2 ^ (prefixWord ++ tailWord_1755108).sum := by decide
  have hdescent : baseEnd_1755108 < baseStart_1755108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755162 : List Nat := [3, 1, 1, 3, 1, 4, 2, 1, 2, 2, 3]
def baseStart_1755162 : Nat := 118140960795 + 1755162 * 2 ^ 59
def prefixEnd_1755162 : Nat := 4983230072969 + 3 ^ 40 * 1755162 * 2
def baseEnd_1755162 : Nat := 901241732506767154303163

theorem tailTrace_1755162 : CollatzResearch.WordTrace tailWord_1755162 prefixEnd_1755162 901241732506767154303163 := by
  unfold tailWord_1755162
  simp only [CollatzResearch.WordTrace]
  refine ⟨16004004316838826662442935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42677344844903537766514493 16004004316838826662442935)
  ·
    refine ⟨24006006475258239993664403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16004004316838826662442935 24006006475258239993664403)
    ·
      refine ⟨36009009712887359990496605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24006006475258239993664403 36009009712887359990496605)
      ·
        refine ⟨13503378642332759996436227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36009009712887359990496605 13503378642332759996436227)
        ·
          refine ⟨20255067963499139994654341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13503378642332759996436227 20255067963499139994654341)
          ·
            refine ⟨3797825243156088748997689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20255067963499139994654341 3797825243156088748997689)
            ·
              refine ⟨2848368932367066561748267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3797825243156088748997689 2848368932367066561748267)
              ·
                refine ⟨4272553398550599842622401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2848368932367066561748267 4272553398550599842622401)
                ·
                  refine ⟨3204415048912949881966801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4272553398550599842622401 3204415048912949881966801)
                  ·
                    refine ⟨2403311286684712411475101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3204415048912949881966801 2403311286684712411475101)
                    ·
                      refine ⟨901241732506767154303163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2403311286684712411475101 901241732506767154303163)
                      ·
                        rfl

theorem cell23_1755162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_1755162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755162 prefixEnd_1755162 := by exact prefixLift 1755162
  have htrace : WordTrace (prefixWord ++ tailWord_1755162) baseStart_1755162 baseEnd_1755162 := by
    simpa [prefixWord, tailWord_1755162, baseEnd_1755162] using wordTrace_append hprefix tailTrace_1755162
  have hstable : (prefixWord ++ tailWord_1755162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755162).length < 2 ^ (prefixWord ++ tailWord_1755162).sum := by decide
  have hdescent : baseEnd_1755162 < baseStart_1755162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755182 : List Nat := [4, 1, 3, 1, 1, 3, 2, 2, 6]
def baseStart_1755182 : Nat := 118140960795 + 1755182 * 2 ^ 59
def prefixEnd_1755182 : Nat := 4983230072969 + 3 ^ 40 * 1755182 * 2
def baseEnd_1755182 : Nat := 100139111346650786228119

theorem tailTrace_1755182 : CollatzResearch.WordTrace tailWord_1755182 prefixEnd_1755182 100139111346650786228119 := by
  unfold tailWord_1755182
  simp only [CollatzResearch.WordTrace]
  refine ⟨8002093340910356258187475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42677831151521900043666533 8002093340910356258187475)
  ·
    refine ⟨12003140011365534387281213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8002093340910356258187475 12003140011365534387281213)
    ·
      refine ⟨4501177504262075395230455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12003140011365534387281213 4501177504262075395230455)
      ·
        refine ⟨6751766256393113092845683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4501177504262075395230455 6751766256393113092845683)
        ·
          refine ⟨10127649384589669639268525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6751766256393113092845683 10127649384589669639268525)
          ·
            refine ⟨3797868519221126114725697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10127649384589669639268525 3797868519221126114725697)
            ·
              refine ⟨2848401389415844586044273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3797868519221126114725697 2848401389415844586044273)
              ·
                refine ⟨2136301042061883439533205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2848401389415844586044273 2136301042061883439533205)
                ·
                  refine ⟨100139111346650786228119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2136301042061883439533205 100139111346650786228119)
                  ·
                    rfl

theorem cell23_1755182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 6].length) (baseStart_1755182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755182 prefixEnd_1755182 := by exact prefixLift 1755182
  have htrace : WordTrace (prefixWord ++ tailWord_1755182) baseStart_1755182 baseEnd_1755182 := by
    simpa [prefixWord, tailWord_1755182, baseEnd_1755182] using wordTrace_append hprefix tailTrace_1755182
  have hstable : (prefixWord ++ tailWord_1755182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755182).length < 2 ^ (prefixWord ++ tailWord_1755182).sum := by decide
  have hdescent : baseEnd_1755182 < baseStart_1755182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755186 : List Nat := [3, 2, 1, 1, 2, 5, 2, 2, 1, 4]
def baseStart_1755186 : Nat := 118140960795 + 1755186 * 2 ^ 59
def prefixEnd_1755186 : Nat := 4983230072969 + 3 ^ 40 * 1755186 * 2
def baseEnd_1755186 : Nat := 300418018680825020134351

theorem tailTrace_1755186 : CollatzResearch.WordTrace tailWord_1755186 prefixEnd_1755186 300418018680825020134351 := by
  unfold tailWord_1755186
  simp only [CollatzResearch.WordTrace]
  refine ⟨16004223154817089687161353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42677928412845572499096941 16004223154817089687161353)
  ·
    refine ⟨12003167366112817265371015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16004223154817089687161353 12003167366112817265371015)
    ·
      refine ⟨18004751049169225898056523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12003167366112817265371015 18004751049169225898056523)
      ·
        refine ⟨27007126573753838847084785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18004751049169225898056523 27007126573753838847084785)
        ·
          refine ⟨20255344930315379135313589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27007126573753838847084785 20255344930315379135313589)
          ·
            refine ⟨1898938587217066793935649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20255344930315379135313589 1898938587217066793935649)
            ·
              refine ⟨1424203940412800095451737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1898938587217066793935649 1424203940412800095451737)
              ·
                refine ⟨1068152955309600071588803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1424203940412800095451737 1068152955309600071588803)
                ·
                  refine ⟨1602229432964400107383205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1068152955309600071588803 1602229432964400107383205)
                  ·
                    refine ⟨300418018680825020134351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1602229432964400107383205 300418018680825020134351)
                    ·
                      rfl

theorem cell23_1755186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_1755186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755186 prefixEnd_1755186 := by exact prefixLift 1755186
  have htrace : WordTrace (prefixWord ++ tailWord_1755186) baseStart_1755186 baseEnd_1755186 := by
    simpa [prefixWord, tailWord_1755186, baseEnd_1755186] using wordTrace_append hprefix tailTrace_1755186
  have hstable : (prefixWord ++ tailWord_1755186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755186).length < 2 ^ (prefixWord ++ tailWord_1755186).sum := by decide
  have hdescent : baseEnd_1755186 < baseStart_1755186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755215 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 2, 6, 2]
def baseStart_1755215 : Nat := 118140960795 + 1755215 * 2 ^ 59
def prefixEnd_1755215 : Nat := 4983230072969 + 3 ^ 40 * 1755215 * 2
def baseEnd_1755215 : Nat := 901268946981455446940419

theorem tailTrace_1755215 : CollatzResearch.WordTrace tailWord_1755215 prefixEnd_1755215 901268946981455446940419 := by
  unfold tailWord_1755215
  simp only [CollatzResearch.WordTrace]
  refine ⟨64017950336163296701451099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42678633557442197800967399 64017950336163296701451099)
  ·
    refine ⟨96026925504244945052176649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64017950336163296701451099 96026925504244945052176649)
    ·
      refine ⟨72020194128183708789132487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96026925504244945052176649 72020194128183708789132487)
      ·
        refine ⟨108030291192275563183698731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72020194128183708789132487 108030291192275563183698731)
        ·
          refine ⟨162045436788413344775548097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108030291192275563183698731 162045436788413344775548097)
          ·
            refine ⟨121534077591310008581661073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162045436788413344775548097 121534077591310008581661073)
            ·
              refine ⟨91150558193482506436245805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121534077591310008581661073 91150558193482506436245805)
              ·
                refine ⟨34181459322555939913592177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91150558193482506436245805 34181459322555939913592177)
                ·
                  refine ⟨25636094491916954935194133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34181459322555939913592177 25636094491916954935194133)
                  ·
                    refine ⟨1201691929308607262587225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25636094491916954935194133 1201691929308607262587225)
                    ·
                      refine ⟨901268946981455446940419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1201691929308607262587225 901268946981455446940419)
                      ·
                        rfl

theorem cell23_1755215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 6, 2].length) (baseStart_1755215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755215 prefixEnd_1755215 := by exact prefixLift 1755215
  have htrace : WordTrace (prefixWord ++ tailWord_1755215) baseStart_1755215 baseEnd_1755215 := by
    simpa [prefixWord, tailWord_1755215, baseEnd_1755215] using wordTrace_append hprefix tailTrace_1755215
  have hstable : (prefixWord ++ tailWord_1755215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755215).length < 2 ^ (prefixWord ++ tailWord_1755215).sum := by decide
  have hdescent : baseEnd_1755215 < baseStart_1755215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755225 : List Nat := [1, 2, 1, 2, 2, 1, 4, 2, 4, 4]
def baseStart_1755225 : Nat := 118140960795 + 1755225 * 2 ^ 59
def prefixEnd_1755225 : Nat := 4983230072969 + 3 ^ 40 * 1755225 * 2
def baseEnd_1755225 : Nat := 300424693929333469271791

theorem tailTrace_1755225 : CollatzResearch.WordTrace tailWord_1755225 prefixEnd_1755225 300424693929333469271791 := by
  unfold tailWord_1755225
  simp only [CollatzResearch.WordTrace]
  refine ⟨64018315066127068409315129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42678876710751378939543419 64018315066127068409315129)
  ·
    refine ⟨48013736299595301306986347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64018315066127068409315129 48013736299595301306986347)
    ·
      refine ⟨72020604449392951960479521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48013736299595301306986347 72020604449392951960479521)
      ·
        refine ⟨54015453337044713970359641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72020604449392951960479521 54015453337044713970359641)
        ·
          refine ⟨40511590002783535477769731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54015453337044713970359641 40511590002783535477769731)
          ·
            refine ⟨60767385004175303216654597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40511590002783535477769731 60767385004175303216654597)
            ·
              refine ⟨11393884688282869353122737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60767385004175303216654597 11393884688282869353122737)
              ·
                refine ⟨8545413516212152014842053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11393884688282869353122737 8545413516212152014842053)
                ·
                  refine ⟨1602265034289778502782885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8545413516212152014842053 1602265034289778502782885)
                  ·
                    refine ⟨300424693929333469271791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1602265034289778502782885 300424693929333469271791)
                    ·
                      rfl

theorem cell23_1755225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 4, 4].length) (baseStart_1755225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755225 prefixEnd_1755225 := by exact prefixLift 1755225
  have htrace : WordTrace (prefixWord ++ tailWord_1755225) baseStart_1755225 baseEnd_1755225 := by
    simpa [prefixWord, tailWord_1755225, baseEnd_1755225] using wordTrace_append hprefix tailTrace_1755225
  have hstable : (prefixWord ++ tailWord_1755225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755225).length < 2 ^ (prefixWord ++ tailWord_1755225).sum := by decide
  have hdescent : baseEnd_1755225 < baseStart_1755225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755229 : List Nat := [1, 4, 4, 1, 1, 2, 1, 3, 1, 5]
def baseStart_1755229 : Nat := 118140960795 + 1755229 * 2 ^ 59
def prefixEnd_1755229 : Nat := 4983230072969 + 3 ^ 40 * 1755229 * 2
def baseEnd_1755229 : Nat := 300425378570206130721785

theorem tailTrace_1755229 : CollatzResearch.WordTrace tailWord_1755229 prefixEnd_1755229 300425378570206130721785 := by
  unfold tailWord_1755229
  simp only [CollatzResearch.WordTrace]
  refine ⟨64018460958112577092460741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42678973972075051394973827 64018460958112577092460741)
  ·
    refine ⟨12003461429646108204836389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64018460958112577092460741 12003461429646108204836389)
    ·
      refine ⟨2250649018058645288406823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12003461429646108204836389 2250649018058645288406823)
      ·
        refine ⟨3375973527087967932610235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2250649018058645288406823 3375973527087967932610235)
        ·
          refine ⟨5063960290631951898915353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3375973527087967932610235 5063960290631951898915353)
          ·
            refine ⟨3797970217973963924186515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5063960290631951898915353 3797970217973963924186515)
            ·
              refine ⟨5696955326960945886279773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3797970217973963924186515 5696955326960945886279773)
              ·
                refine ⟨2136358247610354707354915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5696955326960945886279773 2136358247610354707354915)
                ·
                  refine ⟨3204537371415532061032373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2136358247610354707354915 3204537371415532061032373)
                  ·
                    refine ⟨300425378570206130721785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3204537371415532061032373 300425378570206130721785)
                    ·
                      rfl

theorem cell23_1755229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_1755229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755229 prefixEnd_1755229 := by exact prefixLift 1755229
  have htrace : WordTrace (prefixWord ++ tailWord_1755229) baseStart_1755229 baseEnd_1755229 := by
    simpa [prefixWord, tailWord_1755229, baseEnd_1755229] using wordTrace_append hprefix tailTrace_1755229
  have hstable : (prefixWord ++ tailWord_1755229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755229).length < 2 ^ (prefixWord ++ tailWord_1755229).sum := by decide
  have hdescent : baseEnd_1755229 < baseStart_1755229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755232 : List Nat := [2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 4]
def baseStart_1755232 : Nat := 118140960795 + 1755232 * 2 ^ 59
def prefixEnd_1755232 : Nat := 4983230072969 + 3 ^ 40 * 1755232 * 2
def baseEnd_1755232 : Nat := 901277676152581880427841

theorem tailTrace_1755232 : CollatzResearch.WordTrace tailWord_1755232 prefixEnd_1755232 901277676152581880427841 := by
  unfold tailWord_1755232
  simp only [CollatzResearch.WordTrace]
  refine ⟨32009285188550854302409975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42679046918067805736546633 32009285188550854302409975)
  ·
    refine ⟨48013927782826281453614963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32009285188550854302409975 48013927782826281453614963)
    ·
      refine ⟨72020891674239422180422445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48013927782826281453614963 72020891674239422180422445)
      ·
        refine ⟨27007834377839783317658417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72020891674239422180422445 27007834377839783317658417)
        ·
          refine ⟨20255875783379837488243813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27007834377839783317658417 20255875783379837488243813)
          ·
            refine ⟨3797976709383719529045715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20255875783379837488243813 3797976709383719529045715)
            ·
              refine ⟨5696965064075579293568573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3797976709383719529045715 5696965064075579293568573)
              ·
                refine ⟨2136361899028342235088215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5696965064075579293568573 2136361899028342235088215)
                ·
                  refine ⟨3204542848542513352632323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2136361899028342235088215 3204542848542513352632323)
                  ·
                    refine ⟨4806814272813770028948485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3204542848542513352632323 4806814272813770028948485)
                    ·
                      refine ⟨901277676152581880427841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4806814272813770028948485 901277676152581880427841)
                      ·
                        rfl

theorem cell23_1755232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_1755232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755232 prefixEnd_1755232 := by exact prefixLift 1755232
  have htrace : WordTrace (prefixWord ++ tailWord_1755232) baseStart_1755232 baseEnd_1755232 := by
    simpa [prefixWord, tailWord_1755232, baseEnd_1755232] using wordTrace_append hprefix tailTrace_1755232
  have hstable : (prefixWord ++ tailWord_1755232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755232).length < 2 ^ (prefixWord ++ tailWord_1755232).sum := by decide
  have hdescent : baseEnd_1755232 < baseStart_1755232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755245 : List Nat := [1, 5, 1, 1, 2, 1, 2, 2, 1, 1, 6]
def baseStart_1755245 : Nat := 118140960795 + 1755245 * 2 ^ 59
def prefixEnd_1755245 : Nat := 4983230072969 + 3 ^ 40 * 1755245 * 2
def baseEnd_1755245 : Nat := 901284351401090329565281

theorem tailTrace_1755245 : CollatzResearch.WordTrace tailWord_1755245 prefixEnd_1755245 901284351401090329565281 := by
  unfold tailWord_1755245
  simp only [CollatzResearch.WordTrace]
  refine ⟨64019044526054611825043189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42679363017369741216695459 64019044526054611825043189)
  ·
    refine ⟨6001785424317619858597799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64019044526054611825043189 6001785424317619858597799)
    ·
      refine ⟨9002678136476429787896699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6001785424317619858597799 9002678136476429787896699)
      ·
        refine ⟨13504017204714644681845049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9002678136476429787896699 13504017204714644681845049)
        ·
          refine ⟨10128012903535983511383787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13504017204714644681845049 10128012903535983511383787)
          ·
            refine ⟨15192019355303975267075681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10128012903535983511383787 15192019355303975267075681)
            ·
              refine ⟨11394014516477981450306761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15192019355303975267075681 11394014516477981450306761)
              ·
                refine ⟨8545510887358486087730071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11394014516477981450306761 8545510887358486087730071)
                ·
                  refine ⟨12818266331037729131595107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8545510887358486087730071 12818266331037729131595107)
                  ·
                    refine ⟨19227399496556593697392661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12818266331037729131595107 19227399496556593697392661)
                    ·
                      refine ⟨901284351401090329565281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19227399496556593697392661 901284351401090329565281)
                      ·
                        rfl

theorem cell23_1755245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_1755245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755245 prefixEnd_1755245 := by exact prefixLift 1755245
  have htrace : WordTrace (prefixWord ++ tailWord_1755245) baseStart_1755245 baseEnd_1755245 := by
    simpa [prefixWord, tailWord_1755245, baseEnd_1755245] using wordTrace_append hprefix tailTrace_1755245
  have hstable : (prefixWord ++ tailWord_1755245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755245).length < 2 ^ (prefixWord ++ tailWord_1755245).sum := by decide
  have hdescent : baseEnd_1755245 < baseStart_1755245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755249 : List Nat := [1, 2, 2, 2, 1, 1, 6, 1, 3, 2, 2]
def baseStart_1755249 : Nat := 118140960795 + 1755249 * 2 ^ 59
def prefixEnd_1755249 : Nat := 4983230072969 + 3 ^ 40 * 1755249 * 2
def baseEnd_1755249 : Nat := 901286405323708313915263

theorem tailTrace_1755249 : CollatzResearch.WordTrace tailWord_1755249 prefixEnd_1755249 901286405323708313915263 := by
  unfold tailWord_1755249
  simp only [CollatzResearch.WordTrace]
  refine ⟨64019190418040120508188801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42679460278693413672125867 64019190418040120508188801)
  ·
    refine ⟨48014392813530090381141601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64019190418040120508188801 48014392813530090381141601)
    ·
      refine ⟨36010794610147567785856201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48014392813530090381141601 36010794610147567785856201)
      ·
        refine ⟨27008095957610675839392151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36010794610147567785856201 27008095957610675839392151)
        ·
          refine ⟨40512143936416013759088227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27008095957610675839392151 40512143936416013759088227)
          ·
            refine ⟨60768215904624020638632341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40512143936416013759088227 60768215904624020638632341)
            ·
              refine ⟨2848510120529250967435891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60768215904624020638632341 2848510120529250967435891)
              ·
                refine ⟨4272765180793876451153837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2848510120529250967435891 4272765180793876451153837)
                ·
                  refine ⟨1602286942797703669182689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4272765180793876451153837 1602286942797703669182689)
                  ·
                    refine ⟨1201715207098277751887017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1602286942797703669182689 1201715207098277751887017)
                    ·
                      refine ⟨901286405323708313915263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1201715207098277751887017 901286405323708313915263)
                      ·
                        rfl

theorem cell23_1755249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 3, 2, 2].length) (baseStart_1755249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755249 prefixEnd_1755249 := by exact prefixLift 1755249
  have htrace : WordTrace (prefixWord ++ tailWord_1755249) baseStart_1755249 baseEnd_1755249 := by
    simpa [prefixWord, tailWord_1755249, baseEnd_1755249] using wordTrace_append hprefix tailTrace_1755249
  have hstable : (prefixWord ++ tailWord_1755249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755249).length < 2 ^ (prefixWord ++ tailWord_1755249).sum := by decide
  have hdescent : baseEnd_1755249 < baseStart_1755249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755269 : List Nat := [1, 3, 1, 1, 5, 2, 2, 2, 1, 2, 3]
def baseStart_1755269 : Nat := 118140960795 + 1755269 * 2 ^ 59
def prefixEnd_1755269 : Nat := 4983230072969 + 3 ^ 40 * 1755269 * 2
def baseEnd_1755269 : Nat := 901296674936798235665171

theorem tailTrace_1755269 : CollatzResearch.WordTrace tailWord_1755269 prefixEnd_1755269 901296674936798235665171 := by
  unfold tailWord_1755269
  simp only [CollatzResearch.WordTrace]
  refine ⟨64019919877967663923916861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42679946585311775949277907 64019919877967663923916861)
  ·
    refine ⟨24007469954237873971468823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64019919877967663923916861 24007469954237873971468823)
    ·
      refine ⟨36011204931356810957203235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24007469954237873971468823 36011204931356810957203235)
      ·
        refine ⟨54016807397035216435804853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36011204931356810957203235 54016807397035216435804853)
        ·
          refine ⟨5064075693472051540856705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54016807397035216435804853 5064075693472051540856705)
          ·
            refine ⟨3798056770104038655642529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5064075693472051540856705 3798056770104038655642529)
            ·
              refine ⟨2848542577578028991731897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3798056770104038655642529 2848542577578028991731897)
              ·
                refine ⟨2136406933183521743798923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2848542577578028991731897 2136406933183521743798923)
                ·
                  refine ⟨3204610399775282615698385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2136406933183521743798923 3204610399775282615698385)
                  ·
                    refine ⟨2403457799831461961773789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3204610399775282615698385 2403457799831461961773789)
                    ·
                      refine ⟨901296674936798235665171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2403457799831461961773789 901296674936798235665171)
                      ·
                        rfl

theorem cell23_1755269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 2, 3].length) (baseStart_1755269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755269 prefixEnd_1755269 := by exact prefixLift 1755269
  have htrace : WordTrace (prefixWord ++ tailWord_1755269) baseStart_1755269 baseEnd_1755269 := by
    simpa [prefixWord, tailWord_1755269, baseEnd_1755269] using wordTrace_append hprefix tailTrace_1755269
  have hstable : (prefixWord ++ tailWord_1755269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755269).length < 2 ^ (prefixWord ++ tailWord_1755269).sum := by decide
  have hdescent : baseEnd_1755269 < baseStart_1755269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755272 : List Nat := [2, 1, 3, 4, 1, 1, 4, 7]
def baseStart_1755272 : Nat := 118140960795 + 1755272 * 2 ^ 59
def prefixEnd_1755272 : Nat := 4983230072969 + 3 ^ 40 * 1755272 * 2
def baseEnd_1755272 : Nat := 33381415384398582367691

theorem tailTrace_1755272 : CollatzResearch.WordTrace tailWord_1755272 prefixEnd_1755272 33381415384398582367691 := by
  unfold tailWord_1755272
  simp only [CollatzResearch.WordTrace]
  refine ⟨32010014648478397718138035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42680019531304530290850713 32010014648478397718138035)
  ·
    refine ⟨48015021972717596577207053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32010014648478397718138035 48015021972717596577207053)
    ·
      refine ⟨18005633239769098716452645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48015021972717596577207053 18005633239769098716452645)
      ·
        refine ⟨3376056232456706009334871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18005633239769098716452645 3376056232456706009334871)
        ·
          refine ⟨5064084348685059014002307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3376056232456706009334871 5064084348685059014002307)
          ·
            refine ⟨7596126523027588521003461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5064084348685059014002307 7596126523027588521003461)
            ·
              refine ⟨1424273723067672847688149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7596126523027588521003461 1424273723067672847688149)
              ·
                refine ⟨33381415384398582367691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1424273723067672847688149 33381415384398582367691)
                ·
                  rfl

theorem cell23_1755272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 7].length) (baseStart_1755272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755272 prefixEnd_1755272 := by exact prefixLift 1755272
  have htrace : WordTrace (prefixWord ++ tailWord_1755272) baseStart_1755272 baseEnd_1755272 := by
    simpa [prefixWord, tailWord_1755272, baseEnd_1755272] using wordTrace_append hprefix tailTrace_1755272
  have hstable : (prefixWord ++ tailWord_1755272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755272).length < 2 ^ (prefixWord ++ tailWord_1755272).sum := by decide
  have hdescent : baseEnd_1755272 < baseStart_1755272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755282 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 3, 3, 3]
def baseStart_1755282 : Nat := 118140960795 + 1755282 * 2 ^ 59
def prefixEnd_1755282 : Nat := 4983230072969 + 3 ^ 40 * 1755282 * 2
def baseEnd_1755282 : Nat := 901303350185306684802611

theorem tailTrace_1755282 : CollatzResearch.WordTrace tailWord_1755282 prefixEnd_1755282 901303350185306684802611 := by
  unfold tailWord_1755282
  simp only [CollatzResearch.WordTrace]
  refine ⟨16005098506730141786035025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42680262684613711429426733 16005098506730141786035025)
  ·
    refine ⟨12003823880047606339526269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16005098506730141786035025 12003823880047606339526269)
    ·
      refine ⟨4501433955017852377322351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12003823880047606339526269 4501433955017852377322351)
      ·
        refine ⟨6752150932526778565983527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4501433955017852377322351 6752150932526778565983527)
        ·
          refine ⟨10128226398790167848975291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6752150932526778565983527 10128226398790167848975291)
          ·
            refine ⟨15192339598185251773462937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10128226398790167848975291 15192339598185251773462937)
            ·
              refine ⟨11394254698638938830097203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15192339598185251773462937 11394254698638938830097203)
              ·
                refine ⟨17091382047958408245145805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11394254698638938830097203 17091382047958408245145805)
                ·
                  refine ⟨6409268267984403091929677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17091382047958408245145805 6409268267984403091929677)
                  ·
                    refine ⟨2403475600494151159473629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6409268267984403091929677 2403475600494151159473629)
                    ·
                      refine ⟨901303350185306684802611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2403475600494151159473629 901303350185306684802611)
                      ·
                        rfl

theorem cell23_1755282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_1755282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755282 prefixEnd_1755282 := by exact prefixLift 1755282
  have htrace : WordTrace (prefixWord ++ tailWord_1755282) baseStart_1755282 baseEnd_1755282 := by
    simpa [prefixWord, tailWord_1755282, baseEnd_1755282] using wordTrace_append hprefix tailTrace_1755282
  have hstable : (prefixWord ++ tailWord_1755282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755282).length < 2 ^ (prefixWord ++ tailWord_1755282).sum := by decide
  have hdescent : baseEnd_1755282 < baseStart_1755282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755300 : List Nat := [2, 3, 1, 2, 4, 1, 3, 2, 1, 2, 2]
def baseStart_1755300 : Nat := 118140960795 + 1755300 * 2 ^ 59
def prefixEnd_1755300 : Nat := 4983230072969 + 3 ^ 40 * 1755300 * 2
def baseEnd_1755300 : Nat := 901312592837087614377529

theorem tailTrace_1755300 : CollatzResearch.WordTrace tailWord_1755300 prefixEnd_1755300 901312592837087614377529 := by
  unfold tailWord_1755300
  simp only [CollatzResearch.WordTrace]
  refine ⟨32010525270427678109147677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42680700360570237478863569 32010525270427678109147677)
  ·
    refine ⟨12003946976410379290930379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32010525270427678109147677 12003946976410379290930379)
    ·
      refine ⟨18005920464615568936395569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12003946976410379290930379 18005920464615568936395569)
      ·
        refine ⟨13504440348461676702296677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18005920464615568936395569 13504440348461676702296677)
        ·
          refine ⟨2532082565336564381680627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13504440348461676702296677 2532082565336564381680627)
          ·
            refine ⟨3798123848004846572520941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2532082565336564381680627 3798123848004846572520941)
            ·
              refine ⟨1424296443001817464695353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3798123848004846572520941 1424296443001817464695353)
              ·
                refine ⟨1068222332251363098521515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1424296443001817464695353 1068222332251363098521515)
                ·
                  refine ⟨1602333498377044647782273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1068222332251363098521515 1602333498377044647782273)
                  ·
                    refine ⟨1201750123782783485836705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1602333498377044647782273 1201750123782783485836705)
                    ·
                      refine ⟨901312592837087614377529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1201750123782783485836705 901312592837087614377529)
                      ·
                        rfl

theorem cell23_1755300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_1755300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755300 prefixEnd_1755300 := by exact prefixLift 1755300
  have htrace : WordTrace (prefixWord ++ tailWord_1755300) baseStart_1755300 baseEnd_1755300 := by
    simpa [prefixWord, tailWord_1755300, baseEnd_1755300] using wordTrace_append hprefix tailTrace_1755300
  have hstable : (prefixWord ++ tailWord_1755300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755300).length < 2 ^ (prefixWord ++ tailWord_1755300).sum := by decide
  have hdescent : baseEnd_1755300 < baseStart_1755300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755310 : List Nat := [4, 1, 4, 2, 1, 2, 2, 1, 2, 4]
def baseStart_1755310 : Nat := 118140960795 + 1755310 * 2 ^ 59
def prefixEnd_1755310 : Nat := 4983230072969 + 3 ^ 40 * 1755310 * 2
def baseEnd_1755310 : Nat := 300439242547877525084161

theorem tailTrace_1755310 : CollatzResearch.WordTrace tailWord_1755310 prefixEnd_1755310 300439242547877525084161 := by
  unfold tailWord_1755310
  simp only [CollatzResearch.WordTrace]
  refine ⟨8002676908852390990769923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42680943513879418617439589 8002676908852390990769923)
  ·
    refine ⟨12004015363278586486154885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8002676908852390990769923 12004015363278586486154885)
    ·
      refine ⟨2250752880614734966154041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12004015363278586486154885 2250752880614734966154041)
      ·
        refine ⟨1688064660461051224615531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2250752880614734966154041 1688064660461051224615531)
        ·
          refine ⟨2532096990691576836923297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1688064660461051224615531 2532096990691576836923297)
          ·
            refine ⟨1899072743018682627692473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2532096990691576836923297 1899072743018682627692473)
            ·
              refine ⟨1424304557264011970769355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1899072743018682627692473 1424304557264011970769355)
              ·
                refine ⟨2136456835896017956154033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1424304557264011970769355 2136456835896017956154033)
                ·
                  refine ⟨1602342626922013467115525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2136456835896017956154033 1602342626922013467115525)
                  ·
                    refine ⟨300439242547877525084161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1602342626922013467115525 300439242547877525084161)
                    ·
                      rfl

theorem cell23_1755310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_1755310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755310 prefixEnd_1755310 := by exact prefixLift 1755310
  have htrace : WordTrace (prefixWord ++ tailWord_1755310) baseStart_1755310 baseEnd_1755310 := by
    simpa [prefixWord, tailWord_1755310, baseEnd_1755310] using wordTrace_append hprefix tailTrace_1755310
  have hstable : (prefixWord ++ tailWord_1755310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755310).length < 2 ^ (prefixWord ++ tailWord_1755310).sum := by decide
  have hdescent : baseEnd_1755310 < baseStart_1755310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755326 : List Nat := [4, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2]
def baseStart_1755326 : Nat := 118140960795 + 1755326 * 2 ^ 59
def prefixEnd_1755326 : Nat := 4983230072969 + 3 ^ 40 * 1755326 * 2
def baseEnd_1755326 : Nat := 901325943334104512652409

theorem tailTrace_1755326 : CollatzResearch.WordTrace tailWord_1755326 prefixEnd_1755326 901325943334104512652409 := by
  unfold tailWord_1755326
  simp only [CollatzResearch.WordTrace]
  refine ⟨8002749854845145332342729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42681332559174108439161221 8002749854845145332342729)
  ·
    refine ⟨6002062391133858999257047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8002749854845145332342729 6002062391133858999257047)
    ·
      refine ⟨9003093586700788498885571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6002062391133858999257047 9003093586700788498885571)
      ·
        refine ⟨13504640380051182748328357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9003093586700788498885571 13504640380051182748328357)
        ·
          refine ⟨2532120071259596765311567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13504640380051182748328357 2532120071259596765311567)
          ·
            refine ⟨3798180106889395147967351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2532120071259596765311567 3798180106889395147967351)
            ·
              refine ⟨5697270160334092721951027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3798180106889395147967351 5697270160334092721951027)
              ·
                refine ⟨8545905240501139082926541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5697270160334092721951027 8545905240501139082926541)
                ·
                  refine ⟨3204714465187927156097453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8545905240501139082926541 3204714465187927156097453)
                  ·
                    refine ⟨1201767924445472683536545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3204714465187927156097453 1201767924445472683536545)
                    ·
                      refine ⟨901325943334104512652409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1201767924445472683536545 901325943334104512652409)
                      ·
                        rfl

theorem cell23_1755326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_1755326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755326 prefixEnd_1755326 := by exact prefixLift 1755326
  have htrace : WordTrace (prefixWord ++ tailWord_1755326) baseStart_1755326 baseEnd_1755326 := by
    simpa [prefixWord, tailWord_1755326, baseEnd_1755326] using wordTrace_append hprefix tailTrace_1755326
  have hstable : (prefixWord ++ tailWord_1755326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755326).length < 2 ^ (prefixWord ++ tailWord_1755326).sum := by decide
  have hdescent : baseEnd_1755326 < baseStart_1755326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755335 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 4]
def baseStart_1755335 : Nat := 118140960795 + 1755335 * 2 ^ 59
def prefixEnd_1755335 : Nat := 4983230072969 + 3 ^ 40 * 1755335 * 2
def baseEnd_1755335 : Nat := 901330564659994977439867

theorem tailTrace_1755335 : CollatzResearch.WordTrace tailWord_1755335 prefixEnd_1755335 901330564659994977439867 := by
  unfold tailWord_1755335
  simp only [CollatzResearch.WordTrace]
  refine ⟨64022327095728557195819459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42681551397152371463879639 64022327095728557195819459)
  ·
    refine ⟨96033490643592835793729189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64022327095728557195819459 96033490643592835793729189)
    ·
      refine ⟨18006279495673656711324223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96033490643592835793729189 18006279495673656711324223)
      ·
        refine ⟨27009419243510485066986335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18006279495673656711324223 27009419243510485066986335)
        ·
          refine ⟨40514128865265727600479503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27009419243510485066986335 40514128865265727600479503)
          ·
            refine ⟨60771193297898591400719255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40514128865265727600479503 60771193297898591400719255)
            ·
              refine ⟨91156789946847887101078883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60771193297898591400719255 91156789946847887101078883)
              ·
                refine ⟨136735184920271830651618325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91156789946847887101078883 136735184920271830651618325)
                ·
                  refine ⟨6409461793137742061794609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 136735184920271830651618325 6409461793137742061794609)
                  ·
                    refine ⟨4807096344853306546345957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6409461793137742061794609 4807096344853306546345957)
                    ·
                      refine ⟨901330564659994977439867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4807096344853306546345957 901330564659994977439867)
                      ·
                        rfl

theorem cell23_1755335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_1755335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755335 prefixEnd_1755335 := by exact prefixLift 1755335
  have htrace : WordTrace (prefixWord ++ tailWord_1755335) baseStart_1755335 baseEnd_1755335 := by
    simpa [prefixWord, tailWord_1755335, baseEnd_1755335] using wordTrace_append hprefix tailTrace_1755335
  have hstable : (prefixWord ++ tailWord_1755335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755335).length < 2 ^ (prefixWord ++ tailWord_1755335).sum := by decide
  have hdescent : baseEnd_1755335 < baseStart_1755335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755342 : List Nat := [4, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5]
def baseStart_1755342 : Nat := 118140960795 + 1755342 * 2 ^ 59
def prefixEnd_1755342 : Nat := 4983230072969 + 3 ^ 40 * 1755342 * 2
def baseEnd_1755342 : Nat := 901334159024576450052335

theorem tailTrace_1755342 : CollatzResearch.WordTrace tailWord_1755342 prefixEnd_1755342 901334159024576450052335 := by
  unfold tailWord_1755342
  simp only [CollatzResearch.WordTrace]
  refine ⟨8002822800837899673915535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42681721604468798260882853 8002822800837899673915535)
  ·
    refine ⟨12004234201256849510873303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8002822800837899673915535 12004234201256849510873303)
    ·
      refine ⟨18006351301885274266309955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12004234201256849510873303 18006351301885274266309955)
      ·
        refine ⟨27009526952827911399464933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18006351301885274266309955 27009526952827911399464933)
        ·
          refine ⟨5064286303655233387399675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27009526952827911399464933 5064286303655233387399675)
          ·
            refine ⟨7596429455482850081099513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5064286303655233387399675 7596429455482850081099513)
            ·
              refine ⟨5697322091612137560824635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7596429455482850081099513 5697322091612137560824635)
              ·
                refine ⟨8545983137418206341236953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5697322091612137560824635 8545983137418206341236953)
                ·
                  refine ⟨6409487353063654755927715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8545983137418206341236953 6409487353063654755927715)
                  ·
                    refine ⟨9614231029595482133891573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6409487353063654755927715 9614231029595482133891573)
                    ·
                      refine ⟨901334159024576450052335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9614231029595482133891573 901334159024576450052335)
                      ·
                        rfl

theorem cell23_1755342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_1755342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755342 prefixEnd_1755342 := by exact prefixLift 1755342
  have htrace : WordTrace (prefixWord ++ tailWord_1755342) baseStart_1755342 baseEnd_1755342 := by
    simpa [prefixWord, tailWord_1755342, baseEnd_1755342] using wordTrace_append hprefix tailTrace_1755342
  have hstable : (prefixWord ++ tailWord_1755342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755342).length < 2 ^ (prefixWord ++ tailWord_1755342).sum := by decide
  have hdescent : baseEnd_1755342 < baseStart_1755342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755372 : List Nat := [2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 3]
def baseStart_1755372 : Nat := 118140960795 + 1755372 * 2 ^ 59
def prefixEnd_1755372 : Nat := 4983230072969 + 3 ^ 40 * 1755372 * 2
def baseEnd_1755372 : Nat := 901349563444211332677197

theorem tailTrace_1755372 : CollatzResearch.WordTrace tailWord_1755372 prefixEnd_1755372 901349563444211332677197 := by
  unfold tailWord_1755372
  simp only [CollatzResearch.WordTrace]
  refine ⟨32011838298297256257458185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42682451064396341676610913 32011838298297256257458185)
  ·
    refine ⟨24008878723722942193093639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32011838298297256257458185 24008878723722942193093639)
    ·
      refine ⟨36013318085584413289640459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24008878723722942193093639 36013318085584413289640459)
      ·
        refine ⟨54019977128376619934460689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36013318085584413289640459 54019977128376619934460689)
        ·
          refine ⟨40514982846282464950845517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54019977128376619934460689 40514982846282464950845517)
          ·
            refine ⟨15193118567355924356567069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40514982846282464950845517 15193118567355924356567069)
            ·
              refine ⟨5697419462758471633712651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15193118567355924356567069 5697419462758471633712651)
              ·
                refine ⟨8546129194137707450568977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5697419462758471633712651 8546129194137707450568977)
                ·
                  refine ⟨6409596895603280587926733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8546129194137707450568977 6409596895603280587926733)
                  ·
                    refine ⟨2403598835851230220472525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6409596895603280587926733 2403598835851230220472525)
                    ·
                      refine ⟨901349563444211332677197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2403598835851230220472525 901349563444211332677197)
                      ·
                        rfl

theorem cell23_1755372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 3].length) (baseStart_1755372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755372 prefixEnd_1755372 := by exact prefixLift 1755372
  have htrace : WordTrace (prefixWord ++ tailWord_1755372) baseStart_1755372 baseEnd_1755372 := by
    simpa [prefixWord, tailWord_1755372, baseEnd_1755372] using wordTrace_append hprefix tailTrace_1755372
  have hstable : (prefixWord ++ tailWord_1755372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755372).length < 2 ^ (prefixWord ++ tailWord_1755372).sum := by decide
  have hdescent : baseEnd_1755372 < baseStart_1755372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755385 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 3, 2, 5]
def baseStart_1755385 : Nat := 118140960795 + 1755385 * 2 ^ 59
def prefixEnd_1755385 : Nat := 4983230072969 + 3 ^ 40 * 1755385 * 2
def baseEnd_1755385 : Nat := 901356238692719781814637

theorem tailTrace_1755385 : CollatzResearch.WordTrace tailWord_1755385 prefixEnd_1755385 901356238692719781814637 := by
  unfold tailWord_1755385
  simp only [CollatzResearch.WordTrace]
  refine ⟨64024150745547415735139609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42682767163698277156759739 64024150745547415735139609)
  ·
    refine ⟨48018113059160561801354707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64024150745547415735139609 48018113059160561801354707)
    ·
      refine ⟨72027169588740842702032061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48018113059160561801354707 72027169588740842702032061)
      ·
        refine ⟨27010188595777816013262023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72027169588740842702032061 27010188595777816013262023)
        ·
          refine ⟨40515282893666724019893035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27010188595777816013262023 40515282893666724019893035)
          ·
            refine ⟨60772924340500086029839553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40515282893666724019893035 60772924340500086029839553)
            ·
              refine ⟨45579693255375064522379665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60772924340500086029839553 45579693255375064522379665)
              ·
                refine ⟨34184769941531298391784749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45579693255375064522379665 34184769941531298391784749)
                ·
                  refine ⟨12819288728074236896919281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34184769941531298391784749 12819288728074236896919281)
                  ·
                    refine ⟨9614466546055677672689461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12819288728074236896919281 9614466546055677672689461)
                    ·
                      refine ⟨901356238692719781814637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9614466546055677672689461 901356238692719781814637)
                      ·
                        rfl

theorem cell23_1755385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_1755385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755385 prefixEnd_1755385 := by exact prefixLift 1755385
  have htrace : WordTrace (prefixWord ++ tailWord_1755385) baseStart_1755385 baseEnd_1755385 := by
    simpa [prefixWord, tailWord_1755385, baseEnd_1755385] using wordTrace_append hprefix tailTrace_1755385
  have hstable : (prefixWord ++ tailWord_1755385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755385).length < 2 ^ (prefixWord ++ tailWord_1755385).sum := by decide
  have hdescent : baseEnd_1755385 < baseStart_1755385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755392 : List Nat := [2, 1, 1, 2, 1, 1, 7, 1, 2, 5]
def baseStart_1755392 : Nat := 118140960795 + 1755392 * 2 ^ 59
def prefixEnd_1755392 : Nat := 4983230072969 + 3 ^ 40 * 1755392 * 2
def baseEnd_1755392 : Nat := 300453277685767084809035

theorem tailTrace_1755392 : CollatzResearch.WordTrace tailWord_1755392 prefixEnd_1755392 300453277685767084809035 := by
  unfold tailWord_1755392
  simp only [CollatzResearch.WordTrace]
  refine ⟨32012203028261027965322215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42682937371014703953762953 32012203028261027965322215)
  ·
    refine ⟨48018304542391541947983323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32012203028261027965322215 48018304542391541947983323)
    ·
      refine ⟨72027456813587312921974985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48018304542391541947983323 72027456813587312921974985)
      ·
        refine ⟨54020592610190484691481239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72027456813587312921974985 54020592610190484691481239)
        ·
          refine ⟨81030888915285727037221859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54020592610190484691481239 81030888915285727037221859)
          ·
            refine ⟨121546333372928590555832789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81030888915285727037221859 121546333372928590555832789)
            ·
              refine ⟨2848742188428013841152331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 121546333372928590555832789 2848742188428013841152331)
              ·
                refine ⟨4273113282642020761728497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2848742188428013841152331 4273113282642020761728497)
                ·
                  refine ⟨3204834961981515571296373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4273113282642020761728497 3204834961981515571296373)
                  ·
                    refine ⟨300453277685767084809035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3204834961981515571296373 300453277685767084809035)
                    ·
                      rfl

theorem cell23_1755392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 2, 5].length) (baseStart_1755392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755392 prefixEnd_1755392 := by exact prefixLift 1755392
  have htrace : WordTrace (prefixWord ++ tailWord_1755392) baseStart_1755392 baseEnd_1755392 := by
    simpa [prefixWord, tailWord_1755392, baseEnd_1755392] using wordTrace_append hprefix tailTrace_1755392
  have hstable : (prefixWord ++ tailWord_1755392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755392).length < 2 ^ (prefixWord ++ tailWord_1755392).sum := by decide
  have hdescent : baseEnd_1755392 < baseStart_1755392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755396 : List Nat := [2, 3, 2, 2, 3, 1, 2, 3, 5]
def baseStart_1755396 : Nat := 118140960795 + 1755396 * 2 ^ 59
def prefixEnd_1755396 : Nat := 4983230072969 + 3 ^ 40 * 1755396 * 2
def baseEnd_1755396 : Nat := 100151320775546582086343

theorem tailTrace_1755396 : CollatzResearch.WordTrace tailWord_1755396 prefixEnd_1755396 100151320775546582086343 := by
  unfold tailWord_1755396
  simp only [CollatzResearch.WordTrace]
  refine ⟨32012275974253782306895021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42683034632338376409193361 32012275974253782306895021)
  ·
    refine ⟨12004603490345168365085633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32012275974253782306895021 12004603490345168365085633)
    ·
      refine ⟨9003452617758876273814225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12004603490345168365085633 9003452617758876273814225)
      ·
        refine ⟨6752589463319157205360669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9003452617758876273814225 6752589463319157205360669)
        ·
          refine ⟨2532221048744683952010251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6752589463319157205360669 2532221048744683952010251)
          ·
            refine ⟨3798331573117025928015377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2532221048744683952010251 3798331573117025928015377)
            ·
              refine ⟨2848748679837769446011533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3798331573117025928015377 2848748679837769446011533)
              ·
                refine ⟨1068280754939163542254325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2848748679837769446011533 1068280754939163542254325)
                ·
                  refine ⟨100151320775546582086343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1068280754939163542254325 100151320775546582086343)
                  ·
                    rfl

theorem cell23_1755396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 3, 5].length) (baseStart_1755396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755396 prefixEnd_1755396 := by exact prefixLift 1755396
  have htrace : WordTrace (prefixWord ++ tailWord_1755396) baseStart_1755396 baseEnd_1755396 := by
    simpa [prefixWord, tailWord_1755396, baseEnd_1755396] using wordTrace_append hprefix tailTrace_1755396
  have hstable : (prefixWord ++ tailWord_1755396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755396).length < 2 ^ (prefixWord ++ tailWord_1755396).sum := by decide
  have hdescent : baseEnd_1755396 < baseStart_1755396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755449 : List Nat := [1, 2, 1, 6, 1, 1, 2, 1, 1, 4, 3]
def baseStart_1755449 : Nat := 118140960795 + 1755449 * 2 ^ 59
def prefixEnd_1755449 : Nat := 4983230072969 + 3 ^ 40 * 1755449 * 2
def baseEnd_1755449 : Nat := 901389101454607531414343

theorem tailTrace_1755449 : CollatzResearch.WordTrace tailWord_1755449 prefixEnd_1755449 901389101454607531414343 := by
  unfold tailWord_1755449
  simp only [CollatzResearch.WordTrace]
  refine ⟨64026485017315554665469401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42684323344877036443646267 64026485017315554665469401)
  ·
    refine ⟨48019863762986665999102051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64026485017315554665469401 48019863762986665999102051)
    ·
      refine ⟨72029795644479998998653077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48019863762986665999102051 72029795644479998998653077)
      ·
        refine ⟨3376396670834999953061863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 72029795644479998998653077 3376396670834999953061863)
        ·
          refine ⟨5064595006252499929592795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3376396670834999953061863 5064595006252499929592795)
          ·
            refine ⟨7596892509378749894389193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5064595006252499929592795 7596892509378749894389193)
            ·
              refine ⟨5697669382034062420791895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7596892509378749894389193 5697669382034062420791895)
              ·
                refine ⟨8546504073051093631187843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5697669382034062420791895 8546504073051093631187843)
                ·
                  refine ⟨12819756109576640446781765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8546504073051093631187843 12819756109576640446781765)
                  ·
                    refine ⟨2403704270545620083771581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12819756109576640446781765 2403704270545620083771581)
                    ·
                      refine ⟨901389101454607531414343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2403704270545620083771581 901389101454607531414343)
                      ·
                        rfl

theorem cell23_1755449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_1755449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755449 prefixEnd_1755449 := by exact prefixLift 1755449
  have htrace : WordTrace (prefixWord ++ tailWord_1755449) baseStart_1755449 baseEnd_1755449 := by
    simpa [prefixWord, tailWord_1755449, baseEnd_1755449] using wordTrace_append hprefix tailTrace_1755449
  have hstable : (prefixWord ++ tailWord_1755449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755449).length < 2 ^ (prefixWord ++ tailWord_1755449).sum := by decide
  have hdescent : baseEnd_1755449 < baseStart_1755449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755473 : List Nat := [1, 2, 2, 1, 4, 3, 3, 2, 1, 4]
def baseStart_1755473 : Nat := 118140960795 + 1755473 * 2 ^ 59
def prefixEnd_1755473 : Nat := 4983230072969 + 3 ^ 40 * 1755473 * 2
def baseEnd_1755473 : Nat := 300467141663438479171411

theorem tailTrace_1755473 : CollatzResearch.WordTrace tailWord_1755473 prefixEnd_1755473 300467141663438479171411 := by
  unfold tailWord_1755473
  simp only [CollatzResearch.WordTrace]
  refine ⟨64027360369228606764343073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42684906912819071176228715 64027360369228606764343073)
  ·
    refine ⟨48020520276921455073257305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64027360369228606764343073 48020520276921455073257305)
    ·
      refine ⟨36015390207691091304942979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48020520276921455073257305 36015390207691091304942979)
      ·
        refine ⟨54023085311536636957414469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36015390207691091304942979 54023085311536636957414469)
        ·
          refine ⟨10129328495913119429515213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54023085311536636957414469 10129328495913119429515213)
          ·
            refine ⟨3798498185967419786068205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10129328495913119429515213 3798498185967419786068205)
            ·
              refine ⟨1424436819737782419775577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3798498185967419786068205 1424436819737782419775577)
              ·
                refine ⟨1068327614803336814831683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1424436819737782419775577 1068327614803336814831683)
                ·
                  refine ⟨1602491422205005222247525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1068327614803336814831683 1602491422205005222247525)
                  ·
                    refine ⟨300467141663438479171411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1602491422205005222247525 300467141663438479171411)
                    ·
                      rfl

theorem cell23_1755473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 2, 1, 4].length) (baseStart_1755473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755473 prefixEnd_1755473 := by exact prefixLift 1755473
  have htrace : WordTrace (prefixWord ++ tailWord_1755473) baseStart_1755473 baseEnd_1755473 := by
    simpa [prefixWord, tailWord_1755473, baseEnd_1755473] using wordTrace_append hprefix tailTrace_1755473
  have hstable : (prefixWord ++ tailWord_1755473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755473).length < 2 ^ (prefixWord ++ tailWord_1755473).sum := by decide
  have hdescent : baseEnd_1755473 < baseStart_1755473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755482 : List Nat := [3, 1, 1, 2, 1, 2, 1, 4, 3, 5]
def baseStart_1755482 : Nat := 118140960795 + 1755482 * 2 ^ 59
def prefixEnd_1755482 : Nat := 4983230072969 + 3 ^ 40 * 1755482 * 2
def baseEnd_1755482 : Nat := 300468682105401967433897

theorem tailTrace_1755482 : CollatzResearch.WordTrace tailWord_1755482 prefixEnd_1755482 300468682105401967433897 := by
  unfold tailWord_1755482
  simp only [CollatzResearch.WordTrace]
  refine ⟨16006922156549000325355175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42685125750797334200947133 16006922156549000325355175)
  ·
    refine ⟨24010383234823500488032763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16006922156549000325355175 24010383234823500488032763)
    ·
      refine ⟨36015574852235250732049145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24010383234823500488032763 36015574852235250732049145)
      ·
        refine ⟨27011681139176438049036859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36015574852235250732049145 27011681139176438049036859)
        ·
          refine ⟨40517521708764657073555289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27011681139176438049036859 40517521708764657073555289)
          ·
            refine ⟨30388141281573492805166467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40517521708764657073555289 30388141281573492805166467)
            ·
              refine ⟨45582211922360239207749701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30388141281573492805166467 45582211922360239207749701)
              ·
                refine ⟨8546664735442544851453069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45582211922360239207749701 8546664735442544851453069)
                ·
                  refine ⟨3204999275790954319294901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8546664735442544851453069 3204999275790954319294901)
                  ·
                    refine ⟨300468682105401967433897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3204999275790954319294901 300468682105401967433897)
                    ·
                      rfl

theorem cell23_1755482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 3, 5].length) (baseStart_1755482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755482 prefixEnd_1755482 := by exact prefixLift 1755482
  have htrace : WordTrace (prefixWord ++ tailWord_1755482) baseStart_1755482 baseEnd_1755482 := by
    simpa [prefixWord, tailWord_1755482, baseEnd_1755482] using wordTrace_append hprefix tailTrace_1755482
  have hstable : (prefixWord ++ tailWord_1755482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755482).length < 2 ^ (prefixWord ++ tailWord_1755482).sum := by decide
  have hdescent : baseEnd_1755482 < baseStart_1755482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755506 : List Nat := [3, 2, 1, 2, 1, 3, 1, 3, 2, 3, 2]
def baseStart_1755506 : Nat := 118140960795 + 1755506 * 2 ^ 59
def prefixEnd_1755506 : Nat := 4983230072969 + 3 ^ 40 * 1755506 * 2
def baseEnd_1755506 : Nat := 901418369851913808401581

theorem tailTrace_1755506 : CollatzResearch.WordTrace tailWord_1755506 prefixEnd_1755506 901418369851913808401581 := by
  unfold tailWord_1755506
  simp only [CollatzResearch.WordTrace]
  refine ⟨16007140994527263350073593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42685709318739368933529581 16007140994527263350073593)
  ·
    refine ⟨12005355745895447512555195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16007140994527263350073593 12005355745895447512555195)
    ·
      refine ⟨18008033618843171268832793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12005355745895447512555195 18008033618843171268832793)
      ·
        refine ⟨13506025214132378451624595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18008033618843171268832793 13506025214132378451624595)
        ·
          refine ⟨20259037821198567677436893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13506025214132378451624595 20259037821198567677436893)
          ·
            refine ⟨7597139182949462879038835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20259037821198567677436893 7597139182949462879038835)
            ·
              refine ⟨11395708774424194318558253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7597139182949462879038835 11395708774424194318558253)
              ·
                refine ⟨4273390790409072869459345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11395708774424194318558253 4273390790409072869459345)
                ·
                  refine ⟨3205043092806804652094509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4273390790409072869459345 3205043092806804652094509)
                  ·
                    refine ⟨1201891159802551744535441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3205043092806804652094509 1201891159802551744535441)
                    ·
                      refine ⟨901418369851913808401581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1201891159802551744535441 901418369851913808401581)
                      ·
                        rfl

theorem cell23_1755506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_1755506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755506 prefixEnd_1755506 := by exact prefixLift 1755506
  have htrace : WordTrace (prefixWord ++ tailWord_1755506) baseStart_1755506 baseEnd_1755506 := by
    simpa [prefixWord, tailWord_1755506, baseEnd_1755506] using wordTrace_append hprefix tailTrace_1755506
  have hstable : (prefixWord ++ tailWord_1755506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755506).length < 2 ^ (prefixWord ++ tailWord_1755506).sum := by decide
  have hdescent : baseEnd_1755506 < baseStart_1755506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755546 : List Nat := [3, 1, 1, 4, 1, 2, 2, 3, 2, 4]
def baseStart_1755546 : Nat := 118140960795 + 1755546 * 2 ^ 59
def prefixEnd_1755546 : Nat := 4983230072969 + 3 ^ 40 * 1755546 * 2
def baseEnd_1755546 : Nat := 300479636359364550633799

theorem tailTrace_1755546 : CollatzResearch.WordTrace tailWord_1755546 prefixEnd_1755546 300479636359364550633799 := by
  unfold tailWord_1755546
  simp only [CollatzResearch.WordTrace]
  refine ⟨16007505724491035057937623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42686681931976093487833661 16007505724491035057937623)
  ·
    refine ⟨24011258586736552586906435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16007505724491035057937623 24011258586736552586906435)
    ·
      refine ⟨36016887880104828880359653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24011258586736552586906435 36016887880104828880359653)
      ·
        refine ⟨6753166477519655415067435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36016887880104828880359653 6753166477519655415067435)
        ·
          refine ⟨10129749716279483122601153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6753166477519655415067435 10129749716279483122601153)
          ·
            refine ⟨7597312287209612341950865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10129749716279483122601153 7597312287209612341950865)
            ·
              refine ⟨5697984215407209256463149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7597312287209612341950865 5697984215407209256463149)
              ·
                refine ⟨2136744080777703471173681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5697984215407209256463149 2136744080777703471173681)
                ·
                  refine ⟨1602558060583277603380261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2136744080777703471173681 1602558060583277603380261)
                  ·
                    refine ⟨300479636359364550633799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1602558060583277603380261 300479636359364550633799)
                    ·
                      rfl

theorem cell23_1755546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 2, 4].length) (baseStart_1755546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755546 prefixEnd_1755546 := by exact prefixLift 1755546
  have htrace : WordTrace (prefixWord ++ tailWord_1755546) baseStart_1755546 baseEnd_1755546 := by
    simpa [prefixWord, tailWord_1755546, baseEnd_1755546] using wordTrace_append hprefix tailTrace_1755546
  have hstable : (prefixWord ++ tailWord_1755546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755546).length < 2 ^ (prefixWord ++ tailWord_1755546).sum := by decide
  have hdescent : baseEnd_1755546 < baseStart_1755546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755570 : List Nat := [3, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2]
def baseStart_1755570 : Nat := 118140960795 + 1755570 * 2 ^ 59
def prefixEnd_1755570 : Nat := 4983230072969 + 3 ^ 40 * 1755570 * 2
def baseEnd_1755570 : Nat := 901451232613801558001287

theorem tailTrace_1755570 : CollatzResearch.WordTrace tailWord_1755570 prefixEnd_1755570 901451232613801558001287 := by
  unfold tailWord_1755570
  simp only [CollatzResearch.WordTrace]
  refine ⟨16007724562469298082656041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42687265499918128220416109 16007724562469298082656041)
  ·
    refine ⟨12005793421851973561992031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16007724562469298082656041 12005793421851973561992031)
    ·
      refine ⟨18008690132777960342988047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12005793421851973561992031 18008690132777960342988047)
      ·
        refine ⟨27013035199166940514482071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18008690132777960342988047 27013035199166940514482071)
        ·
          refine ⟨40519552798750410771723107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27013035199166940514482071 40519552798750410771723107)
          ·
            refine ⟨60779329198125616157584661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40519552798750410771723107 60779329198125616157584661)
            ·
              refine ⟨2849031056162138257386781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60779329198125616157584661 2849031056162138257386781)
              ·
                refine ⟨1068386646060801846520043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2849031056162138257386781 1068386646060801846520043)
                ·
                  refine ⟨1602579969091202769780065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1068386646060801846520043 1602579969091202769780065)
                  ·
                    refine ⟨1201934976818402077335049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1602579969091202769780065 1201934976818402077335049)
                    ·
                      refine ⟨901451232613801558001287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1201934976818402077335049 901451232613801558001287)
                      ·
                        rfl

theorem cell23_1755570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2].length) (baseStart_1755570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755570 prefixEnd_1755570 := by exact prefixLift 1755570
  have htrace : WordTrace (prefixWord ++ tailWord_1755570) baseStart_1755570 baseEnd_1755570 := by
    simpa [prefixWord, tailWord_1755570, baseEnd_1755570] using wordTrace_append hprefix tailTrace_1755570
  have hstable : (prefixWord ++ tailWord_1755570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755570).length < 2 ^ (prefixWord ++ tailWord_1755570).sum := by decide
  have hdescent : baseEnd_1755570 < baseStart_1755570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755573 : List Nat := [1, 3, 3, 2, 3, 1, 1, 3, 1, 2, 3]
def baseStart_1755573 : Nat := 118140960795 + 1755573 * 2 ^ 59
def prefixEnd_1755573 : Nat := 4983230072969 + 3 ^ 40 * 1755573 * 2
def baseEnd_1755573 : Nat := 901452773055765046263773

theorem tailTrace_1755573 : CollatzResearch.WordTrace tailWord_1755573 prefixEnd_1755573 901452773055765046263773 := by
  unfold tailWord_1755573
  simp only [CollatzResearch.WordTrace]
  refine ⟨64031007668866323842983373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42687338445910882561988915 64031007668866323842983373)
  ·
    refine ⟨24011627875824871441118765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64031007668866323842983373 24011627875824871441118765)
    ·
      refine ⟨9004360453434326790419537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24011627875824871441118765 9004360453434326790419537)
      ·
        refine ⟨6753270340075745092814653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9004360453434326790419537 6753270340075745092814653)
        ·
          refine ⟨2532476377528404409805495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6753270340075745092814653 2532476377528404409805495)
          ·
            refine ⟨3798714566292606614708243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2532476377528404409805495 3798714566292606614708243)
            ·
              refine ⟨5698071849438909922062365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3798714566292606614708243 5698071849438909922062365)
              ·
                refine ⟨2136776943539591220773387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5698071849438909922062365 2136776943539591220773387)
                ·
                  refine ⟨3205165415309386831160081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2136776943539591220773387 3205165415309386831160081)
                  ·
                    refine ⟨2403874061482040123370061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3205165415309386831160081 2403874061482040123370061)
                    ·
                      refine ⟨901452773055765046263773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2403874061482040123370061 901452773055765046263773)
                      ·
                        rfl

theorem cell23_1755573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_1755573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755573 prefixEnd_1755573 := by exact prefixLift 1755573
  have htrace : WordTrace (prefixWord ++ tailWord_1755573) baseStart_1755573 baseEnd_1755573 := by
    simpa [prefixWord, tailWord_1755573, baseEnd_1755573] using wordTrace_append hprefix tailTrace_1755573
  have hstable : (prefixWord ++ tailWord_1755573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755573).length < 2 ^ (prefixWord ++ tailWord_1755573).sum := by decide
  have hdescent : baseEnd_1755573 < baseStart_1755573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755654 : List Nat := [6, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_1755654 : Nat := 118140960795 + 1755654 * 2 ^ 59
def prefixEnd_1755654 : Nat := 4983230072969 + 3 ^ 40 * 1755654 * 2
def baseEnd_1755654 : Nat := 901494364988779229350901

theorem tailTrace_1755654 : CollatzResearch.WordTrace tailWord_1755654 prefixEnd_1755654 901494364988779229350901 := by
  unfold tailWord_1755654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2001061311924152333646313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42689307987715249784454677 2001061311924152333646313)
  ·
    refine ⟨1500795983943114250234735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2001061311924152333646313 1500795983943114250234735)
    ·
      refine ⟨2251193975914671375352103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1500795983943114250234735 2251193975914671375352103)
      ·
        refine ⟨3376790963872007063028155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2251193975914671375352103 3376790963872007063028155)
        ·
          refine ⟨5065186445808010594542233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3376790963872007063028155 5065186445808010594542233)
          ·
            refine ⟨3798889834356007945906675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5065186445808010594542233 3798889834356007945906675)
            ·
              refine ⟨5698334751534011918860013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3798889834356007945906675 5698334751534011918860013)
              ·
                refine ⟨2136875531825254469572505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5698334751534011918860013 2136875531825254469572505)
                ·
                  refine ⟨1602656648868940852179379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2136875531825254469572505 1602656648868940852179379)
                  ·
                    refine ⟨2403984973303411278269069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1602656648868940852179379 2403984973303411278269069)
                    ·
                      refine ⟨901494364988779229350901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2403984973303411278269069 901494364988779229350901)
                      ·
                        rfl

theorem cell23_1755654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_1755654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755654 prefixEnd_1755654 := by exact prefixLift 1755654
  have htrace : WordTrace (prefixWord ++ tailWord_1755654) baseStart_1755654 baseEnd_1755654 := by
    simpa [prefixWord, tailWord_1755654, baseEnd_1755654] using wordTrace_append hprefix tailTrace_1755654
  have hstable : (prefixWord ++ tailWord_1755654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755654).length < 2 ^ (prefixWord ++ tailWord_1755654).sum := by decide
  have hdescent : baseEnd_1755654 < baseStart_1755654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755660 : List Nat := [2, 2, 1, 2, 4, 2, 1, 3, 2, 2, 2]
def baseStart_1755660 : Nat := 118140960795 + 1755660 * 2 ^ 59
def prefixEnd_1755660 : Nat := 4983230072969 + 3 ^ 40 * 1755660 * 2
def baseEnd_1755660 : Nat := 901497445872706205875873

theorem tailTrace_1755660 : CollatzResearch.WordTrace tailWord_1755660 prefixEnd_1755660 901497445872706205875873 := by
  unfold tailWord_1755660
  simp only [CollatzResearch.WordTrace]
  refine ⟨32017090409775568850700217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42689453879700758467600289 32017090409775568850700217)
  ·
    refine ⟨24012817807331676638025163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32017090409775568850700217 24012817807331676638025163)
    ·
      refine ⟨36019226710997514957037745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24012817807331676638025163 36019226710997514957037745)
      ·
        refine ⟨27014420033248136217778309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36019226710997514957037745 27014420033248136217778309)
        ·
          refine ⟨5065203756234025540833433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27014420033248136217778309 5065203756234025540833433)
          ·
            refine ⟨3798902817175519155625075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5065203756234025540833433 3798902817175519155625075)
            ·
              refine ⟨5698354225763278733437613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3798902817175519155625075 5698354225763278733437613)
              ·
                refine ⟨2136882834661229525039105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5698354225763278733437613 2136882834661229525039105)
                ·
                  refine ⟨1602662125995922143779329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2136882834661229525039105 1602662125995922143779329)
                  ·
                    refine ⟨1201996594496941607834497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1602662125995922143779329 1201996594496941607834497)
                    ·
                      refine ⟨901497445872706205875873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1201996594496941607834497 901497445872706205875873)
                      ·
                        rfl

theorem cell23_1755660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 2, 2, 2].length) (baseStart_1755660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755660 prefixEnd_1755660 := by exact prefixLift 1755660
  have htrace : WordTrace (prefixWord ++ tailWord_1755660) baseStart_1755660 baseEnd_1755660 := by
    simpa [prefixWord, tailWord_1755660, baseEnd_1755660] using wordTrace_append hprefix tailTrace_1755660
  have hstable : (prefixWord ++ tailWord_1755660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755660).length < 2 ^ (prefixWord ++ tailWord_1755660).sum := by decide
  have hdescent : baseEnd_1755660 < baseStart_1755660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755710 : List Nat := [4, 2, 1, 4, 1, 1, 1, 1, 2, 3, 3]
def baseStart_1755710 : Nat := 118140960795 + 1755710 * 2 ^ 59
def prefixEnd_1755710 : Nat := 4983230072969 + 3 ^ 40 * 1755710 * 2
def baseEnd_1755710 : Nat := 901523119905431010250643

theorem tailTrace_1755710 : CollatzResearch.WordTrace tailWord_1755710 prefixEnd_1755710 901523119905431010250643 := by
  unfold tailWord_1755710
  simp only [CollatzResearch.WordTrace]
  refine ⟨8004500558671249530090073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42690669646246664160480389 8004500558671249530090073)
  ·
    refine ⟨6003375419003437147567555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8004500558671249530090073 6003375419003437147567555)
    ·
      refine ⟨9005063128505155721351333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6003375419003437147567555 9005063128505155721351333)
      ·
        refine ⟨1688449336594716697753375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9005063128505155721351333 1688449336594716697753375)
        ·
          refine ⟨2532674004892075046630063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1688449336594716697753375 2532674004892075046630063)
          ·
            refine ⟨3799011007338112569945095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2532674004892075046630063 3799011007338112569945095)
            ·
              refine ⟨5698516511007168854917643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3799011007338112569945095 5698516511007168854917643)
              ·
                refine ⟨8547774766510753282376465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5698516511007168854917643 8547774766510753282376465)
                ·
                  refine ⟨6410831074883064961782349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8547774766510753282376465 6410831074883064961782349)
                  ·
                    refine ⟨2404061653081149360668381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6410831074883064961782349 2404061653081149360668381)
                    ·
                      refine ⟨901523119905431010250643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2404061653081149360668381 901523119905431010250643)
                      ·
                        rfl

theorem cell23_1755710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_1755710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755710 prefixEnd_1755710 := by exact prefixLift 1755710
  have htrace : WordTrace (prefixWord ++ tailWord_1755710) baseStart_1755710 baseEnd_1755710 := by
    simpa [prefixWord, tailWord_1755710, baseEnd_1755710] using wordTrace_append hprefix tailTrace_1755710
  have hstable : (prefixWord ++ tailWord_1755710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755710).length < 2 ^ (prefixWord ++ tailWord_1755710).sum := by decide
  have hdescent : baseEnd_1755710 < baseStart_1755710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755726 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 5, 4]
def baseStart_1755726 : Nat := 118140960795 + 1755726 * 2 ^ 59
def prefixEnd_1755726 : Nat := 4983230072969 + 3 ^ 40 * 1755726 * 2
def baseEnd_1755726 : Nat := 300510445198634315883523

theorem tailTrace_1755726 : CollatzResearch.WordTrace tailWord_1755726 prefixEnd_1755726 300510445198634315883523 := by
  unfold tailWord_1755726
  simp only [CollatzResearch.WordTrace]
  refine ⟨8004573504664003871662879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42691058691541353982202021 8004573504664003871662879)
  ·
    refine ⟨12006860256996005807494319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8004573504664003871662879 12006860256996005807494319)
    ·
      refine ⟨18010290385494008711241479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12006860256996005807494319 18010290385494008711241479)
      ·
        refine ⟨27015435578241013066862219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18010290385494008711241479 27015435578241013066862219)
        ·
          refine ⟨40523153367361519600293329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27015435578241013066862219 40523153367361519600293329)
          ·
            refine ⟨30392365025521139700219997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40523153367361519600293329 30392365025521139700219997)
            ·
              refine ⟨11397136884570427387582499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30392365025521139700219997 11397136884570427387582499)
              ·
                refine ⟨17095705326855641081373749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11397136884570427387582499 17095705326855641081373749)
                ·
                  refine ⟨1602722374392716351378789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17095705326855641081373749 1602722374392716351378789)
                  ·
                    refine ⟨300510445198634315883523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1602722374392716351378789 300510445198634315883523)
                    ·
                      rfl

theorem cell23_1755726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_1755726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755726 prefixEnd_1755726 := by exact prefixLift 1755726
  have htrace : WordTrace (prefixWord ++ tailWord_1755726) baseStart_1755726 baseEnd_1755726 := by
    simpa [prefixWord, tailWord_1755726, baseEnd_1755726] using wordTrace_append hprefix tailTrace_1755726
  have hstable : (prefixWord ++ tailWord_1755726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755726).length < 2 ^ (prefixWord ++ tailWord_1755726).sum := by decide
  have hdescent : baseEnd_1755726 < baseStart_1755726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755756 : List Nat := [2, 2, 1, 1, 3, 1, 5, 2, 6]
def baseStart_1755756 : Nat := 118140960795 + 1755756 * 2 ^ 59
def prefixEnd_1755756 : Nat := 4983230072969 + 3 ^ 40 * 1755756 * 2
def baseEnd_1755756 : Nat := 100171860001726425586159

theorem tailTrace_1755756 : CollatzResearch.WordTrace tailWord_1755756 prefixEnd_1755756 100171860001726425586159 := by
  unfold tailWord_1755756
  simp only [CollatzResearch.WordTrace]
  refine ⟨32018841113601673048447561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42691788151468897397930081 32018841113601673048447561)
  ·
    refine ⟨24014130835201254786335671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32018841113601673048447561 24014130835201254786335671)
    ·
      refine ⟨36021196252801882179503507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24014130835201254786335671 36021196252801882179503507)
      ·
        refine ⟨54031794379202823269255261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36021196252801882179503507 54031794379202823269255261)
        ·
          refine ⟨20261922892201058725970723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54031794379202823269255261 20261922892201058725970723)
          ·
            refine ⟨30392884338301588088956085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20261922892201058725970723 30392884338301588088956085)
            ·
              refine ⟨2849332906715773883339633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30392884338301588088956085 2849332906715773883339633)
              ·
                refine ⟨2136999680036830412504725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2849332906715773883339633 2136999680036830412504725)
                ·
                  refine ⟨100171860001726425586159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2136999680036830412504725 100171860001726425586159)
                  ·
                    rfl

theorem cell23_1755756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 6].length) (baseStart_1755756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755756 prefixEnd_1755756 := by exact prefixLift 1755756
  have htrace : WordTrace (prefixWord ++ tailWord_1755756) baseStart_1755756 baseEnd_1755756 := by
    simpa [prefixWord, tailWord_1755756, baseEnd_1755756] using wordTrace_append hprefix tailTrace_1755756
  have hstable : (prefixWord ++ tailWord_1755756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755756).length < 2 ^ (prefixWord ++ tailWord_1755756).sum := by decide
  have hdescent : baseEnd_1755756 < baseStart_1755756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755759 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 6]
def baseStart_1755759 : Nat := 118140960795 + 1755759 * 2 ^ 59
def prefixEnd_1755759 : Nat := 4983230072969 + 3 ^ 40 * 1755759 * 2
def baseEnd_1755759 : Nat := 901548280457501318537917

theorem tailTrace_1755759 : CollatzResearch.WordTrace tailWord_1755759 prefixEnd_1755759 901548280457501318537917 := by
  unfold tailWord_1755759
  simp only [CollatzResearch.WordTrace]
  refine ⟨64037791646192477609254331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42691861097461651739502887 64037791646192477609254331)
  ·
    refine ⟨96056687469288716413881497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64037791646192477609254331 96056687469288716413881497)
    ·
      refine ⟨72042515601966537310411123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96056687469288716413881497 72042515601966537310411123)
      ·
        refine ⟨108063773402949805965616685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72042515601966537310411123 108063773402949805965616685)
        ·
          refine ⟨40523915026106177237106257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108063773402949805965616685 40523915026106177237106257)
          ·
            refine ⟨30392936269579632927829693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40523915026106177237106257 30392936269579632927829693)
            ·
              refine ⟨11397351101092362347936135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30392936269579632927829693 11397351101092362347936135)
              ·
                refine ⟨17096026651638543521904203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11397351101092362347936135 17096026651638543521904203)
                ·
                  refine ⟨25644039977457815282856305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17096026651638543521904203 25644039977457815282856305)
                  ·
                    refine ⟨19233029983093361462142229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25644039977457815282856305 19233029983093361462142229)
                    ·
                      refine ⟨901548280457501318537917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19233029983093361462142229 901548280457501318537917)
                      ·
                        rfl

theorem cell23_1755759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 6].length) (baseStart_1755759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755759 prefixEnd_1755759 := by exact prefixLift 1755759
  have htrace : WordTrace (prefixWord ++ tailWord_1755759) baseStart_1755759 baseEnd_1755759 := by
    simpa [prefixWord, tailWord_1755759, baseEnd_1755759] using wordTrace_append hprefix tailTrace_1755759
  have hstable : (prefixWord ++ tailWord_1755759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755759).length < 2 ^ (prefixWord ++ tailWord_1755759).sum := by decide
  have hdescent : baseEnd_1755759 < baseStart_1755759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755779 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 7]
def baseStart_1755779 : Nat := 118140960795 + 1755779 * 2 ^ 59
def prefixEnd_1755779 : Nat := 4983230072969 + 3 ^ 40 * 1755779 * 2
def baseEnd_1755779 : Nat := 901558550070591240287825

theorem tailTrace_1755779 : CollatzResearch.WordTrace tailWord_1755779 prefixEnd_1755779 901558550070591240287825 := by
  unfold tailWord_1755779
  simp only [CollatzResearch.WordTrace]
  refine ⟨64038521106120021024982391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42692347404080014016654927 64038521106120021024982391)
  ·
    refine ⟨96057781659180031537473587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64038521106120021024982391 96057781659180031537473587)
    ·
      refine ⟨144086672488770047306210381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96057781659180031537473587 144086672488770047306210381)
      ·
        refine ⟨54032502183288767739828893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144086672488770047306210381 54032502183288767739828893)
        ·
          refine ⟨20262188318733287902435835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54032502183288767739828893 20262188318733287902435835)
          ·
            refine ⟨30393282478099931853653753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20262188318733287902435835 30393282478099931853653753)
            ·
              refine ⟨22794961858574948890240315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30393282478099931853653753 22794961858574948890240315)
              ·
                refine ⟨34192442787862423335360473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22794961858574948890240315 34192442787862423335360473)
                ·
                  refine ⟨25644332090896817501520355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34192442787862423335360473 25644332090896817501520355)
                  ·
                    refine ⟨38466498136345226252280533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25644332090896817501520355 38466498136345226252280533)
                    ·
                      refine ⟨901558550070591240287825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 38466498136345226252280533 901558550070591240287825)
                      ·
                        rfl

theorem cell23_1755779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_1755779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755779 prefixEnd_1755779 := by exact prefixLift 1755779
  have htrace : WordTrace (prefixWord ++ tailWord_1755779) baseStart_1755779 baseEnd_1755779 := by
    simpa [prefixWord, tailWord_1755779, baseEnd_1755779] using wordTrace_append hprefix tailTrace_1755779
  have hstable : (prefixWord ++ tailWord_1755779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755779).length < 2 ^ (prefixWord ++ tailWord_1755779).sum := by decide
  have hdescent : baseEnd_1755779 < baseStart_1755779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755783 : List Nat := [1, 1, 4, 2, 1, 2, 1, 4, 3, 1, 3]
def baseStart_1755783 : Nat := 118140960795 + 1755783 * 2 ^ 59
def prefixEnd_1755783 : Nat := 4983230072969 + 3 ^ 40 * 1755783 * 2
def baseEnd_1755783 : Nat := 901560603993209224637807

theorem tailTrace_1755783 : CollatzResearch.WordTrace tailWord_1755783 prefixEnd_1755783 901560603993209224637807 := by
  unfold tailWord_1755783
  simp only [CollatzResearch.WordTrace]
  refine ⟨64038666998105529708128003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42692444665403686472085335 64038666998105529708128003)
  ·
    refine ⟨96058000497158294562192005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64038666998105529708128003 96058000497158294562192005)
    ·
      refine ⟨18010875093217180230411001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96058000497158294562192005 18010875093217180230411001)
      ·
        refine ⟨13508156319912885172808251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18010875093217180230411001 13508156319912885172808251)
        ·
          refine ⟨20262234479869327759212377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13508156319912885172808251 20262234479869327759212377)
          ·
            refine ⟨15196675859901995819409283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20262234479869327759212377 15196675859901995819409283)
            ·
              refine ⟨22795013789852993729113925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15196675859901995819409283 22795013789852993729113925)
              ·
                refine ⟨4274065085597436324208861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22795013789852993729113925 4274065085597436324208861)
                ·
                  refine ⟨1602774407099038621578323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4274065085597436324208861 1602774407099038621578323)
                  ·
                    refine ⟨2404161610648557932367485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1602774407099038621578323 2404161610648557932367485)
                    ·
                      refine ⟨901560603993209224637807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2404161610648557932367485 901560603993209224637807)
                      ·
                        rfl

theorem cell23_1755783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_1755783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755783 prefixEnd_1755783 := by exact prefixLift 1755783
  have htrace : WordTrace (prefixWord ++ tailWord_1755783) baseStart_1755783 baseEnd_1755783 := by
    simpa [prefixWord, tailWord_1755783, baseEnd_1755783] using wordTrace_append hprefix tailTrace_1755783
  have hstable : (prefixWord ++ tailWord_1755783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755783).length < 2 ^ (prefixWord ++ tailWord_1755783).sum := by decide
  have hdescent : baseEnd_1755783 < baseStart_1755783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755826 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3]
def baseStart_1755826 : Nat := 118140960795 + 1755826 * 2 ^ 59
def prefixEnd_1755826 : Nat := 4983230072969 + 3 ^ 40 * 1755826 * 2
def baseEnd_1755826 : Nat := 901582683661352556400109

theorem tailTrace_1755826 : CollatzResearch.WordTrace tailWord_1755826 prefixEnd_1755826 901582683661352556400109 := by
  unfold tailWord_1755826
  simp only [CollatzResearch.WordTrace]
  refine ⟨16010058834237437012985833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42693490224633165367962221 16010058834237437012985833)
  ·
    refine ⟨12007544125678077759739375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16010058834237437012985833 12007544125678077759739375)
    ·
      refine ⟨18011316188517116639609063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12007544125678077759739375 18011316188517116639609063)
      ·
        refine ⟨27016974282775674959413595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18011316188517116639609063 27016974282775674959413595)
        ·
          refine ⟨40525461424163512439120393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27016974282775674959413595 40525461424163512439120393)
          ·
            refine ⟨30394096068122634329340295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40525461424163512439120393 30394096068122634329340295)
            ·
              refine ⟨45591144102183951494010443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30394096068122634329340295 45591144102183951494010443)
              ·
                refine ⟨68386716153275927241015665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45591144102183951494010443 68386716153275927241015665)
                ·
                  refine ⟨51290037114956945430761749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68386716153275927241015665 51290037114956945430761749)
                  ·
                    refine ⟨2404220489763606817066957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51290037114956945430761749 2404220489763606817066957)
                    ·
                      refine ⟨901582683661352556400109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2404220489763606817066957 901582683661352556400109)
                      ·
                        rfl

theorem cell23_1755826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_1755826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755826 prefixEnd_1755826 := by exact prefixLift 1755826
  have htrace : WordTrace (prefixWord ++ tailWord_1755826) baseStart_1755826 baseEnd_1755826 := by
    simpa [prefixWord, tailWord_1755826, baseEnd_1755826] using wordTrace_append hprefix tailTrace_1755826
  have hstable : (prefixWord ++ tailWord_1755826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755826).length < 2 ^ (prefixWord ++ tailWord_1755826).sum := by decide
  have hdescent : baseEnd_1755826 < baseStart_1755826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755836 : List Nat := [2, 2, 2, 3, 1, 1, 1, 3, 1, 1, 6]
def baseStart_1755836 : Nat := 118140960795 + 1755836 * 2 ^ 59
def prefixEnd_1755836 : Nat := 4983230072969 + 3 ^ 40 * 1755836 * 2
def baseEnd_1755836 : Nat := 901587818467897517275063

theorem tailTrace_1755836 : CollatzResearch.WordTrace tailWord_1755836 prefixEnd_1755836 901587818467897517275063 := by
  unfold tailWord_1755836
  simp only [CollatzResearch.WordTrace]
  refine ⟨32020300033456759879903681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42693733377942346506538241 32020300033456759879903681)
  ·
    refine ⟨24015225025092569909927761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32020300033456759879903681 24015225025092569909927761)
    ·
      refine ⟨18011418768819427432445821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24015225025092569909927761 18011418768819427432445821)
      ·
        refine ⟨6754282038307285287167183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18011418768819427432445821 6754282038307285287167183)
        ·
          refine ⟨10131423057460927930750775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6754282038307285287167183 10131423057460927930750775)
          ·
            refine ⟨15197134586191391896126163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10131423057460927930750775 15197134586191391896126163)
            ·
              refine ⟨22795701879287087844189245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15197134586191391896126163 22795701879287087844189245)
              ·
                refine ⟨8548388204732657941570967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22795701879287087844189245 8548388204732657941570967)
                ·
                  refine ⟨12822582307098986912356451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8548388204732657941570967 12822582307098986912356451)
                  ·
                    refine ⟨19233873460648480368534677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12822582307098986912356451 19233873460648480368534677)
                    ·
                      refine ⟨901587818467897517275063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19233873460648480368534677 901587818467897517275063)
                      ·
                        rfl

theorem cell23_1755836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_1755836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755836 prefixEnd_1755836 := by exact prefixLift 1755836
  have htrace : WordTrace (prefixWord ++ tailWord_1755836) baseStart_1755836 baseEnd_1755836 := by
    simpa [prefixWord, tailWord_1755836, baseEnd_1755836] using wordTrace_append hprefix tailTrace_1755836
  have hstable : (prefixWord ++ tailWord_1755836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755836).length < 2 ^ (prefixWord ++ tailWord_1755836).sum := by decide
  have hdescent : baseEnd_1755836 < baseStart_1755836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755840 : List Nat := [2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 4]
def baseStart_1755840 : Nat := 118140960795 + 1755840 * 2 ^ 59
def prefixEnd_1755840 : Nat := 4983230072969 + 3 ^ 40 * 1755840 * 2
def baseEnd_1755840 : Nat := 901589872390515501625045

theorem tailTrace_1755840 : CollatzResearch.WordTrace tailWord_1755840 prefixEnd_1755840 901589872390515501625045 := by
  unfold tailWord_1755840
  simp only [CollatzResearch.WordTrace]
  refine ⟨32020372979449514221476487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42693830639266018961968649 32020372979449514221476487)
  ·
    refine ⟨48030559469174271332214731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32020372979449514221476487 48030559469174271332214731)
    ·
      refine ⟨72045839203761406998322097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48030559469174271332214731 72045839203761406998322097)
      ·
        refine ⟨54034379402821055248741573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72045839203761406998322097 54034379402821055248741573)
        ·
          refine ⟨10131446138028947859139045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54034379402821055248741573 10131446138028947859139045)
          ·
            refine ⟨1899646150880427723588571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10131446138028947859139045 1899646150880427723588571)
            ·
              refine ⟨2849469226320641585382857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1899646150880427723588571 2849469226320641585382857)
              ·
                refine ⟨2137101919740481189037143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2849469226320641585382857 2137101919740481189037143)
                ·
                  refine ⟨3205652879610721783555715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2137101919740481189037143 3205652879610721783555715)
                  ·
                    refine ⟨4808479319416082675333573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3205652879610721783555715 4808479319416082675333573)
                    ·
                      refine ⟨901589872390515501625045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4808479319416082675333573 901589872390515501625045)
                      ·
                        rfl

theorem cell23_1755840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 4].length) (baseStart_1755840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755840 prefixEnd_1755840 := by exact prefixLift 1755840
  have htrace : WordTrace (prefixWord ++ tailWord_1755840) baseStart_1755840 baseEnd_1755840 := by
    simpa [prefixWord, tailWord_1755840, baseEnd_1755840] using wordTrace_append hprefix tailTrace_1755840
  have hstable : (prefixWord ++ tailWord_1755840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755840).length < 2 ^ (prefixWord ++ tailWord_1755840).sum := by decide
  have hdescent : baseEnd_1755840 < baseStart_1755840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755857 : List Nat := [1, 2, 2, 1, 2, 3, 2, 5, 1, 2, 2]
def baseStart_1755857 : Nat := 118140960795 + 1755857 * 2 ^ 59
def prefixEnd_1755857 : Nat := 4983230072969 + 3 ^ 40 * 1755857 * 2
def baseEnd_1755857 : Nat := 901598601561641935112467

theorem tailTrace_1755857 : CollatzResearch.WordTrace tailWord_1755857 prefixEnd_1755857 901598601561641935112467 := by
  unfold tailWord_1755857
  simp only [CollatzResearch.WordTrace]
  refine ⟨64041365999837440346321825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42694243999891626897547883 64041365999837440346321825)
  ·
    refine ⟨48031024499878080259741369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64041365999837440346321825 48031024499878080259741369)
    ·
      refine ⟨36023268374908560194806027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48031024499878080259741369 36023268374908560194806027)
      ·
        refine ⟨54034902562362840292209041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36023268374908560194806027 54034902562362840292209041)
        ·
          refine ⟨40526176921772130219156781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54034902562362840292209041 40526176921772130219156781)
          ·
            refine ⟨15197316345664548832183793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40526176921772130219156781 15197316345664548832183793)
            ·
              refine ⟨11397987259248411624137845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15197316345664548832183793 11397987259248411624137845)
              ·
                refine ⟨1068561305554538589762923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11397987259248411624137845 1068561305554538589762923)
                ·
                  refine ⟨1602841958331807884644385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1068561305554538589762923 1602841958331807884644385)
                  ·
                    refine ⟨1202131468748855913483289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1602841958331807884644385 1202131468748855913483289)
                    ·
                      refine ⟨901598601561641935112467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1202131468748855913483289 901598601561641935112467)
                      ·
                        rfl

theorem cell23_1755857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 5, 1, 2, 2].length) (baseStart_1755857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755857 prefixEnd_1755857 := by exact prefixLift 1755857
  have htrace : WordTrace (prefixWord ++ tailWord_1755857) baseStart_1755857 baseEnd_1755857 := by
    simpa [prefixWord, tailWord_1755857, baseEnd_1755857] using wordTrace_append hprefix tailTrace_1755857
  have hstable : (prefixWord ++ tailWord_1755857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755857).length < 2 ^ (prefixWord ++ tailWord_1755857).sum := by decide
  have hdescent : baseEnd_1755857 < baseStart_1755857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755876 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 2, 7]
def baseStart_1755876 : Nat := 118140960795 + 1755876 * 2 ^ 59
def prefixEnd_1755876 : Nat := 4983230072969 + 3 ^ 40 * 1755876 * 2
def baseEnd_1755876 : Nat := 300536119231359120258293

theorem tailTrace_1755876 : CollatzResearch.WordTrace tailWord_1755876 prefixEnd_1755876 300536119231359120258293 := by
  unfold tailWord_1755876
  simp only [CollatzResearch.WordTrace]
  refine ⟨32021029493384303295631741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42694705991179071060842321 32021029493384303295631741)
  ·
    refine ⟨12007886060019113735861903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32021029493384303295631741 12007886060019113735861903)
    ·
      refine ⟨18011829090028670603792855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12007886060019113735861903 18011829090028670603792855)
      ·
        refine ⟨27017743635043005905689283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18011829090028670603792855 27017743635043005905689283)
        ·
          refine ⟨40526615452564508858533925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27017743635043005905689283 40526615452564508858533925)
          ·
            refine ⟨7598740397355845410975111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40526615452564508858533925 7598740397355845410975111)
            ·
              refine ⟨11398110596033768116462667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7598740397355845410975111 11398110596033768116462667)
              ·
                refine ⟨17097165894050652174694001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11398110596033768116462667 17097165894050652174694001)
                ·
                  refine ⟨12822874420537989131020501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17097165894050652174694001 12822874420537989131020501)
                  ·
                    refine ⟨300536119231359120258293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12822874420537989131020501 300536119231359120258293)
                    ·
                      rfl

theorem cell23_1755876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_1755876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755876 prefixEnd_1755876 := by exact prefixLift 1755876
  have htrace : WordTrace (prefixWord ++ tailWord_1755876) baseStart_1755876 baseEnd_1755876 := by
    simpa [prefixWord, tailWord_1755876, baseEnd_1755876] using wordTrace_append hprefix tailTrace_1755876
  have hstable : (prefixWord ++ tailWord_1755876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755876).length < 2 ^ (prefixWord ++ tailWord_1755876).sum := by decide
  have hdescent : baseEnd_1755876 < baseStart_1755876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755880 : List Nat := [2, 1, 4, 1, 5, 1, 1, 8]
def baseStart_1755880 : Nat := 118140960795 + 1755880 * 2 ^ 59
def prefixEnd_1755880 : Nat := 4983230072969 + 3 ^ 40 * 1755880 * 2
def baseEnd_1755880 : Nat := 33392978208025753523143

theorem tailTrace_1755880 : CollatzResearch.WordTrace tailWord_1755880 prefixEnd_1755880 33392978208025753523143 := by
  unfold tailWord_1755880
  simp only [CollatzResearch.WordTrace]
  refine ⟨32021102439377057637204547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42694803252502743516272729 32021102439377057637204547)
  ·
    refine ⟨48031653659065586455806821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32021102439377057637204547 48031653659065586455806821)
    ·
      refine ⟨9005935061074797460463779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48031653659065586455806821 9005935061074797460463779)
      ·
        refine ⟨13508902591612196190695669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9005935061074797460463779 13508902591612196190695669)
        ·
          refine ⟨1266459617963643392877719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13508902591612196190695669 1266459617963643392877719)
          ·
            refine ⟨1899689426945465089316579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1266459617963643392877719 1899689426945465089316579)
            ·
              refine ⟨2849534140418197633974869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1899689426945465089316579 2849534140418197633974869)
              ·
                refine ⟨33392978208025753523143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2849534140418197633974869 33392978208025753523143)
                ·
                  rfl

theorem cell23_1755880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 8].length) (baseStart_1755880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755880 prefixEnd_1755880 := by exact prefixLift 1755880
  have htrace : WordTrace (prefixWord ++ tailWord_1755880) baseStart_1755880 baseEnd_1755880 := by
    simpa [prefixWord, tailWord_1755880, baseEnd_1755880] using wordTrace_append hprefix tailTrace_1755880
  have hstable : (prefixWord ++ tailWord_1755880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755880).length < 2 ^ (prefixWord ++ tailWord_1755880).sum := by decide
  have hdescent : baseEnd_1755880 < baseStart_1755880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755890 : List Nat := [3, 2, 1, 3, 1, 3, 2, 1, 1, 3, 3]
def baseStart_1755890 : Nat := 118140960795 + 1755890 * 2 ^ 59
def prefixEnd_1755890 : Nat := 4983230072969 + 3 ^ 40 * 1755890 * 2
def baseEnd_1755890 : Nat := 901615546423240305999815

theorem tailTrace_1755890 : CollatzResearch.WordTrace tailWord_1755890 prefixEnd_1755890 901615546423240305999815 := by
  unfold tailWord_1755890
  simp only [CollatzResearch.WordTrace]
  refine ⟨16010642402179471745568281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42695046405811924654848749 16010642402179471745568281)
  ·
    refine ⟨12007981801634603809176211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16010642402179471745568281 12007981801634603809176211)
    ·
      refine ⟨18011972702451905713764317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12007981801634603809176211 18011972702451905713764317)
      ·
        refine ⟨6754489763419464642661619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18011972702451905713764317 6754489763419464642661619)
        ·
          refine ⟨10131734645129196963992429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6754489763419464642661619 10131734645129196963992429)
          ·
            refine ⟨3799400491923448861497161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10131734645129196963992429 3799400491923448861497161)
            ·
              refine ⟨2849550368942586646122871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3799400491923448861497161 2849550368942586646122871)
              ·
                refine ⟨4274325553413879969184307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2849550368942586646122871 4274325553413879969184307)
                ·
                  refine ⟨6411488330120819953776461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4274325553413879969184307 6411488330120819953776461)
                  ·
                    refine ⟨2404308123795307482666173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6411488330120819953776461 2404308123795307482666173)
                    ·
                      refine ⟨901615546423240305999815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2404308123795307482666173 901615546423240305999815)
                      ·
                        rfl

theorem cell23_1755890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_1755890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755890 prefixEnd_1755890 := by exact prefixLift 1755890
  have htrace : WordTrace (prefixWord ++ tailWord_1755890) baseStart_1755890 baseEnd_1755890 := by
    simpa [prefixWord, tailWord_1755890, baseEnd_1755890] using wordTrace_append hprefix tailTrace_1755890
  have hstable : (prefixWord ++ tailWord_1755890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755890).length < 2 ^ (prefixWord ++ tailWord_1755890).sum := by decide
  have hdescent : baseEnd_1755890 < baseStart_1755890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755896 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 2, 3, 4]
def baseStart_1755896 : Nat := 118140960795 + 1755896 * 2 ^ 59
def prefixEnd_1755896 : Nat := 4983230072969 + 3 ^ 40 * 1755896 * 2
def baseEnd_1755896 : Nat := 901618627307167282524787

theorem tailTrace_1755896 : CollatzResearch.WordTrace tailWord_1755896 prefixEnd_1755896 901618627307167282524787 := by
  unfold tailWord_1755896
  simp only [CollatzResearch.WordTrace]
  refine ⟨32021394223348075003495771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42695192297797433337994361 32021394223348075003495771)
  ·
    refine ⟨48032091335022112505243657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32021394223348075003495771 48032091335022112505243657)
    ·
      refine ⟨36024068501266584378932743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48032091335022112505243657 36024068501266584378932743)
      ·
        refine ⟨54036102751899876568399115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36024068501266584378932743 54036102751899876568399115)
        ·
          refine ⟨81054154127849814852598673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54036102751899876568399115 81054154127849814852598673)
          ·
            refine ⟨60790615595887361139449005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81054154127849814852598673 60790615595887361139449005)
            ·
              refine ⟨22796480848457760427293377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60790615595887361139449005 22796480848457760427293377)
              ·
                refine ⟨17097360636343320320470033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22796480848457760427293377 17097360636343320320470033)
                ·
                  refine ⟨12823020477257490240352525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17097360636343320320470033 12823020477257490240352525)
                  ·
                    refine ⟨4808632678971558840132197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12823020477257490240352525 4808632678971558840132197)
                    ·
                      refine ⟨901618627307167282524787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4808632678971558840132197 901618627307167282524787)
                      ·
                        rfl

theorem cell23_1755896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_1755896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755896 prefixEnd_1755896 := by exact prefixLift 1755896
  have htrace : WordTrace (prefixWord ++ tailWord_1755896) baseStart_1755896 baseEnd_1755896 := by
    simpa [prefixWord, tailWord_1755896, baseEnd_1755896] using wordTrace_append hprefix tailTrace_1755896
  have hstable : (prefixWord ++ tailWord_1755896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755896).length < 2 ^ (prefixWord ++ tailWord_1755896).sum := by decide
  have hdescent : baseEnd_1755896 < baseStart_1755896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755900 : List Nat := [2, 2, 2, 1, 3, 2, 2, 1, 3, 3, 2]
def baseStart_1755900 : Nat := 118140960795 + 1755900 * 2 ^ 59
def prefixEnd_1755900 : Nat := 4983230072969 + 3 ^ 40 * 1755900 * 2
def baseEnd_1755900 : Nat := 901620681229785266874769

theorem tailTrace_1755900 : CollatzResearch.WordTrace tailWord_1755900 prefixEnd_1755900 901620681229785266874769 := by
  unfold tailWord_1755900
  simp only [CollatzResearch.WordTrace]
  refine ⟨32021467169340829345068577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42695289559121105793424769 32021467169340829345068577)
  ·
    refine ⟨24016100377005622008801433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32021467169340829345068577 24016100377005622008801433)
    ·
      refine ⟨18012075282754216506601075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24016100377005622008801433 18012075282754216506601075)
      ·
        refine ⟨27018112924131324759901613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18012075282754216506601075 27018112924131324759901613)
        ·
          refine ⟨10131792346549246784963105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27018112924131324759901613 10131792346549246784963105)
          ·
            refine ⟨7598844259911935088722329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10131792346549246784963105 7598844259911935088722329)
            ·
              refine ⟨5699133194933951316541747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7598844259911935088722329 5699133194933951316541747)
              ·
                refine ⟨8548699792400926974812621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5699133194933951316541747 8548699792400926974812621)
                ·
                  refine ⟨3205762422150347615554733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8548699792400926974812621 3205762422150347615554733)
                  ·
                    refine ⟨1202160908306380355833025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3205762422150347615554733 1202160908306380355833025)
                    ·
                      refine ⟨901620681229785266874769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1202160908306380355833025 901620681229785266874769)
                      ·
                        rfl

theorem cell23_1755900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 3, 3, 2].length) (baseStart_1755900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755900 prefixEnd_1755900 := by exact prefixLift 1755900
  have htrace : WordTrace (prefixWord ++ tailWord_1755900) baseStart_1755900 baseEnd_1755900 := by
    simpa [prefixWord, tailWord_1755900, baseEnd_1755900] using wordTrace_append hprefix tailTrace_1755900
  have hstable : (prefixWord ++ tailWord_1755900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755900).length < 2 ^ (prefixWord ++ tailWord_1755900).sum := by decide
  have hdescent : baseEnd_1755900 < baseStart_1755900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755916 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 1, 3, 5]
def baseStart_1755916 : Nat := 118140960795 + 1755916 * 2 ^ 59
def prefixEnd_1755916 : Nat := 4983230072969 + 3 ^ 40 * 1755916 * 2
def baseEnd_1755916 : Nat := 901628896920257204274695

theorem tailTrace_1755916 : CollatzResearch.WordTrace tailWord_1755916 prefixEnd_1755916 901628896920257204274695 := by
  unfold tailWord_1755916
  simp only [CollatzResearch.WordTrace]
  refine ⟨32021758953311846711359801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42695678604415795615146401 32021758953311846711359801)
  ·
    refine ⟨24016319214983885033519851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32021758953311846711359801 24016319214983885033519851)
    ·
      refine ⟨36024478822475827550279777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24016319214983885033519851 36024478822475827550279777)
      ·
        refine ⟨27018359116856870662709833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36024478822475827550279777 27018359116856870662709833)
        ·
          refine ⟨20263769337642652997032375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27018359116856870662709833 20263769337642652997032375)
          ·
            refine ⟨30395654006463979495548563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20263769337642652997032375 30395654006463979495548563)
            ·
              refine ⟨45593481009695969243322845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30395654006463979495548563 45593481009695969243322845)
              ·
                refine ⟨17097555378635988466246067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45593481009695969243322845 17097555378635988466246067)
                ·
                  refine ⟨25646333067953982699369101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17097555378635988466246067 25646333067953982699369101)
                  ·
                    refine ⟨9617374900482743512263413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25646333067953982699369101 9617374900482743512263413)
                    ·
                      refine ⟨901628896920257204274695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9617374900482743512263413 901628896920257204274695)
                      ·
                        rfl

theorem cell23_1755916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_1755916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755916 prefixEnd_1755916 := by exact prefixLift 1755916
  have htrace : WordTrace (prefixWord ++ tailWord_1755916) baseStart_1755916 baseEnd_1755916 := by
    simpa [prefixWord, tailWord_1755916, baseEnd_1755916] using wordTrace_append hprefix tailTrace_1755916
  have hstable : (prefixWord ++ tailWord_1755916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755916).length < 2 ^ (prefixWord ++ tailWord_1755916).sum := by decide
  have hdescent : baseEnd_1755916 < baseStart_1755916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755993 : List Nat := [1, 2, 1, 2, 2, 5, 1, 1, 1, 2, 5]
def baseStart_1755993 : Nat := 118140960795 + 1755993 * 2 ^ 59
def prefixEnd_1755993 : Nat := 4983230072969 + 3 ^ 40 * 1755993 * 2
def baseEnd_1755993 : Nat := 901668434930653403011841

theorem tailTrace_1755993 : CollatzResearch.WordTrace tailWord_1755993 prefixEnd_1755993 901668434930653403011841 := by
  unfold tailWord_1755993
  simp only [CollatzResearch.WordTrace]
  refine ⟨64046326327344735573272633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42697550884896490382181755 64046326327344735573272633)
  ·
    refine ⟨48034744745508551679954475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64046326327344735573272633 48034744745508551679954475)
    ·
      refine ⟨72052117118262827519931713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48034744745508551679954475 72052117118262827519931713)
      ·
        refine ⟨54039087838697120639948785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72052117118262827519931713 54039087838697120639948785)
        ·
          refine ⟨40529315879022840479961589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54039087838697120639948785 40529315879022840479961589)
          ·
            refine ⟨3799623363658391294996399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40529315879022840479961589 3799623363658391294996399)
            ·
              refine ⟨5699435045487586942494599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3799623363658391294996399 5699435045487586942494599)
              ·
                refine ⟨8549152568231380413741899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5699435045487586942494599 8549152568231380413741899)
                ·
                  refine ⟨12823728852347070620612849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8549152568231380413741899 12823728852347070620612849)
                  ·
                    refine ⟨9617796639260302965459637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12823728852347070620612849 9617796639260302965459637)
                    ·
                      refine ⟨901668434930653403011841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9617796639260302965459637 901668434930653403011841)
                      ·
                        rfl

theorem cell23_1755993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_1755993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1755993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1755993 prefixEnd_1755993 := by exact prefixLift 1755993
  have htrace : WordTrace (prefixWord ++ tailWord_1755993) baseStart_1755993 baseEnd_1755993 := by
    simpa [prefixWord, tailWord_1755993, baseEnd_1755993] using wordTrace_append hprefix tailTrace_1755993
  have hstable : (prefixWord ++ tailWord_1755993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755993).length < 2 ^ (prefixWord ++ tailWord_1755993).sum := by decide
  have hdescent : baseEnd_1755993 < baseStart_1755993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756023 : List Nat := [1, 1, 3, 1, 1, 2, 1, 5, 1, 4, 3]
def baseStart_1756023 : Nat := 118140960795 + 1756023 * 2 ^ 59
def prefixEnd_1756023 : Nat := 4983230072969 + 3 ^ 40 * 1756023 * 2
def baseEnd_1756023 : Nat := 901683839350288285636703

theorem tailTrace_1756023 : CollatzResearch.WordTrace tailWord_1756023 prefixEnd_1756023 901683839350288285636703 := by
  unfold tailWord_1756023
  simp only [CollatzResearch.WordTrace]
  refine ⟨64047420517236050696864723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42698280344824033797909815 64047420517236050696864723)
  ·
    refine ⟨96071130775854076045297085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64047420517236050696864723 96071130775854076045297085)
    ·
      refine ⟨36026674040945278516986407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96071130775854076045297085 36026674040945278516986407)
      ·
        refine ⟨54040011061417917775479611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36026674040945278516986407 54040011061417917775479611)
        ·
          refine ⟨81060016592126876663219417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54040011061417917775479611 81060016592126876663219417)
          ·
            refine ⟨60795012444095157497414563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81060016592126876663219417 60795012444095157497414563)
            ·
              refine ⟨91192518666142736246121845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60795012444095157497414563 91192518666142736246121845)
              ·
                refine ⟨8549298624950881523073923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91192518666142736246121845 8549298624950881523073923)
                ·
                  refine ⟨12823947937426322284610885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8549298624950881523073923 12823947937426322284610885)
                  ·
                    refine ⟨2404490238267435428364541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12823947937426322284610885 2404490238267435428364541)
                    ·
                      refine ⟨901683839350288285636703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2404490238267435428364541 901683839350288285636703)
                      ·
                        rfl

theorem cell23_1756023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 4, 3].length) (baseStart_1756023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756023 prefixEnd_1756023 := by exact prefixLift 1756023
  have htrace : WordTrace (prefixWord ++ tailWord_1756023) baseStart_1756023 baseEnd_1756023 := by
    simpa [prefixWord, tailWord_1756023, baseEnd_1756023] using wordTrace_append hprefix tailTrace_1756023
  have hstable : (prefixWord ++ tailWord_1756023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756023).length < 2 ^ (prefixWord ++ tailWord_1756023).sum := by decide
  have hdescent : baseEnd_1756023 < baseStart_1756023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756043 : List Nat := [1, 1, 1, 1, 4, 2, 3, 4, 6]
def baseStart_1756043 : Nat := 118140960795 + 1756043 * 2 ^ 59
def prefixEnd_1756043 : Nat := 4983230072969 + 3 ^ 40 * 1756043 * 2
def baseEnd_1756043 : Nat := 100188234329264245265179

theorem tailTrace_1756043 : CollatzResearch.WordTrace tailWord_1756043 prefixEnd_1756043 100188234329264245265179 := by
  unfold tailWord_1756043
  simp only [CollatzResearch.WordTrace]
  refine ⟨64048149977163594112592783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42698766651442396075061855 64048149977163594112592783)
  ·
    refine ⟨96072224965745391168889175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64048149977163594112592783 96072224965745391168889175)
    ·
      refine ⟨144108337448618086753333763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96072224965745391168889175 144108337448618086753333763)
      ·
        refine ⟨216162506172927130130000645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144108337448618086753333763 216162506172927130130000645)
        ·
          refine ⟨40530469907423836899375121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216162506172927130130000645 40530469907423836899375121)
          ·
            refine ⟨30397852430567877674531341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40530469907423836899375121 30397852430567877674531341)
            ·
              refine ⟨11399194661462954127949253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30397852430567877674531341 11399194661462954127949253)
              ·
                refine ⟨2137348999024303898990485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11399194661462954127949253 2137348999024303898990485)
                ·
                  refine ⟨100188234329264245265179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2137348999024303898990485 100188234329264245265179)
                  ·
                    rfl

theorem cell23_1756043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 6].length) (baseStart_1756043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756043 prefixEnd_1756043 := by exact prefixLift 1756043
  have htrace : WordTrace (prefixWord ++ tailWord_1756043) baseStart_1756043 baseEnd_1756043 := by
    simpa [prefixWord, tailWord_1756043, baseEnd_1756043] using wordTrace_append hprefix tailTrace_1756043
  have hstable : (prefixWord ++ tailWord_1756043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756043).length < 2 ^ (prefixWord ++ tailWord_1756043).sum := by decide
  have hdescent : baseEnd_1756043 < baseStart_1756043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756073 : List Nat := [1, 2, 1, 1, 1, 1, 5, 3, 3, 5]
def baseStart_1756073 : Nat := 118140960795 + 1756073 * 2 ^ 59
def prefixEnd_1756073 : Nat := 4983230072969 + 3 ^ 40 * 1756073 * 2
def baseEnd_1756073 : Nat := 300569837794337696670491

theorem tailTrace_1756073 : CollatzResearch.WordTrace tailWord_1756073 prefixEnd_1756073 300569837794337696670491 := by
  unfold tailWord_1756073
  simp only [CollatzResearch.WordTrace]
  refine ⟨64049244167054909236184873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42699496111369939490789915 64049244167054909236184873)
  ·
    refine ⟨48036933125291181927138655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64049244167054909236184873 48036933125291181927138655)
    ·
      refine ⟨72055399687936772890707983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48036933125291181927138655 72055399687936772890707983)
      ·
        refine ⟨108083099531905159336061975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72055399687936772890707983 108083099531905159336061975)
        ·
          refine ⟨162124649297857739004092963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108083099531905159336061975 162124649297857739004092963)
          ·
            refine ⟨243186973946786608506139445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162124649297857739004092963 243186973946786608506139445)
            ·
              refine ⟨22798778807511244547450573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 243186973946786608506139445 22798778807511244547450573)
              ·
                refine ⟨8549542052816716705293965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22798778807511244547450573 8549542052816716705293965)
                ·
                  refine ⟨3206078269806268764485237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8549542052816716705293965 3206078269806268764485237)
                  ·
                    refine ⟨300569837794337696670491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3206078269806268764485237 300569837794337696670491)
                    ·
                      rfl

theorem cell23_1756073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 5].length) (baseStart_1756073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756073 prefixEnd_1756073 := by exact prefixLift 1756073
  have htrace : WordTrace (prefixWord ++ tailWord_1756073) baseStart_1756073 baseEnd_1756073 := by
    simpa [prefixWord, tailWord_1756073, baseEnd_1756073] using wordTrace_append hprefix tailTrace_1756073
  have hstable : (prefixWord ++ tailWord_1756073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756073).length < 2 ^ (prefixWord ++ tailWord_1756073).sum := by decide
  have hdescent : baseEnd_1756073 < baseStart_1756073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756090 : List Nat := [3, 1, 1, 1, 2, 1, 5, 3, 1, 5]
def baseStart_1756090 : Nat := 118140960795 + 1756090 * 2 ^ 59
def prefixEnd_1756090 : Nat := 4983230072969 + 3 ^ 40 * 1756090 * 2
def baseEnd_1756090 : Nat := 300572747518046507832965

theorem tailTrace_1756090 : CollatzResearch.WordTrace tailWord_1756090 prefixEnd_1756090 300572747518046507832965 := by
  unfold tailWord_1756090
  simp only [CollatzResearch.WordTrace]
  refine ⟨16012466051998330284888431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42699909471995547426369149 16012466051998330284888431)
  ·
    refine ⟨24018699077997495427332647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16012466051998330284888431 24018699077997495427332647)
    ·
      refine ⟨36028048616996243140998971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24018699077997495427332647 36028048616996243140998971)
      ·
        refine ⟨54042072925494364711498457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36028048616996243140998971 54042072925494364711498457)
        ·
          refine ⟨40531554694120773533623843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54042072925494364711498457 40531554694120773533623843)
          ·
            refine ⟨60797332041181160300435765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40531554694120773533623843 60797332041181160300435765)
            ·
              refine ⟨5699749878860733778165853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60797332041181160300435765 5699749878860733778165853)
              ·
                refine ⟨2137406204572775166812195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5699749878860733778165853 2137406204572775166812195)
                ·
                  refine ⟨3206109306859162750218293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2137406204572775166812195 3206109306859162750218293)
                  ·
                    refine ⟨300572747518046507832965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3206109306859162750218293 300572747518046507832965)
                    ·
                      rfl

theorem cell23_1756090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 1, 5].length) (baseStart_1756090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756090 prefixEnd_1756090 := by exact prefixLift 1756090
  have htrace : WordTrace (prefixWord ++ tailWord_1756090) baseStart_1756090 baseEnd_1756090 := by
    simpa [prefixWord, tailWord_1756090, baseEnd_1756090] using wordTrace_append hprefix tailTrace_1756090
  have hstable : (prefixWord ++ tailWord_1756090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756090).length < 2 ^ (prefixWord ++ tailWord_1756090).sum := by decide
  have hdescent : baseEnd_1756090 < baseStart_1756090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756103 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 3, 6]
def baseStart_1756103 : Nat := 118140960795 + 1756103 * 2 ^ 59
def prefixEnd_1756103 : Nat := 4983230072969 + 3 ^ 40 * 1756103 * 2
def baseEnd_1756103 : Nat := 300574972600882657545445

theorem tailTrace_1756103 : CollatzResearch.WordTrace tailWord_1756103 prefixEnd_1756103 300574972600882657545445 := by
  unfold tailWord_1756103
  simp only [CollatzResearch.WordTrace]
  refine ⟨64050338356946224359776963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42700225571297482906517975 64050338356946224359776963)
  ·
    refine ⟨96075507535419336539665445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64050338356946224359776963 96075507535419336539665445)
    ·
      refine ⟨18014157662891125601187271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96075507535419336539665445 18014157662891125601187271)
      ·
        refine ⟨27021236494336688401780907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18014157662891125601187271 27021236494336688401780907)
        ·
          refine ⟨40531854741505032602671361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27021236494336688401780907 40531854741505032602671361)
          ·
            refine ⟨30398891056128774452003521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40531854741505032602671361 30398891056128774452003521)
            ·
              refine ⟨22799168292096580839002641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30398891056128774452003521 22799168292096580839002641)
              ·
                refine ⟨17099376219072435629251981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22799168292096580839002641 17099376219072435629251981)
                ·
                  refine ⟨6412266082152163360969493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17099376219072435629251981 6412266082152163360969493)
                  ·
                    refine ⟨300574972600882657545445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6412266082152163360969493 300574972600882657545445)
                    ·
                      rfl

theorem cell23_1756103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_1756103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756103 prefixEnd_1756103 := by exact prefixLift 1756103
  have htrace : WordTrace (prefixWord ++ tailWord_1756103) baseStart_1756103 baseEnd_1756103 := by
    simpa [prefixWord, tailWord_1756103, baseEnd_1756103] using wordTrace_append hprefix tailTrace_1756103
  have hstable : (prefixWord ++ tailWord_1756103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756103).length < 2 ^ (prefixWord ++ tailWord_1756103).sum := by decide
  have hdescent : baseEnd_1756103 < baseStart_1756103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756104 : List Nat := [2, 1, 3, 1, 5, 1, 2, 1, 3, 1, 3]
def baseStart_1756104 : Nat := 118140960795 + 1756104 * 2 ^ 59
def prefixEnd_1756104 : Nat := 4983230072969 + 3 ^ 40 * 1756104 * 2
def baseEnd_1756104 : Nat := 901725431283302468723831

theorem tailTrace_1756104 : CollatzResearch.WordTrace tailWord_1756104 prefixEnd_1756104 901725431283302468723831 := by
  unfold tailWord_1756104
  simp only [CollatzResearch.WordTrace]
  refine ⟨32025187414971300765281683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42700249886628401020375577 32025187414971300765281683)
  ·
    refine ⟨48037781122456951147922525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32025187414971300765281683 48037781122456951147922525)
    ·
      refine ⟨18014167920921356680470947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48037781122456951147922525 18014167920921356680470947)
      ·
        refine ⟨27021251881382035020706421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18014167920921356680470947 27021251881382035020706421)
        ·
          refine ⟨2533242363879565783191227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27021251881382035020706421 2533242363879565783191227)
          ·
            refine ⟨3799863545819348674786841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2533242363879565783191227 3799863545819348674786841)
            ·
              refine ⟨2849897659364511506090131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3799863545819348674786841 2849897659364511506090131)
              ·
                refine ⟨4274846489046767259135197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2849897659364511506090131 4274846489046767259135197)
                ·
                  refine ⟨1603067433392537722175699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4274846489046767259135197 1603067433392537722175699)
                  ·
                    refine ⟨2404601150088806583263549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1603067433392537722175699 2404601150088806583263549)
                    ·
                      refine ⟨901725431283302468723831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2404601150088806583263549 901725431283302468723831)
                      ·
                        rfl

theorem cell23_1756104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_1756104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756104 prefixEnd_1756104 := by exact prefixLift 1756104
  have htrace : WordTrace (prefixWord ++ tailWord_1756104) baseStart_1756104 baseEnd_1756104 := by
    simpa [prefixWord, tailWord_1756104, baseEnd_1756104] using wordTrace_append hprefix tailTrace_1756104
  have hstable : (prefixWord ++ tailWord_1756104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756104).length < 2 ^ (prefixWord ++ tailWord_1756104).sum := by decide
  have hdescent : baseEnd_1756104 < baseStart_1756104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756120 : List Nat := [2, 1, 2, 2, 2, 3, 3, 1, 1, 6]
def baseStart_1756120 : Nat := 118140960795 + 1756120 * 2 ^ 59
def prefixEnd_1756120 : Nat := 4983230072969 + 3 ^ 40 * 1756120 * 2
def baseEnd_1756120 : Nat := 300577882324591468707919

theorem tailTrace_1756120 : CollatzResearch.WordTrace tailWord_1756120 prefixEnd_1756120 300577882324591468707919 := by
  unfold tailWord_1756120
  simp only [CollatzResearch.WordTrace]
  refine ⟨32025479198942318131572907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42700638931923090842097209 32025479198942318131572907)
  ·
    refine ⟨48038218798413477197359361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32025479198942318131572907 48038218798413477197359361)
    ·
      refine ⟨36028664098810107898019521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48038218798413477197359361 36028664098810107898019521)
      ·
        refine ⟨27021498074107580923514641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36028664098810107898019521 27021498074107580923514641)
        ·
          refine ⟨20266123555580685692635981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27021498074107580923514641 20266123555580685692635981)
          ·
            refine ⟨7599796333342757134738493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20266123555580685692635981 7599796333342757134738493)
            ·
              refine ⟨2849923625003533925526935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7599796333342757134738493 2849923625003533925526935)
              ·
                refine ⟨4274885437505300888290403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2849923625003533925526935 4274885437505300888290403)
                ·
                  refine ⟨6412328156257951332435605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4274885437505300888290403 6412328156257951332435605)
                  ·
                    refine ⟨300577882324591468707919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6412328156257951332435605 300577882324591468707919)
                    ·
                      rfl

theorem cell23_1756120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 1, 6].length) (baseStart_1756120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756120 prefixEnd_1756120 := by exact prefixLift 1756120
  have htrace : WordTrace (prefixWord ++ tailWord_1756120) baseStart_1756120 baseEnd_1756120 := by
    simpa [prefixWord, tailWord_1756120, baseEnd_1756120] using wordTrace_append hprefix tailTrace_1756120
  have hstable : (prefixWord ++ tailWord_1756120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756120).length < 2 ^ (prefixWord ++ tailWord_1756120).sum := by decide
  have hdescent : baseEnd_1756120 < baseStart_1756120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756150 : List Nat := [5, 1, 1, 1, 3, 1, 11]
def baseStart_1756150 : Nat := 118140960795 + 1756150 * 2 ^ 59
def prefixEnd_1756150 : Nat := 4983230072969 + 3 ^ 40 * 1756150 * 2
def baseEnd_1756150 : Nat := 11132704338190238132699

theorem tailTrace_1756150 : CollatzResearch.WordTrace tailWord_1756150 prefixEnd_1756150 11132704338190238132699 := by
  unfold tailWord_1756150
  simp only [CollatzResearch.WordTrace]
  refine ⟨4003253286735996961671119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42701368391850634257825269 4003253286735996961671119)
  ·
    refine ⟨6004879930103995442506679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4003253286735996961671119 6004879930103995442506679)
    ·
      refine ⟨9007319895155993163760019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6004879930103995442506679 9007319895155993163760019)
      ·
        refine ⟨13510979842733989745640029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9007319895155993163760019 13510979842733989745640029)
        ·
          refine ⟨5066617441025246154615011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13510979842733989745640029 5066617441025246154615011)
          ·
            refine ⟨7599926161537869231922517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5066617441025246154615011 7599926161537869231922517)
            ·
              refine ⟨11132704338190238132699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7599926161537869231922517 11132704338190238132699)
              ·
                rfl

theorem cell23_1756150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 11].length) (baseStart_1756150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756150 prefixEnd_1756150 := by exact prefixLift 1756150
  have htrace : WordTrace (prefixWord ++ tailWord_1756150) baseStart_1756150 baseEnd_1756150 := by
    simpa [prefixWord, tailWord_1756150, baseEnd_1756150] using wordTrace_append hprefix tailTrace_1756150
  have hstable : (prefixWord ++ tailWord_1756150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756150).length < 2 ^ (prefixWord ++ tailWord_1756150).sum := by decide
  have hdescent : baseEnd_1756150 < baseStart_1756150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756161 : List Nat := [1, 2, 4, 1, 2, 4, 1, 1, 3, 2, 2]
def baseStart_1756161 : Nat := 118140960795 + 1756161 * 2 ^ 59
def prefixEnd_1756161 : Nat := 4983230072969 + 3 ^ 40 * 1756161 * 2
def baseEnd_1756161 : Nat := 901754699680608745711069

theorem tailTrace_1756161 : CollatzResearch.WordTrace tailWord_1756161 prefixEnd_1756161 901754699680608745711069 := by
  unfold tailWord_1756161
  simp only [CollatzResearch.WordTrace]
  refine ⟨64052453790736100265388337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42701635860490733510258891 64052453790736100265388337)
  ·
    refine ⟨48039340343052075199041253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64052453790736100265388337 48039340343052075199041253)
    ·
      refine ⟨9007376314322264099820235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48039340343052075199041253 9007376314322264099820235)
      ·
        refine ⟨13511064471483396149730353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9007376314322264099820235 13511064471483396149730353)
        ·
          refine ⟨10133298353612547112297765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13511064471483396149730353 10133298353612547112297765)
          ·
            refine ⟨1899993441302352583555831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10133298353612547112297765 1899993441302352583555831)
            ·
              refine ⟨2849990161953528875333747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1899993441302352583555831 2849990161953528875333747)
              ·
                refine ⟨4274985242930293313000621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2849990161953528875333747 4274985242930293313000621)
                ·
                  refine ⟨1603119466098859992375233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4274985242930293313000621 1603119466098859992375233)
                  ·
                    refine ⟨1202339599574144994281425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1603119466098859992375233 1202339599574144994281425)
                    ·
                      refine ⟨901754699680608745711069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1202339599574144994281425 901754699680608745711069)
                      ·
                        rfl

theorem cell23_1756161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_1756161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756161 prefixEnd_1756161 := by exact prefixLift 1756161
  have htrace : WordTrace (prefixWord ++ tailWord_1756161) baseStart_1756161 baseEnd_1756161 := by
    simpa [prefixWord, tailWord_1756161, baseEnd_1756161] using wordTrace_append hprefix tailTrace_1756161
  have hstable : (prefixWord ++ tailWord_1756161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756161).length < 2 ^ (prefixWord ++ tailWord_1756161).sum := by decide
  have hdescent : baseEnd_1756161 < baseStart_1756161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756210 : List Nat := [3, 2, 1, 1, 2, 2, 2, 2, 2, 6]
def baseStart_1756210 : Nat := 118140960795 + 1756210 * 2 ^ 59
def prefixEnd_1756210 : Nat := 4983230072969 + 3 ^ 40 * 1756210 * 2
def baseEnd_1756210 : Nat := 300593286744226351332781

theorem tailTrace_1756210 : CollatzResearch.WordTrace tailWord_1756210 prefixEnd_1756210 300593286744226351332781 := by
  unfold tailWord_1756210
  simp only [CollatzResearch.WordTrace]
  refine ⟨16013560241889645408480521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42702827311705721089281389 16013560241889645408480521)
  ·
    refine ⟨12010170181417234056360391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16013560241889645408480521 12010170181417234056360391)
    ·
      refine ⟨18015255272125851084540587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12010170181417234056360391 18015255272125851084540587)
      ·
        refine ⟨27022882908188776626810881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18015255272125851084540587 27022882908188776626810881)
        ·
          refine ⟨20267162181141582470108161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27022882908188776626810881 20267162181141582470108161)
          ·
            refine ⟨15200371635856186852581121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20267162181141582470108161 15200371635856186852581121)
            ·
              refine ⟨11400278726892140139435841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15200371635856186852581121 11400278726892140139435841)
              ·
                refine ⟨8550209045169105104576881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11400278726892140139435841 8550209045169105104576881)
                ·
                  refine ⟨6412656783876828828432661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8550209045169105104576881 6412656783876828828432661)
                  ·
                    refine ⟨300593286744226351332781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6412656783876828828432661 300593286744226351332781)
                    ·
                      rfl

theorem cell23_1756210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_1756210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756210 prefixEnd_1756210 := by exact prefixLift 1756210
  have htrace : WordTrace (prefixWord ++ tailWord_1756210) baseStart_1756210 baseEnd_1756210 := by
    simpa [prefixWord, tailWord_1756210, baseEnd_1756210] using wordTrace_append hprefix tailTrace_1756210
  have hstable : (prefixWord ++ tailWord_1756210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756210).length < 2 ^ (prefixWord ++ tailWord_1756210).sum := by decide
  have hdescent : baseEnd_1756210 < baseStart_1756210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
