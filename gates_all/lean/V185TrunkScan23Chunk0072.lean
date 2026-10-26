import V185TrunkScan23Chunk0071

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_428690 : List Nat := [3, 2, 3, 1, 2, 1, 1, 4, 2, 2, 2]
def baseStart_428690 : Nat := 118140960795 + 428690 * 2 ^ 59
def prefixEnd_428690 : Nat := 4983230072969 + 3 ^ 40 * 428690 * 2
def baseEnd_428690 : Nat := 220124021776032982103497

theorem tailTrace_428690 : CollatzResearch.WordTrace tailWord_428690 prefixEnd_428690 220124021776032982103497 := by
  unfold tailWord_428690
  simp only [CollatzResearch.WordTrace]
  refine ⟨3908902204234204817052881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10423739211291212845474349 3908902204234204817052881)
  ·
    refine ⟨2931676653175653612789661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3908902204234204817052881 2931676653175653612789661)
    ·
      refine ⟨1099378744940870104796123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2931676653175653612789661 1099378744940870104796123)
      ·
        refine ⟨1649068117411305157194185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1099378744940870104796123 1649068117411305157194185)
        ·
          refine ⟨1236801088058478867895639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1649068117411305157194185 1236801088058478867895639)
          ·
            refine ⟨1855201632087718301843459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1236801088058478867895639 1855201632087718301843459)
            ·
              refine ⟨2782802448131577452765189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1855201632087718301843459 2782802448131577452765189)
              ·
                refine ⟨521775459024670772393473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2782802448131577452765189 521775459024670772393473)
                ·
                  refine ⟨391331594268503079295105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 521775459024670772393473 391331594268503079295105)
                  ·
                    refine ⟨293498695701377309471329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 391331594268503079295105 293498695701377309471329)
                    ·
                      refine ⟨220124021776032982103497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 293498695701377309471329 220124021776032982103497)
                      ·
                        rfl

theorem cell23_428690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_428690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428690 prefixEnd_428690 := by exact prefixLift 428690
  have htrace : WordTrace (prefixWord ++ tailWord_428690) baseStart_428690 baseEnd_428690 := by
    simpa [prefixWord, tailWord_428690, baseEnd_428690] using wordTrace_append hprefix tailTrace_428690
  have hstable : (prefixWord ++ tailWord_428690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428690).length < 2 ^ (prefixWord ++ tailWord_428690).sum := by decide
  have hdescent : baseEnd_428690 < baseStart_428690 := by decide
  rcases family_descends (prefixWord ++ tailWord_428690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428696 : List Nat := [2, 1, 2, 4, 1, 1, 3, 4, 5]
def baseStart_428696 : Nat := 118140960795 + 428696 * 2 ^ 59
def prefixEnd_428696 : Nat := 4983230072969 + 3 ^ 40 * 428696 * 2
def baseEnd_428696 : Nat := 24458566962217773180941

theorem tailTrace_428696 : CollatzResearch.WordTrace tailWord_428696 prefixEnd_428696 24458566962217773180941 := by
  unfold tailWord_428696
  simp only [CollatzResearch.WordTrace]
  refine ⟨7817913827457541146464971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10423885103276721528619961 7817913827457541146464971)
  ·
    refine ⟨11726870741186311719697457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7817913827457541146464971 11726870741186311719697457)
    ·
      refine ⟨8795153055889733789773093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11726870741186311719697457 8795153055889733789773093)
      ·
        refine ⟨1649091197979325085582455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8795153055889733789773093 1649091197979325085582455)
        ·
          refine ⟨2473636796968987628373683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1649091197979325085582455 2473636796968987628373683)
          ·
            refine ⟨3710455195453481442560525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2473636796968987628373683 3710455195453481442560525)
            ·
              refine ⟨1391420698295055540960197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3710455195453481442560525 1391420698295055540960197)
              ·
                refine ⟨260891380930322913930037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1391420698295055540960197 260891380930322913930037)
                ·
                  refine ⟨24458566962217773180941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 260891380930322913930037 24458566962217773180941)
                  ·
                    rfl

theorem cell23_428696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 4, 5].length) (baseStart_428696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428696 prefixEnd_428696 := by exact prefixLift 428696
  have htrace : WordTrace (prefixWord ++ tailWord_428696) baseStart_428696 baseEnd_428696 := by
    simpa [prefixWord, tailWord_428696, baseEnd_428696] using wordTrace_append hprefix tailTrace_428696
  have hstable : (prefixWord ++ tailWord_428696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428696).length < 2 ^ (prefixWord ++ tailWord_428696).sum := by decide
  have hdescent : baseEnd_428696 < baseStart_428696 := by decide
  rcases family_descends (prefixWord ++ tailWord_428696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428779 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 1, 7, 3]
def baseStart_428779 : Nat := 118140960795 + 428779 * 2 ^ 59
def prefixEnd_428779 : Nat := 4983230072969 + 3 ^ 40 * 428779 * 2
def baseEnd_428779 : Nat := 220169721554283133890587

theorem tailTrace_428779 : CollatzResearch.WordTrace tailWord_428779 prefixEnd_428779 220169721554283133890587 := by
  unfold tailWord_428779
  simp only [CollatzResearch.WordTrace]
  refine ⟨15638854913614387468201391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10425903275742924978800927 15638854913614387468201391)
  ·
    refine ⟨23458282370421581202302087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15638854913614387468201391 23458282370421581202302087)
    ·
      refine ⟨35187423555632371803453131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23458282370421581202302087 35187423555632371803453131)
      ·
        refine ⟨52781135333448557705179697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35187423555632371803453131 52781135333448557705179697)
        ·
          refine ⟨39585851500086418278884773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52781135333448557705179697 39585851500086418278884773)
          ·
            refine ⟨7422347156266203427290895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39585851500086418278884773 7422347156266203427290895)
            ·
              refine ⟨11133520734399305140936343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7422347156266203427290895 11133520734399305140936343)
              ·
                refine ⟨16700281101598957711404515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11133520734399305140936343 16700281101598957711404515)
                ·
                  refine ⟨25050421652398436567106773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16700281101598957711404515 25050421652398436567106773)
                  ·
                    refine ⟨587119257478088357041565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25050421652398436567106773 587119257478088357041565)
                    ·
                      refine ⟨220169721554283133890587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 587119257478088357041565 220169721554283133890587)
                      ·
                        rfl

theorem cell23_428779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 7, 3].length) (baseStart_428779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428779 prefixEnd_428779 := by exact prefixLift 428779
  have htrace : WordTrace (prefixWord ++ tailWord_428779) baseStart_428779 baseEnd_428779 := by
    simpa [prefixWord, tailWord_428779, baseEnd_428779] using wordTrace_append hprefix tailTrace_428779
  have hstable : (prefixWord ++ tailWord_428779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428779).length < 2 ^ (prefixWord ++ tailWord_428779).sum := by decide
  have hdescent : baseEnd_428779 < baseStart_428779 := by decide
  rcases family_descends (prefixWord ++ tailWord_428779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428799 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 5, 5]
def baseStart_428799 : Nat := 118140960795 + 428799 * 2 ^ 59
def prefixEnd_428799 : Nat := 4983230072969 + 3 ^ 40 * 428799 * 2
def baseEnd_428799 : Nat := 73393330389124351880165

theorem tailTrace_428799 : CollatzResearch.WordTrace tailWord_428799 prefixEnd_428799 73393330389124351880165 := by
  unfold tailWord_428799
  simp only [CollatzResearch.WordTrace]
  refine ⟨15639584373541930883929451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10426389582361287255952967 15639584373541930883929451)
  ·
    refine ⟨23459376560312896325894177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15639584373541930883929451 23459376560312896325894177)
    ·
      refine ⟨17594532420234672244420633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23459376560312896325894177 17594532420234672244420633)
      ·
        refine ⟨13195899315176004183315475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17594532420234672244420633 13195899315176004183315475)
        ·
          refine ⟨19793848972764006274973213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13195899315176004183315475 19793848972764006274973213)
          ·
            refine ⟨7422693364786502353114955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19793848972764006274973213 7422693364786502353114955)
            ·
              refine ⟨11134040047179753529672433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7422693364786502353114955 11134040047179753529672433)
              ·
                refine ⟨8350530035384815147254325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11134040047179753529672433 8350530035384815147254325)
                ·
                  refine ⟨782862190817326420055093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8350530035384815147254325 782862190817326420055093)
                  ·
                    refine ⟨73393330389124351880165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 782862190817326420055093 73393330389124351880165)
                    ·
                      rfl

theorem cell23_428799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 5].length) (baseStart_428799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428799 prefixEnd_428799 := by exact prefixLift 428799
  have htrace : WordTrace (prefixWord ++ tailWord_428799) baseStart_428799 baseEnd_428799 := by
    simpa [prefixWord, tailWord_428799, baseEnd_428799] using wordTrace_append hprefix tailTrace_428799
  have hstable : (prefixWord ++ tailWord_428799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428799).length < 2 ^ (prefixWord ++ tailWord_428799).sum := by decide
  have hdescent : baseEnd_428799 < baseStart_428799 := by decide
  rcases family_descends (prefixWord ++ tailWord_428799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428807 : List Nat := [1, 1, 4, 4, 1, 2, 3, 2, 1, 4]
def baseStart_428807 : Nat := 118140960795 + 428807 * 2 ^ 59
def prefixEnd_428807 : Nat := 4983230072969 + 3 ^ 40 * 428807 * 2
def baseEnd_428807 : Nat := 73394699670869674780153

theorem tailTrace_428807 : CollatzResearch.WordTrace tailWord_428807 prefixEnd_428807 73394699670869674780153 := by
  unfold tailWord_428807
  simp only [CollatzResearch.WordTrace]
  refine ⟨15639876157512948250220675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10426584105008632166813783 15639876157512948250220675)
  ·
    refine ⟨23459814236269422375331013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15639876157512948250220675 23459814236269422375331013)
    ·
      refine ⟨4398715169300516695374565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23459814236269422375331013 4398715169300516695374565)
      ·
        refine ⟨824759094243846880382731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4398715169300516695374565 824759094243846880382731)
        ·
          refine ⟨1237138641365770320574097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 824759094243846880382731 1237138641365770320574097)
          ·
            refine ⟨927853981024327740430573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1237138641365770320574097 927853981024327740430573)
            ·
              refine ⟨347945242884122902661465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 927853981024327740430573 347945242884122902661465)
              ·
                refine ⟨260958932163092176996099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347945242884122902661465 260958932163092176996099)
                ·
                  refine ⟨391438398244638265494149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 260958932163092176996099 391438398244638265494149)
                  ·
                    refine ⟨73394699670869674780153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 391438398244638265494149 73394699670869674780153)
                    ·
                      rfl

theorem cell23_428807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_428807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428807 prefixEnd_428807 := by exact prefixLift 428807
  have htrace : WordTrace (prefixWord ++ tailWord_428807) baseStart_428807 baseEnd_428807 := by
    simpa [prefixWord, tailWord_428807, baseEnd_428807] using wordTrace_append hprefix tailTrace_428807
  have hstable : (prefixWord ++ tailWord_428807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428807).length < 2 ^ (prefixWord ++ tailWord_428807).sum := by decide
  have hdescent : baseEnd_428807 < baseStart_428807 := by decide
  rcases family_descends (prefixWord ++ tailWord_428807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428840 : List Nat := [2, 1, 5, 1, 1, 1, 4, 1, 2, 3, 2]
def baseStart_428840 : Nat := 118140960795 + 428840 * 2 ^ 59
def prefixEnd_428840 : Nat := 4983230072969 + 3 ^ 40 * 428840 * 2
def baseEnd_428840 : Nat := 220201043874207395227807

theorem tailTrace_428840 : CollatzResearch.WordTrace tailWord_428840 prefixEnd_428840 220201043874207395227807 := by
  unfold tailWord_428840
  simp only [CollatzResearch.WordTrace]
  refine ⟨7820539883196697443085987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10427386510928929924114649 7820539883196697443085987)
  ·
    refine ⟨11730809824795046164628981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7820539883196697443085987 11730809824795046164628981)
    ·
      refine ⟨1099763421074535577933967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11730809824795046164628981 1099763421074535577933967)
      ·
        refine ⟨1649645131611803366900951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1099763421074535577933967 1649645131611803366900951)
        ·
          refine ⟨2474467697417705050351427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1649645131611803366900951 2474467697417705050351427)
          ·
            refine ⟨3711701546126557575527141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2474467697417705050351427 3711701546126557575527141)
            ·
              refine ⟨695944039898729545411339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3711701546126557575527141 695944039898729545411339)
              ·
                refine ⟨1043916059848094318117009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 695944039898729545411339 1043916059848094318117009)
                ·
                  refine ⟨782937044886070738587757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1043916059848094318117009 782937044886070738587757)
                  ·
                    refine ⟨293601391832276526970409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 782937044886070738587757 293601391832276526970409)
                    ·
                      refine ⟨220201043874207395227807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 293601391832276526970409 220201043874207395227807)
                      ·
                        rfl

theorem cell23_428840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_428840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428840 prefixEnd_428840 := by exact prefixLift 428840
  have htrace : WordTrace (prefixWord ++ tailWord_428840) baseStart_428840 baseEnd_428840 := by
    simpa [prefixWord, tailWord_428840, baseEnd_428840] using wordTrace_append hprefix tailTrace_428840
  have hstable : (prefixWord ++ tailWord_428840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428840).length < 2 ^ (prefixWord ++ tailWord_428840).sum := by decide
  have hdescent : baseEnd_428840 < baseStart_428840 := by decide
  rcases family_descends (prefixWord ++ tailWord_428840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428863 : List Nat := [1, 1, 2, 2, 5, 1, 1, 4, 2, 4]
def baseStart_428863 : Nat := 118140960795 + 428863 * 2 ^ 59
def prefixEnd_428863 : Nat := 4983230072969 + 3 ^ 40 * 428863 * 2
def baseEnd_428863 : Nat := 73404284643086935080067

theorem tailTrace_428863 : CollatzResearch.WordTrace tailWord_428863 prefixEnd_428863 73404284643086935080067 := by
  unfold tailWord_428863
  simp only [CollatzResearch.WordTrace]
  refine ⟨15641918645310069814259243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10427945763540046542839495 15641918645310069814259243)
  ·
    refine ⟨23462877967965104721388865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15641918645310069814259243 23462877967965104721388865)
    ·
      refine ⟨17597158475973828541041649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23462877967965104721388865 17597158475973828541041649)
      ·
        refine ⟨13197868856980371405781237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17597158475973828541041649 13197868856980371405781237)
        ·
          refine ⟨1237300205341909819291991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13197868856980371405781237 1237300205341909819291991)
          ·
            refine ⟨1855950308012864728937987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1237300205341909819291991 1855950308012864728937987)
            ·
              refine ⟨2783925462019297093406981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1855950308012864728937987 2783925462019297093406981)
              ·
                refine ⟨521986024128618205013809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2783925462019297093406981 521986024128618205013809)
                ·
                  refine ⟨391489518096463653760357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 521986024128618205013809 391489518096463653760357)
                  ·
                    refine ⟨73404284643086935080067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 391489518096463653760357 73404284643086935080067)
                    ·
                      rfl

theorem cell23_428863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 2, 4].length) (baseStart_428863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428863 prefixEnd_428863 := by exact prefixLift 428863
  have htrace : WordTrace (prefixWord ++ tailWord_428863) baseStart_428863 baseEnd_428863 := by
    simpa [prefixWord, tailWord_428863, baseEnd_428863] using wordTrace_append hprefix tailTrace_428863
  have hstable : (prefixWord ++ tailWord_428863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428863).length < 2 ^ (prefixWord ++ tailWord_428863).sum := by decide
  have hdescent : baseEnd_428863 < baseStart_428863 := by decide
  rcases family_descends (prefixWord ++ tailWord_428863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428869 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 2, 2, 7]
def baseStart_428869 : Nat := 118140960795 + 428869 * 2 ^ 59
def prefixEnd_428869 : Nat := 4983230072969 + 3 ^ 40 * 428869 * 2
def baseEnd_428869 : Nat := 220215934813187781765173

theorem tailTrace_428869 : CollatzResearch.WordTrace tailWord_428869 prefixEnd_428869 220215934813187781765173 := by
  unfold tailWord_428869
  simp only [CollatzResearch.WordTrace]
  refine ⟨15642137483288332838977661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10428091655525555225985107 15642137483288332838977661)
  ·
    refine ⟨5865801556233124814616623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15642137483288332838977661 5865801556233124814616623)
    ·
      refine ⟨8798702334349687221924935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5865801556233124814616623 8798702334349687221924935)
      ·
        refine ⟨13198053501524530832887403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8798702334349687221924935 13198053501524530832887403)
        ·
          refine ⟨19797080252286796249331105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13198053501524530832887403 19797080252286796249331105)
          ·
            refine ⟨14847810189215097186998329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19797080252286796249331105 14847810189215097186998329)
            ·
              refine ⟨11135857641911322890248747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14847810189215097186998329 11135857641911322890248747)
              ·
                refine ⟨16703786462866984335373121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11135857641911322890248747 16703786462866984335373121)
                ·
                  refine ⟨12527839847150238251529841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16703786462866984335373121 12527839847150238251529841)
                  ·
                    refine ⟨9395879885362678688647381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12527839847150238251529841 9395879885362678688647381)
                    ·
                      refine ⟨220215934813187781765173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 9395879885362678688647381 220215934813187781765173)
                      ·
                        rfl

theorem cell23_428869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_428869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428869 prefixEnd_428869 := by exact prefixLift 428869
  have htrace : WordTrace (prefixWord ++ tailWord_428869) baseStart_428869 baseEnd_428869 := by
    simpa [prefixWord, tailWord_428869, baseEnd_428869] using wordTrace_append hprefix tailTrace_428869
  have hstable : (prefixWord ++ tailWord_428869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428869).length < 2 ^ (prefixWord ++ tailWord_428869).sum := by decide
  have hdescent : baseEnd_428869 < baseStart_428869 := by decide
  rcases family_descends (prefixWord ++ tailWord_428869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428876 : List Nat := [2, 2, 1, 3, 3, 1, 3, 8]
def baseStart_428876 : Nat := 118140960795 + 428876 * 2 ^ 59
def prefixEnd_428876 : Nat := 4983230072969 + 3 ^ 40 * 428876 * 2
def baseEnd_428876 : Nat := 8156278858435898310283

theorem tailTrace_428876 : CollatzResearch.WordTrace tailWord_428876 prefixEnd_428876 8156278858435898310283 := by
  unfold tailWord_428876
  simp only [CollatzResearch.WordTrace]
  refine ⟨7821196397131486517241241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10428261862841982022988321 7821196397131486517241241)
  ·
    refine ⟨5865897297848614887930931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7821196397131486517241241 5865897297848614887930931)
    ·
      refine ⟨8798845946772922331896397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5865897297848614887930931 8798845946772922331896397)
      ·
        refine ⟨3299567230039845874461149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8798845946772922331896397 3299567230039845874461149)
        ·
          refine ⟨1237337711264942202922931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3299567230039845874461149 1237337711264942202922931)
          ·
            refine ⟨1856006566897413304384397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1237337711264942202922931 1856006566897413304384397)
            ·
              refine ⟨696002462586529989144149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1856006566897413304384397 696002462586529989144149)
              ·
                refine ⟨8156278858435898310283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 696002462586529989144149 8156278858435898310283)
                ·
                  rfl

theorem cell23_428876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 8].length) (baseStart_428876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428876 prefixEnd_428876 := by exact prefixLift 428876
  have htrace : WordTrace (prefixWord ++ tailWord_428876) baseStart_428876 baseEnd_428876 := by
    simpa [prefixWord, tailWord_428876, baseEnd_428876] using wordTrace_append hprefix tailTrace_428876
  have hstable : (prefixWord ++ tailWord_428876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428876).length < 2 ^ (prefixWord ++ tailWord_428876).sum := by decide
  have hdescent : baseEnd_428876 < baseStart_428876 := by decide
  rcases family_descends (prefixWord ++ tailWord_428876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428903 : List Nat := [1, 1, 5, 1, 2, 2, 2, 2, 1, 3, 3]
def baseStart_428903 : Nat := 118140960795 + 428903 * 2 ^ 59
def prefixEnd_428903 : Nat := 4983230072969 + 3 ^ 40 * 428903 * 2
def baseEnd_428903 : Nat := 220233393155440648740017

theorem tailTrace_428903 : CollatzResearch.WordTrace tailWord_428903 prefixEnd_428903 220233393155440648740017 := by
  unfold tailWord_428903
  simp only [CollatzResearch.WordTrace]
  refine ⟨15643377565165156645715363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10428918376776771097143575 15643377565165156645715363)
  ·
    refine ⟨23465066347747734968573045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15643377565165156645715363 23465066347747734968573045)
    ·
      refine ⟨2199849970101350153303723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23465066347747734968573045 2199849970101350153303723)
      ·
        refine ⟨3299774955152025229955585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2199849970101350153303723 3299774955152025229955585)
        ·
          refine ⟨2474831216364018922466689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3299774955152025229955585 2474831216364018922466689)
          ·
            refine ⟨1856123412273014191850017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2474831216364018922466689 1856123412273014191850017)
            ·
              refine ⟨1392092559204760643887513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1856123412273014191850017 1392092559204760643887513)
              ·
                refine ⟨1044069419403570482915635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1392092559204760643887513 1044069419403570482915635)
                ·
                  refine ⟨1566104129105355724373453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1044069419403570482915635 1566104129105355724373453)
                  ·
                    refine ⟨587289048414508396640045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1566104129105355724373453 587289048414508396640045)
                    ·
                      refine ⟨220233393155440648740017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 587289048414508396640045 220233393155440648740017)
                      ·
                        rfl

theorem cell23_428903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_428903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428903 prefixEnd_428903 := by exact prefixLift 428903
  have htrace : WordTrace (prefixWord ++ tailWord_428903) baseStart_428903 baseEnd_428903 := by
    simpa [prefixWord, tailWord_428903, baseEnd_428903] using wordTrace_append hprefix tailTrace_428903
  have hstable : (prefixWord ++ tailWord_428903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428903).length < 2 ^ (prefixWord ++ tailWord_428903).sum := by decide
  have hdescent : baseEnd_428903 < baseStart_428903 := by decide
  rcases family_descends (prefixWord ++ tailWord_428903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428904 : List Nat := [2, 1, 4, 2, 1, 3, 2, 3, 1, 2, 2]
def baseStart_428904 : Nat := 118140960795 + 428904 * 2 ^ 59
def prefixEnd_428904 : Nat := 4983230072969 + 3 ^ 40 * 428904 * 2
def baseEnd_428904 : Nat := 220233906636095144827513

theorem tailTrace_428904 : CollatzResearch.WordTrace tailWord_428904 prefixEnd_428904 220233906636095144827513 := by
  unfold tailWord_428904
  simp only [CollatzResearch.WordTrace]
  refine ⟨7821707019080766908250883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10428942692107689211001177 7821707019080766908250883)
  ·
    refine ⟨11732560528621150362376325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7821707019080766908250883 11732560528621150362376325)
    ·
      refine ⟨2199855099116465692945561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11732560528621150362376325 2199855099116465692945561)
      ·
        refine ⟨1649891324337349269709171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2199855099116465692945561 1649891324337349269709171)
        ·
          refine ⟨2474836986506023904563757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1649891324337349269709171 2474836986506023904563757)
          ·
            refine ⟨928063869939758964211409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2474836986506023904563757 928063869939758964211409)
            ·
              refine ⟨696047902454819223158557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 928063869939758964211409 696047902454819223158557)
              ·
                refine ⟨261017963420557208684459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 696047902454819223158557 261017963420557208684459)
                ·
                  refine ⟨391526945130835813026689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 261017963420557208684459 391526945130835813026689)
                  ·
                    refine ⟨293645208848126859770017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 391526945130835813026689 293645208848126859770017)
                    ·
                      refine ⟨220233906636095144827513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 293645208848126859770017 220233906636095144827513)
                      ·
                        rfl

theorem cell23_428904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_428904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428904 prefixEnd_428904 := by exact prefixLift 428904
  have htrace : WordTrace (prefixWord ++ tailWord_428904) baseStart_428904 baseEnd_428904 := by
    simpa [prefixWord, tailWord_428904, baseEnd_428904] using wordTrace_append hprefix tailTrace_428904
  have hstable : (prefixWord ++ tailWord_428904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428904).length < 2 ^ (prefixWord ++ tailWord_428904).sum := by decide
  have hdescent : baseEnd_428904 < baseStart_428904 := by decide
  rcases family_descends (prefixWord ++ tailWord_428904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428937 : List Nat := [1, 2, 1, 1, 5, 3, 3, 1, 2, 1, 3]
def baseStart_428937 : Nat := 118140960795 + 428937 * 2 ^ 59
def prefixEnd_428937 : Nat := 4983230072969 + 3 ^ 40 * 428937 * 2
def baseEnd_428937 : Nat := 220250851497693515714861

theorem tailTrace_428937 : CollatzResearch.WordTrace tailWord_428937 prefixEnd_428937 220250851497693515714861 := by
  unfold tailWord_428937
  simp only [CollatzResearch.WordTrace]
  refine ⟨15644617647041980452453065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10429745098027986968302043 15644617647041980452453065)
  ·
    refine ⟨11733463235281485339339799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15644617647041980452453065 11733463235281485339339799)
    ·
      refine ⟨17600194852922228009009699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11733463235281485339339799 17600194852922228009009699)
      ·
        refine ⟨26400292279383342013514549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17600194852922228009009699 26400292279383342013514549)
        ·
          refine ⟨2475027401192188313766989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26400292279383342013514549 2475027401192188313766989)
          ·
            refine ⟨928135275447070617662621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2475027401192188313766989 928135275447070617662621)
            ·
              refine ⟨348050728292651481623483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 928135275447070617662621 348050728292651481623483)
              ·
                refine ⟨522076092438977222435225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 348050728292651481623483 522076092438977222435225)
                ·
                  refine ⟨391557069329232916826419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 522076092438977222435225 391557069329232916826419)
                  ·
                    refine ⟨587335603993849375239629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 391557069329232916826419 587335603993849375239629)
                    ·
                      refine ⟨220250851497693515714861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 587335603993849375239629 220250851497693515714861)
                      ·
                        rfl

theorem cell23_428937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 2, 1, 3].length) (baseStart_428937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428937 prefixEnd_428937 := by exact prefixLift 428937
  have htrace : WordTrace (prefixWord ++ tailWord_428937) baseStart_428937 baseEnd_428937 := by
    simpa [prefixWord, tailWord_428937, baseEnd_428937] using wordTrace_append hprefix tailTrace_428937
  have hstable : (prefixWord ++ tailWord_428937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428937).length < 2 ^ (prefixWord ++ tailWord_428937).sum := by decide
  have hdescent : baseEnd_428937 < baseStart_428937 := by decide
  rcases family_descends (prefixWord ++ tailWord_428937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428960 : List Nat := [2, 1, 1, 4, 1, 1, 3, 2, 4, 2, 2]
def baseStart_428960 : Nat := 118140960795 + 428960 * 2 ^ 59
def prefixEnd_428960 : Nat := 4983230072969 + 3 ^ 40 * 428960 * 2
def baseEnd_428960 : Nat := 220262661552746925727255

theorem tailTrace_428960 : CollatzResearch.WordTrace tailWord_428960 prefixEnd_428960 220262661552746925727255 := by
  unfold tailWord_428960
  simp only [CollatzResearch.WordTrace]
  refine ⟨7822728262979327690270167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10430304350639103587026889 7822728262979327690270167)
  ·
    refine ⟨11734092394468991535405251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7822728262979327690270167 11734092394468991535405251)
    ·
      refine ⟨17601138591703487303107877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11734092394468991535405251 17601138591703487303107877)
      ·
        refine ⟨3300213485944403869332727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17601138591703487303107877 3300213485944403869332727)
        ·
          refine ⟨4950320228916605803999091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3300213485944403869332727 4950320228916605803999091)
          ·
            refine ⟨7425480343374908705998637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4950320228916605803999091 7425480343374908705998637)
            ·
              refine ⟨2784555128765590764749489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7425480343374908705998637 2784555128765590764749489)
              ·
                refine ⟨2088416346574193073562117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2784555128765590764749489 2088416346574193073562117)
                ·
                  refine ⟨391578064982661201292897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2088416346574193073562117 391578064982661201292897)
                  ·
                    refine ⟨293683548736995900969673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 391578064982661201292897 293683548736995900969673)
                    ·
                      refine ⟨220262661552746925727255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 293683548736995900969673 220262661552746925727255)
                      ·
                        rfl

theorem cell23_428960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_428960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428960 prefixEnd_428960 := by exact prefixLift 428960
  have htrace : WordTrace (prefixWord ++ tailWord_428960) baseStart_428960 baseEnd_428960 := by
    simpa [prefixWord, tailWord_428960, baseEnd_428960] using wordTrace_append hprefix tailTrace_428960
  have hstable : (prefixWord ++ tailWord_428960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428960).length < 2 ^ (prefixWord ++ tailWord_428960).sum := by decide
  have hdescent : baseEnd_428960 < baseStart_428960 := by decide
  rcases family_descends (prefixWord ++ tailWord_428960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428983 : List Nat := [1, 1, 3, 1, 3, 1, 2, 6, 5]
def baseStart_428983 : Nat := 118140960795 + 428983 * 2 ^ 59
def prefixEnd_428983 : Nat := 4983230072969 + 3 ^ 40 * 428983 * 2
def baseEnd_428983 : Nat := 24474941289755592859961

theorem tailTrace_428983 : CollatzResearch.WordTrace tailWord_428983 prefixEnd_428983 24474941289755592859961 := by
  unfold tailWord_428983
  simp only [CollatzResearch.WordTrace]
  refine ⟨15646295404875330308627603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10430863603250220205751735 15646295404875330308627603)
  ·
    refine ⟨23469443107312995462941405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15646295404875330308627603 23469443107312995462941405)
    ·
      refine ⟨8801041165242373298603027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23469443107312995462941405 8801041165242373298603027)
      ·
        refine ⟨13201561747863559947904541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8801041165242373298603027 13201561747863559947904541)
        ·
          refine ⟨4950585655448834980464203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13201561747863559947904541 4950585655448834980464203)
          ·
            refine ⟨7425878483173252470696305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4950585655448834980464203 7425878483173252470696305)
            ·
              refine ⟨5569408862379939353022229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7425878483173252470696305 5569408862379939353022229)
              ·
                refine ⟨261066040424059657172917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5569408862379939353022229 261066040424059657172917)
                ·
                  refine ⟨24474941289755592859961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 261066040424059657172917 24474941289755592859961)
                  ·
                    rfl

theorem cell23_428983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 6, 5].length) (baseStart_428983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428983 prefixEnd_428983 := by exact prefixLift 428983
  have htrace : WordTrace (prefixWord ++ tailWord_428983) baseStart_428983 baseEnd_428983 := by
    simpa [prefixWord, tailWord_428983, baseEnd_428983] using wordTrace_append hprefix tailTrace_428983
  have hstable : (prefixWord ++ tailWord_428983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428983).length < 2 ^ (prefixWord ++ tailWord_428983).sum := by decide
  have hdescent : baseEnd_428983 < baseStart_428983 := by decide
  rcases family_descends (prefixWord ++ tailWord_428983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428998 : List Nat := [6, 1, 3, 1, 1, 1, 1, 1, 3, 3, 2]
def baseStart_428998 : Nat := 118140960795 + 428998 * 2 ^ 59
def prefixEnd_428998 : Nat := 4983230072969 + 3 ^ 40 * 428998 * 2
def baseEnd_428998 : Nat := 220282173817617777052081

theorem tailTrace_428998 : CollatzResearch.WordTrace tailWord_428998 prefixEnd_428998 220282173817617777052081 := by
  unfold tailWord_428998
  simp only [CollatzResearch.WordTrace]
  refine ⟨488963828119405870950739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10431228333213991913615765 488963828119405870950739)
  ·
    refine ⟨733445742179108806426109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 488963828119405870950739 733445742179108806426109)
    ·
      refine ⟨275042153317165802409791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 733445742179108806426109 275042153317165802409791)
      ·
        refine ⟨412563229975748703614687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275042153317165802409791 412563229975748703614687)
        ·
          refine ⟨618844844963623055422031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412563229975748703614687 618844844963623055422031)
          ·
            refine ⟨928267267445434583133047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618844844963623055422031 928267267445434583133047)
            ·
              refine ⟨1392400901168151874699571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 928267267445434583133047 1392400901168151874699571)
              ·
                refine ⟨2088601351752227812049357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1392400901168151874699571 2088601351752227812049357)
                ·
                  refine ⟨783225506907085429518509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2088601351752227812049357 783225506907085429518509)
                  ·
                    refine ⟨293709565090157036069441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 783225506907085429518509 293709565090157036069441)
                    ·
                      refine ⟨220282173817617777052081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 293709565090157036069441 220282173817617777052081)
                      ·
                        rfl

theorem cell23_428998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_428998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_428998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_428998 prefixEnd_428998 := by exact prefixLift 428998
  have htrace : WordTrace (prefixWord ++ tailWord_428998) baseStart_428998 baseEnd_428998 := by
    simpa [prefixWord, tailWord_428998, baseEnd_428998] using wordTrace_append hprefix tailTrace_428998
  have hstable : (prefixWord ++ tailWord_428998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428998).length < 2 ^ (prefixWord ++ tailWord_428998).sum := by decide
  have hdescent : baseEnd_428998 < baseStart_428998 := by decide
  rcases family_descends (prefixWord ++ tailWord_428998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429033 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 5, 6, 2]
def baseStart_429033 : Nat := 118140960795 + 429033 * 2 ^ 59
def prefixEnd_429033 : Nat := 4983230072969 + 3 ^ 40 * 429033 * 2
def baseEnd_429033 : Nat := 220300145640525140114419

theorem tailTrace_429033 : CollatzResearch.WordTrace tailWord_429033 prefixEnd_429033 220300145640525140114419 := by
  unfold tailWord_429033
  simp only [CollatzResearch.WordTrace]
  refine ⟨15648119054694188847947753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10432079369796125898631835 15648119054694188847947753)
  ·
    refine ⟨11736089291020641635960815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15648119054694188847947753 11736089291020641635960815)
    ·
      refine ⟨17604133936530962453941223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11736089291020641635960815 17604133936530962453941223)
      ·
        refine ⟨26406200904796443680911835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17604133936530962453941223 26406200904796443680911835)
        ·
          refine ⟨39609301357194665521367753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26406200904796443680911835 39609301357194665521367753)
          ·
            refine ⟨29706976017895999141025815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39609301357194665521367753 29706976017895999141025815)
            ·
              refine ⟨44560464026843998711538723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29706976017895999141025815 44560464026843998711538723)
              ·
                refine ⟨66840696040265998067308085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44560464026843998711538723 66840696040265998067308085)
                ·
                  refine ⟨6266315253774937318810133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66840696040265998067308085 6266315253774937318810133)
                  ·
                    refine ⟨293733527520700186819225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6266315253774937318810133 293733527520700186819225)
                    ·
                      refine ⟨220300145640525140114419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 293733527520700186819225 220300145640525140114419)
                      ·
                        rfl

theorem cell23_429033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 6, 2].length) (baseStart_429033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429033 prefixEnd_429033 := by exact prefixLift 429033
  have htrace : WordTrace (prefixWord ++ tailWord_429033) baseStart_429033 baseEnd_429033 := by
    simpa [prefixWord, tailWord_429033, baseEnd_429033] using wordTrace_append hprefix tailTrace_429033
  have hstable : (prefixWord ++ tailWord_429033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429033).length < 2 ^ (prefixWord ++ tailWord_429033).sum := by decide
  have hdescent : baseEnd_429033 < baseStart_429033 := by decide
  rcases family_descends (prefixWord ++ tailWord_429033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429053 : List Nat := [1, 4, 1, 1, 1, 2, 1, 4, 1, 4, 3]
def baseStart_429053 : Nat := 118140960795 + 429053 * 2 ^ 59
def prefixEnd_429053 : Nat := 4983230072969 + 3 ^ 40 * 429053 * 2
def baseEnd_429053 : Nat := 220310415253615061864327

theorem tailTrace_429053 : CollatzResearch.WordTrace tailWord_429053 prefixEnd_429053 220310415253615061864327 := by
  unfold tailWord_429053
  simp only [CollatzResearch.WordTrace]
  refine ⟨15648848514621732263675813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10432565676414488175783875 15648848514621732263675813)
  ·
    refine ⟨2934159096491574799439215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15648848514621732263675813 2934159096491574799439215)
    ·
      refine ⟨4401238644737362199158823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2934159096491574799439215 4401238644737362199158823)
      ·
        refine ⟨6601857967106043298738235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4401238644737362199158823 6601857967106043298738235)
        ·
          refine ⟨9902786950659064948107353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6601857967106043298738235 9902786950659064948107353)
          ·
            refine ⟨7427090212994298711080515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9902786950659064948107353 7427090212994298711080515)
            ·
              refine ⟨11140635319491448066620773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7427090212994298711080515 11140635319491448066620773)
              ·
                refine ⟨2088869122404646512491395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11140635319491448066620773 2088869122404646512491395)
                ·
                  refine ⟨3133303683606969768737093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2088869122404646512491395 3133303683606969768737093)
                  ·
                    refine ⟨587494440676306831638205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3133303683606969768737093 587494440676306831638205)
                    ·
                      refine ⟨220310415253615061864327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 587494440676306831638205 220310415253615061864327)
                      ·
                        rfl

theorem cell23_429053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_429053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429053 prefixEnd_429053 := by exact prefixLift 429053
  have htrace : WordTrace (prefixWord ++ tailWord_429053) baseStart_429053 baseEnd_429053 := by
    simpa [prefixWord, tailWord_429053, baseEnd_429053] using wordTrace_append hprefix tailTrace_429053
  have hstable : (prefixWord ++ tailWord_429053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429053).length < 2 ^ (prefixWord ++ tailWord_429053).sum := by decide
  have hdescent : baseEnd_429053 < baseStart_429053 := by decide
  rcases family_descends (prefixWord ++ tailWord_429053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429070 : List Nat := [4, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3]
def baseStart_429070 : Nat := 118140960795 + 429070 * 2 ^ 59
def prefixEnd_429070 : Nat := 4983230072969 + 3 ^ 40 * 429070 * 2
def baseEnd_429070 : Nat := 220319144424741495351749

theorem tailTrace_429070 : CollatzResearch.WordTrace tailWord_429070 prefixEnd_429070 220319144424741495351749 := by
  unfold tailWord_429070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1956183569445018020880583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10432979037040096111363109 1956183569445018020880583)
  ·
    refine ⟨2934275354167527031320875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1956183569445018020880583 2934275354167527031320875)
    ·
      refine ⟨4401413031251290546981313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2934275354167527031320875 4401413031251290546981313)
      ·
        refine ⟨3301059773438467910235985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4401413031251290546981313 3301059773438467910235985)
        ·
          refine ⟨2475794830078850932676989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3301059773438467910235985 2475794830078850932676989)
          ·
            refine ⟨928423061279569099753871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2475794830078850932676989 928423061279569099753871)
            ·
              refine ⟨1392634591919353649630807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 928423061279569099753871 1392634591919353649630807)
              ·
                refine ⟨2088951887879030474446211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1392634591919353649630807 2088951887879030474446211)
                ·
                  refine ⟨3133427831818545711669317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2088951887879030474446211 3133427831818545711669317)
                  ·
                    refine ⟨587517718465977320937997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3133427831818545711669317 587517718465977320937997)
                    ·
                      refine ⟨220319144424741495351749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 587517718465977320937997 220319144424741495351749)
                      ·
                        rfl

theorem cell23_429070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_429070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429070 prefixEnd_429070 := by exact prefixLift 429070
  have htrace : WordTrace (prefixWord ++ tailWord_429070) baseStart_429070 baseEnd_429070 := by
    simpa [prefixWord, tailWord_429070, baseEnd_429070] using wordTrace_append hprefix tailTrace_429070
  have hstable : (prefixWord ++ tailWord_429070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429070).length < 2 ^ (prefixWord ++ tailWord_429070).sum := by decide
  have hdescent : baseEnd_429070 < baseStart_429070 := by decide
  rcases family_descends (prefixWord ++ tailWord_429070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429077 : List Nat := [1, 3, 2, 1, 4, 1, 1, 5, 1, 4]
def baseStart_429077 : Nat := 118140960795 + 429077 * 2 ^ 59
def prefixEnd_429077 : Nat := 4983230072969 + 3 ^ 40 * 429077 * 2
def baseEnd_429077 : Nat := 73440912929774322654739

theorem tailTrace_429077 : CollatzResearch.WordTrace tailWord_429077 prefixEnd_429077 73440912929774322654739 := by
  unfold tailWord_429077
  simp only [CollatzResearch.WordTrace]
  refine ⟨15649723866534784362549485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10433149244356522908366323 15649723866534784362549485)
  ·
    refine ⟨5868646449950544135956057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15649723866534784362549485 5868646449950544135956057)
    ·
      refine ⟨4401484837462908101967043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5868646449950544135956057 4401484837462908101967043)
      ·
        refine ⟨6602227256194362152950565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4401484837462908101967043 6602227256194362152950565)
        ·
          refine ⟨1237917610536442903678231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6602227256194362152950565 1237917610536442903678231)
          ·
            refine ⟨1856876415804664355517347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1237917610536442903678231 1856876415804664355517347)
            ·
              refine ⟨2785314623706996533276021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1856876415804664355517347 2785314623706996533276021)
              ·
                refine ⟨261123245972530924994627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2785314623706996533276021 261123245972530924994627)
                ·
                  refine ⟨391684868958796387491941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 261123245972530924994627 391684868958796387491941)
                  ·
                    refine ⟨73440912929774322654739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 391684868958796387491941 73440912929774322654739)
                    ·
                      rfl

theorem cell23_429077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_429077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429077 prefixEnd_429077 := by exact prefixLift 429077
  have htrace : WordTrace (prefixWord ++ tailWord_429077) baseStart_429077 baseEnd_429077 := by
    simpa [prefixWord, tailWord_429077, baseEnd_429077] using wordTrace_append hprefix tailTrace_429077
  have hstable : (prefixWord ++ tailWord_429077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429077).length < 2 ^ (prefixWord ++ tailWord_429077).sum := by decide
  have hdescent : baseEnd_429077 < baseStart_429077 := by decide
  rcases family_descends (prefixWord ++ tailWord_429077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429090 : List Nat := [3, 3, 1, 1, 1, 3, 3, 2, 6]
def baseStart_429090 : Nat := 118140960795 + 429090 * 2 ^ 59
def prefixEnd_429090 : Nat := 4983230072969 + 3 ^ 40 * 429090 * 2
def baseEnd_429090 : Nat := 24481046004203490789073

theorem tailTrace_429090 : CollatzResearch.WordTrace tailWord_429090 prefixEnd_429090 24481046004203490789073 := by
  unfold tailWord_429090
  simp only [CollatzResearch.WordTrace]
  refine ⟨3912549503871921895693181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10433465343658458388515149 3912549503871921895693181)
  ·
    refine ⟨1467206063951970710884943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3912549503871921895693181 1467206063951970710884943)
    ·
      refine ⟨2200809095927956066327415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1467206063951970710884943 2200809095927956066327415)
      ·
        refine ⟨3301213643891934099491123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2200809095927956066327415 3301213643891934099491123)
        ·
          refine ⟨4951820465837901149236685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3301213643891934099491123 4951820465837901149236685)
          ·
            refine ⟨1856932674689212930963757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4951820465837901149236685 1856932674689212930963757)
            ·
              refine ⟨696349753008454849111409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1856932674689212930963757 696349753008454849111409)
              ·
                refine ⟨522262314756341136833557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 696349753008454849111409 522262314756341136833557)
                ·
                  refine ⟨24481046004203490789073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 522262314756341136833557 24481046004203490789073)
                  ·
                    rfl

theorem cell23_429090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_429090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429090 prefixEnd_429090 := by exact prefixLift 429090
  have htrace : WordTrace (prefixWord ++ tailWord_429090) baseStart_429090 baseEnd_429090 := by
    simpa [prefixWord, tailWord_429090, baseEnd_429090] using wordTrace_append hprefix tailTrace_429090
  have hstable : (prefixWord ++ tailWord_429090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429090).length < 2 ^ (prefixWord ++ tailWord_429090).sum := by decide
  have hdescent : baseEnd_429090 < baseStart_429090 := by decide
  rcases family_descends (prefixWord ++ tailWord_429090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429117 : List Nat := [1, 4, 1, 3, 1, 2, 2, 2, 3, 1, 3]
def baseStart_429117 : Nat := 118140960795 + 429117 * 2 ^ 59
def prefixEnd_429117 : Nat := 4983230072969 + 3 ^ 40 * 429117 * 2
def baseEnd_429117 : Nat := 220343278015502811464033

theorem tailTrace_429117 : CollatzResearch.WordTrace tailWord_429117 prefixEnd_429117 220343278015502811464033 := by
  unfold tailWord_429117
  simp only [CollatzResearch.WordTrace]
  refine ⟨15651182786389871194005605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10434121857593247462670403 15651182786389871194005605)
  ·
    refine ⟨2934596772448100848876051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15651182786389871194005605 2934596772448100848876051)
    ·
      refine ⟨4401895158672151273314077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2934596772448100848876051 4401895158672151273314077)
      ·
        refine ⟨1650710684502056727492779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4401895158672151273314077 1650710684502056727492779)
        ·
          refine ⟨2476066026753085091239169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1650710684502056727492779 2476066026753085091239169)
          ·
            refine ⟨1857049520064813818429377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2476066026753085091239169 1857049520064813818429377)
            ·
              refine ⟨1392787140048610363822033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1857049520064813818429377 1392787140048610363822033)
              ·
                refine ⟨1044590355036457772866525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1392787140048610363822033 1044590355036457772866525)
                ·
                  refine ⟨391721383138671664824947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1044590355036457772866525 391721383138671664824947)
                  ·
                    refine ⟨587582074708007497237421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 391721383138671664824947 587582074708007497237421)
                    ·
                      refine ⟨220343278015502811464033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 587582074708007497237421 220343278015502811464033)
                      ·
                        rfl

theorem cell23_429117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_429117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429117 prefixEnd_429117 := by exact prefixLift 429117
  have htrace : WordTrace (prefixWord ++ tailWord_429117) baseStart_429117 baseEnd_429117 := by
    simpa [prefixWord, tailWord_429117, baseEnd_429117] using wordTrace_append hprefix tailTrace_429117
  have hstable : (prefixWord ++ tailWord_429117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429117).length < 2 ^ (prefixWord ++ tailWord_429117).sum := by decide
  have hdescent : baseEnd_429117 < baseStart_429117 := by decide
  rcases family_descends (prefixWord ++ tailWord_429117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429120 : List Nat := [2, 1, 1, 2, 2, 3, 4, 2, 1, 5]
def baseStart_429120 : Nat := 118140960795 + 429120 * 2 ^ 59
def prefixEnd_429120 : Nat := 4983230072969 + 3 ^ 40 * 429120 * 2
def baseEnd_429120 : Nat := 73448272819155433242173

theorem tailTrace_429120 : CollatzResearch.WordTrace tailWord_429120 prefixEnd_429120 73448272819155433242173 := by
  unfold tailWord_429120
  simp only [CollatzResearch.WordTrace]
  refine ⟨7825646102689501353182407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10434194803586001804243209 7825646102689501353182407)
  ·
    refine ⟨11738469154034252029773611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7825646102689501353182407 11738469154034252029773611)
    ·
      refine ⟨17607703731051378044660417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11738469154034252029773611 17607703731051378044660417)
      ·
        refine ⟨13205777798288533533495313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17607703731051378044660417 13205777798288533533495313)
        ·
          refine ⟨9904333348716400150121485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13205777798288533533495313 9904333348716400150121485)
          ·
            refine ⟨3714125005768650056295557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9904333348716400150121485 3714125005768650056295557)
            ·
              refine ⟨696398438581621885555417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3714125005768650056295557 696398438581621885555417)
              ·
                refine ⟨522298828936216414166563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 696398438581621885555417 522298828936216414166563)
                ·
                  refine ⟨783448243404324621249845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 522298828936216414166563 783448243404324621249845)
                  ·
                    refine ⟨73448272819155433242173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 783448243404324621249845 73448272819155433242173)
                    ·
                      rfl

theorem cell23_429120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 1, 5].length) (baseStart_429120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429120 prefixEnd_429120 := by exact prefixLift 429120
  have htrace : WordTrace (prefixWord ++ tailWord_429120) baseStart_429120 baseEnd_429120 := by
    simpa [prefixWord, tailWord_429120, baseEnd_429120] using wordTrace_append hprefix tailTrace_429120
  have hstable : (prefixWord ++ tailWord_429120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429120).length < 2 ^ (prefixWord ++ tailWord_429120).sum := by decide
  have hdescent : baseEnd_429120 < baseStart_429120 := by decide
  rcases family_descends (prefixWord ++ tailWord_429120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429153 : List Nat := [1, 2, 3, 1, 1, 2, 3, 2, 1, 1, 6]
def baseStart_429153 : Nat := 118140960795 + 429153 * 2 ^ 59
def prefixEnd_429153 : Nat := 4983230072969 + 3 ^ 40 * 429153 * 2
def baseEnd_429153 : Nat := 220361763319064670613867

theorem tailTrace_429153 : CollatzResearch.WordTrace tailWord_429153 prefixEnd_429153 220361763319064670613867 := by
  unfold tailWord_429153
  simp only [CollatzResearch.WordTrace]
  refine ⟨15652495814259449342316113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10434997209506299561544075 15652495814259449342316113)
  ·
    refine ⟨11739371860694587006737085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15652495814259449342316113 11739371860694587006737085)
    ·
      refine ⟨4402264447760470127526407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11739371860694587006737085 4402264447760470127526407)
      ·
        refine ⟨6603396671640705191289611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4402264447760470127526407 6603396671640705191289611)
        ·
          refine ⟨9905095007461057786934417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6603396671640705191289611 9905095007461057786934417)
          ·
            refine ⟨7428821255595793340200813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9905095007461057786934417 7428821255595793340200813)
            ·
              refine ⟨2785807970848422502575305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7428821255595793340200813 2785807970848422502575305)
              ·
                refine ⟨2089355978136316876931479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2785807970848422502575305 2089355978136316876931479)
                ·
                  refine ⟨3134033967204475315397219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2089355978136316876931479 3134033967204475315397219)
                  ·
                    refine ⟨4701050950806712973095829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3134033967204475315397219 4701050950806712973095829)
                    ·
                      refine ⟨220361763319064670613867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4701050950806712973095829 220361763319064670613867)
                      ·
                        rfl

theorem cell23_429153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_429153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429153 prefixEnd_429153 := by exact prefixLift 429153
  have htrace : WordTrace (prefixWord ++ tailWord_429153) baseStart_429153 baseEnd_429153 := by
    simpa [prefixWord, tailWord_429153, baseEnd_429153] using wordTrace_append hprefix tailTrace_429153
  have hstable : (prefixWord ++ tailWord_429153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429153).length < 2 ^ (prefixWord ++ tailWord_429153).sum := by decide
  have hdescent : baseEnd_429153 < baseStart_429153 := by decide
  rcases family_descends (prefixWord ++ tailWord_429153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429170 : List Nat := [3, 2, 1, 2, 2, 1, 2, 3, 1, 2, 4]
def baseStart_429170 : Nat := 118140960795 + 429170 * 2 ^ 59
def prefixEnd_429170 : Nat := 4983230072969 + 3 ^ 40 * 429170 * 2
def baseEnd_429170 : Nat := 220370492490191104101289

theorem tailTrace_429170 : CollatzResearch.WordTrace tailWord_429170 prefixEnd_429170 220370492490191104101289 := by
  unfold tailWord_429170
  simp only [CollatzResearch.WordTrace]
  refine ⟨3913278963799465311421241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10435410570131907497123309 3913278963799465311421241)
  ·
    refine ⟨2934959222849598983565931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3913278963799465311421241 2934959222849598983565931)
    ·
      refine ⟨4402438834274398475348897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2934959222849598983565931 4402438834274398475348897)
      ·
        refine ⟨3301829125705798856511673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4402438834274398475348897 3301829125705798856511673)
        ·
          refine ⟨2476371844279349142383755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3301829125705798856511673 2476371844279349142383755)
          ·
            refine ⟨3714557766419023713575633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2476371844279349142383755 3714557766419023713575633)
            ·
              refine ⟨2785918324814267785181725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3714557766419023713575633 2785918324814267785181725)
              ·
                refine ⟨1044719371805350419443147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2785918324814267785181725 1044719371805350419443147)
                ·
                  refine ⟨1567079057708025629164721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1044719371805350419443147 1567079057708025629164721)
                  ·
                    refine ⟨1175309293281019221873541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1567079057708025629164721 1175309293281019221873541)
                    ·
                      refine ⟨220370492490191104101289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1175309293281019221873541 220370492490191104101289)
                      ·
                        rfl

theorem cell23_429170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_429170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429170 prefixEnd_429170 := by exact prefixLift 429170
  have htrace : WordTrace (prefixWord ++ tailWord_429170) baseStart_429170 baseEnd_429170 := by
    simpa [prefixWord, tailWord_429170, baseEnd_429170] using wordTrace_append hprefix tailTrace_429170
  have hstable : (prefixWord ++ tailWord_429170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429170).length < 2 ^ (prefixWord ++ tailWord_429170).sum := by decide
  have hdescent : baseEnd_429170 < baseStart_429170 := by decide
  rcases family_descends (prefixWord ++ tailWord_429170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429174 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2]
def baseStart_429174 : Nat := 118140960795 + 429174 * 2 ^ 59
def prefixEnd_429174 : Nat := 4983230072969 + 3 ^ 40 * 429174 * 2
def baseEnd_429174 : Nat := 220372546412809088451271

theorem tailTrace_429174 : CollatzResearch.WordTrace tailWord_429174 prefixEnd_429174 220372546412809088451271 := by
  unfold tailWord_429174
  simp only [CollatzResearch.WordTrace]
  refine ⟨978328859198960620551911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10435507831455579952553717 978328859198960620551911)
  ·
    refine ⟨1467493288798440930827867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 978328859198960620551911 1467493288798440930827867)
    ·
      refine ⟨2201239933197661396241801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1467493288798440930827867 2201239933197661396241801)
      ·
        refine ⟨1650929949898246047181351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2201239933197661396241801 1650929949898246047181351)
        ·
          refine ⟨2476394924847369070772027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1650929949898246047181351 2476394924847369070772027)
          ·
            refine ⟨3714592387271053606158041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2476394924847369070772027 3714592387271053606158041)
            ·
              refine ⟨2785944290453290204618531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3714592387271053606158041 2785944290453290204618531)
              ·
                refine ⟨4178916435679935306927797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2785944290453290204618531 4178916435679935306927797)
                ·
                  refine ⟨391773415844993935024481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4178916435679935306927797 391773415844993935024481)
                  ·
                    refine ⟨293830061883745451268361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 391773415844993935024481 293830061883745451268361)
                    ·
                      refine ⟨220372546412809088451271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 293830061883745451268361 220372546412809088451271)
                      ·
                        rfl

theorem cell23_429174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_429174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429174 prefixEnd_429174 := by exact prefixLift 429174
  have htrace : WordTrace (prefixWord ++ tailWord_429174) baseStart_429174 baseEnd_429174 := by
    simpa [prefixWord, tailWord_429174, baseEnd_429174] using wordTrace_append hprefix tailTrace_429174
  have hstable : (prefixWord ++ tailWord_429174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429174).length < 2 ^ (prefixWord ++ tailWord_429174).sum := by decide
  have hdescent : baseEnd_429174 < baseStart_429174 := by decide
  rcases family_descends (prefixWord ++ tailWord_429174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429177 : List Nat := [1, 2, 1, 3, 5, 1, 1, 1, 3, 2, 3]
def baseStart_429177 : Nat := 118140960795 + 429177 * 2 ^ 59
def prefixEnd_429177 : Nat := 4983230072969 + 3 ^ 40 * 429177 * 2
def baseEnd_429177 : Nat := 220374086854772576713757

theorem tailTrace_429177 : CollatzResearch.WordTrace tailWord_429177 prefixEnd_429177 220374086854772576713757 := by
  unfold tailWord_429177
  simp only [CollatzResearch.WordTrace]
  refine ⟨15653371166172501441189785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10435580777448334294126523 15653371166172501441189785)
  ·
    refine ⟨11740028374629376080892339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15653371166172501441189785 11740028374629376080892339)
    ·
      refine ⟨17610042561944064121338509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11740028374629376080892339 17610042561944064121338509)
      ·
        refine ⟨6603765960729024045501941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17610042561944064121338509 6603765960729024045501941)
        ·
          refine ⟨619103058818346004265807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6603765960729024045501941 619103058818346004265807)
          ·
            refine ⟨928654588227519006398711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619103058818346004265807 928654588227519006398711)
            ·
              refine ⟨1392981882341278509598067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 928654588227519006398711 1392981882341278509598067)
              ·
                refine ⟨2089472823511917764397101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1392981882341278509598067 2089472823511917764397101)
                ·
                  refine ⟨783552308816969161648913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2089472823511917764397101 783552308816969161648913)
                  ·
                    refine ⟨587664231612726871236685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 783552308816969161648913 587664231612726871236685)
                    ·
                      refine ⟨220374086854772576713757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 587664231612726871236685 220374086854772576713757)
                      ·
                        rfl

theorem cell23_429177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_429177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429177 prefixEnd_429177 := by exact prefixLift 429177
  have htrace : WordTrace (prefixWord ++ tailWord_429177) baseStart_429177 baseEnd_429177 := by
    simpa [prefixWord, tailWord_429177, baseEnd_429177] using wordTrace_append hprefix tailTrace_429177
  have hstable : (prefixWord ++ tailWord_429177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429177).length < 2 ^ (prefixWord ++ tailWord_429177).sum := by decide
  have hdescent : baseEnd_429177 < baseStart_429177 := by decide
  rcases family_descends (prefixWord ++ tailWord_429177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429194 : List Nat := [3, 1, 2, 3, 1, 1, 5, 1, 1, 2, 3]
def baseStart_429194 : Nat := 118140960795 + 429194 * 2 ^ 59
def prefixEnd_429194 : Nat := 4983230072969 + 3 ^ 40 * 429194 * 2
def baseEnd_429194 : Nat := 220382816025899010201179

theorem tailTrace_429194 : CollatzResearch.WordTrace tailWord_429194 prefixEnd_429194 220382816025899010201179 := by
  unfold tailWord_429194
  simp only [CollatzResearch.WordTrace]
  refine ⟨3913497801777728336139659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10435994138073942229705757 3913497801777728336139659)
  ·
    refine ⟨5870246702666592504209489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3913497801777728336139659 5870246702666592504209489)
    ·
      refine ⟨4402685026999944378157117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5870246702666592504209489 4402685026999944378157117)
      ·
        refine ⟨1651006885124979141808919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4402685026999944378157117 1651006885124979141808919)
        ·
          refine ⟨2476510327687468712713379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1651006885124979141808919 2476510327687468712713379)
          ·
            refine ⟨3714765491531203069070069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2476510327687468712713379 3714765491531203069070069)
            ·
              refine ⟨348259264831050287725319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3714765491531203069070069 348259264831050287725319)
              ·
                refine ⟨522388897246575431587979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 348259264831050287725319 522388897246575431587979)
                ·
                  refine ⟨783583345869863147381969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 522388897246575431587979 783583345869863147381969)
                  ·
                    refine ⟨587687509402397360536477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 783583345869863147381969 587687509402397360536477)
                    ·
                      refine ⟨220382816025899010201179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 587687509402397360536477 220382816025899010201179)
                      ·
                        rfl

theorem cell23_429194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_429194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429194 prefixEnd_429194 := by exact prefixLift 429194
  have htrace : WordTrace (prefixWord ++ tailWord_429194) baseStart_429194 baseEnd_429194 := by
    simpa [prefixWord, tailWord_429194, baseEnd_429194] using wordTrace_append hprefix tailTrace_429194
  have hstable : (prefixWord ++ tailWord_429194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429194).length < 2 ^ (prefixWord ++ tailWord_429194).sum := by decide
  have hdescent : baseEnd_429194 < baseStart_429194 := by decide
  rcases family_descends (prefixWord ++ tailWord_429194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429203 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 5]
def baseStart_429203 : Nat := 118140960795 + 429203 * 2 ^ 59
def prefixEnd_429203 : Nat := 4983230072969 + 3 ^ 40 * 429203 * 2
def baseEnd_429203 : Nat := 220387437351789474988637

theorem tailTrace_429203 : CollatzResearch.WordTrace tailWord_429203 prefixEnd_429203 220387437351789474988637 := by
  unfold tailWord_429203
  simp only [CollatzResearch.WordTrace]
  refine ⟨15654319464078307881636263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10436212976052205254424175 15654319464078307881636263)
  ·
    refine ⟨23481479196117461822454395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15654319464078307881636263 23481479196117461822454395)
    ·
      refine ⟨35222218794176192733681593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23481479196117461822454395 35222218794176192733681593)
      ·
        refine ⟨26416664095632144550261195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35222218794176192733681593 26416664095632144550261195)
        ·
          refine ⟨39624996143448216825391793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26416664095632144550261195 39624996143448216825391793)
          ·
            refine ⟨29718747107586162619043845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39624996143448216825391793 29718747107586162619043845)
            ·
              refine ⟨5572265082672405491070721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29718747107586162619043845 5572265082672405491070721)
              ·
                refine ⟨4179198812004304118303041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5572265082672405491070721 4179198812004304118303041)
                ·
                  refine ⟨3134399109003228088727281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4179198812004304118303041 3134399109003228088727281)
                  ·
                    refine ⟨2350799331752421066545461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3134399109003228088727281 2350799331752421066545461)
                    ·
                      refine ⟨220387437351789474988637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2350799331752421066545461 220387437351789474988637)
                      ·
                        rfl

theorem cell23_429203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 5].length) (baseStart_429203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429203 prefixEnd_429203 := by exact prefixLift 429203
  have htrace : WordTrace (prefixWord ++ tailWord_429203) baseStart_429203 baseEnd_429203 := by
    simpa [prefixWord, tailWord_429203, baseEnd_429203] using wordTrace_append hprefix tailTrace_429203
  have hstable : (prefixWord ++ tailWord_429203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429203).length < 2 ^ (prefixWord ++ tailWord_429203).sum := by decide
  have hdescent : baseEnd_429203 < baseStart_429203 := by decide
  rcases family_descends (prefixWord ++ tailWord_429203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429208 : List Nat := [2, 1, 2, 4, 2, 1, 4, 2, 1, 2, 2]
def baseStart_429208 : Nat := 118140960795 + 429208 * 2 ^ 59
def prefixEnd_429208 : Nat := 4983230072969 + 3 ^ 40 * 429208 * 2
def baseEnd_429208 : Nat := 220390004755061955426115

theorem tailTrace_429208 : CollatzResearch.WordTrace tailWord_429208 prefixEnd_429208 220390004755061955426115 := by
  unfold tailWord_429208
  simp only [CollatzResearch.WordTrace]
  refine ⟨7827250914530096867784139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10436334552706795823712185 7827250914530096867784139)
  ·
    refine ⟨11740876371795145301676209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7827250914530096867784139 11740876371795145301676209)
    ·
      refine ⟨8805657278846358976257157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11740876371795145301676209 8805657278846358976257157)
      ·
        refine ⟨1651060739783692308048217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8805657278846358976257157 1651060739783692308048217)
        ·
          refine ⟨1238295554837769231036163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1651060739783692308048217 1238295554837769231036163)
          ·
            refine ⟨1857443332256653846554245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1238295554837769231036163 1857443332256653846554245)
            ·
              refine ⟨348270624798122596228921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1857443332256653846554245 348270624798122596228921)
              ·
                refine ⟨261202968598591947171691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 348270624798122596228921 261202968598591947171691)
                ·
                  refine ⟨391804452897887920757537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 261202968598591947171691 391804452897887920757537)
                  ·
                    refine ⟨293853339673415940568153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 391804452897887920757537 293853339673415940568153)
                    ·
                      refine ⟨220390004755061955426115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 293853339673415940568153 220390004755061955426115)
                      ·
                        rfl

theorem cell23_429208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_429208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429208 prefixEnd_429208 := by exact prefixLift 429208
  have htrace : WordTrace (prefixWord ++ tailWord_429208) baseStart_429208 baseEnd_429208 := by
    simpa [prefixWord, tailWord_429208, baseEnd_429208] using wordTrace_append hprefix tailTrace_429208
  have hstable : (prefixWord ++ tailWord_429208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429208).length < 2 ^ (prefixWord ++ tailWord_429208).sum := by decide
  have hdescent : baseEnd_429208 < baseStart_429208 := by decide
  rcases family_descends (prefixWord ++ tailWord_429208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429210 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 2, 7]
def baseStart_429210 : Nat := 118140960795 + 429210 * 2 ^ 59
def prefixEnd_429210 : Nat := 4983230072969 + 3 ^ 40 * 429210 * 2
def baseEnd_429210 : Nat := 73463677238790315867035

theorem tailTrace_429210 : CollatzResearch.WordTrace tailWord_429210 prefixEnd_429210 73463677238790315867035 := by
  unfold tailWord_429210
  simp only [CollatzResearch.WordTrace]
  refine ⟨3913643693763237019285271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10436383183368632051427389 3913643693763237019285271)
  ·
    refine ⟨5870465540644855528927907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3913643693763237019285271 5870465540644855528927907)
    ·
      refine ⟨8805698310967283293391861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5870465540644855528927907 8805698310967283293391861)
      ·
        refine ⟨825534216653182808755487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8805698310967283293391861 825534216653182808755487)
        ·
          refine ⟨1238301324979774213133231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 825534216653182808755487 1238301324979774213133231)
          ·
            refine ⟨1857451987469661319699847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1238301324979774213133231 1857451987469661319699847)
            ·
              refine ⟨2786177981204491979549771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1857451987469661319699847 2786177981204491979549771)
              ·
                refine ⟨4179266971806737969324657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2786177981204491979549771 4179266971806737969324657)
                ·
                  refine ⟨3134450228855053476993493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4179266971806737969324657 3134450228855053476993493)
                  ·
                    refine ⟨73463677238790315867035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3134450228855053476993493 73463677238790315867035)
                    ·
                      rfl

theorem cell23_429210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 2, 7].length) (baseStart_429210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429210 prefixEnd_429210 := by exact prefixLift 429210
  have htrace : WordTrace (prefixWord ++ tailWord_429210) baseStart_429210 baseEnd_429210 := by
    simpa [prefixWord, tailWord_429210, baseEnd_429210] using wordTrace_append hprefix tailTrace_429210
  have hstable : (prefixWord ++ tailWord_429210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429210).length < 2 ^ (prefixWord ++ tailWord_429210).sum := by decide
  have hdescent : baseEnd_429210 < baseStart_429210 := by decide
  rcases family_descends (prefixWord ++ tailWord_429210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429217 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 5, 3, 2]
def baseStart_429217 : Nat := 118140960795 + 429217 * 2 ^ 59
def prefixEnd_429217 : Nat := 4983230072969 + 3 ^ 40 * 429217 * 2
def baseEnd_429217 : Nat := 220394626080952420213573

theorem tailTrace_429217 : CollatzResearch.WordTrace tailWord_429217 prefixEnd_429217 220394626080952420213573 := by
  unfold tailWord_429217
  simp only [CollatzResearch.WordTrace]
  refine ⟨15654830086027588272645905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10436553390685058848430603 15654830086027588272645905)
  ·
    refine ⟨11741122564520691204484429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15654830086027588272645905 11741122564520691204484429)
    ·
      refine ⟨4402920961695259201681661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11741122564520691204484429 4402920961695259201681661)
      ·
        refine ⟨1651095360635722200630623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4402920961695259201681661 1651095360635722200630623)
        ·
          refine ⟨2476643040953583300945935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1651095360635722200630623 2476643040953583300945935)
          ·
            refine ⟨3714964561430374951418903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2476643040953583300945935 3714964561430374951418903)
            ·
              refine ⟨5572446842145562427128355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3714964561430374951418903 5572446842145562427128355)
              ·
                refine ⟨8358670263218343640692533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5572446842145562427128355 8358670263218343640692533)
                ·
                  refine ⟨783625337176719716314925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8358670263218343640692533 783625337176719716314925)
                  ·
                    refine ⟨293859501441269893618097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 783625337176719716314925 293859501441269893618097)
                    ·
                      refine ⟨220394626080952420213573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 293859501441269893618097 220394626080952420213573)
                      ·
                        rfl

theorem cell23_429217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_429217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429217 prefixEnd_429217 := by exact prefixLift 429217
  have htrace : WordTrace (prefixWord ++ tailWord_429217) baseStart_429217 baseEnd_429217 := by
    simpa [prefixWord, tailWord_429217, baseEnd_429217] using wordTrace_append hprefix tailTrace_429217
  have hstable : (prefixWord ++ tailWord_429217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429217).length < 2 ^ (prefixWord ++ tailWord_429217).sum := by decide
  have hdescent : baseEnd_429217 < baseStart_429217 := by decide
  rcases family_descends (prefixWord ++ tailWord_429217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429247 : List Nat := [1, 1, 2, 2, 2, 2, 4, 2, 1, 4, 2]
def baseStart_429247 : Nat := 118140960795 + 429247 * 2 ^ 59
def prefixEnd_429247 : Nat := 4983230072969 + 3 ^ 40 * 429247 * 2
def baseEnd_429247 : Nat := 220410030500587302838435

theorem tailTrace_429247 : CollatzResearch.WordTrace tailWord_429247 prefixEnd_429247 220410030500587302838435 := by
  unfold tailWord_429247
  simp only [CollatzResearch.WordTrace]
  refine ⟨15655924275918903396237995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10437282850612602264158663 15655924275918903396237995)
  ·
    refine ⟨23483886413878355094356993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15655924275918903396237995 23483886413878355094356993)
    ·
      refine ⟨17612914810408766320767745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23483886413878355094356993 17612914810408766320767745)
      ·
        refine ⟨13209686107806574740575809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17612914810408766320767745 13209686107806574740575809)
        ·
          refine ⟨9907264580854931055431857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13209686107806574740575809 9907264580854931055431857)
          ·
            refine ⟨7430448435641198291573893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9907264580854931055431857 7430448435641198291573893)
            ·
              refine ⟨1393209081682724679670105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7430448435641198291573893 1393209081682724679670105)
              ·
                refine ⟨1044906811262043509752579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1393209081682724679670105 1044906811262043509752579)
                ·
                  refine ⟨1567360216893065264628869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1044906811262043509752579 1567360216893065264628869)
                  ·
                    refine ⟨293880040667449737117913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1567360216893065264628869 293880040667449737117913)
                    ·
                      refine ⟨220410030500587302838435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 293880040667449737117913 220410030500587302838435)
                      ·
                        rfl

theorem cell23_429247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 4, 2].length) (baseStart_429247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429247 prefixEnd_429247 := by exact prefixLift 429247
  have htrace : WordTrace (prefixWord ++ tailWord_429247) baseStart_429247 baseEnd_429247 := by
    simpa [prefixWord, tailWord_429247, baseEnd_429247] using wordTrace_append hprefix tailTrace_429247
  have hstable : (prefixWord ++ tailWord_429247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429247).length < 2 ^ (prefixWord ++ tailWord_429247).sum := by decide
  have hdescent : baseEnd_429247 < baseStart_429247 := by decide
  rcases family_descends (prefixWord ++ tailWord_429247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429253 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 11]
def baseStart_429253 : Nat := 118140960795 + 429253 * 2 ^ 59
def prefixEnd_429253 : Nat := 4983230072969 + 3 ^ 40 * 429253 * 2
def baseEnd_429253 : Nat := 24490345709390475484823

theorem tailTrace_429253 : CollatzResearch.WordTrace tailWord_429253 prefixEnd_429253 24490345709390475484823 := by
  unfold tailWord_429253
  simp only [CollatzResearch.WordTrace]
  refine ⟨15656143113897166420956413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10437428742598110947304275 15656143113897166420956413)
  ·
    refine ⟨5871053667711437407858655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15656143113897166420956413 5871053667711437407858655)
    ·
      refine ⟨8806580501567156111787983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5871053667711437407858655 8806580501567156111787983)
      ·
        refine ⟨13209870752350734167681975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8806580501567156111787983 13209870752350734167681975)
        ·
          refine ⟨19814806128526101251522963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13209870752350734167681975 19814806128526101251522963)
          ·
            refine ⟨29722209192789151877284445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19814806128526101251522963 29722209192789151877284445)
            ·
              refine ⟨11145828447295931953981667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29722209192789151877284445 11145828447295931953981667)
              ·
                refine ⟨16718742670943897930972501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11145828447295931953981667 16718742670943897930972501)
                ·
                  refine ⟨24490345709390475484823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 16718742670943897930972501 24490345709390475484823)
                  ·
                    rfl

theorem cell23_429253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 11].length) (baseStart_429253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429253 prefixEnd_429253 := by exact prefixLift 429253
  have htrace : WordTrace (prefixWord ++ tailWord_429253) baseStart_429253 baseEnd_429253 := by
    simpa [prefixWord, tailWord_429253, baseEnd_429253] using wordTrace_append hprefix tailTrace_429253
  have hstable : (prefixWord ++ tailWord_429253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429253).length < 2 ^ (prefixWord ++ tailWord_429253).sum := by decide
  have hdescent : baseEnd_429253 < baseStart_429253 := by decide
  rcases family_descends (prefixWord ++ tailWord_429253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429263 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 9]
def baseStart_429263 : Nat := 118140960795 + 429263 * 2 ^ 59
def prefixEnd_429263 : Nat := 4983230072969 + 3 ^ 40 * 429263 * 2
def baseEnd_429263 : Nat := 220418246191059240238361

theorem tailTrace_429263 : CollatzResearch.WordTrace tailWord_429263 prefixEnd_429263 220418246191059240238361 := by
  unfold tailWord_429263
  simp only [CollatzResearch.WordTrace]
  refine ⟨15656507843860938128820443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10437671895907292085880295 15656507843860938128820443)
  ·
    refine ⟨23484761765791407193230665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15656507843860938128820443 23484761765791407193230665)
    ·
      refine ⟨17613571324343555394922999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23484761765791407193230665 17613571324343555394922999)
      ·
        refine ⟨26420356986515333092384499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17613571324343555394922999 26420356986515333092384499)
        ·
          refine ⟨39630535479772999638576749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26420356986515333092384499 39630535479772999638576749)
          ·
            refine ⟨14861450804914874864466281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39630535479772999638576749 14861450804914874864466281)
            ·
              refine ⟨11146088103686156148349711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14861450804914874864466281 11146088103686156148349711)
              ·
                refine ⟨16719132155529234222524567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11146088103686156148349711 16719132155529234222524567)
                ·
                  refine ⟨25078698233293851333786851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16719132155529234222524567 25078698233293851333786851)
                  ·
                    refine ⟨37618047349940777000680277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25078698233293851333786851 37618047349940777000680277)
                    ·
                      refine ⟨220418246191059240238361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 37618047349940777000680277 220418246191059240238361)
                      ·
                        rfl

theorem cell23_429263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 9].length) (baseStart_429263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429263 prefixEnd_429263 := by exact prefixLift 429263
  have htrace : WordTrace (prefixWord ++ tailWord_429263) baseStart_429263 baseEnd_429263 := by
    simpa [prefixWord, tailWord_429263, baseEnd_429263] using wordTrace_append hprefix tailTrace_429263
  have hstable : (prefixWord ++ tailWord_429263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429263).length < 2 ^ (prefixWord ++ tailWord_429263).sum := by decide
  have hdescent : baseEnd_429263 < baseStart_429263 := by decide
  rcases family_descends (prefixWord ++ tailWord_429263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429354 : List Nat := [3, 1, 4, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_429354 : Nat := 118140960795 + 429354 * 2 ^ 59
def prefixEnd_429354 : Nat := 4983230072969 + 3 ^ 40 * 429354 * 2
def baseEnd_429354 : Nat := 220464972930618384200443

theorem tailTrace_429354 : CollatzResearch.WordTrace tailWord_429354 prefixEnd_429354 220464972930618384200443 := by
  unfold tailWord_429354
  simp only [CollatzResearch.WordTrace]
  refine ⟨3914956721632815167595779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10439884591020840446922077 3914956721632815167595779)
  ·
    refine ⟨5872435082449222751393669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3914956721632815167595779 5872435082449222751393669)
    ·
      refine ⟨1101081577959229265886313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5872435082449222751393669 1101081577959229265886313)
      ·
        refine ⟨825811183469421949414735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1101081577959229265886313 825811183469421949414735)
        ·
          refine ⟨1238716775204132924122103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 825811183469421949414735 1238716775204132924122103)
          ·
            refine ⟨1858075162806199386183155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1238716775204132924122103 1858075162806199386183155)
            ·
              refine ⟨2787112744209299079274733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1858075162806199386183155 2787112744209299079274733)
              ·
                refine ⟨1045167279078487154728025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2787112744209299079274733 1045167279078487154728025)
                ·
                  refine ⟨783875459308865366046019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1045167279078487154728025 783875459308865366046019)
                  ·
                    refine ⟨1175813188963298049069029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 783875459308865366046019 1175813188963298049069029)
                    ·
                      refine ⟨220464972930618384200443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1175813188963298049069029 220464972930618384200443)
                      ·
                        rfl

theorem cell23_429354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_429354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429354 prefixEnd_429354 := by exact prefixLift 429354
  have htrace : WordTrace (prefixWord ++ tailWord_429354) baseStart_429354 baseEnd_429354 := by
    simpa [prefixWord, tailWord_429354, baseEnd_429354] using wordTrace_append hprefix tailTrace_429354
  have hstable : (prefixWord ++ tailWord_429354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429354).length < 2 ^ (prefixWord ++ tailWord_429354).sum := by decide
  have hdescent : baseEnd_429354 < baseStart_429354 := by decide
  rcases family_descends (prefixWord ++ tailWord_429354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429374 : List Nat := [4, 2, 1, 2, 1, 1, 1, 4, 2, 2, 3]
def baseStart_429374 : Nat := 118140960795 + 429374 * 2 ^ 59
def prefixEnd_429374 : Nat := 4983230072969 + 3 ^ 40 * 429374 * 2
def baseEnd_429374 : Nat := 220475242543708305950351

theorem tailTrace_429374 : CollatzResearch.WordTrace tailWord_429374 prefixEnd_429374 220475242543708305950351 := by
  unfold tailWord_429374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1957569543307350510763897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10440370897639202724074117 1957569543307350510763897)
  ·
    refine ⟨1468177157480512883072923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1957569543307350510763897 1468177157480512883072923)
    ·
      refine ⟨2202265736220769324609385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1468177157480512883072923 2202265736220769324609385)
      ·
        refine ⟨1651699302165576993457039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2202265736220769324609385 1651699302165576993457039)
        ·
          refine ⟨2477548953248365490185559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1651699302165576993457039 2477548953248365490185559)
          ·
            refine ⟨3716323429872548235278339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2477548953248365490185559 3716323429872548235278339)
            ·
              refine ⟨5574485144808822352917509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3716323429872548235278339 5574485144808822352917509)
              ·
                refine ⟨1045215964651654191172033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5574485144808822352917509 1045215964651654191172033)
                ·
                  refine ⟨783911973488740643379025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1045215964651654191172033 783911973488740643379025)
                  ·
                    refine ⟨587933980116555482534269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 783911973488740643379025 587933980116555482534269)
                    ·
                      refine ⟨220475242543708305950351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 587933980116555482534269 220475242543708305950351)
                      ·
                        rfl

theorem cell23_429374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_429374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429374 prefixEnd_429374 := by exact prefixLift 429374
  have htrace : WordTrace (prefixWord ++ tailWord_429374) baseStart_429374 baseEnd_429374 := by
    simpa [prefixWord, tailWord_429374, baseEnd_429374] using wordTrace_append hprefix tailTrace_429374
  have hstable : (prefixWord ++ tailWord_429374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429374).length < 2 ^ (prefixWord ++ tailWord_429374).sum := by decide
  have hdescent : baseEnd_429374 < baseStart_429374 := by decide
  rcases family_descends (prefixWord ++ tailWord_429374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429400 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 2, 1, 7]
def baseStart_429400 : Nat := 118140960795 + 429400 * 2 ^ 59
def prefixEnd_429400 : Nat := 4983230072969 + 3 ^ 40 * 429400 * 2
def baseEnd_429400 : Nat := 220488593040725204225231

theorem tailTrace_429400 : CollatzResearch.WordTrace tailWord_429400 prefixEnd_429400 220488593040725204225231 := by
  unfold tailWord_429400
  simp only [CollatzResearch.WordTrace]
  refine ⟨7830752322182305263278827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10441003096243073684371769 7830752322182305263278827)
  ·
    refine ⟨11746128483273457894918241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7830752322182305263278827 11746128483273457894918241)
    ·
      refine ⟨8809596362455093421188681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11746128483273457894918241 8809596362455093421188681)
      ·
        refine ⟨6607197271841320065891511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8809596362455093421188681 6607197271841320065891511)
        ·
          refine ⟨9910795907761980098837267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6607197271841320065891511 9910795907761980098837267)
          ·
            refine ⟨14866193861642970148255901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9910795907761980098837267 14866193861642970148255901)
            ·
              refine ⟨5574822698116113805595963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14866193861642970148255901 5574822698116113805595963)
              ·
                refine ⟨8362234047174170708393945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5574822698116113805595963 8362234047174170708393945)
                ·
                  refine ⟨6271675535380628031295459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8362234047174170708393945 6271675535380628031295459)
                  ·
                    refine ⟨9407513303070942046943189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6271675535380628031295459 9407513303070942046943189)
                    ·
                      refine ⟨220488593040725204225231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 9407513303070942046943189 220488593040725204225231)
                      ·
                        rfl

theorem cell23_429400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_429400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429400 prefixEnd_429400 := by exact prefixLift 429400
  have htrace : WordTrace (prefixWord ++ tailWord_429400) baseStart_429400 baseEnd_429400 := by
    simpa [prefixWord, tailWord_429400, baseEnd_429400] using wordTrace_append hprefix tailTrace_429400
  have hstable : (prefixWord ++ tailWord_429400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429400).length < 2 ^ (prefixWord ++ tailWord_429400).sum := by decide
  have hdescent : baseEnd_429400 < baseStart_429400 := by decide
  rcases family_descends (prefixWord ++ tailWord_429400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429405 : List Nat := [1, 4, 5, 1, 1, 2, 1, 1, 2, 1, 4]
def baseStart_429405 : Nat := 118140960795 + 429405 * 2 ^ 59
def prefixEnd_429405 : Nat := 4983230072969 + 3 ^ 40 * 429405 * 2
def baseEnd_429405 : Nat := 220491160443997684662709

theorem tailTrace_429405 : CollatzResearch.WordTrace tailWord_429405 prefixEnd_429405 220491160443997684662709 := by
  unfold tailWord_429405
  simp only [CollatzResearch.WordTrace]
  refine ⟨15661687009346496380489669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10441124672897664253659779 15661687009346496380489669)
  ·
    refine ⟨2936566314252468071341813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15661687009346496380489669 2936566314252468071341813)
    ·
      refine ⟨275303091961168881688295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2936566314252468071341813 275303091961168881688295)
      ·
        refine ⟨412954637941753322532443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275303091961168881688295 412954637941753322532443)
        ·
          refine ⟨619431956912629983798665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412954637941753322532443 619431956912629983798665)
          ·
            refine ⟨464573967684472487848999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 619431956912629983798665 464573967684472487848999)
            ·
              refine ⟨696860951526708731773499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464573967684472487848999 696860951526708731773499)
              ·
                refine ⟨1045291427290063097660249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 696860951526708731773499 1045291427290063097660249)
                ·
                  refine ⟨783968570467547323245187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1045291427290063097660249 783968570467547323245187)
                  ·
                    refine ⟨1175952855701320984867781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 783968570467547323245187 1175952855701320984867781)
                    ·
                      refine ⟨220491160443997684662709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1175952855701320984867781 220491160443997684662709)
                      ·
                        rfl

theorem cell23_429405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_429405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429405 prefixEnd_429405 := by exact prefixLift 429405
  have htrace : WordTrace (prefixWord ++ tailWord_429405) baseStart_429405 baseEnd_429405 := by
    simpa [prefixWord, tailWord_429405, baseEnd_429405] using wordTrace_append hprefix tailTrace_429405
  have hstable : (prefixWord ++ tailWord_429405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429405).length < 2 ^ (prefixWord ++ tailWord_429405).sum := by decide
  have hdescent : baseEnd_429405 < baseStart_429405 := by decide
  rcases family_descends (prefixWord ++ tailWord_429405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429407 : List Nat := [1, 1, 2, 3, 1, 2, 1, 6, 1, 5]
def baseStart_429407 : Nat := 118140960795 + 429407 * 2 ^ 59
def prefixEnd_429407 : Nat := 4983230072969 + 3 ^ 40 * 429407 * 2
def baseEnd_429407 : Nat := 73497395801768892279233

theorem tailTrace_429407 : CollatzResearch.WordTrace tailWord_429407 prefixEnd_429407 73497395801768892279233 := by
  unfold tailWord_429407
  simp only [CollatzResearch.WordTrace]
  refine ⟨15661759955339250722062475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10441173303559500481374983 15661759955339250722062475)
  ·
    refine ⟨23492639933008876083093713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15661759955339250722062475 23492639933008876083093713)
    ·
      refine ⟨17619479949756657062320285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23492639933008876083093713 17619479949756657062320285)
      ·
        refine ⟨6607304981158746398370107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17619479949756657062320285 6607304981158746398370107)
        ·
          refine ⟨9910957471738119597555161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6607304981158746398370107 9910957471738119597555161)
          ·
            refine ⟨7433218103803589698166371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9910957471738119597555161 7433218103803589698166371)
            ·
              refine ⟨11149827155705384547249557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7433218103803589698166371 11149827155705384547249557)
              ·
                refine ⟨522648147923689900652323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11149827155705384547249557 522648147923689900652323)
                ·
                  refine ⟨783972221885534850978485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 522648147923689900652323 783972221885534850978485)
                  ·
                    refine ⟨73497395801768892279233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 783972221885534850978485 73497395801768892279233)
                    ·
                      rfl

theorem cell23_429407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 5].length) (baseStart_429407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429407 prefixEnd_429407 := by exact prefixLift 429407
  have htrace : WordTrace (prefixWord ++ tailWord_429407) baseStart_429407 baseEnd_429407 := by
    simpa [prefixWord, tailWord_429407, baseEnd_429407] using wordTrace_append hprefix tailTrace_429407
  have hstable : (prefixWord ++ tailWord_429407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429407).length < 2 ^ (prefixWord ++ tailWord_429407).sum := by decide
  have hdescent : baseEnd_429407 < baseStart_429407 := by decide
  rcases family_descends (prefixWord ++ tailWord_429407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429447 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 5]
def baseStart_429447 : Nat := 118140960795 + 429447 * 2 ^ 59
def prefixEnd_429447 : Nat := 4983230072969 + 3 ^ 40 * 429447 * 2
def baseEnd_429447 : Nat := 220512726631486520337515

theorem tailTrace_429447 : CollatzResearch.WordTrace tailWord_429447 prefixEnd_429447 220512726631486520337515 := by
  unfold tailWord_429447
  simp only [CollatzResearch.WordTrace]
  refine ⟨15663218875194337553518595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10442145916796225035679063 15663218875194337553518595)
  ·
    refine ⟨23494828312791506330277893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15663218875194337553518595 23494828312791506330277893)
    ·
      refine ⟨4405280308648407436927105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23494828312791506330277893 4405280308648407436927105)
      ·
        refine ⟨3303960231486305577695329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4405280308648407436927105 3303960231486305577695329)
        ·
          refine ⟨2477970173614729183271497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3303960231486305577695329 2477970173614729183271497)
          ·
            refine ⟨1858477630211046887453623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2477970173614729183271497 1858477630211046887453623)
            ·
              refine ⟨2787716445316570331180435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1858477630211046887453623 2787716445316570331180435)
              ·
                refine ⟨4181574667974855496770653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2787716445316570331180435 4181574667974855496770653)
                ·
                  refine ⟨1568090500490570811288995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4181574667974855496770653 1568090500490570811288995)
                  ·
                    refine ⟨2352135750735856216933493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1568090500490570811288995 2352135750735856216933493)
                    ·
                      refine ⟨220512726631486520337515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2352135750735856216933493 220512726631486520337515)
                      ·
                        rfl

theorem cell23_429447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_429447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429447 prefixEnd_429447 := by exact prefixLift 429447
  have htrace : WordTrace (prefixWord ++ tailWord_429447) baseStart_429447 baseEnd_429447 := by
    simpa [prefixWord, tailWord_429447, baseEnd_429447] using wordTrace_append hprefix tailTrace_429447
  have hstable : (prefixWord ++ tailWord_429447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429447).length < 2 ^ (prefixWord ++ tailWord_429447).sum := by decide
  have hdescent : baseEnd_429447 < baseStart_429447 := by decide
  rcases family_descends (prefixWord ++ tailWord_429447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429458 : List Nat := [3, 2, 3, 3, 1, 1, 2, 2, 1, 5]
def baseStart_429458 : Nat := 118140960795 + 429458 * 2 ^ 59
def prefixEnd_429458 : Nat := 4983230072969 + 3 ^ 40 * 429458 * 2
def baseEnd_429458 : Nat := 73506124972895325766655

theorem tailTrace_429458 : CollatzResearch.WordTrace tailWord_429458 prefixEnd_429458 73506124972895325766655 := by
  unfold tailWord_429458
  simp only [CollatzResearch.WordTrace]
  refine ⟨3915905019538621608042257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10442413385436324288112685 3915905019538621608042257)
  ·
    refine ⟨2936928764653966206031693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3915905019538621608042257 2936928764653966206031693)
    ·
      refine ⟨1101348286745237327261885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2936928764653966206031693 1101348286745237327261885)
      ·
        refine ⟨413005607529463997723207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1101348286745237327261885 413005607529463997723207)
        ·
          refine ⟨619508411294195996584811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413005607529463997723207 619508411294195996584811)
          ·
            refine ⟨929262616941293994877217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619508411294195996584811 929262616941293994877217)
            ·
              refine ⟨696946962705970496157913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 929262616941293994877217 696946962705970496157913)
              ·
                refine ⟨522710222029477872118435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 696946962705970496157913 522710222029477872118435)
                ·
                  refine ⟨784065333044216808177653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 522710222029477872118435 784065333044216808177653)
                  ·
                    refine ⟨73506124972895325766655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 784065333044216808177653 73506124972895325766655)
                    ·
                      rfl

theorem cell23_429458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_429458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429458 prefixEnd_429458 := by exact prefixLift 429458
  have htrace : WordTrace (prefixWord ++ tailWord_429458) baseStart_429458 baseEnd_429458 := by
    simpa [prefixWord, tailWord_429458, baseEnd_429458] using wordTrace_append hprefix tailTrace_429458
  have hstable : (prefixWord ++ tailWord_429458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429458).length < 2 ^ (prefixWord ++ tailWord_429458).sum := by decide
  have hdescent : baseEnd_429458 < baseStart_429458 := by decide
  rcases family_descends (prefixWord ++ tailWord_429458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429461 : List Nat := [1, 3, 2, 1, 1, 2, 4, 2, 3, 2, 2]
def baseStart_429461 : Nat := 118140960795 + 429461 * 2 ^ 59
def prefixEnd_429461 : Nat := 4983230072969 + 3 ^ 40 * 429461 * 2
def baseEnd_429461 : Nat := 220519915360649465562451

theorem tailTrace_429461 : CollatzResearch.WordTrace tailWord_429461 prefixEnd_429461 220519915360649465562451 := by
  unfold tailWord_429461
  simp only [CollatzResearch.WordTrace]
  refine ⟨15663729497143617944528237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10442486331429078629685491 15663729497143617944528237)
  ·
    refine ⟨5873898561428856729198089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15663729497143617944528237 5873898561428856729198089)
    ·
      refine ⟨4405423921071642546898567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5873898561428856729198089 4405423921071642546898567)
      ·
        refine ⟨6608135881607463820347851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4405423921071642546898567 6608135881607463820347851)
        ·
          refine ⟨9912203822411195730521777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6608135881607463820347851 9912203822411195730521777)
          ·
            refine ⟨7434152866808396797891333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9912203822411195730521777 7434152866808396797891333)
            ·
              refine ⟨1393903662526574399604625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7434152866808396797891333 1393903662526574399604625)
              ·
                refine ⟨1045427746894930799703469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1393903662526574399604625 1045427746894930799703469)
                ·
                  refine ⟨392035405085599049888801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1045427746894930799703469 392035405085599049888801)
                  ·
                    refine ⟨294026553814199287416601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 392035405085599049888801 294026553814199287416601)
                    ·
                      refine ⟨220519915360649465562451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 294026553814199287416601 220519915360649465562451)
                      ·
                        rfl

theorem cell23_429461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 3, 2, 2].length) (baseStart_429461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429461 prefixEnd_429461 := by exact prefixLift 429461
  have htrace : WordTrace (prefixWord ++ tailWord_429461) baseStart_429461 baseEnd_429461 := by
    simpa [prefixWord, tailWord_429461, baseEnd_429461] using wordTrace_append hprefix tailTrace_429461
  have hstable : (prefixWord ++ tailWord_429461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429461).length < 2 ^ (prefixWord ++ tailWord_429461).sum := by decide
  have hdescent : baseEnd_429461 < baseStart_429461 := by decide
  rcases family_descends (prefixWord ++ tailWord_429461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429495 : List Nat := [1, 1, 3, 1, 3, 2, 5, 2, 1, 2, 2]
def baseStart_429495 : Nat := 118140960795 + 429495 * 2 ^ 59
def prefixEnd_429495 : Nat := 4983230072969 + 3 ^ 40 * 429495 * 2
def baseEnd_429495 : Nat := 220537373702902332537295

theorem tailTrace_429495 : CollatzResearch.WordTrace tailWord_429495 prefixEnd_429495 220537373702902332537295 := by
  unfold tailWord_429495
  simp only [CollatzResearch.WordTrace]
  refine ⟨15664969579020441751265939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10443313052680294500843959 15664969579020441751265939)
  ·
    refine ⟨23497454368530662626898909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15664969579020441751265939 23497454368530662626898909)
    ·
      refine ⟨8811545388198998485087091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23497454368530662626898909 8811545388198998485087091)
      ·
        refine ⟨13217318082298497727630637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8811545388198998485087091 13217318082298497727630637)
        ·
          refine ⟨4956494280861936647861489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13217318082298497727630637 4956494280861936647861489)
          ·
            refine ⟨3717370710646452485896117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4956494280861936647861489 3717370710646452485896117)
            ·
              refine ⟨348503504123104920552761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3717370710646452485896117 348503504123104920552761)
              ·
                refine ⟨261377628092328690414571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 348503504123104920552761 261377628092328690414571)
                ·
                  refine ⟨392066442138493035621857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 261377628092328690414571 392066442138493035621857)
                  ·
                    refine ⟨294049831603869776716393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 392066442138493035621857 294049831603869776716393)
                    ·
                      refine ⟨220537373702902332537295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 294049831603869776716393 220537373702902332537295)
                      ·
                        rfl

theorem cell23_429495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 1, 2, 2].length) (baseStart_429495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429495 prefixEnd_429495 := by exact prefixLift 429495
  have htrace : WordTrace (prefixWord ++ tailWord_429495) baseStart_429495 baseEnd_429495 := by
    simpa [prefixWord, tailWord_429495, baseEnd_429495] using wordTrace_append hprefix tailTrace_429495
  have hstable : (prefixWord ++ tailWord_429495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429495).length < 2 ^ (prefixWord ++ tailWord_429495).sum := by decide
  have hdescent : baseEnd_429495 < baseStart_429495 := by decide
  rcases family_descends (prefixWord ++ tailWord_429495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429511 : List Nat := [1, 1, 4, 1, 1, 3, 3, 3, 2, 1, 3]
def baseStart_429511 : Nat := 118140960795 + 429511 * 2 ^ 59
def prefixEnd_429511 : Nat := 4983230072969 + 3 ^ 40 * 429511 * 2
def baseEnd_429511 : Nat := 220545589393374269937221

theorem tailTrace_429511 : CollatzResearch.WordTrace tailWord_429511 prefixEnd_429511 220545589393374269937221 := by
  unfold tailWord_429511
  simp only [CollatzResearch.WordTrace]
  refine ⟨15665553146962476483848387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10443702097974984322565591 15665553146962476483848387)
  ·
    refine ⟨23498329720443714725772581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15665553146962476483848387 23498329720443714725772581)
    ·
      refine ⟨4405936822583196511082359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23498329720443714725772581 4405936822583196511082359)
      ·
        refine ⟨6608905233874794766623539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4405936822583196511082359 6608905233874794766623539)
        ·
          refine ⟨9913357850812192149935309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6608905233874794766623539 9913357850812192149935309)
          ·
            refine ⟨3717509194054572056225741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9913357850812192149935309 3717509194054572056225741)
            ·
              refine ⟨1394065947770464521084653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3717509194054572056225741 1394065947770464521084653)
              ·
                refine ⟨522774730413924195406745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1394065947770464521084653 522774730413924195406745)
                ·
                  refine ⟨392081047810443146555059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 522774730413924195406745 392081047810443146555059)
                  ·
                    refine ⟨588121571715664719832589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 392081047810443146555059 588121571715664719832589)
                    ·
                      refine ⟨220545589393374269937221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 588121571715664719832589 220545589393374269937221)
                      ·
                        rfl

theorem cell23_429511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_429511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429511 prefixEnd_429511 := by exact prefixLift 429511
  have htrace : WordTrace (prefixWord ++ tailWord_429511) baseStart_429511 baseEnd_429511 := by
    simpa [prefixWord, tailWord_429511, baseEnd_429511] using wordTrace_append hprefix tailTrace_429511
  have hstable : (prefixWord ++ tailWord_429511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429511).length < 2 ^ (prefixWord ++ tailWord_429511).sum := by decide
  have hdescent : baseEnd_429511 < baseStart_429511 := by decide
  rcases family_descends (prefixWord ++ tailWord_429511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429551 : List Nat := [1, 1, 2, 1, 4, 1, 2, 3, 4, 2, 2]
def baseStart_429551 : Nat := 118140960795 + 429551 * 2 ^ 59
def prefixEnd_429551 : Nat := 4983230072969 + 3 ^ 40 * 429551 * 2
def baseEnd_429551 : Nat := 220566128619554113437037

theorem tailTrace_429551 : CollatzResearch.WordTrace tailWord_429551 prefixEnd_429551 220566128619554113437037 := by
  unfold tailWord_429551
  simp only [CollatzResearch.WordTrace]
  refine ⟨15667012066817563315304507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10444674711211708876869671 15667012066817563315304507)
  ·
    refine ⟨23500518100226344972956761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15667012066817563315304507 23500518100226344972956761)
    ·
      refine ⟨17625388575169758729717571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23500518100226344972956761 17625388575169758729717571)
      ·
        refine ⟨26438082862754638094576357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17625388575169758729717571 26438082862754638094576357)
        ·
          refine ⟨4957140536766494642733067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26438082862754638094576357 4957140536766494642733067)
          ·
            refine ⟨7435710805149741964099601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4957140536766494642733067 7435710805149741964099601)
            ·
              refine ⟨5576783103862306473074701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7435710805149741964099601 5576783103862306473074701)
              ·
                refine ⟨2091293663948364927403013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5576783103862306473074701 2091293663948364927403013)
                ·
                  refine ⟨392117561990318423888065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2091293663948364927403013 392117561990318423888065)
                  ·
                    refine ⟨294088171492738817916049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 392117561990318423888065 294088171492738817916049)
                    ·
                      refine ⟨220566128619554113437037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 294088171492738817916049 220566128619554113437037)
                      ·
                        rfl

theorem cell23_429551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 4, 2, 2].length) (baseStart_429551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429551 prefixEnd_429551 := by exact prefixLift 429551
  have htrace : WordTrace (prefixWord ++ tailWord_429551) baseStart_429551 baseEnd_429551 := by
    simpa [prefixWord, tailWord_429551, baseEnd_429551] using wordTrace_append hprefix tailTrace_429551
  have hstable : (prefixWord ++ tailWord_429551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429551).length < 2 ^ (prefixWord ++ tailWord_429551).sum := by decide
  have hdescent : baseEnd_429551 < baseStart_429551 := by decide
  rcases family_descends (prefixWord ++ tailWord_429551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429624 : List Nat := [2, 1, 2, 1, 4, 2, 1, 2, 1, 3, 4]
def baseStart_429624 : Nat := 118140960795 + 429624 * 2 ^ 59
def prefixEnd_429624 : Nat := 4983230072969 + 3 ^ 40 * 429624 * 2
def baseEnd_429624 : Nat := 220603612707332327824201

theorem tailTrace_429624 : CollatzResearch.WordTrace tailWord_429624 prefixEnd_429624 220603612707332327824201 := by
  unfold tailWord_429624
  simp only [CollatzResearch.WordTrace]
  refine ⟨7834837297776548391355963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10446449730368731188474617 7834837297776548391355963)
  ·
    refine ⟨11752255946664822587033945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7834837297776548391355963 11752255946664822587033945)
    ·
      refine ⟨8814191959998616940275459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11752255946664822587033945 8814191959998616940275459)
      ·
        refine ⟨13221287939997925410413189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8814191959998616940275459 13221287939997925410413189)
        ·
          refine ⟨2478991488749611014452473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13221287939997925410413189 2478991488749611014452473)
          ·
            refine ⟨1859243616562208260839355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2478991488749611014452473 1859243616562208260839355)
            ·
              refine ⟨2788865424843312391259033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1859243616562208260839355 2788865424843312391259033)
              ·
                refine ⟨2091649068632484293444275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2788865424843312391259033 2091649068632484293444275)
                ·
                  refine ⟨3137473602948726440166413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2091649068632484293444275 3137473602948726440166413)
                  ·
                    refine ⟨1176552601105772415062405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3137473602948726440166413 1176552601105772415062405)
                    ·
                      refine ⟨220603612707332327824201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1176552601105772415062405 220603612707332327824201)
                      ·
                        rfl

theorem cell23_429624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_429624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429624 prefixEnd_429624 := by exact prefixLift 429624
  have htrace : WordTrace (prefixWord ++ tailWord_429624) baseStart_429624 baseEnd_429624 := by
    simpa [prefixWord, tailWord_429624, baseEnd_429624] using wordTrace_append hprefix tailTrace_429624
  have hstable : (prefixWord ++ tailWord_429624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429624).length < 2 ^ (prefixWord ++ tailWord_429624).sum := by decide
  have hdescent : baseEnd_429624 < baseStart_429624 := by decide
  rcases family_descends (prefixWord ++ tailWord_429624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429664 : List Nat := [2, 1, 1, 3, 2, 1, 1, 6, 6]
def baseStart_429664 : Nat := 118140960795 + 429664 * 2 ^ 59
def prefixEnd_429664 : Nat := 4983230072969 + 3 ^ 40 * 429664 * 2
def baseEnd_429664 : Nat := 24513794659279130147113

theorem tailTrace_429664 : CollatzResearch.WordTrace tailWord_429664 prefixEnd_429664 24513794659279130147113 := by
  unfold tailWord_429664
  simp only [CollatzResearch.WordTrace]
  refine ⟨7835566757704091807084023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10447422343605455742778697 7835566757704091807084023)
  ·
    refine ⟨11753350136556137710626035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7835566757704091807084023 11753350136556137710626035)
    ·
      refine ⟨17630025204834206565939053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11753350136556137710626035 17630025204834206565939053)
      ·
        refine ⟨6611259451812827462227145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17630025204834206565939053 6611259451812827462227145)
        ·
          refine ⟨4958444588859620596670359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6611259451812827462227145 4958444588859620596670359)
          ·
            refine ⟨7437666883289430895005539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4958444588859620596670359 7437666883289430895005539)
            ·
              refine ⟨11156500324934146342508309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7437666883289430895005539 11156500324934146342508309)
              ·
                refine ⟨522960952731288109805077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11156500324934146342508309 522960952731288109805077)
                ·
                  refine ⟨24513794659279130147113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 522960952731288109805077 24513794659279130147113)
                  ·
                    rfl

theorem cell23_429664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 6].length) (baseStart_429664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429664 prefixEnd_429664 := by exact prefixLift 429664
  have htrace : WordTrace (prefixWord ++ tailWord_429664) baseStart_429664 baseEnd_429664 := by
    simpa [prefixWord, tailWord_429664, baseEnd_429664] using wordTrace_append hprefix tailTrace_429664
  have hstable : (prefixWord ++ tailWord_429664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429664).length < 2 ^ (prefixWord ++ tailWord_429664).sum := by decide
  have hdescent : baseEnd_429664 < baseStart_429664 := by decide
  rcases family_descends (prefixWord ++ tailWord_429664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429668 : List Nat := [2, 3, 1, 1, 2, 5, 1, 1, 3, 4]
def baseStart_429668 : Nat := 118140960795 + 429668 * 2 ^ 59
def prefixEnd_429668 : Nat := 4983230072969 + 3 ^ 40 * 429668 * 2
def baseEnd_429668 : Nat := 73542068618710051891333

theorem tailTrace_429668 : CollatzResearch.WordTrace tailWord_429668 prefixEnd_429668 73542068618710051891333 := by
  unfold tailWord_429668
  simp only [CollatzResearch.WordTrace]
  refine ⟨7835639703696846148656829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10447519604929128198209105 7835639703696846148656829)
  ·
    refine ⟨2938364888886317305746311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7835639703696846148656829 2938364888886317305746311)
    ·
      refine ⟨4407547333329475958619467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2938364888886317305746311 4407547333329475958619467)
      ·
        refine ⟨6611320999994213937929201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4407547333329475958619467 6611320999994213937929201)
        ·
          refine ⟨4958490749995660453446901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6611320999994213937929201 4958490749995660453446901)
          ·
            refine ⟨464858507812093167510647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4958490749995660453446901 464858507812093167510647)
            ·
              refine ⟨697287761718139751265971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464858507812093167510647 697287761718139751265971)
              ·
                refine ⟨1045931642577209626898957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 697287761718139751265971 1045931642577209626898957)
                ·
                  refine ⟨392224365966453610087109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1045931642577209626898957 392224365966453610087109)
                  ·
                    refine ⟨73542068618710051891333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 392224365966453610087109 73542068618710051891333)
                    ·
                      rfl

theorem cell23_429668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_429668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429668 prefixEnd_429668 := by exact prefixLift 429668
  have htrace : WordTrace (prefixWord ++ tailWord_429668) baseStart_429668 baseEnd_429668 := by
    simpa [prefixWord, tailWord_429668, baseEnd_429668] using wordTrace_append hprefix tailTrace_429668
  have hstable : (prefixWord ++ tailWord_429668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429668).length < 2 ^ (prefixWord ++ tailWord_429668).sum := by decide
  have hdescent : baseEnd_429668 < baseStart_429668 := by decide
  rcases family_descends (prefixWord ++ tailWord_429668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429691 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 5, 1, 3]
def baseStart_429691 : Nat := 118140960795 + 429691 * 2 ^ 59
def prefixEnd_429691 : Nat := 4983230072969 + 3 ^ 40 * 429691 * 2
def baseEnd_429691 : Nat := 220638015911183565686393

theorem tailTrace_429691 : CollatzResearch.WordTrace tailWord_429691 prefixEnd_429691 220638015911183565686393 := by
  unfold tailWord_429691
  simp only [CollatzResearch.WordTrace]
  refine ⟨15672118286310367225400927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10448078857540244816933951 15672118286310367225400927)
  ·
    refine ⟨23508177429465550838101391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15672118286310367225400927 23508177429465550838101391)
    ·
      refine ⟨35262266144198326257152087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23508177429465550838101391 35262266144198326257152087)
      ·
        refine ⟨52893399216297489385728131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35262266144198326257152087 52893399216297489385728131)
        ·
          refine ⟨79340098824446234078592197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52893399216297489385728131 79340098824446234078592197)
          ·
            refine ⟨14876268529583668889736037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79340098824446234078592197 14876268529583668889736037)
            ·
              refine ⟨2789300349296937916825507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14876268529583668889736037 2789300349296937916825507)
              ·
                refine ⟨4183950523945406875238261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2789300349296937916825507 4183950523945406875238261)
                ·
                  refine ⟨392245361619881894553587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4183950523945406875238261 392245361619881894553587)
                  ·
                    refine ⟨588368042429822841830381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 392245361619881894553587 588368042429822841830381)
                    ·
                      refine ⟨220638015911183565686393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 588368042429822841830381 220638015911183565686393)
                      ·
                        rfl

theorem cell23_429691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 5, 1, 3].length) (baseStart_429691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429691 prefixEnd_429691 := by exact prefixLift 429691
  have htrace : WordTrace (prefixWord ++ tailWord_429691) baseStart_429691 baseEnd_429691 := by
    simpa [prefixWord, tailWord_429691, baseEnd_429691] using wordTrace_append hprefix tailTrace_429691
  have hstable : (prefixWord ++ tailWord_429691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429691).length < 2 ^ (prefixWord ++ tailWord_429691).sum := by decide
  have hdescent : baseEnd_429691 < baseStart_429691 := by decide
  rcases family_descends (prefixWord ++ tailWord_429691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429742 : List Nat := [4, 1, 4, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_429742 : Nat := 118140960795 + 429742 * 2 ^ 59
def prefixEnd_429742 : Nat := 4983230072969 + 3 ^ 40 * 429742 * 2
def baseEnd_429742 : Nat := 220664203424562866148659

theorem tailTrace_429742 : CollatzResearch.WordTrace tailWord_429742 prefixEnd_429742 220664203424562866148659 := by
  unfold tailWord_429742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1959247301140700366938435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10449318939417068623671653 1959247301140700366938435)
  ·
    refine ⟨2938870951711050550407653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1959247301140700366938435 2938870951711050550407653)
    ·
      refine ⟨551038303445821978201435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2938870951711050550407653 551038303445821978201435)
      ·
        refine ⟨826557455168732967302153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551038303445821978201435 826557455168732967302153)
        ·
          refine ⟨619918091376549725476615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 826557455168732967302153 619918091376549725476615)
          ·
            refine ⟨929877137064824588214923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619918091376549725476615 929877137064824588214923)
            ·
              refine ⟨1394815705597236882322385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 929877137064824588214923 1394815705597236882322385)
              ·
                refine ⟨1046111779197927661741789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1394815705597236882322385 1046111779197927661741789)
                ·
                  refine ⟨392291917199222873153171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1046111779197927661741789 392291917199222873153171)
                  ·
                    refine ⟨588437875798834309729757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 392291917199222873153171 588437875798834309729757)
                    ·
                      refine ⟨220664203424562866148659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 588437875798834309729757 220664203424562866148659)
                      ·
                        rfl

theorem cell23_429742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_429742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429742 prefixEnd_429742 := by exact prefixLift 429742
  have htrace : WordTrace (prefixWord ++ tailWord_429742) baseStart_429742 baseEnd_429742 := by
    simpa [prefixWord, tailWord_429742, baseEnd_429742] using wordTrace_append hprefix tailTrace_429742
  have hstable : (prefixWord ++ tailWord_429742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429742).length < 2 ^ (prefixWord ++ tailWord_429742).sum := by decide
  have hdescent : baseEnd_429742 < baseStart_429742 := by decide
  rcases family_descends (prefixWord ++ tailWord_429742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429744 : List Nat := [2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 6]
def baseStart_429744 : Nat := 118140960795 + 429744 * 2 ^ 59
def prefixEnd_429744 : Nat := 4983230072969 + 3 ^ 40 * 429744 * 2
def baseEnd_429744 : Nat := 220665230385871858323649

theorem tailTrace_429744 : CollatzResearch.WordTrace tailWord_429744 prefixEnd_429744 220665230385871858323649 := by
  unfold tailWord_429744
  simp only [CollatzResearch.WordTrace]
  refine ⟨7837025677559178638540143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10449367570078904851386857 7837025677559178638540143)
  ·
    refine ⟨11755538516338767957810215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7837025677559178638540143 11755538516338767957810215)
    ·
      refine ⟨17633307774508151936715323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11755538516338767957810215 17633307774508151936715323)
      ·
        refine ⟨26449961661762227905072985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17633307774508151936715323 26449961661762227905072985)
        ·
          refine ⟨19837471246321670928804739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26449961661762227905072985 19837471246321670928804739)
          ·
            refine ⟨29756206869482506393207109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19837471246321670928804739 29756206869482506393207109)
            ·
              refine ⟨5579288788027969948726333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29756206869482506393207109 5579288788027969948726333)
              ·
                refine ⟨2092233295510488730772375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5579288788027969948726333 2092233295510488730772375)
                ·
                  refine ⟨3138349943265733096158563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2092233295510488730772375 3138349943265733096158563)
                  ·
                    refine ⟨4707524914898599644237845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3138349943265733096158563 4707524914898599644237845)
                    ·
                      refine ⟨220665230385871858323649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4707524914898599644237845 220665230385871858323649)
                      ·
                        rfl

theorem cell23_429744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 6].length) (baseStart_429744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429744 prefixEnd_429744 := by exact prefixLift 429744
  have htrace : WordTrace (prefixWord ++ tailWord_429744) baseStart_429744 baseEnd_429744 := by
    simpa [prefixWord, tailWord_429744, baseEnd_429744] using wordTrace_append hprefix tailTrace_429744
  have hstable : (prefixWord ++ tailWord_429744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429744).length < 2 ^ (prefixWord ++ tailWord_429744).sum := by decide
  have hdescent : baseEnd_429744 < baseStart_429744 := by decide
  rcases family_descends (prefixWord ++ tailWord_429744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429768 : List Nat := [2, 1, 3, 1, 2, 2, 3, 3, 1, 2, 3]
def baseStart_429768 : Nat := 118140960795 + 429768 * 2 ^ 59
def prefixEnd_429768 : Nat := 4983230072969 + 3 ^ 40 * 429768 * 2
def baseEnd_429768 : Nat := 220677553921579764423539

theorem tailTrace_429768 : CollatzResearch.WordTrace tailWord_429768 prefixEnd_429768 220677553921579764423539 := by
  unfold tailWord_429768
  simp only [CollatzResearch.WordTrace]
  refine ⟨7837463353515704687976979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10449951138020939583969305 7837463353515704687976979)
  ·
    refine ⟨11756195030273557031965469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7837463353515704687976979 11756195030273557031965469)
    ·
      refine ⟨4408573136352583886987051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11756195030273557031965469 4408573136352583886987051)
      ·
        refine ⟨6612859704528875830480577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4408573136352583886987051 6612859704528875830480577)
        ·
          refine ⟨4959644778396656872860433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6612859704528875830480577 4959644778396656872860433)
          ·
            refine ⟨3719733583797492654645325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4959644778396656872860433 3719733583797492654645325)
            ·
              refine ⟨1394900093924059745491997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3719733583797492654645325 1394900093924059745491997)
              ·
                refine ⟨523087535221522404559499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1394900093924059745491997 523087535221522404559499)
                ·
                  refine ⟨784631302832283606839249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 523087535221522404559499 784631302832283606839249)
                  ·
                    refine ⟨588473477124212705129437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 784631302832283606839249 588473477124212705129437)
                    ·
                      refine ⟨220677553921579764423539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 588473477124212705129437 220677553921579764423539)
                      ·
                        rfl

theorem cell23_429768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_429768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429768 prefixEnd_429768 := by exact prefixLift 429768
  have htrace : WordTrace (prefixWord ++ tailWord_429768) baseStart_429768 baseEnd_429768 := by
    simpa [prefixWord, tailWord_429768, baseEnd_429768] using wordTrace_append hprefix tailTrace_429768
  have hstable : (prefixWord ++ tailWord_429768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429768).length < 2 ^ (prefixWord ++ tailWord_429768).sum := by decide
  have hdescent : baseEnd_429768 < baseStart_429768 := by decide
  rcases family_descends (prefixWord ++ tailWord_429768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429795 : List Nat := [1, 1, 1, 7, 2, 2, 1, 1, 1, 2, 4]
def baseStart_429795 : Nat := 118140960795 + 429795 * 2 ^ 59
def prefixEnd_429795 : Nat := 4983230072969 + 3 ^ 40 * 429795 * 2
def baseEnd_429795 : Nat := 220691417899251158785915

theorem tailTrace_429795 : CollatzResearch.WordTrace tailWord_429795 prefixEnd_429795 220691417899251158785915 := by
  unfold tailWord_429795
  simp only [CollatzResearch.WordTrace]
  refine ⟨15675911477933592987186839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10450607651955728658124559 15675911477933592987186839)
  ·
    refine ⟨23513867216900389480780259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15675911477933592987186839 23513867216900389480780259)
    ·
      refine ⟨35270800825350584221170389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23513867216900389480780259 35270800825350584221170389)
      ·
        refine ⟨826659394344154317683681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 35270800825350584221170389 826659394344154317683681)
        ·
          refine ⟨619994545758115738262761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 826659394344154317683681 619994545758115738262761)
          ·
            refine ⟨464995909318586803697071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 619994545758115738262761 464995909318586803697071)
            ·
              refine ⟨697493863977880205545607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464995909318586803697071 697493863977880205545607)
              ·
                refine ⟨1046240795966820308318411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 697493863977880205545607 1046240795966820308318411)
                ·
                  refine ⟨1569361193950230462477617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1046240795966820308318411 1569361193950230462477617)
                  ·
                    refine ⟨1177020895462672846858213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1569361193950230462477617 1177020895462672846858213)
                    ·
                      refine ⟨220691417899251158785915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1177020895462672846858213 220691417899251158785915)
                      ·
                        rfl

theorem cell23_429795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_429795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429795 prefixEnd_429795 := by exact prefixLift 429795
  have htrace : WordTrace (prefixWord ++ tailWord_429795) baseStart_429795 baseEnd_429795 := by
    simpa [prefixWord, tailWord_429795, baseEnd_429795] using wordTrace_append hprefix tailTrace_429795
  have hstable : (prefixWord ++ tailWord_429795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429795).length < 2 ^ (prefixWord ++ tailWord_429795).sum := by decide
  have hdescent : baseEnd_429795 < baseStart_429795 := by decide
  rcases family_descends (prefixWord ++ tailWord_429795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429825 : List Nat := [1, 2, 4, 1, 1, 1, 4, 3, 1, 3, 2]
def baseStart_429825 : Nat := 118140960795 + 429825 * 2 ^ 59
def prefixEnd_429825 : Nat := 4983230072969 + 3 ^ 40 * 429825 * 2
def baseEnd_429825 : Nat := 220706822318886041410777

theorem tailTrace_429825 : CollatzResearch.WordTrace tailWord_429825 prefixEnd_429825 220706822318886041410777 := by
  unfold tailWord_429825
  simp only [CollatzResearch.WordTrace]
  refine ⟨15677005667824908110778929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10451337111883272073852619 15677005667824908110778929)
  ·
    refine ⟨11757754250868681083084197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15677005667824908110778929 11757754250868681083084197)
    ·
      refine ⟨2204578922037877703078287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11757754250868681083084197 2204578922037877703078287)
      ·
        refine ⟨3306868383056816554617431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2204578922037877703078287 3306868383056816554617431)
        ·
          refine ⟨4960302574585224831926147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3306868383056816554617431 4960302574585224831926147)
          ·
            refine ⟨7440453861877837247889221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4960302574585224831926147 7440453861877837247889221)
            ·
              refine ⟨1395085099102094483979229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7440453861877837247889221 1395085099102094483979229)
              ·
                refine ⟨523156912163285431492211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1395085099102094483979229 523156912163285431492211)
                ·
                  refine ⟨784735368244928147238317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 523156912163285431492211 784735368244928147238317)
                  ·
                    refine ⟨294275763091848055214369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 784735368244928147238317 294275763091848055214369)
                    ·
                      refine ⟨220706822318886041410777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 294275763091848055214369 220706822318886041410777)
                      ·
                        rfl

theorem cell23_429825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_429825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429825 prefixEnd_429825 := by exact prefixLift 429825
  have htrace : WordTrace (prefixWord ++ tailWord_429825) baseStart_429825 baseEnd_429825 := by
    simpa [prefixWord, tailWord_429825, baseEnd_429825] using wordTrace_append hprefix tailTrace_429825
  have hstable : (prefixWord ++ tailWord_429825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429825).length < 2 ^ (prefixWord ++ tailWord_429825).sum := by decide
  have hdescent : baseEnd_429825 < baseStart_429825 := by decide
  rcases family_descends (prefixWord ++ tailWord_429825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429841 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 3]
def baseStart_429841 : Nat := 118140960795 + 429841 * 2 ^ 59
def prefixEnd_429841 : Nat := 4983230072969 + 3 ^ 40 * 429841 * 2
def baseEnd_429841 : Nat := 220715038009357978810703

theorem tailTrace_429841 : CollatzResearch.WordTrace tailWord_429841 prefixEnd_429841 220715038009357978810703 := by
  unfold tailWord_429841
  simp only [CollatzResearch.WordTrace]
  refine ⟨15677589235766942843361377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10451726157177961895574251 15677589235766942843361377)
  ·
    refine ⟨11758191926825207132521033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15677589235766942843361377 11758191926825207132521033)
    ·
      refine ⟨8818643945118905349390775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11758191926825207132521033 8818643945118905349390775)
      ·
        refine ⟨13227965917678358024086163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8818643945118905349390775 13227965917678358024086163)
        ·
          refine ⟨19841948876517537036129245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13227965917678358024086163 19841948876517537036129245)
          ·
            refine ⟨7440730828694076388548467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19841948876517537036129245 7440730828694076388548467)
            ·
              refine ⟨11161096243041114582822701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7440730828694076388548467 11161096243041114582822701)
              ·
                refine ⟨4185411091140417968558513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11161096243041114582822701 4185411091140417968558513)
                ·
                  refine ⟨3139058318355313476418885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4185411091140417968558513 3139058318355313476418885)
                  ·
                    refine ⟨588573434691621276828541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3139058318355313476418885 588573434691621276828541)
                    ·
                      refine ⟨220715038009357978810703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 588573434691621276828541 220715038009357978810703)
                      ·
                        rfl

theorem cell23_429841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 3].length) (baseStart_429841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429841 prefixEnd_429841 := by exact prefixLift 429841
  have htrace : WordTrace (prefixWord ++ tailWord_429841) baseStart_429841 baseEnd_429841 := by
    simpa [prefixWord, tailWord_429841, baseEnd_429841] using wordTrace_append hprefix tailTrace_429841
  have hstable : (prefixWord ++ tailWord_429841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429841).length < 2 ^ (prefixWord ++ tailWord_429841).sum := by decide
  have hdescent : baseEnd_429841 < baseStart_429841 := by decide
  rcases family_descends (prefixWord ++ tailWord_429841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429871 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 1, 5, 3]
def baseStart_429871 : Nat := 118140960795 + 429871 * 2 ^ 59
def prefixEnd_429871 : Nat := 4983230072969 + 3 ^ 40 * 429871 * 2
def baseEnd_429871 : Nat := 220730442428992861435565

theorem tailTrace_429871 : CollatzResearch.WordTrace tailWord_429871 prefixEnd_429871 220730442428992861435565 := by
  unfold tailWord_429871
  simp only [CollatzResearch.WordTrace]
  refine ⟨15678683425658257966953467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10452455617105505311302311 15678683425658257966953467)
  ·
    refine ⟨23518025138487386950430201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15678683425658257966953467 23518025138487386950430201)
    ·
      refine ⟨17638518853865540212822651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23518025138487386950430201 17638518853865540212822651)
      ·
        refine ⟨26457778280798310319233977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17638518853865540212822651 26457778280798310319233977)
        ·
          refine ⟨19843333710598732739425483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26457778280798310319233977 19843333710598732739425483)
          ·
            refine ⟨29765000565898099109138225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19843333710598732739425483 29765000565898099109138225)
            ·
              refine ⟨22323750424423574331853669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29765000565898099109138225 22323750424423574331853669)
              ·
                refine ⟨4185703204579420187222563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22323750424423574331853669 4185703204579420187222563)
                ·
                  refine ⟨6278554806869130280833845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4185703204579420187222563 6278554806869130280833845)
                  ·
                    refine ⟨588614513143980963828173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6278554806869130280833845 588614513143980963828173)
                    ·
                      refine ⟨220730442428992861435565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 588614513143980963828173 220730442428992861435565)
                      ·
                        rfl

theorem cell23_429871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 5, 3].length) (baseStart_429871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429871 prefixEnd_429871 := by exact prefixLift 429871
  have htrace : WordTrace (prefixWord ++ tailWord_429871) baseStart_429871 baseEnd_429871 := by
    simpa [prefixWord, tailWord_429871, baseEnd_429871] using wordTrace_append hprefix tailTrace_429871
  have hstable : (prefixWord ++ tailWord_429871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429871).length < 2 ^ (prefixWord ++ tailWord_429871).sum := by decide
  have hdescent : baseEnd_429871 < baseStart_429871 := by decide
  rcases family_descends (prefixWord ++ tailWord_429871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429895 : List Nat := [1, 1, 4, 1, 2, 1, 6, 2, 5]
def baseStart_429895 : Nat := 118140960795 + 429895 * 2 ^ 59
def prefixEnd_429895 : Nat := 4983230072969 + 3 ^ 40 * 429895 * 2
def baseEnd_429895 : Nat := 24526973996077863059495

theorem tailTrace_429895 : CollatzResearch.WordTrace tailWord_429895 prefixEnd_429895 24526973996077863059495 := by
  unfold tailWord_429895
  simp only [CollatzResearch.WordTrace]
  refine ⟨15679558777571310065827139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10453039185047540043884759 15679558777571310065827139)
  ·
    refine ⟨23519338166356965098740709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15679558777571310065827139 23519338166356965098740709)
    ·
      refine ⟨4409875906191930956013883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23519338166356965098740709 4409875906191930956013883)
      ·
        refine ⟨6614813859287896434020825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4409875906191930956013883 6614813859287896434020825)
        ·
          refine ⟨4961110394465922325515619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6614813859287896434020825 4961110394465922325515619)
          ·
            refine ⟨7441665591698883488273429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4961110394465922325515619 7441665591698883488273429)
            ·
              refine ⟨348828074610885163512817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7441665591698883488273429 348828074610885163512817)
              ·
                refine ⟨261621055958163872634613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 348828074610885163512817 261621055958163872634613)
                ·
                  refine ⟨24526973996077863059495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 261621055958163872634613 24526973996077863059495)
                  ·
                    rfl

theorem cell23_429895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 2, 5].length) (baseStart_429895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429895 prefixEnd_429895 := by exact prefixLift 429895
  have htrace : WordTrace (prefixWord ++ tailWord_429895) baseStart_429895 baseEnd_429895 := by
    simpa [prefixWord, tailWord_429895, baseEnd_429895] using wordTrace_append hprefix tailTrace_429895
  have hstable : (prefixWord ++ tailWord_429895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429895).length < 2 ^ (prefixWord ++ tailWord_429895).sum := by decide
  have hdescent : baseEnd_429895 < baseStart_429895 := by decide
  rcases family_descends (prefixWord ++ tailWord_429895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429898 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 1, 7, 2]
def baseStart_429898 : Nat := 118140960795 + 429898 * 2 ^ 59
def prefixEnd_429898 : Nat := 4983230072969 + 3 ^ 40 * 429898 * 2
def baseEnd_429898 : Nat := 220744306406664255797941

theorem tailTrace_429898 : CollatzResearch.WordTrace tailWord_429898 prefixEnd_429898 220744306406664255797941 := by
  unfold tailWord_429898
  simp only [CollatzResearch.WordTrace]
  refine ⟨3919917049140110394546587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10453112131040294385457565 3919917049140110394546587)
  ·
    refine ⟨5879875573710165591819881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3919917049140110394546587 5879875573710165591819881)
    ·
      refine ⟨4409906680282624193864911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5879875573710165591819881 4409906680282624193864911)
      ·
        refine ⟨6614860020423936290797367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4409906680282624193864911 6614860020423936290797367)
        ·
          refine ⟨9922290030635904436196051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6614860020423936290797367 9922290030635904436196051)
          ·
            refine ⟨14883435045953856654294077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9922290030635904436196051 14883435045953856654294077)
            ·
              refine ⟨5581288142232696245360279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14883435045953856654294077 5581288142232696245360279)
              ·
                refine ⟨8371932213349044368040419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5581288142232696245360279 8371932213349044368040419)
                ·
                  refine ⟨12557898320023566552060629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8371932213349044368040419 12557898320023566552060629)
                  ·
                    refine ⟨294325741875552341063921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12557898320023566552060629 294325741875552341063921)
                    ·
                      refine ⟨220744306406664255797941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 294325741875552341063921 220744306406664255797941)
                      ·
                        rfl

theorem cell23_429898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 1, 7, 2].length) (baseStart_429898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429898 prefixEnd_429898 := by exact prefixLift 429898
  have htrace : WordTrace (prefixWord ++ tailWord_429898) baseStart_429898 baseEnd_429898 := by
    simpa [prefixWord, tailWord_429898, baseEnd_429898] using wordTrace_append hprefix tailTrace_429898
  have hstable : (prefixWord ++ tailWord_429898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429898).length < 2 ^ (prefixWord ++ tailWord_429898).sum := by decide
  have hdescent : baseEnd_429898 < baseStart_429898 := by decide
  rcases family_descends (prefixWord ++ tailWord_429898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429928 : List Nat := [2, 1, 4, 2, 1, 1, 3, 1, 1, 3, 4]
def baseStart_429928 : Nat := 118140960795 + 429928 * 2 ^ 59
def prefixEnd_429928 : Nat := 4983230072969 + 3 ^ 40 * 429928 * 2
def baseEnd_429928 : Nat := 220759710826299138422803

theorem tailTrace_429928 : CollatzResearch.WordTrace tailWord_429928 prefixEnd_429928 220759710826299138422803 := by
  unfold tailWord_429928
  simp only [CollatzResearch.WordTrace]
  refine ⟨7840381193225878350889219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10453841590967837801185625 7840381193225878350889219)
  ·
    refine ⟨11760571789838817526333829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7840381193225878350889219 11760571789838817526333829)
    ·
      refine ⟨2205107210594778286187593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11760571789838817526333829 2205107210594778286187593)
      ·
        refine ⟨1653830407946083714640695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2205107210594778286187593 1653830407946083714640695)
        ·
          refine ⟨2480745611919125571961043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1653830407946083714640695 2480745611919125571961043)
          ·
            refine ⟨3721118417878688357941565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2480745611919125571961043 3721118417878688357941565)
            ·
              refine ⟨1395419406704508134228087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3721118417878688357941565 1395419406704508134228087)
              ·
                refine ⟨2093129110056762201342131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1395419406704508134228087 2093129110056762201342131)
                ·
                  refine ⟨3139693665085143302013197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2093129110056762201342131 3139693665085143302013197)
                  ·
                    refine ⟨1177385124406928738254949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3139693665085143302013197 1177385124406928738254949)
                    ·
                      refine ⟨220759710826299138422803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1177385124406928738254949 220759710826299138422803)
                      ·
                        rfl

theorem cell23_429928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_429928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429928 prefixEnd_429928 := by exact prefixLift 429928
  have htrace : WordTrace (prefixWord ++ tailWord_429928) baseStart_429928 baseEnd_429928 := by
    simpa [prefixWord, tailWord_429928, baseEnd_429928] using wordTrace_append hprefix tailTrace_429928
  have hstable : (prefixWord ++ tailWord_429928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429928).length < 2 ^ (prefixWord ++ tailWord_429928).sum := by decide
  have hdescent : baseEnd_429928 < baseStart_429928 := by decide
  rcases family_descends (prefixWord ++ tailWord_429928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429938 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 7, 4]
def baseStart_429938 : Nat := 118140960795 + 429938 * 2 ^ 59
def prefixEnd_429938 : Nat := 4983230072969 + 3 ^ 40 * 429938 * 2
def baseEnd_429938 : Nat := 73588281877614699765919

theorem tailTrace_429938 : CollatzResearch.WordTrace tailWord_429938 prefixEnd_429938 73588281877614699765919 := by
  unfold tailWord_429938
  simp only [CollatzResearch.WordTrace]
  refine ⟨3920281779103882102410617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10454084744277018939761645 3920281779103882102410617)
  ·
    refine ⟨2940211334327911576807963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3920281779103882102410617 2940211334327911576807963)
    ·
      refine ⟨4410317001491867365211945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2940211334327911576807963 4410317001491867365211945)
      ·
        refine ⟨3307737751118900523908959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4410317001491867365211945 3307737751118900523908959)
        ·
          refine ⟨4961606626678350785863439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3307737751118900523908959 4961606626678350785863439)
          ·
            refine ⟨7442409940017526178795159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4961606626678350785863439 7442409940017526178795159)
            ·
              refine ⟨11163614910026289268192739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7442409940017526178795159 11163614910026289268192739)
              ·
                refine ⟨16745422365039433902289109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11163614910026289268192739 16745422365039433902289109)
                ·
                  refine ⟨392470836680611732084901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16745422365039433902289109 392470836680611732084901)
                  ·
                    refine ⟨73588281877614699765919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 392470836680611732084901 73588281877614699765919)
                    ·
                      rfl

theorem cell23_429938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_429938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429938 prefixEnd_429938 := by exact prefixLift 429938
  have htrace : WordTrace (prefixWord ++ tailWord_429938) baseStart_429938 baseEnd_429938 := by
    simpa [prefixWord, tailWord_429938, baseEnd_429938] using wordTrace_append hprefix tailTrace_429938
  have hstable : (prefixWord ++ tailWord_429938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429938).length < 2 ^ (prefixWord ++ tailWord_429938).sum := by decide
  have hdescent : baseEnd_429938 < baseStart_429938 := by decide
  rcases family_descends (prefixWord ++ tailWord_429938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429955 : List Nat := [1, 1, 1, 3, 4, 3, 2, 1, 3, 4]
def baseStart_429955 : Nat := 118140960795 + 429955 * 2 ^ 59
def prefixEnd_429955 : Nat := 4983230072969 + 3 ^ 40 * 429955 * 2
def baseEnd_429955 : Nat := 73591191601323510928393

theorem tailTrace_429955 : CollatzResearch.WordTrace tailWord_429955 prefixEnd_429955 73591191601323510928393 := by
  unfold tailWord_429955
  simp only [CollatzResearch.WordTrace]
  refine ⟨15681747157353940313011319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10454498104902626875340879 15681747157353940313011319)
  ·
    refine ⟨23522620736030910469516979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15681747157353940313011319 23522620736030910469516979)
    ·
      refine ⟨35283931104046365704275469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23522620736030910469516979 35283931104046365704275469)
      ·
        refine ⟨13231474164017387139103301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35283931104046365704275469 13231474164017387139103301)
        ·
          refine ⟨2480901405753260088581869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13231474164017387139103301 2480901405753260088581869)
          ·
            refine ⟨930338027157472533218201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2480901405753260088581869 930338027157472533218201)
            ·
              refine ⟨697753520368104399913651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 930338027157472533218201 697753520368104399913651)
              ·
                refine ⟨1046630280552156599870477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 697753520368104399913651 1046630280552156599870477)
                ·
                  refine ⟨392486355207058724951429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1046630280552156599870477 392486355207058724951429)
                  ·
                    refine ⟨73591191601323510928393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 392486355207058724951429 73591191601323510928393)
                    ·
                      rfl

theorem cell23_429955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 3, 4].length) (baseStart_429955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_429955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_429955 prefixEnd_429955 := by exact prefixLift 429955
  have htrace : WordTrace (prefixWord ++ tailWord_429955) baseStart_429955 baseEnd_429955 := by
    simpa [prefixWord, tailWord_429955, baseEnd_429955] using wordTrace_append hprefix tailTrace_429955
  have hstable : (prefixWord ++ tailWord_429955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429955).length < 2 ^ (prefixWord ++ tailWord_429955).sum := by decide
  have hdescent : baseEnd_429955 < baseStart_429955 := by decide
  rcases family_descends (prefixWord ++ tailWord_429955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430052 : List Nat := [2, 3, 1, 1, 1, 1, 7, 1, 1, 1, 4]
def baseStart_430052 : Nat := 118140960795 + 430052 * 2 ^ 59
def prefixEnd_430052 : Nat := 4983230072969 + 3 ^ 40 * 430052 * 2
def baseEnd_430052 : Nat := 220823382427456653272233

theorem tailTrace_430052 : CollatzResearch.WordTrace tailWord_430052 prefixEnd_430052 220823382427456653272233 := by
  unfold tailWord_430052
  simp only [CollatzResearch.WordTrace]
  refine ⟨7842642519001262939646205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10456856692001683919528273 7842642519001262939646205)
  ·
    refine ⟨2940990944625473602367327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7842642519001262939646205 2940990944625473602367327)
    ·
      refine ⟨4411486416938210403550991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2940990944625473602367327 4411486416938210403550991)
      ·
        refine ⟨6617229625407315605326487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4411486416938210403550991 6617229625407315605326487)
        ·
          refine ⟨9925844438110973407989731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6617229625407315605326487 9925844438110973407989731)
          ·
            refine ⟨14888766657166460111984597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9925844438110973407989731 14888766657166460111984597)
            ·
              refine ⟨348955468527338908874639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 14888766657166460111984597 348955468527338908874639)
              ·
                refine ⟨523433202791008363311959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 348955468527338908874639 523433202791008363311959)
                ·
                  refine ⟨785149804186512544967939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 523433202791008363311959 785149804186512544967939)
                  ·
                    refine ⟨1177724706279768817451909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 785149804186512544967939 1177724706279768817451909)
                    ·
                      refine ⟨220823382427456653272233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1177724706279768817451909 220823382427456653272233)
                      ·
                        rfl

theorem cell23_430052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 1, 1, 4].length) (baseStart_430052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430052 prefixEnd_430052 := by exact prefixLift 430052
  have htrace : WordTrace (prefixWord ++ tailWord_430052) baseStart_430052 baseEnd_430052 := by
    simpa [prefixWord, tailWord_430052, baseEnd_430052] using wordTrace_append hprefix tailTrace_430052
  have hstable : (prefixWord ++ tailWord_430052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430052).length < 2 ^ (prefixWord ++ tailWord_430052).sum := by decide
  have hdescent : baseEnd_430052 < baseStart_430052 := by decide
  rcases family_descends (prefixWord ++ tailWord_430052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430062 : List Nat := [4, 1, 2, 1, 3, 1, 1, 4, 2, 4]
def baseStart_430062 : Nat := 118140960795 + 430062 * 2 ^ 59
def prefixEnd_430062 : Nat := 4983230072969 + 3 ^ 40 * 430062 * 2
def baseEnd_430062 : Nat := 73609505744667204715729

theorem tailTrace_430062 : CollatzResearch.WordTrace tailWord_430062 prefixEnd_430062 73609505744667204715729 := by
  unfold tailWord_430062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1960706220995787198394555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10457099845310865058104293 1960706220995787198394555)
  ·
    refine ⟨2941059331493680797591833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1960706220995787198394555 2941059331493680797591833)
    ·
      refine ⟨2205794498620260598193875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2941059331493680797591833 2205794498620260598193875)
      ·
        refine ⟨3308691747930390897290813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2205794498620260598193875 3308691747930390897290813)
        ·
          refine ⟨1240759405473896586484055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3308691747930390897290813 1240759405473896586484055)
          ·
            refine ⟨1861139108210844879726083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1240759405473896586484055 1861139108210844879726083)
            ·
              refine ⟨2791708662316267319589125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1861139108210844879726083 2791708662316267319589125)
              ·
                refine ⟨523445374184300122422961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2791708662316267319589125 523445374184300122422961)
                ·
                  refine ⟨392584030638225091817221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 523445374184300122422961 392584030638225091817221)
                  ·
                    refine ⟨73609505744667204715729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 392584030638225091817221 73609505744667204715729)
                    ·
                      rfl

theorem cell23_430062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_430062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430062 prefixEnd_430062 := by exact prefixLift 430062
  have htrace : WordTrace (prefixWord ++ tailWord_430062) baseStart_430062 baseEnd_430062 := by
    simpa [prefixWord, tailWord_430062, baseEnd_430062] using wordTrace_append hprefix tailTrace_430062
  have hstable : (prefixWord ++ tailWord_430062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430062).length < 2 ^ (prefixWord ++ tailWord_430062).sum := by decide
  have hdescent : baseEnd_430062 < baseStart_430062 := by decide
  rcases family_descends (prefixWord ++ tailWord_430062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430085 : List Nat := [1, 3, 1, 1, 2, 4, 1, 3, 1, 3, 3]
def baseStart_430085 : Nat := 118140960795 + 430085 * 2 ^ 59
def prefixEnd_430085 : Nat := 4983230072969 + 3 ^ 40 * 430085 * 2
def baseEnd_430085 : Nat := 220840327289055024159581

theorem tailTrace_430085 : CollatzResearch.WordTrace tailWord_430085 prefixEnd_430085 220840327289055024159581 := by
  unfold tailWord_430085
  simp only [CollatzResearch.WordTrace]
  refine ⟨15686488646882972515243709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10457659097921981676829139 15686488646882972515243709)
  ·
    refine ⟨5882433242581114693216391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15686488646882972515243709 5882433242581114693216391)
    ·
      refine ⟨8823649863871672039824587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5882433242581114693216391 8823649863871672039824587)
      ·
        refine ⟨13235474795807508059736881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8823649863871672039824587 13235474795807508059736881)
        ·
          refine ⟨9926606096855631044802661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13235474795807508059736881 9926606096855631044802661)
          ·
            refine ⟨1861238643160430820900499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9926606096855631044802661 1861238643160430820900499)
            ·
              refine ⟨2791857964740646231350749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1861238643160430820900499 2791857964740646231350749)
              ·
                refine ⟨1046946736777742336756531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2791857964740646231350749 1046946736777742336756531)
                ·
                  refine ⟨1570420105166613505134797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1046946736777742336756531 1570420105166613505134797)
                  ·
                    refine ⟨588907539437480064425549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1570420105166613505134797 588907539437480064425549)
                    ·
                      refine ⟨220840327289055024159581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 588907539437480064425549 220840327289055024159581)
                      ·
                        rfl

theorem cell23_430085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 3, 3].length) (baseStart_430085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430085 prefixEnd_430085 := by exact prefixLift 430085
  have htrace : WordTrace (prefixWord ++ tailWord_430085) baseStart_430085 baseEnd_430085 := by
    simpa [prefixWord, tailWord_430085, baseEnd_430085] using wordTrace_append hprefix tailTrace_430085
  have hstable : (prefixWord ++ tailWord_430085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430085).length < 2 ^ (prefixWord ++ tailWord_430085).sum := by decide
  have hdescent : baseEnd_430085 < baseStart_430085 := by decide
  rcases family_descends (prefixWord ++ tailWord_430085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430088 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 2, 7]
def baseStart_430088 : Nat := 118140960795 + 430088 * 2 ^ 59
def prefixEnd_430088 : Nat := 4983230072969 + 3 ^ 40 * 430088 * 2
def baseEnd_430088 : Nat := 73613955910339504140689

theorem tailTrace_430088 : CollatzResearch.WordTrace tailWord_430088 prefixEnd_430088 73613955910339504140689 := by
  unfold tailWord_430088
  simp only [CollatzResearch.WordTrace]
  refine ⟨7843299032936052013801459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10457732043914736018401945 7843299032936052013801459)
  ·
    refine ⟨11764948549404078020702189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7843299032936052013801459 11764948549404078020702189)
    ·
      refine ⟨4411855706026529257763321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11764948549404078020702189 4411855706026529257763321)
      ·
        refine ⟨3308891779519896943322491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4411855706026529257763321 3308891779519896943322491)
        ·
          refine ⟨4963337669279845414983737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3308891779519896943322491 4963337669279845414983737)
          ·
            refine ⟨3722503251959884061237803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4963337669279845414983737 3722503251959884061237803)
            ·
              refine ⟨5583754877939826091856705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3722503251959884061237803 5583754877939826091856705)
              ·
                refine ⟨4187816158454869568892529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5583754877939826091856705 4187816158454869568892529)
                ·
                  refine ⟨3140862118841152176669397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4187816158454869568892529 3140862118841152176669397)
                  ·
                    refine ⟨73613955910339504140689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3140862118841152176669397 73613955910339504140689)
                    ·
                      rfl

theorem cell23_430088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_430088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430088 prefixEnd_430088 := by exact prefixLift 430088
  have htrace : WordTrace (prefixWord ++ tailWord_430088) baseStart_430088 baseEnd_430088 := by
    simpa [prefixWord, tailWord_430088, baseEnd_430088] using wordTrace_append hprefix tailTrace_430088
  have hstable : (prefixWord ++ tailWord_430088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430088).length < 2 ^ (prefixWord ++ tailWord_430088).sum := by decide
  have hdescent : baseEnd_430088 < baseStart_430088 := by decide
  rcases family_descends (prefixWord ++ tailWord_430088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430103 : List Nat := [1, 1, 3, 5, 2, 1, 2, 3, 1, 2, 2]
def baseStart_430103 : Nat := 118140960795 + 430103 * 2 ^ 59
def prefixEnd_430103 : Nat := 4983230072969 + 3 ^ 40 * 430103 * 2
def baseEnd_430103 : Nat := 220849569940835953734499

theorem tailTrace_430103 : CollatzResearch.WordTrace tailWord_430103 prefixEnd_430103 220849569940835953734499 := by
  unfold tailWord_430103
  simp only [CollatzResearch.WordTrace]
  refine ⟨15687145160817761589398963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10458096773878507726265975 15687145160817761589398963)
  ·
    refine ⟨23530717741226642384098445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15687145160817761589398963 23530717741226642384098445)
    ·
      refine ⟨8824019152959990894036917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23530717741226642384098445 8824019152959990894036917)
      ·
        refine ⟨827251795589999146315961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8824019152959990894036917 827251795589999146315961)
        ·
          refine ⟨620438846692499359736971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 827251795589999146315961 620438846692499359736971)
          ·
            refine ⟨930658270038749039605457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620438846692499359736971 930658270038749039605457)
            ·
              refine ⟨697993702529061779704093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 930658270038749039605457 697993702529061779704093)
              ·
                refine ⟨261747638448398167389035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 697993702529061779704093 261747638448398167389035)
                ·
                  refine ⟨392621457672597251083553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 261747638448398167389035 392621457672597251083553)
                  ·
                    refine ⟨294466093254447938312665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 392621457672597251083553 294466093254447938312665)
                    ·
                      refine ⟨220849569940835953734499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 294466093254447938312665 220849569940835953734499)
                      ·
                        rfl

theorem cell23_430103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_430103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430103 prefixEnd_430103 := by exact prefixLift 430103
  have htrace : WordTrace (prefixWord ++ tailWord_430103) baseStart_430103 baseEnd_430103 := by
    simpa [prefixWord, tailWord_430103, baseEnd_430103] using wordTrace_append hprefix tailTrace_430103
  have hstable : (prefixWord ++ tailWord_430103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430103).length < 2 ^ (prefixWord ++ tailWord_430103).sum := by decide
  have hdescent : baseEnd_430103 < baseStart_430103 := by decide
  rcases family_descends (prefixWord ++ tailWord_430103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430136 : List Nat := [2, 1, 2, 1, 6, 1, 3, 1, 2, 1, 3]
def baseStart_430136 : Nat := 118140960795 + 430136 * 2 ^ 59
def prefixEnd_430136 : Nat := 4983230072969 + 3 ^ 40 * 430136 * 2
def baseEnd_430136 : Nat := 220866514802434324621847

theorem tailTrace_430136 : CollatzResearch.WordTrace tailWord_430136 prefixEnd_430136 220866514802434324621847 := by
  unfold tailWord_430136
  simp only [CollatzResearch.WordTrace]
  refine ⟨7844174384849104112675131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10458899179798805483566841 7844174384849104112675131)
  ·
    refine ⟨11766261577273656169012697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7844174384849104112675131 11766261577273656169012697)
    ·
      refine ⟨8824696182955242126759523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11766261577273656169012697 8824696182955242126759523)
      ·
        refine ⟨13237044274432863190139285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8824696182955242126759523 13237044274432863190139285)
        ·
          refine ⟨620486450364040462037779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13237044274432863190139285 620486450364040462037779)
          ·
            refine ⟨930729675546060693056669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620486450364040462037779 930729675546060693056669)
            ·
              refine ⟨349023628329772759896251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 930729675546060693056669 349023628329772759896251)
              ·
                refine ⟨523535442494659139844377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349023628329772759896251 523535442494659139844377)
                ·
                  refine ⟨392651581870994354883283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 523535442494659139844377 392651581870994354883283)
                  ·
                    refine ⟨588977372806491532324925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 392651581870994354883283 588977372806491532324925)
                    ·
                      refine ⟨220866514802434324621847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 588977372806491532324925 220866514802434324621847)
                      ·
                        rfl

theorem cell23_430136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 2, 1, 3].length) (baseStart_430136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430136 prefixEnd_430136 := by exact prefixLift 430136
  have htrace : WordTrace (prefixWord ++ tailWord_430136) baseStart_430136 baseEnd_430136 := by
    simpa [prefixWord, tailWord_430136, baseEnd_430136] using wordTrace_append hprefix tailTrace_430136
  have hstable : (prefixWord ++ tailWord_430136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430136).length < 2 ^ (prefixWord ++ tailWord_430136).sum := by decide
  have hdescent : baseEnd_430136 < baseStart_430136 := by decide
  rcases family_descends (prefixWord ++ tailWord_430136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430162 : List Nat := [3, 2, 2, 1, 4, 1, 1, 1, 2, 1, 5]
def baseStart_430162 : Nat := 118140960795 + 430162 * 2 ^ 59
def prefixEnd_430162 : Nat := 4983230072969 + 3 ^ 40 * 430162 * 2
def baseEnd_430162 : Nat := 220879865299451222896727

theorem tailTrace_430162 : CollatzResearch.WordTrace tailWord_430162 prefixEnd_430162 220879865299451222896727 := by
  unfold tailWord_430162
  simp only [CollatzResearch.WordTrace]
  refine ⟨3922324266901003666449185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10459531378402676443864493 3922324266901003666449185)
  ·
    refine ⟨2941743200175752749836889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3922324266901003666449185 2941743200175752749836889)
    ·
      refine ⟨2206307400131814562377667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2941743200175752749836889 2206307400131814562377667)
      ·
        refine ⟨3309461100197721843566501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2206307400131814562377667 3309461100197721843566501)
        ·
          refine ⟨620523956287072845668719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3309461100197721843566501 620523956287072845668719)
          ·
            refine ⟨930785934430609268503079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620523956287072845668719 930785934430609268503079)
            ·
              refine ⟨1396178901645913902754619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 930785934430609268503079 1396178901645913902754619)
              ·
                refine ⟨2094268352468870854131929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1396178901645913902754619 2094268352468870854131929)
                ·
                  refine ⟨1570701264351653140598947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2094268352468870854131929 1570701264351653140598947)
                  ·
                    refine ⟨2356051896527479710898421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1570701264351653140598947 2356051896527479710898421)
                    ·
                      refine ⟨220879865299451222896727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2356051896527479710898421 220879865299451222896727)
                      ·
                        rfl

theorem cell23_430162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_430162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430162 prefixEnd_430162 := by exact prefixLift 430162
  have htrace : WordTrace (prefixWord ++ tailWord_430162) baseStart_430162 baseEnd_430162 := by
    simpa [prefixWord, tailWord_430162, baseEnd_430162] using wordTrace_append hprefix tailTrace_430162
  have hstable : (prefixWord ++ tailWord_430162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430162).length < 2 ^ (prefixWord ++ tailWord_430162).sum := by decide
  have hdescent : baseEnd_430162 < baseStart_430162 := by decide
  rcases family_descends (prefixWord ++ tailWord_430162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430175 : List Nat := [1, 1, 2, 3, 1, 1, 2, 4, 2, 3, 3]
def baseStart_430175 : Nat := 118140960795 + 430175 * 2 ^ 59
def prefixEnd_430175 : Nat := 4983230072969 + 3 ^ 40 * 430175 * 2
def baseEnd_430175 : Nat := 220886540547959672034167

theorem tailTrace_430175 : CollatzResearch.WordTrace tailWord_430175 prefixEnd_430175 220886540547959672034167 := by
  unfold tailWord_430175
  simp only [CollatzResearch.WordTrace]
  refine ⟨15689771216556917886019979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10459847477704611924013319 15689771216556917886019979)
  ·
    refine ⟨23534656824835376829029969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15689771216556917886019979 23534656824835376829029969)
    ·
      refine ⟨17650992618626532621772477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23534656824835376829029969 17650992618626532621772477)
      ·
        refine ⟨6619122231984949733164679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17650992618626532621772477 6619122231984949733164679)
        ·
          refine ⟨9928683347977424599747019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6619122231984949733164679 9928683347977424599747019)
          ·
            refine ⟨14893025021966136899620529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9928683347977424599747019 14893025021966136899620529)
            ·
              refine ⟨11169768766474602674715397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14893025021966136899620529 11169768766474602674715397)
              ·
                refine ⟨2094331643713988001509137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11169768766474602674715397 2094331643713988001509137)
                ·
                  refine ⟨1570748732785491001131853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2094331643713988001509137 1570748732785491001131853)
                  ·
                    refine ⟨589030774794559125424445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1570748732785491001131853 589030774794559125424445)
                    ·
                      refine ⟨220886540547959672034167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 589030774794559125424445 220886540547959672034167)
                      ·
                        rfl

theorem cell23_430175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_430175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430175 prefixEnd_430175 := by exact prefixLift 430175
  have htrace : WordTrace (prefixWord ++ tailWord_430175) baseStart_430175 baseEnd_430175 := by
    simpa [prefixWord, tailWord_430175, baseEnd_430175] using wordTrace_append hprefix tailTrace_430175
  have hstable : (prefixWord ++ tailWord_430175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430175).length < 2 ^ (prefixWord ++ tailWord_430175).sum := by decide
  have hdescent : baseEnd_430175 < baseStart_430175 := by decide
  rcases family_descends (prefixWord ++ tailWord_430175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430212 : List Nat := [2, 3, 2, 1, 2, 1, 4, 1, 2, 5]
def baseStart_430212 : Nat := 118140960795 + 430212 * 2 ^ 59
def prefixEnd_430212 : Nat := 4983230072969 + 3 ^ 40 * 430212 * 2
def baseEnd_430212 : Nat := 73635179777392009090499

theorem tailTrace_430212 : CollatzResearch.WordTrace tailWord_430212 prefixEnd_430212 73635179777392009090499 := by
  unfold tailWord_430212
  simp only [CollatzResearch.WordTrace]
  refine ⟨7845560358711436602558445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10460747144948582136744593 7845560358711436602558445)
  ·
    refine ⟨2942085134516788725959417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7845560358711436602558445 2942085134516788725959417)
    ·
      refine ⟨2206563850887591544469563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2942085134516788725959417 2206563850887591544469563)
      ·
        refine ⟨3309845776331387316704345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2206563850887591544469563 3309845776331387316704345)
        ·
          refine ⟨2482384332248540487528259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3309845776331387316704345 2482384332248540487528259)
          ·
            refine ⟨3723576498372810731292389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2482384332248540487528259 3723576498372810731292389)
            ·
              refine ⟨698170593444902012117323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3723576498372810731292389 698170593444902012117323)
              ·
                refine ⟨1047255890167353018175985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 698170593444902012117323 1047255890167353018175985)
                ·
                  refine ⟨785441917625514763631989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1047255890167353018175985 785441917625514763631989)
                  ·
                    refine ⟨73635179777392009090499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 785441917625514763631989 73635179777392009090499)
                    ·
                      rfl

theorem cell23_430212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_430212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430212 prefixEnd_430212 := by exact prefixLift 430212
  have htrace : WordTrace (prefixWord ++ tailWord_430212) baseStart_430212 baseEnd_430212 := by
    simpa [prefixWord, tailWord_430212, baseEnd_430212] using wordTrace_append hprefix tailTrace_430212
  have hstable : (prefixWord ++ tailWord_430212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430212).length < 2 ^ (prefixWord ++ tailWord_430212).sum := by decide
  have hdescent : baseEnd_430212 < baseStart_430212 := by decide
  rcases family_descends (prefixWord ++ tailWord_430212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430215 : List Nat := [1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 4]
def baseStart_430215 : Nat := 118140960795 + 430215 * 2 ^ 59
def prefixEnd_430215 : Nat := 4983230072969 + 3 ^ 40 * 430215 * 2
def baseEnd_430215 : Nat := 220907079774139515533983

theorem tailTrace_430215 : CollatzResearch.WordTrace tailWord_430215 prefixEnd_430215 220907079774139515533983 := by
  unfold tailWord_430215
  simp only [CollatzResearch.WordTrace]
  refine ⟨15691230136412004717476099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10460820090941336478317399 15691230136412004717476099)
  ·
    refine ⟨23536845204618007076214149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15691230136412004717476099 23536845204618007076214149)
    ·
      refine ⟨4413158475865876326790153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23536845204618007076214149 4413158475865876326790153)
      ·
        refine ⟨3309868856899407245092615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4413158475865876326790153 3309868856899407245092615)
        ·
          refine ⟨4964803285349110867638923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3309868856899407245092615 4964803285349110867638923)
          ·
            refine ⟨7447204928023666301458385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4964803285349110867638923 7447204928023666301458385)
            ·
              refine ⟨5585403696017749726093789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7447204928023666301458385 5585403696017749726093789)
              ·
                refine ⟨2094526386006656147285171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5585403696017749726093789 2094526386006656147285171)
                ·
                  refine ⟨3141789579009984220927757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2094526386006656147285171 3141789579009984220927757)
                  ·
                    refine ⟨1178171092128744082847909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3141789579009984220927757 1178171092128744082847909)
                    ·
                      refine ⟨220907079774139515533983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1178171092128744082847909 220907079774139515533983)
                      ·
                        rfl

theorem cell23_430215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_430215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430215 prefixEnd_430215 := by exact prefixLift 430215
  have htrace : WordTrace (prefixWord ++ tailWord_430215) baseStart_430215 baseEnd_430215 := by
    simpa [prefixWord, tailWord_430215, baseEnd_430215] using wordTrace_append hprefix tailTrace_430215
  have hstable : (prefixWord ++ tailWord_430215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430215).length < 2 ^ (prefixWord ++ tailWord_430215).sum := by decide
  have hdescent : baseEnd_430215 < baseStart_430215 := by decide
  rcases family_descends (prefixWord ++ tailWord_430215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430276 : List Nat := [2, 3, 3, 1, 2, 1, 1, 5, 1, 4]
def baseStart_430276 : Nat := 118140960795 + 430276 * 2 ^ 59
def prefixEnd_430276 : Nat := 4983230072969 + 3 ^ 40 * 430276 * 2
def baseEnd_430276 : Nat := 73646134031354592290401

theorem tailTrace_430276 : CollatzResearch.WordTrace tailWord_430276 prefixEnd_430276 73646134031354592290401 := by
  unfold tailWord_430276
  simp only [CollatzResearch.WordTrace]
  refine ⟨7846727494595506067723341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10462303326127341423631121 7846727494595506067723341)
  ·
    refine ⟨2942522810473314775396253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7846727494595506067723341 2942522810473314775396253)
    ·
      refine ⟨1103446053927493040773595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2942522810473314775396253 1103446053927493040773595)
      ·
        refine ⟨1655169080891239561160393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1103446053927493040773595 1655169080891239561160393)
        ·
          refine ⟨1241376810668429670870295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1655169080891239561160393 1241376810668429670870295)
          ·
            refine ⟨1862065216002644506305443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1241376810668429670870295 1862065216002644506305443)
            ·
              refine ⟨2793097824003966759458165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1862065216002644506305443 2793097824003966759458165)
              ·
                refine ⟨261852921000371883699203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2793097824003966759458165 261852921000371883699203)
                ·
                  refine ⟨392779381500557825548805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 261852921000371883699203 392779381500557825548805)
                  ·
                    refine ⟨73646134031354592290401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 392779381500557825548805 73646134031354592290401)
                    ·
                      rfl

theorem cell23_430276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_430276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430276 prefixEnd_430276 := by exact prefixLift 430276
  have htrace : WordTrace (prefixWord ++ tailWord_430276) baseStart_430276 baseEnd_430276 := by
    simpa [prefixWord, tailWord_430276, baseEnd_430276] using wordTrace_append hprefix tailTrace_430276
  have hstable : (prefixWord ++ tailWord_430276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430276).length < 2 ^ (prefixWord ++ tailWord_430276).sum := by decide
  have hdescent : baseEnd_430276 < baseStart_430276 := by decide
  rcases family_descends (prefixWord ++ tailWord_430276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430309 : List Nat := [1, 3, 1, 4, 2, 1, 1, 2, 1, 5, 2]
def baseStart_430309 : Nat := 118140960795 + 430309 * 2 ^ 59
def prefixEnd_430309 : Nat := 4983230072969 + 3 ^ 40 * 430309 * 2
def baseEnd_430309 : Nat := 220955346955662147758551

theorem tailTrace_430309 : CollatzResearch.WordTrace tailWord_430309 prefixEnd_430309 220955346955662147758551 := by
  unfold tailWord_430309
  simp only [CollatzResearch.WordTrace]
  refine ⟨15694658598071458771397981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10463105732047639180931987 15694658598071458771397981)
  ·
    refine ⟨5885496974276797039274243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15694658598071458771397981 5885496974276797039274243)
    ·
      refine ⟨8828245461415195558911365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5885496974276797039274243 8828245461415195558911365)
      ·
        refine ⟨1655296024015349167295881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8828245461415195558911365 1655296024015349167295881)
        ·
          refine ⟨1241472018011511875471911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1655296024015349167295881 1241472018011511875471911)
          ·
            refine ⟨1862208027017267813207867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1241472018011511875471911 1862208027017267813207867)
            ·
              refine ⟨2793312040525901719811801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1862208027017267813207867 2793312040525901719811801)
              ·
                refine ⟨2094984030394426289858851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2793312040525901719811801 2094984030394426289858851)
                ·
                  refine ⟨3142476045591639434788277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2094984030394426289858851 3142476045591639434788277)
                  ·
                    refine ⟨294607129274216197011401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3142476045591639434788277 294607129274216197011401)
                    ·
                      refine ⟨220955346955662147758551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 294607129274216197011401 220955346955662147758551)
                      ·
                        rfl

theorem cell23_430309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_430309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430309 prefixEnd_430309 := by exact prefixLift 430309
  have htrace : WordTrace (prefixWord ++ tailWord_430309) baseStart_430309 baseEnd_430309 := by
    simpa [prefixWord, tailWord_430309, baseEnd_430309] using wordTrace_append hprefix tailTrace_430309
  have hstable : (prefixWord ++ tailWord_430309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430309).length < 2 ^ (prefixWord ++ tailWord_430309).sum := by decide
  have hdescent : baseEnd_430309 < baseStart_430309 := by decide
  rcases family_descends (prefixWord ++ tailWord_430309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430319 : List Nat := [1, 1, 2, 1, 6, 2, 2, 2, 1, 5]
def baseStart_430319 : Nat := 118140960795 + 430319 * 2 ^ 59
def prefixEnd_430319 : Nat := 4983230072969 + 3 ^ 40 * 430319 * 2
def baseEnd_430319 : Nat := 73653493920735702877835

theorem tailTrace_430319 : CollatzResearch.WordTrace tailWord_430319 prefixEnd_430319 73653493920735702877835 := by
  unfold tailWord_430319
  simp only [CollatzResearch.WordTrace]
  refine ⟨15695023328035230479262011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10463348885356820319508007 15695023328035230479262011)
  ·
    refine ⟨23542534992052845718893017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15695023328035230479262011 23542534992052845718893017)
    ·
      refine ⟨17656901244039634289169763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23542534992052845718893017 17656901244039634289169763)
      ·
        refine ⟨26485351866059451433754645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17656901244039634289169763 26485351866059451433754645)
        ·
          refine ⟨1241500868721536785957249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 26485351866059451433754645 1241500868721536785957249)
          ·
            refine ⟨931125651541152589467937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1241500868721536785957249 931125651541152589467937)
            ·
              refine ⟨698344238655864442100953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 931125651541152589467937 698344238655864442100953)
              ·
                refine ⟨523758178991898331575715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 698344238655864442100953 523758178991898331575715)
                ·
                  refine ⟨785637268487847497363573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 523758178991898331575715 785637268487847497363573)
                  ·
                    refine ⟨73653493920735702877835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 785637268487847497363573 73653493920735702877835)
                    ·
                      rfl

theorem cell23_430319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 5].length) (baseStart_430319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430319 prefixEnd_430319 := by exact prefixLift 430319
  have htrace : WordTrace (prefixWord ++ tailWord_430319) baseStart_430319 baseEnd_430319 := by
    simpa [prefixWord, tailWord_430319, baseEnd_430319] using wordTrace_append hprefix tailTrace_430319
  have hstable : (prefixWord ++ tailWord_430319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430319).length < 2 ^ (prefixWord ++ tailWord_430319).sum := by decide
  have hdescent : baseEnd_430319 < baseStart_430319 := by decide
  rcases family_descends (prefixWord ++ tailWord_430319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430343 : List Nat := [1, 1, 4, 5, 1, 1, 1, 2, 2, 3, 2]
def baseStart_430343 : Nat := 118140960795 + 430343 * 2 ^ 59
def prefixEnd_430343 : Nat := 4983230072969 + 3 ^ 40 * 430343 * 2
def baseEnd_430343 : Nat := 220972805297915014733395

theorem tailTrace_430343 : CollatzResearch.WordTrace tailWord_430343 prefixEnd_430343 220972805297915014733395 := by
  unfold tailWord_430343
  simp only [CollatzResearch.WordTrace]
  refine ⟨15695898679948282578135683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10463932453298855052090455 15695898679948282578135683)
  ·
    refine ⟨23543848019922423867203525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15695898679948282578135683 23543848019922423867203525)
    ·
      refine ⟨4414471503735454475100661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23543848019922423867203525 4414471503735454475100661)
      ·
        refine ⟨413856703475198857040687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4414471503735454475100661 413856703475198857040687)
        ·
          refine ⟨620785055212798285561031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413856703475198857040687 620785055212798285561031)
          ·
            refine ⟨931177582819197428341547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620785055212798285561031 931177582819197428341547)
            ·
              refine ⟨1396766374228796142512321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 931177582819197428341547 1396766374228796142512321)
              ·
                refine ⟨1047574780671597106884241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1396766374228796142512321 1047574780671597106884241)
                ·
                  refine ⟨785681085503697830163181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1047574780671597106884241 785681085503697830163181)
                  ·
                    refine ⟨294630407063886686311193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 785681085503697830163181 294630407063886686311193)
                    ·
                      refine ⟨220972805297915014733395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 294630407063886686311193 220972805297915014733395)
                      ·
                        rfl

theorem cell23_430343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_430343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430343 prefixEnd_430343 := by exact prefixLift 430343
  have htrace : WordTrace (prefixWord ++ tailWord_430343) baseStart_430343 baseEnd_430343 := by
    simpa [prefixWord, tailWord_430343, baseEnd_430343] using wordTrace_append hprefix tailTrace_430343
  have hstable : (prefixWord ++ tailWord_430343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430343).length < 2 ^ (prefixWord ++ tailWord_430343).sum := by decide
  have hdescent : baseEnd_430343 < baseStart_430343 := by decide
  rcases family_descends (prefixWord ++ tailWord_430343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430345 : List Nat := [1, 2, 1, 1, 3, 4, 11]
def baseStart_430345 : Nat := 118140960795 + 430345 * 2 ^ 59
def prefixEnd_430345 : Nat := 4983230072969 + 3 ^ 40 * 430345 * 2
def baseEnd_430345 : Nat := 2728072003200296381585

theorem tailTrace_430345 : CollatzResearch.WordTrace tailWord_430345 prefixEnd_430345 2728072003200296381585 := by
  unfold tailWord_430345
  simp only [CollatzResearch.WordTrace]
  refine ⟨15695971625941036919708489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10463981083960691279805659 15695971625941036919708489)
  ·
    refine ⟨11771978719455777689781367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15695971625941036919708489 11771978719455777689781367)
    ·
      refine ⟨17657968079183666534672051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11771978719455777689781367 17657968079183666534672051)
      ·
        refine ⟨26486952118775499802008077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17657968079183666534672051 26486952118775499802008077)
        ·
          refine ⟨9932607044540812425753029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26486952118775499802008077 9932607044540812425753029)
          ·
            refine ⟨1862363820851402329828693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9932607044540812425753029 1862363820851402329828693)
            ·
              refine ⟨2728072003200296381585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 1862363820851402329828693 2728072003200296381585)
              ·
                rfl

theorem cell23_430345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 11].length) (baseStart_430345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430345 prefixEnd_430345 := by exact prefixLift 430345
  have htrace : WordTrace (prefixWord ++ tailWord_430345) baseStart_430345 baseEnd_430345 := by
    simpa [prefixWord, tailWord_430345, baseEnd_430345] using wordTrace_append hprefix tailTrace_430345
  have hstable : (prefixWord ++ tailWord_430345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430345).length < 2 ^ (prefixWord ++ tailWord_430345).sum := by decide
  have hdescent : baseEnd_430345 < baseStart_430345 := by decide
  rcases family_descends (prefixWord ++ tailWord_430345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430373 : List Nat := [1, 3, 1, 2, 6, 1, 1, 2, 1, 1, 4]
def baseStart_430373 : Nat := 118140960795 + 430373 * 2 ^ 59
def prefixEnd_430373 : Nat := 4983230072969 + 3 ^ 40 * 430373 * 2
def baseEnd_430373 : Nat := 220988209717549897358257

theorem tailTrace_430373 : CollatzResearch.WordTrace tailWord_430373 prefixEnd_430373 220988209717549897358257 := by
  unfold tailWord_430373
  simp only [CollatzResearch.WordTrace]
  refine ⟨15696992869839597701727773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10464661913226398467818515 15696992869839597701727773)
  ·
    refine ⟨5886372326189849138147915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15696992869839597701727773 5886372326189849138147915)
    ·
      refine ⟨8829558489284773707221873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5886372326189849138147915 8829558489284773707221873)
      ·
        refine ⟨6622168866963580280416405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8829558489284773707221873 6622168866963580280416405)
        ·
          refine ⟨310414165638917825644519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6622168866963580280416405 310414165638917825644519)
          ·
            refine ⟨465621248458376738466779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310414165638917825644519 465621248458376738466779)
            ·
              refine ⟨698431872687565107700169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465621248458376738466779 698431872687565107700169)
              ·
                refine ⟨523823904515673830775127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 698431872687565107700169 523823904515673830775127)
                ·
                  refine ⟨785735856773510746162691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 523823904515673830775127 785735856773510746162691)
                  ·
                    refine ⟨1178603785160266119244037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 785735856773510746162691 1178603785160266119244037)
                    ·
                      refine ⟨220988209717549897358257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1178603785160266119244037 220988209717549897358257)
                      ·
                        rfl

theorem cell23_430373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 1, 1, 4].length) (baseStart_430373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430373 prefixEnd_430373 := by exact prefixLift 430373
  have htrace : WordTrace (prefixWord ++ tailWord_430373) baseStart_430373 baseEnd_430373 := by
    simpa [prefixWord, tailWord_430373, baseEnd_430373] using wordTrace_append hprefix tailTrace_430373
  have hstable : (prefixWord ++ tailWord_430373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430373).length < 2 ^ (prefixWord ++ tailWord_430373).sum := by decide
  have hdescent : baseEnd_430373 < baseStart_430373 := by decide
  rcases family_descends (prefixWord ++ tailWord_430373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430376 : List Nat := [2, 1, 5, 1, 3, 1, 1, 1, 3, 2, 3]
def baseStart_430376 : Nat := 118140960795 + 430376 * 2 ^ 59
def prefixEnd_430376 : Nat := 4983230072969 + 3 ^ 40 * 430376 * 2
def baseEnd_430376 : Nat := 220989750159513385620743

theorem tailTrace_430376 : CollatzResearch.WordTrace tailWord_430376 prefixEnd_430376 220989750159513385620743 := by
  unfold tailWord_430376
  simp only [CollatzResearch.WordTrace]
  refine ⟨7848551144414364607043491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10464734859219152809391321 7848551144414364607043491)
  ·
    refine ⟨11772826716621546910565237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7848551144414364607043491 11772826716621546910565237)
    ·
      refine ⟨1103702504683270022865491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11772826716621546910565237 1103702504683270022865491)
      ·
        refine ⟨1655553757024905034298237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1103702504683270022865491 1655553757024905034298237)
        ·
          refine ⟨620832658884339387861839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1655553757024905034298237 620832658884339387861839)
          ·
            refine ⟨931248988326509081792759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620832658884339387861839 931248988326509081792759)
            ·
              refine ⟨1396873482489763622689139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 931248988326509081792759 1396873482489763622689139)
              ·
                refine ⟨2095310223734645434033709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1396873482489763622689139 2095310223734645434033709)
                ·
                  refine ⟨785741333900492037762641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2095310223734645434033709 785741333900492037762641)
                  ·
                    refine ⟨589306000425369028321981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 785741333900492037762641 589306000425369028321981)
                    ·
                      refine ⟨220989750159513385620743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 589306000425369028321981 220989750159513385620743)
                      ·
                        rfl

theorem cell23_430376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_430376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430376 prefixEnd_430376 := by exact prefixLift 430376
  have htrace : WordTrace (prefixWord ++ tailWord_430376) baseStart_430376 baseEnd_430376 := by
    simpa [prefixWord, tailWord_430376, baseEnd_430376] using wordTrace_append hprefix tailTrace_430376
  have hstable : (prefixWord ++ tailWord_430376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430376).length < 2 ^ (prefixWord ++ tailWord_430376).sum := by decide
  have hdescent : baseEnd_430376 < baseStart_430376 := by decide
  rcases family_descends (prefixWord ++ tailWord_430376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430389 : List Nat := [1, 3, 3, 1, 2, 1, 3, 2, 1, 3, 3]
def baseStart_430389 : Nat := 118140960795 + 430389 * 2 ^ 59
def prefixEnd_430389 : Nat := 4983230072969 + 3 ^ 40 * 430389 * 2
def baseEnd_430389 : Nat := 220996425408021834758183

theorem tailTrace_430389 : CollatzResearch.WordTrace tailWord_430389 prefixEnd_430389 220996425408021834758183 := by
  unfold tailWord_430389
  simp only [CollatzResearch.WordTrace]
  refine ⟨15697576437781632434310221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10465050958521088289540147 15697576437781632434310221)
  ·
    refine ⟨5886591164168112162866333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15697576437781632434310221 5886591164168112162866333)
    ·
      refine ⟨2207471686563042061074875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5886591164168112162866333 2207471686563042061074875)
      ·
        refine ⟨3311207529844563091612313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2207471686563042061074875 3311207529844563091612313)
        ·
          refine ⟨2483405647383422318709235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3311207529844563091612313 2483405647383422318709235)
          ·
            refine ⟨3725108471075133478063853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2483405647383422318709235 3725108471075133478063853)
            ·
              refine ⟨1396915676653175054273945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3725108471075133478063853 1396915676653175054273945)
              ·
                refine ⟨1047686757489881290705459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1396915676653175054273945 1047686757489881290705459)
                ·
                  refine ⟨1571530136234821936058189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1047686757489881290705459 1571530136234821936058189)
                  ·
                    refine ⟨589323801088058226021821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1571530136234821936058189 589323801088058226021821)
                    ·
                      refine ⟨220996425408021834758183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 589323801088058226021821 220996425408021834758183)
                      ·
                        rfl

theorem cell23_430389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_430389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430389 prefixEnd_430389 := by exact prefixLift 430389
  have htrace : WordTrace (prefixWord ++ tailWord_430389) baseStart_430389 baseEnd_430389 := by
    simpa [prefixWord, tailWord_430389, baseEnd_430389] using wordTrace_append hprefix tailTrace_430389
  have hstable : (prefixWord ++ tailWord_430389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430389).length < 2 ^ (prefixWord ++ tailWord_430389).sum := by decide
  have hdescent : baseEnd_430389 < baseStart_430389 := by decide
  rcases family_descends (prefixWord ++ tailWord_430389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430393 : List Nat := [1, 2, 1, 6, 1, 2, 3, 1, 1, 2, 3]
def baseStart_430393 : Nat := 118140960795 + 430393 * 2 ^ 59
def prefixEnd_430393 : Nat := 4983230072969 + 3 ^ 40 * 430393 * 2
def baseEnd_430393 : Nat := 220998479330639819108165

theorem tailTrace_430393 : CollatzResearch.WordTrace tailWord_430393 prefixEnd_430393 220998479330639819108165 := by
  unfold tailWord_430393
  simp only [CollatzResearch.WordTrace]
  refine ⟨15697722329767141117455833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10465148219844760744970555 15697722329767141117455833)
  ·
    refine ⟨11773291747325355838091875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15697722329767141117455833 11773291747325355838091875)
    ·
      refine ⟨17659937620988033757137813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11773291747325355838091875 17659937620988033757137813)
      ·
        refine ⟨827809575983814082365835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17659937620988033757137813 827809575983814082365835)
        ·
          refine ⟨1241714363975721123548753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 827809575983814082365835 1241714363975721123548753)
          ·
            refine ⟨931285772981790842661565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1241714363975721123548753 931285772981790842661565)
            ·
              refine ⟨349232164868171565998087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 931285772981790842661565 349232164868171565998087)
              ·
                refine ⟨523848247302257348997131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349232164868171565998087 523848247302257348997131)
                ·
                  refine ⟨785772370953386023495697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 523848247302257348997131 785772370953386023495697)
                  ·
                    refine ⟨589329278215039517621773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 785772370953386023495697 589329278215039517621773)
                    ·
                      refine ⟨220998479330639819108165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 589329278215039517621773 220998479330639819108165)
                      ·
                        rfl

theorem cell23_430393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_430393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430393 prefixEnd_430393 := by exact prefixLift 430393
  have htrace : WordTrace (prefixWord ++ tailWord_430393) baseStart_430393 baseEnd_430393 := by
    simpa [prefixWord, tailWord_430393, baseEnd_430393] using wordTrace_append hprefix tailTrace_430393
  have hstable : (prefixWord ++ tailWord_430393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430393).length < 2 ^ (prefixWord ++ tailWord_430393).sum := by decide
  have hdescent : baseEnd_430393 < baseStart_430393 := by decide
  rcases family_descends (prefixWord ++ tailWord_430393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430412 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 1, 5, 4]
def baseStart_430412 : Nat := 118140960795 + 430412 * 2 ^ 59
def prefixEnd_430412 : Nat := 4983230072969 + 3 ^ 40 * 430412 * 2
def baseEnd_430412 : Nat := 221008235463075244770577

theorem tailTrace_430412 : CollatzResearch.WordTrace tailWord_430412 prefixEnd_430412 221008235463075244770577 := by
  unfold tailWord_430412
  simp only [CollatzResearch.WordTrace]
  refine ⟨7849207658349153681198745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10465610211132204908264993 7849207658349153681198745)
  ·
    refine ⟨5886905743761865260899059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7849207658349153681198745 5886905743761865260899059)
    ·
      refine ⟨8830358615642797891348589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5886905743761865260899059 8830358615642797891348589)
      ·
        refine ⟨3311384480866049209255721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8830358615642797891348589 3311384480866049209255721)
        ·
          refine ⟨2483538360649536906941791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3311384480866049209255721 2483538360649536906941791)
          ·
            refine ⟨3725307540974305360412687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2483538360649536906941791 3725307540974305360412687)
            ·
              refine ⟨5587961311461458040619031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3725307540974305360412687 5587961311461458040619031)
              ·
                refine ⟨8381941967192187060928547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5587961311461458040619031 8381941967192187060928547)
                ·
                  refine ⟨12572912950788280591392821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8381941967192187060928547 12572912950788280591392821)
                  ·
                    refine ⟨1178710589136401305443077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12572912950788280591392821 1178710589136401305443077)
                    ·
                      refine ⟨221008235463075244770577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1178710589136401305443077 221008235463075244770577)
                      ·
                        rfl

theorem cell23_430412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_430412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430412 prefixEnd_430412 := by exact prefixLift 430412
  have htrace : WordTrace (prefixWord ++ tailWord_430412) baseStart_430412 baseEnd_430412 := by
    simpa [prefixWord, tailWord_430412, baseEnd_430412] using wordTrace_append hprefix tailTrace_430412
  have hstable : (prefixWord ++ tailWord_430412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430412).length < 2 ^ (prefixWord ++ tailWord_430412).sum := by decide
  have hdescent : baseEnd_430412 < baseStart_430412 := by decide
  rcases family_descends (prefixWord ++ tailWord_430412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430450 : List Nat := [3, 2, 1, 2, 1, 5, 2, 1, 1, 3, 2]
def baseStart_430450 : Nat := 118140960795 + 430450 * 2 ^ 59
def prefixEnd_430450 : Nat := 4983230072969 + 3 ^ 40 * 430450 * 2
def baseEnd_430450 : Nat := 221027747727946096095403

theorem tailTrace_430450 : CollatzResearch.WordTrace tailWord_430450 prefixEnd_430450 221027747727946096095403 := by
  unfold tailWord_430450
  simp only [CollatzResearch.WordTrace]
  refine ⟨3924950322640159963070201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10466534193707093234853869 3924950322640159963070201)
  ·
    refine ⟨2943712741980119972302651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3924950322640159963070201 2943712741980119972302651)
    ·
      refine ⟨4415569112970179958453977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2943712741980119972302651 4415569112970179958453977)
      ·
        refine ⟨3311676834727634968840483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4415569112970179958453977 3311676834727634968840483)
        ·
          refine ⟨4967515252091452453260725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3311676834727634968840483 4967515252091452453260725)
          ·
            refine ⟨465704554883573667493193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4967515252091452453260725 465704554883573667493193)
            ·
              refine ⟨349278416162680250619895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 465704554883573667493193 349278416162680250619895)
              ·
                refine ⟨523917624244020375929843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349278416162680250619895 523917624244020375929843)
                ·
                  refine ⟨785876436366030563894765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 523917624244020375929843 785876436366030563894765)
                  ·
                    refine ⟨294703663637261461460537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 785876436366030563894765 294703663637261461460537)
                    ·
                      refine ⟨221027747727946096095403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 294703663637261461460537 221027747727946096095403)
                      ·
                        rfl

theorem cell23_430450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_430450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430450 prefixEnd_430450 := by exact prefixLift 430450
  have htrace : WordTrace (prefixWord ++ tailWord_430450) baseStart_430450 baseEnd_430450 := by
    simpa [prefixWord, tailWord_430450, baseEnd_430450] using wordTrace_append hprefix tailTrace_430450
  have hstable : (prefixWord ++ tailWord_430450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430450).length < 2 ^ (prefixWord ++ tailWord_430450).sum := by decide
  have hdescent : baseEnd_430450 < baseStart_430450 := by decide
  rcases family_descends (prefixWord ++ tailWord_430450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430503 : List Nat := [1, 1, 6, 1, 1, 4, 1, 3, 5]
def baseStart_430503 : Nat := 118140960795 + 430503 * 2 ^ 59
def prefixEnd_430503 : Nat := 4983230072969 + 3 ^ 40 * 430503 * 2
def baseEnd_430503 : Nat := 24561662466959376525851

theorem tailTrace_430503 : CollatzResearch.WordTrace tailWord_430503 prefixEnd_430503 24561662466959376525851 := by
  unfold tailWord_430503
  simp only [CollatzResearch.WordTrace]
  refine ⟨15701734359368629903960163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10467822906245753269306775 15701734359368629903960163)
  ·
    refine ⟨23552601539052944855940245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15701734359368629903960163 23552601539052944855940245)
    ·
      refine ⟨1104028197143106790122199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23552601539052944855940245 1104028197143106790122199)
      ·
        refine ⟨1656042295714660185183299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1104028197143106790122199 1656042295714660185183299)
        ·
          refine ⟨2484063443571990277774949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1656042295714660185183299 2484063443571990277774949)
          ·
            refine ⟨465761895669748177082803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2484063443571990277774949 465761895669748177082803)
            ·
              refine ⟨698642843504622265624205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465761895669748177082803 698642843504622265624205)
              ·
                refine ⟨261991066314233349609077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 698642843504622265624205 261991066314233349609077)
                ·
                  refine ⟨24561662466959376525851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 261991066314233349609077 24561662466959376525851)
                  ·
                    rfl

theorem cell23_430503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 3, 5].length) (baseStart_430503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430503 prefixEnd_430503 := by exact prefixLift 430503
  have htrace : WordTrace (prefixWord ++ tailWord_430503) baseStart_430503 baseEnd_430503 := by
    simpa [prefixWord, tailWord_430503, baseEnd_430503] using wordTrace_append hprefix tailTrace_430503
  have hstable : (prefixWord ++ tailWord_430503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430503).length < 2 ^ (prefixWord ++ tailWord_430503).sum := by decide
  have hdescent : baseEnd_430503 < baseStart_430503 := by decide
  rcases family_descends (prefixWord ++ tailWord_430503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430519 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 4]
def baseStart_430519 : Nat := 118140960795 + 430519 * 2 ^ 59
def prefixEnd_430519 : Nat := 4983230072969 + 3 ^ 40 * 430519 * 2
def baseEnd_430519 : Nat := 221063177893106326132585

theorem tailTrace_430519 : CollatzResearch.WordTrace tailWord_430519 prefixEnd_430519 221063177893106326132585 := by
  unfold tailWord_430519
  simp only [CollatzResearch.WordTrace]
  refine ⟨15702317927310664636542611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10468211951540443091028407 15702317927310664636542611)
  ·
    refine ⟨23553476890965996954813917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15702317927310664636542611 23553476890965996954813917)
    ·
      refine ⟨8832553834112248858055219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23553476890965996954813917 8832553834112248858055219)
      ·
        refine ⟨13248830751168373287082829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8832553834112248858055219 13248830751168373287082829)
        ·
          refine ⟨4968311531688139982656061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13248830751168373287082829 4968311531688139982656061)
          ·
            refine ⟨1863116824383052493496023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4968311531688139982656061 1863116824383052493496023)
            ·
              refine ⟨2794675236574578740244035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1863116824383052493496023 2794675236574578740244035)
              ·
                refine ⟨4192012854861868110366053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2794675236574578740244035 4192012854861868110366053)
                ·
                  refine ⟨786002410286600270693635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4192012854861868110366053 786002410286600270693635)
                  ·
                    refine ⟨1179003615429900406040453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 786002410286600270693635 1179003615429900406040453)
                    ·
                      refine ⟨221063177893106326132585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1179003615429900406040453 221063177893106326132585)
                      ·
                        rfl

theorem cell23_430519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_430519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430519 prefixEnd_430519 := by exact prefixLift 430519
  have htrace : WordTrace (prefixWord ++ tailWord_430519) baseStart_430519 baseEnd_430519 := by
    simpa [prefixWord, tailWord_430519, baseEnd_430519] using wordTrace_append hprefix tailTrace_430519
  have hstable : (prefixWord ++ tailWord_430519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430519).length < 2 ^ (prefixWord ++ tailWord_430519).sum := by decide
  have hdescent : baseEnd_430519 < baseStart_430519 := by decide
  rcases family_descends (prefixWord ++ tailWord_430519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430539 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 6, 2, 3]
def baseStart_430539 : Nat := 118140960795 + 430539 * 2 ^ 59
def prefixEnd_430539 : Nat := 4983230072969 + 3 ^ 40 * 430539 * 2
def baseEnd_430539 : Nat := 221073447506196247882493

theorem tailTrace_430539 : CollatzResearch.WordTrace tailWord_430539 prefixEnd_430539 221073447506196247882493 := by
  unfold tailWord_430539
  simp only [CollatzResearch.WordTrace]
  refine ⟨15703047387238208052270671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10468698258158805368180447 15703047387238208052270671)
  ·
    refine ⟨23554571080857312078406007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15703047387238208052270671 23554571080857312078406007)
    ·
      refine ⟨35331856621285968117609011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23554571080857312078406007 35331856621285968117609011)
      ·
        refine ⟨52997784931928952176413517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35331856621285968117609011 52997784931928952176413517)
        ·
          refine ⟨19874169349473357066155069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52997784931928952176413517 19874169349473357066155069)
          ·
            refine ⟨7452813506052508899808151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19874169349473357066155069 7452813506052508899808151)
            ·
              refine ⟨11179220259078763349712227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7452813506052508899808151 11179220259078763349712227)
              ·
                refine ⟨16768830388618145024568341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11179220259078763349712227 16768830388618145024568341)
                ·
                  refine ⟨786038924466475548026641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16768830388618145024568341 786038924466475548026641)
                  ·
                    refine ⟨589529193349856661019981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 786038924466475548026641 589529193349856661019981)
                    ·
                      refine ⟨221073447506196247882493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 589529193349856661019981 221073447506196247882493)
                      ·
                        rfl

theorem cell23_430539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 2, 3].length) (baseStart_430539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430539 prefixEnd_430539 := by exact prefixLift 430539
  have htrace : WordTrace (prefixWord ++ tailWord_430539) baseStart_430539 baseEnd_430539 := by
    simpa [prefixWord, tailWord_430539, baseEnd_430539] using wordTrace_append hprefix tailTrace_430539
  have hstable : (prefixWord ++ tailWord_430539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430539).length < 2 ^ (prefixWord ++ tailWord_430539).sum := by decide
  have hdescent : baseEnd_430539 < baseStart_430539 := by decide
  rcases family_descends (prefixWord ++ tailWord_430539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430573 : List Nat := [1, 5, 1, 3, 1, 1, 2, 2, 2, 2, 3]
def baseStart_430573 : Nat := 118140960795 + 430573 * 2 ^ 59
def prefixEnd_430573 : Nat := 4983230072969 + 3 ^ 40 * 430573 * 2
def baseEnd_430573 : Nat := 221090905848449114857337

theorem tailTrace_430573 : CollatzResearch.WordTrace tailWord_430573 prefixEnd_430573 221090905848449114857337 := by
  unfold tailWord_430573
  simp only [CollatzResearch.WordTrace]
  refine ⟨15704287469115031859008373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10469524979410021239338915 15704287469115031859008373)
  ·
    refine ⟨1472276950229534236782035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15704287469115031859008373 1472276950229534236782035)
    ·
      refine ⟨2208415425344301355173053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1472276950229534236782035 2208415425344301355173053)
      ·
        refine ⟨828155784504113008189895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2208415425344301355173053 828155784504113008189895)
        ·
          refine ⟨1242233676756169512284843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 828155784504113008189895 1242233676756169512284843)
          ·
            refine ⟨1863350515134254268427265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1242233676756169512284843 1863350515134254268427265)
            ·
              refine ⟨1397512886350690701320449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1863350515134254268427265 1397512886350690701320449)
              ·
                refine ⟨1048134664763018025990337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1397512886350690701320449 1048134664763018025990337)
                ·
                  refine ⟨786100998572263519492753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1048134664763018025990337 786100998572263519492753)
                  ·
                    refine ⟨589575748929197639619565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 786100998572263519492753 589575748929197639619565)
                    ·
                      refine ⟨221090905848449114857337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 589575748929197639619565 221090905848449114857337)
                      ·
                        rfl

theorem cell23_430573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_430573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430573 prefixEnd_430573 := by exact prefixLift 430573
  have htrace : WordTrace (prefixWord ++ tailWord_430573) baseStart_430573 baseEnd_430573 := by
    simpa [prefixWord, tailWord_430573, baseEnd_430573] using wordTrace_append hprefix tailTrace_430573
  have hstable : (prefixWord ++ tailWord_430573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430573).length < 2 ^ (prefixWord ++ tailWord_430573).sum := by decide
  have hdescent : baseEnd_430573 < baseStart_430573 := by decide
  rcases family_descends (prefixWord ++ tailWord_430573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430589 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 5, 5]
def baseStart_430589 : Nat := 118140960795 + 430589 * 2 ^ 59
def prefixEnd_430589 : Nat := 4983230072969 + 3 ^ 40 * 430589 * 2
def baseEnd_430589 : Nat := 73699707179640350752421

theorem tailTrace_430589 : CollatzResearch.WordTrace tailWord_430589 prefixEnd_430589 73699707179640350752421 := by
  unfold tailWord_430589
  simp only [CollatzResearch.WordTrace]
  refine ⟨15704871037057066591590821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10469914024704711061060547 15704871037057066591590821)
  ·
    refine ⟨2944663319448199985923279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15704871037057066591590821 2944663319448199985923279)
    ·
      refine ⟨4416994979172299978884919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2944663319448199985923279 4416994979172299978884919)
      ·
        refine ⟨6625492468758449968327379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4416994979172299978884919 6625492468758449968327379)
        ·
          refine ⟨9938238703137674952491069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6625492468758449968327379 9938238703137674952491069)
          ·
            refine ⟨3726839513676628107184151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9938238703137674952491069 3726839513676628107184151)
            ·
              refine ⟨5590259270514942160776227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3726839513676628107184151 5590259270514942160776227)
              ·
                refine ⟨8385388905772413241164341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5590259270514942160776227 8385388905772413241164341)
                ·
                  refine ⟨786130209916163741359157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8385388905772413241164341 786130209916163741359157)
                  ·
                    refine ⟨73699707179640350752421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 786130209916163741359157 73699707179640350752421)
                    ·
                      rfl

theorem cell23_430589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_430589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430589 prefixEnd_430589 := by exact prefixLift 430589
  have htrace : WordTrace (prefixWord ++ tailWord_430589) baseStart_430589 baseEnd_430589 := by
    simpa [prefixWord, tailWord_430589, baseEnd_430589] using wordTrace_append hprefix tailTrace_430589
  have hstable : (prefixWord ++ tailWord_430589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430589).length < 2 ^ (prefixWord ++ tailWord_430589).sum := by decide
  have hdescent : baseEnd_430589 < baseStart_430589 := by decide
  rcases family_descends (prefixWord ++ tailWord_430589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430603 : List Nat := [1, 1, 1, 1, 7, 2, 1, 2, 3, 1, 3]
def baseStart_430603 : Nat := 118140960795 + 430603 * 2 ^ 59
def prefixEnd_430603 : Nat := 4983230072969 + 3 ^ 40 * 430603 * 2
def baseEnd_430603 : Nat := 221106310268083997482199

theorem tailTrace_430603 : CollatzResearch.WordTrace tailWord_430603 prefixEnd_430603 221106310268083997482199 := by
  unfold tailWord_430603
  simp only [CollatzResearch.WordTrace]
  refine ⟨15705381659006346982600463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10470254439337564655066975 15705381659006346982600463)
  ·
    refine ⟨23558072488509520473900695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15705381659006346982600463 23558072488509520473900695)
    ·
      refine ⟨35337108732764280710851043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23558072488509520473900695 35337108732764280710851043)
      ·
        refine ⟨53005663099146421066276565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35337108732764280710851043 53005663099146421066276565)
        ·
          refine ⟨1242320228886244243740857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 53005663099146421066276565 1242320228886244243740857)
          ·
            refine ⟨931740171664683182805643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1242320228886244243740857 931740171664683182805643)
            ·
              refine ⟨1397610257497024774208465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 931740171664683182805643 1397610257497024774208465)
              ·
                refine ⟨1048207693122768580656349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1397610257497024774208465 1048207693122768580656349)
                ·
                  refine ⟨393077884921038217746131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1048207693122768580656349 393077884921038217746131)
                  ·
                    refine ⟨589616827381557326619197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 393077884921038217746131 589616827381557326619197)
                    ·
                      refine ⟨221106310268083997482199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 589616827381557326619197 221106310268083997482199)
                      ·
                        rfl

theorem cell23_430603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 3, 1, 3].length) (baseStart_430603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430603 prefixEnd_430603 := by exact prefixLift 430603
  have htrace : WordTrace (prefixWord ++ tailWord_430603) baseStart_430603 baseEnd_430603 := by
    simpa [prefixWord, tailWord_430603, baseEnd_430603] using wordTrace_append hprefix tailTrace_430603
  have hstable : (prefixWord ++ tailWord_430603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430603).length < 2 ^ (prefixWord ++ tailWord_430603).sum := by decide
  have hdescent : baseEnd_430603 < baseStart_430603 := by decide
  rcases family_descends (prefixWord ++ tailWord_430603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430606 : List Nat := [4, 1, 1, 2, 3, 1, 2, 1, 3, 5]
def baseStart_430606 : Nat := 118140960795 + 430606 * 2 ^ 59
def prefixEnd_430606 : Nat := 4983230072969 + 3 ^ 40 * 430606 * 2
def baseEnd_430606 : Nat := 73702616903349161914895

theorem tailTrace_430606 : CollatzResearch.WordTrace tailWord_430606 prefixEnd_430606 73702616903349161914895 := by
  unfold tailWord_430606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1963186384749434811869959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10470327385330318996639781 1963186384749434811869959)
  ·
    refine ⟨2944779577124152217804939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1963186384749434811869959 2944779577124152217804939)
    ·
      refine ⟨4417169365686228326707409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2944779577124152217804939 4417169365686228326707409)
      ·
        refine ⟨3312877024264671245030557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4417169365686228326707409 3312877024264671245030557)
        ·
          refine ⟨1242328884099251716886459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3312877024264671245030557 1242328884099251716886459)
          ·
            refine ⟨1863493326148877575329689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1242328884099251716886459 1863493326148877575329689)
            ·
              refine ⟨1397619994611658181497267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1863493326148877575329689 1397619994611658181497267)
              ·
                refine ⟨2096429991917487272245901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1397619994611658181497267 2096429991917487272245901)
                ·
                  refine ⟨786161246969057727092213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2096429991917487272245901 786161246969057727092213)
                  ·
                    refine ⟨73702616903349161914895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 786161246969057727092213 73702616903349161914895)
                    ·
                      rfl

theorem cell23_430606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_430606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430606 prefixEnd_430606 := by exact prefixLift 430606
  have htrace : WordTrace (prefixWord ++ tailWord_430606) baseStart_430606 baseEnd_430606 := by
    simpa [prefixWord, tailWord_430606, baseEnd_430606] using wordTrace_append hprefix tailTrace_430606
  have hstable : (prefixWord ++ tailWord_430606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430606).length < 2 ^ (prefixWord ++ tailWord_430606).sum := by decide
  have hdescent : baseEnd_430606 < baseStart_430606 := by decide
  rcases family_descends (prefixWord ++ tailWord_430606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430620 : List Nat := [2, 2, 3, 1, 2, 2, 1, 5, 1, 1, 3]
def baseStart_430620 : Nat := 118140960795 + 430620 * 2 ^ 59
def prefixEnd_430620 : Nat := 4983230072969 + 3 ^ 40 * 430620 * 2
def baseEnd_430620 : Nat := 221115039439210430969621

theorem tailTrace_430620 : CollatzResearch.WordTrace tailWord_430620 prefixEnd_430620 221115039439210430969621 := by
  unfold tailWord_430620
  simp only [CollatzResearch.WordTrace]
  refine ⟨7853000849972379442984657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10470667799963172590646209 7853000849972379442984657)
  ·
    refine ⟨5889750637479284582238493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7853000849972379442984657 5889750637479284582238493)
    ·
      refine ⟨2208656489054731718339435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5889750637479284582238493 2208656489054731718339435)
      ·
        refine ⟨3312984733582097577509153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2208656489054731718339435 3312984733582097577509153)
        ·
          refine ⟨2484738550186573183131865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3312984733582097577509153 2484738550186573183131865)
          ·
            refine ⟨1863553912639929887348899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2484738550186573183131865 1863553912639929887348899)
            ·
              refine ⟨2795330868959894831023349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1863553912639929887348899 2795330868959894831023349)
              ·
                refine ⟨262062268964990140408439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2795330868959894831023349 262062268964990140408439)
                ·
                  refine ⟨393093403447485210612659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262062268964990140408439 393093403447485210612659)
                  ·
                    refine ⟨589640105171227815918989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 393093403447485210612659 589640105171227815918989)
                    ·
                      refine ⟨221115039439210430969621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 589640105171227815918989 221115039439210430969621)
                      ·
                        rfl

theorem cell23_430620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_430620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430620 prefixEnd_430620 := by exact prefixLift 430620
  have htrace : WordTrace (prefixWord ++ tailWord_430620) baseStart_430620 baseEnd_430620 := by
    simpa [prefixWord, tailWord_430620, baseEnd_430620] using wordTrace_append hprefix tailTrace_430620
  have hstable : (prefixWord ++ tailWord_430620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430620).length < 2 ^ (prefixWord ++ tailWord_430620).sum := by decide
  have hdescent : baseEnd_430620 < baseStart_430620 := by decide
  rcases family_descends (prefixWord ++ tailWord_430620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430649 : List Nat := [1, 2, 1, 5, 1, 1, 2, 10]
def baseStart_430649 : Nat := 118140960795 + 430649 * 2 ^ 59
def prefixEnd_430649 : Nat := 4983230072969 + 3 ^ 40 * 430649 * 2
def baseEnd_430649 : Nat := 8189997421414474722481

theorem tailTrace_430649 : CollatzResearch.WordTrace tailWord_430649 prefixEnd_430649 8189997421414474722481 := by
  unfold tailWord_430649
  simp only [CollatzResearch.WordTrace]
  refine ⟨15707059416839696838775001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10471372944559797892516667 15707059416839696838775001)
  ·
    refine ⟨11780294562629772629081251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15707059416839696838775001 11780294562629772629081251)
    ·
      refine ⟨17670441843944658943621877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11780294562629772629081251 17670441843944658943621877)
      ·
        refine ⟨1656603922869811775964551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17670441843944658943621877 1656603922869811775964551)
        ·
          refine ⟨2484905884304717663946827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1656603922869811775964551 2484905884304717663946827)
          ·
            refine ⟨3727358826457076495920241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2484905884304717663946827 3727358826457076495920241)
            ·
              refine ⟨2795519119842807371940181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3727358826457076495920241 2795519119842807371940181)
              ·
                refine ⟨8189997421414474722481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2795519119842807371940181 8189997421414474722481)
                ·
                  rfl

theorem cell23_430649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 10].length) (baseStart_430649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430649 prefixEnd_430649 := by exact prefixLift 430649
  have htrace : WordTrace (prefixWord ++ tailWord_430649) baseStart_430649 baseEnd_430649 := by
    simpa [prefixWord, tailWord_430649, baseEnd_430649] using wordTrace_append hprefix tailTrace_430649
  have hstable : (prefixWord ++ tailWord_430649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430649).length < 2 ^ (prefixWord ++ tailWord_430649).sum := by decide
  have hdescent : baseEnd_430649 < baseStart_430649 := by decide
  rcases family_descends (prefixWord ++ tailWord_430649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430653 : List Nat := [1, 4, 1, 3, 2, 3, 1, 1, 1, 6]
def baseStart_430653 : Nat := 118140960795 + 430653 * 2 ^ 59
def prefixEnd_430653 : Nat := 4983230072969 + 3 ^ 40 * 430653 * 2
def baseEnd_430653 : Nat := 73710661433602933952323

theorem tailTrace_430653 : CollatzResearch.WordTrace tailWord_430653 prefixEnd_430653 73710661433602933952323 := by
  unfold tailWord_430653
  simp only [CollatzResearch.WordTrace]
  refine ⟨15707205308825205521920613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10471470205883470347947075 15707205308825205521920613)
  ·
    refine ⟨2945100995404726035360115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15707205308825205521920613 2945100995404726035360115)
    ·
      refine ⟨4417651493107089053040173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2945100995404726035360115 4417651493107089053040173)
      ·
        refine ⟨1656619309915158394890065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4417651493107089053040173 1656619309915158394890065)
        ·
          refine ⟨1242464482436368796167549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1656619309915158394890065 1242464482436368796167549)
          ·
            refine ⟨465924180913638298562831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1242464482436368796167549 465924180913638298562831)
            ·
              refine ⟨698886271370457447844247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465924180913638298562831 698886271370457447844247)
              ·
                refine ⟨1048329407055686171766371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 698886271370457447844247 1048329407055686171766371)
                ·
                  refine ⟨1572494110583529257649557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1048329407055686171766371 1572494110583529257649557)
                  ·
                    refine ⟨73710661433602933952323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1572494110583529257649557 73710661433602933952323)
                    ·
                      rfl

theorem cell23_430653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_430653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430653 prefixEnd_430653 := by exact prefixLift 430653
  have htrace : WordTrace (prefixWord ++ tailWord_430653) baseStart_430653 baseEnd_430653 := by
    simpa [prefixWord, tailWord_430653, baseEnd_430653] using wordTrace_append hprefix tailTrace_430653
  have hstable : (prefixWord ++ tailWord_430653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430653).length < 2 ^ (prefixWord ++ tailWord_430653).sum := by decide
  have hdescent : baseEnd_430653 < baseStart_430653 := by decide
  rcases family_descends (prefixWord ++ tailWord_430653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430656 : List Nat := [2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 4]
def baseStart_430656 : Nat := 118140960795 + 430656 * 2 ^ 59
def prefixEnd_430656 : Nat := 4983230072969 + 3 ^ 40 * 430656 * 2
def baseEnd_430656 : Nat := 221133524742772290119455

theorem tailTrace_430656 : CollatzResearch.WordTrace tailWord_430656 prefixEnd_430656 221133524742772290119455 := by
  unfold tailWord_430656
  simp only [CollatzResearch.WordTrace]
  refine ⟨7853657363907168517139911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10471543151876224689519881 7853657363907168517139911)
  ·
    refine ⟨11780486045860752775709867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7853657363907168517139911 11780486045860752775709867)
    ·
      refine ⟨17670729068791129163564801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11780486045860752775709867 17670729068791129163564801)
      ·
        refine ⟨13253046801593346872673601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17670729068791129163564801 13253046801593346872673601)
        ·
          refine ⟨9939785101195010154505201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13253046801593346872673601 9939785101195010154505201)
          ·
            refine ⟨7454838825896257615878901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9939785101195010154505201 7454838825896257615878901)
            ·
              refine ⟨698891139927774151488647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7454838825896257615878901 698891139927774151488647)
              ·
                refine ⟨1048336709891661227232971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 698891139927774151488647 1048336709891661227232971)
                ·
                  refine ⟨1572505064837491840849457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1048336709891661227232971 1572505064837491840849457)
                  ·
                    refine ⟨1179378798628118880637093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1572505064837491840849457 1179378798628118880637093)
                    ·
                      refine ⟨221133524742772290119455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1179378798628118880637093 221133524742772290119455)
                      ·
                        rfl

theorem cell23_430656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 4].length) (baseStart_430656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430656 prefixEnd_430656 := by exact prefixLift 430656
  have htrace : WordTrace (prefixWord ++ tailWord_430656) baseStart_430656 baseEnd_430656 := by
    simpa [prefixWord, tailWord_430656, baseEnd_430656] using wordTrace_append hprefix tailTrace_430656
  have hstable : (prefixWord ++ tailWord_430656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430656).length < 2 ^ (prefixWord ++ tailWord_430656).sum := by decide
  have hdescent : baseEnd_430656 < baseStart_430656 := by decide
  rcases family_descends (prefixWord ++ tailWord_430656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430663 : List Nat := [1, 1, 4, 1, 4, 1, 1, 4, 1, 2, 3]
def baseStart_430663 : Nat := 118140960795 + 430663 * 2 ^ 59
def prefixEnd_430663 : Nat := 4983230072969 + 3 ^ 40 * 430663 * 2
def baseEnd_430663 : Nat := 221137119107353762731923

theorem tailTrace_430663 : CollatzResearch.WordTrace tailWord_430663 prefixEnd_430663 221137119107353762731923 := by
  unfold tailWord_430663
  simp only [CollatzResearch.WordTrace]
  refine ⟨15707570038788977229784643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10471713359192651486523095 15707570038788977229784643)
  ·
    refine ⟨23561355058183465844676965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15707570038788977229784643 23561355058183465844676965)
    ·
      refine ⟨4417754073409399845876931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23561355058183465844676965 4417754073409399845876931)
      ·
        refine ⟨6626631110114099768815397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4417754073409399845876931 6626631110114099768815397)
        ·
          refine ⟨1242493333146393706652887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6626631110114099768815397 1242493333146393706652887)
          ·
            refine ⟨1863739999719590559979331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1242493333146393706652887 1863739999719590559979331)
            ·
              refine ⟨2795609999579385839968997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1863739999719590559979331 2795609999579385839968997)
              ·
                refine ⟨524176874921134844994187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2795609999579385839968997 524176874921134844994187)
                ·
                  refine ⟨786265312381702267491281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 524176874921134844994187 786265312381702267491281)
                  ·
                    refine ⟨589698984286276700618461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 786265312381702267491281 589698984286276700618461)
                    ·
                      refine ⟨221137119107353762731923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 589698984286276700618461 221137119107353762731923)
                      ·
                        rfl

theorem cell23_430663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_430663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430663 prefixEnd_430663 := by exact prefixLift 430663
  have htrace : WordTrace (prefixWord ++ tailWord_430663) baseStart_430663 baseEnd_430663 := by
    simpa [prefixWord, tailWord_430663, baseEnd_430663] using wordTrace_append hprefix tailTrace_430663
  have hstable : (prefixWord ++ tailWord_430663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430663).length < 2 ^ (prefixWord ++ tailWord_430663).sum := by decide
  have hdescent : baseEnd_430663 < baseStart_430663 := by decide
  rcases family_descends (prefixWord ++ tailWord_430663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430666 : List Nat := [3, 1, 2, 1, 1, 4, 4, 7]
def baseStart_430666 : Nat := 118140960795 + 430666 * 2 ^ 59
def prefixEnd_430666 : Nat := 4983230072969 + 3 ^ 40 * 430666 * 2
def baseEnd_430666 : Nat := 8190320724048787073867

theorem tailTrace_430666 : CollatzResearch.WordTrace tailWord_430666 prefixEnd_430666 8190320724048787073867 := by
  unfold tailWord_430666
  simp only [CollatzResearch.WordTrace]
  refine ⟨3926919864444527185535963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10471786305185405828095901 3926919864444527185535963)
  ·
    refine ⟨5890379796666790778303945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3926919864444527185535963 5890379796666790778303945)
    ·
      refine ⟨4417784847500093083727959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5890379796666790778303945 4417784847500093083727959)
      ·
        refine ⟨6626677271250139625591939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4417784847500093083727959 6626677271250139625591939)
        ·
          refine ⟨9940015906875209438387909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6626677271250139625591939 9940015906875209438387909)
          ·
            refine ⟨1863752982539101769697733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9940015906875209438387909 1863752982539101769697733)
            ·
              refine ⟨349453684226081581818325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1863752982539101769697733 349453684226081581818325)
              ·
                refine ⟨8190320724048787073867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 349453684226081581818325 8190320724048787073867)
                ·
                  rfl

theorem cell23_430666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 7].length) (baseStart_430666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430666 prefixEnd_430666 := by exact prefixLift 430666
  have htrace : WordTrace (prefixWord ++ tailWord_430666) baseStart_430666 baseEnd_430666 := by
    simpa [prefixWord, tailWord_430666, baseEnd_430666] using wordTrace_append hprefix tailTrace_430666
  have hstable : (prefixWord ++ tailWord_430666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430666).length < 2 ^ (prefixWord ++ tailWord_430666).sum := by decide
  have hdescent : baseEnd_430666 < baseStart_430666 := by decide
  rcases family_descends (prefixWord ++ tailWord_430666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430677 : List Nat := [1, 3, 2, 2, 1, 1, 5, 3, 1, 2, 2]
def baseStart_430677 : Nat := 118140960795 + 430677 * 2 ^ 59
def prefixEnd_430677 : Nat := 4983230072969 + 3 ^ 40 * 430677 * 2
def baseEnd_430677 : Nat := 221144307836516707956859

theorem tailTrace_430677 : CollatzResearch.WordTrace tailWord_430677 prefixEnd_430677 221144307836516707956859 := by
  unfold tailWord_430677
  simp only [CollatzResearch.WordTrace]
  refine ⟨15708080660738257620794285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10472053773825505080529523 15708080660738257620794285)
  ·
    refine ⟨5890530247776846607797857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15708080660738257620794285 5890530247776846607797857)
    ·
      refine ⟨4417897685832634955848393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5890530247776846607797857 4417897685832634955848393)
      ·
        refine ⟨3313423264374476216886295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4417897685832634955848393 3313423264374476216886295)
        ·
          refine ⟨4970134896561714325329443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3313423264374476216886295 4970134896561714325329443)
          ·
            refine ⟨7455202344842571487994165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4970134896561714325329443 7455202344842571487994165)
            ·
              refine ⟨698925219828991076999453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7455202344842571487994165 698925219828991076999453)
              ·
                refine ⟨262096957435871653874795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 698925219828991076999453 262096957435871653874795)
                ·
                  refine ⟨393145436153807480812193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262096957435871653874795 393145436153807480812193)
                  ·
                    refine ⟨294859077115355610609145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 393145436153807480812193 294859077115355610609145)
                    ·
                      refine ⟨221144307836516707956859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 294859077115355610609145 221144307836516707956859)
                      ·
                        rfl

theorem cell23_430677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_430677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430677 prefixEnd_430677 := by exact prefixLift 430677
  have htrace : WordTrace (prefixWord ++ tailWord_430677) baseStart_430677 baseEnd_430677 := by
    simpa [prefixWord, tailWord_430677, baseEnd_430677] using wordTrace_append hprefix tailTrace_430677
  have hstable : (prefixWord ++ tailWord_430677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430677).length < 2 ^ (prefixWord ++ tailWord_430677).sum := by decide
  have hdescent : baseEnd_430677 < baseStart_430677 := by decide
  rcases family_descends (prefixWord ++ tailWord_430677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430720 : List Nat := [2, 1, 1, 2, 1, 5, 3, 2, 1, 3, 2]
def baseStart_430720 : Nat := 118140960795 + 430720 * 2 ^ 59
def prefixEnd_430720 : Nat := 4983230072969 + 3 ^ 40 * 430720 * 2
def baseEnd_430720 : Nat := 221166387504660039719161

theorem tailTrace_430720 : CollatzResearch.WordTrace tailWord_430720 prefixEnd_430720 221166387504660039719161 := by
  unfold tailWord_430720
  simp only [CollatzResearch.WordTrace]
  refine ⟨7854824499791237982304807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10473099333054983976406409 7854824499791237982304807)
  ·
    refine ⟨11782236749686856973457211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7854824499791237982304807 11782236749686856973457211)
    ·
      refine ⟨17673355124530285460185817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11782236749686856973457211 17673355124530285460185817)
      ·
        refine ⟨13255016343397714095139363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17673355124530285460185817 13255016343397714095139363)
        ·
          refine ⟨19882524515096571142709045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13255016343397714095139363 19882524515096571142709045)
          ·
            refine ⟨1863986673290303544628973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19882524515096571142709045 1863986673290303544628973)
            ·
              refine ⟨698995002483863829235865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1863986673290303544628973 698995002483863829235865)
              ·
                refine ⟨524246251862897871926899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 698995002483863829235865 524246251862897871926899)
                ·
                  refine ⟨786369377794346807890349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 524246251862897871926899 786369377794346807890349)
                  ·
                    refine ⟨294888516672880052958881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 786369377794346807890349 294888516672880052958881)
                    ·
                      refine ⟨221166387504660039719161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 294888516672880052958881 221166387504660039719161)
                      ·
                        rfl

theorem cell23_430720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 1, 3, 2].length) (baseStart_430720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430720 prefixEnd_430720 := by exact prefixLift 430720
  have htrace : WordTrace (prefixWord ++ tailWord_430720) baseStart_430720 baseEnd_430720 := by
    simpa [prefixWord, tailWord_430720, baseEnd_430720] using wordTrace_append hprefix tailTrace_430720
  have hstable : (prefixWord ++ tailWord_430720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430720).length < 2 ^ (prefixWord ++ tailWord_430720).sum := by decide
  have hdescent : baseEnd_430720 < baseStart_430720 := by decide
  rcases family_descends (prefixWord ++ tailWord_430720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430739 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 9]
def baseStart_430739 : Nat := 118140960795 + 430739 * 2 ^ 59
def prefixEnd_430739 : Nat := 4983230072969 + 3 ^ 40 * 430739 * 2
def baseEnd_430739 : Nat := 24575127070788385042397

theorem tailTrace_430739 : CollatzResearch.WordTrace tailWord_430739 prefixEnd_430739 24575127070788385042397 := by
  unfold tailWord_430739
  simp only [CollatzResearch.WordTrace]
  refine ⟨15710341986513642209551271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10473561324342428139700847 15710341986513642209551271)
  ·
    refine ⟨23565512979770463314326907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15710341986513642209551271 23565512979770463314326907)
    ·
      refine ⟨35348269469655694971490361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23565512979770463314326907 35348269469655694971490361)
      ·
        refine ⟨26511202102241771228617771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35348269469655694971490361 26511202102241771228617771)
        ·
          refine ⟨39766803153362656842926657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26511202102241771228617771 39766803153362656842926657)
          ·
            refine ⟨29825102365021992632194993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39766803153362656842926657 29825102365021992632194993)
            ·
              refine ⟨22368826773766494474146245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29825102365021992632194993 22368826773766494474146245)
              ·
                refine ⟨4194155020081217713902421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22368826773766494474146245 4194155020081217713902421)
                ·
                  refine ⟨24575127070788385042397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4194155020081217713902421 24575127070788385042397)
                  ·
                    rfl

theorem cell23_430739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 9].length) (baseStart_430739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430739 prefixEnd_430739 := by exact prefixLift 430739
  have htrace : WordTrace (prefixWord ++ tailWord_430739) baseStart_430739 baseEnd_430739 := by
    simpa [prefixWord, tailWord_430739, baseEnd_430739] using wordTrace_append hprefix tailTrace_430739
  have hstable : (prefixWord ++ tailWord_430739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430739).length < 2 ^ (prefixWord ++ tailWord_430739).sum := by decide
  have hdescent : baseEnd_430739 < baseStart_430739 := by decide
  rcases family_descends (prefixWord ++ tailWord_430739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430750 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 3, 4, 2]
def baseStart_430750 : Nat := 118140960795 + 430750 * 2 ^ 59
def prefixEnd_430750 : Nat := 4983230072969 + 3 ^ 40 * 430750 * 2
def baseEnd_430750 : Nat := 221181791924294922344023

theorem tailTrace_430750 : CollatzResearch.WordTrace tailWord_430750 prefixEnd_430750 221181791924294922344023 := by
  unfold tailWord_430750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1963842898684223886025213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10473828792982527392134469 1963842898684223886025213)
  ·
    refine ⟨736441087006583957259455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1963842898684223886025213 736441087006583957259455)
    ·
      refine ⟨1104661630509875935889183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 736441087006583957259455 1104661630509875935889183)
      ·
        refine ⟨1656992445764813903833775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1104661630509875935889183 1656992445764813903833775)
        ·
          refine ⟨2485488668647220855750663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1656992445764813903833775 2485488668647220855750663)
          ·
            refine ⟨3728233002970831283625995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2485488668647220855750663 3728233002970831283625995)
            ·
              refine ⟨5592349504456246925438993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3728233002970831283625995 5592349504456246925438993)
              ·
                refine ⟨4194262128342185194079245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5592349504456246925438993 4194262128342185194079245)
                ·
                  refine ⟨1572848298128319447779717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4194262128342185194079245 1572848298128319447779717)
                  ·
                    refine ⟨294909055899059896458697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1572848298128319447779717 294909055899059896458697)
                    ·
                      refine ⟨221181791924294922344023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 294909055899059896458697 221181791924294922344023)
                      ·
                        rfl

theorem cell23_430750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_430750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430750 prefixEnd_430750 := by exact prefixLift 430750
  have htrace : WordTrace (prefixWord ++ tailWord_430750) baseStart_430750 baseEnd_430750 := by
    simpa [prefixWord, tailWord_430750, baseEnd_430750] using wordTrace_append hprefix tailTrace_430750
  have hstable : (prefixWord ++ tailWord_430750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430750).length < 2 ^ (prefixWord ++ tailWord_430750).sum := by decide
  have hdescent : baseEnd_430750 < baseStart_430750 := by decide
  rcases family_descends (prefixWord ++ tailWord_430750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430756 : List Nat := [2, 3, 1, 2, 2, 1, 2, 3, 7]
def baseStart_430756 : Nat := 118140960795 + 430756 * 2 ^ 59
def prefixEnd_430756 : Nat := 4983230072969 + 3 ^ 40 * 430756 * 2
def baseEnd_430756 : Nat := 24576096978691322096555

theorem tailTrace_430756 : CollatzResearch.WordTrace tailWord_430756 prefixEnd_430756 24576096978691322096555 := by
  unfold tailWord_430756
  simp only [CollatzResearch.WordTrace]
  refine ⟨7855481013726027056460061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10473974684968036075280081 7855481013726027056460061)
  ·
    refine ⟨2945805380147260146172523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7855481013726027056460061 2945805380147260146172523)
    ·
      refine ⟨4418708070220890219258785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2945805380147260146172523 4418708070220890219258785)
      ·
        refine ⟨3314031052665667664444089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4418708070220890219258785 3314031052665667664444089)
        ·
          refine ⟨2485523289499250748333067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3314031052665667664444089 2485523289499250748333067)
          ·
            refine ⟨3728284934248876122499601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2485523289499250748333067 3728284934248876122499601)
            ·
              refine ⟨2796213700686657091874701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3728284934248876122499601 2796213700686657091874701)
              ·
                refine ⟨1048580137757496409453013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2796213700686657091874701 1048580137757496409453013)
                ·
                  refine ⟨24576096978691322096555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1048580137757496409453013 24576096978691322096555)
                  ·
                    rfl

theorem cell23_430756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 7].length) (baseStart_430756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430756 prefixEnd_430756 := by exact prefixLift 430756
  have htrace : WordTrace (prefixWord ++ tailWord_430756) baseStart_430756 baseEnd_430756 := by
    simpa [prefixWord, tailWord_430756, baseEnd_430756] using wordTrace_append hprefix tailTrace_430756
  have hstable : (prefixWord ++ tailWord_430756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430756).length < 2 ^ (prefixWord ++ tailWord_430756).sum := by decide
  have hdescent : baseEnd_430756 < baseStart_430756 := by decide
  rcases family_descends (prefixWord ++ tailWord_430756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430773 : List Nat := [1, 3, 3, 3, 1, 2, 1, 2, 7]
def baseStart_430773 : Nat := 118140960795 + 430773 * 2 ^ 59
def prefixEnd_430773 : Nat := 4983230072969 + 3 ^ 40 * 430773 * 2
def baseEnd_430773 : Nat := 24577066886594259150713

theorem tailTrace_430773 : CollatzResearch.WordTrace tailWord_430773 prefixEnd_430773 24577066886594259150713 := by
  unfold tailWord_430773
  simp only [CollatzResearch.WordTrace]
  refine ⟨15711582068390466016288973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10474388045593644010859315 15711582068390466016288973)
  ·
    refine ⟨5891843275646424756108365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15711582068390466016288973 5891843275646424756108365)
    ·
      refine ⟨2209441228367409283540637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5891843275646424756108365 2209441228367409283540637)
      ·
        refine ⟨828540460637778481327739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2209441228367409283540637 828540460637778481327739)
        ·
          refine ⟨1242810690956667721991609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 828540460637778481327739 1242810690956667721991609)
          ·
            refine ⟨932108018217500791493707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1242810690956667721991609 932108018217500791493707)
            ·
              refine ⟨1398162027326251187240561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 932108018217500791493707 1398162027326251187240561)
              ·
                refine ⟨1048621520494688390430421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1398162027326251187240561 1048621520494688390430421)
                ·
                  refine ⟨24577066886594259150713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1048621520494688390430421 24577066886594259150713)
                  ·
                    rfl

theorem cell23_430773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 7].length) (baseStart_430773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430773 prefixEnd_430773 := by exact prefixLift 430773
  have htrace : WordTrace (prefixWord ++ tailWord_430773) baseStart_430773 baseEnd_430773 := by
    simpa [prefixWord, tailWord_430773, baseEnd_430773] using wordTrace_append hprefix tailTrace_430773
  have hstable : (prefixWord ++ tailWord_430773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430773).length < 2 ^ (prefixWord ++ tailWord_430773).sum := by decide
  have hdescent : baseEnd_430773 < baseStart_430773 := by decide
  rcases family_descends (prefixWord ++ tailWord_430773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430833 : List Nat := [1, 2, 2, 2, 2, 2, 1, 4, 3, 4]
def baseStart_430833 : Nat := 118140960795 + 430833 * 2 ^ 59
def prefixEnd_430833 : Nat := 4983230072969 + 3 ^ 40 * 430833 * 2
def baseEnd_430833 : Nat := 73741470272872699202047

theorem tailTrace_430833 : CollatzResearch.WordTrace tailWord_430833 prefixEnd_430833 73741470272872699202047 := by
  unfold tailWord_430833
  simp only [CollatzResearch.WordTrace]
  refine ⟨15713770448173096263473153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10475846965448730842315435 15713770448173096263473153)
  ·
    refine ⟨11785327836129822197604865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15713770448173096263473153 11785327836129822197604865)
    ·
      refine ⟨8838995877097366648203649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11785327836129822197604865 8838995877097366648203649)
      ·
        refine ⟨6629246907823024986152737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8838995877097366648203649 6629246907823024986152737)
        ·
          refine ⟨4971935180867268739614553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6629246907823024986152737 4971935180867268739614553)
          ·
            refine ⟨3728951385650451554710915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4971935180867268739614553 3728951385650451554710915)
            ·
              refine ⟨5593427078475677332066373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3728951385650451554710915 5593427078475677332066373)
              ·
                refine ⟨1048767577214189499762445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5593427078475677332066373 1048767577214189499762445)
                ·
                  refine ⟨393287841455321062410917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1048767577214189499762445 393287841455321062410917)
                  ·
                    refine ⟨73741470272872699202047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 393287841455321062410917 73741470272872699202047)
                    ·
                      rfl

theorem cell23_430833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 3, 4].length) (baseStart_430833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430833 prefixEnd_430833 := by exact prefixLift 430833
  have htrace : WordTrace (prefixWord ++ tailWord_430833) baseStart_430833 baseEnd_430833 := by
    simpa [prefixWord, tailWord_430833, baseEnd_430833] using wordTrace_append hprefix tailTrace_430833
  have hstable : (prefixWord ++ tailWord_430833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430833).length < 2 ^ (prefixWord ++ tailWord_430833).sum := by decide
  have hdescent : baseEnd_430833 < baseStart_430833 := by decide
  rcases family_descends (prefixWord ++ tailWord_430833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430867 : List Nat := [1, 1, 1, 2, 1, 3, 7, 2, 1, 4]
def baseStart_430867 : Nat := 118140960795 + 430867 * 2 ^ 59
def prefixEnd_430867 : Nat := 4983230072969 + 3 ^ 40 * 430867 * 2
def baseEnd_430867 : Nat := 73747289720290321526995

theorem tailTrace_430867 : CollatzResearch.WordTrace tailWord_430867 prefixEnd_430867 73747289720290321526995 := by
  unfold tailWord_430867
  simp only [CollatzResearch.WordTrace]
  refine ⟨15715010530049920070210855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10476673686699946713473903 15715010530049920070210855)
  ·
    refine ⟨23572515795074880105316283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15715010530049920070210855 23572515795074880105316283)
    ·
      refine ⟨35358773692612320157974425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23572515795074880105316283 35358773692612320157974425)
      ·
        refine ⟨26519080269459240118480819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35358773692612320157974425 26519080269459240118480819)
        ·
          refine ⟨39778620404188860177721229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26519080269459240118480819 39778620404188860177721229)
          ·
            refine ⟨14916982651570822566645461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39778620404188860177721229 14916982651570822566645461)
            ·
              refine ⟨349616780896191153905753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 14916982651570822566645461 349616780896191153905753)
              ·
                refine ⟨262212585672143365429315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349616780896191153905753 262212585672143365429315)
                ·
                  refine ⟨393318878508215048143973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262212585672143365429315 393318878508215048143973)
                  ·
                    refine ⟨73747289720290321526995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 393318878508215048143973 73747289720290321526995)
                    ·
                      rfl

theorem cell23_430867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 2, 1, 4].length) (baseStart_430867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430867 prefixEnd_430867 := by exact prefixLift 430867
  have htrace : WordTrace (prefixWord ++ tailWord_430867) baseStart_430867 baseEnd_430867 := by
    simpa [prefixWord, tailWord_430867, baseEnd_430867] using wordTrace_append hprefix tailTrace_430867
  have hstable : (prefixWord ++ tailWord_430867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430867).length < 2 ^ (prefixWord ++ tailWord_430867).sum := by decide
  have hdescent : baseEnd_430867 < baseStart_430867 := by decide
  rcases family_descends (prefixWord ++ tailWord_430867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430880 : List Nat := [2, 1, 1, 5, 1, 2, 4, 1, 6]
def baseStart_430880 : Nat := 118140960795 + 430880 * 2 ^ 59
def prefixEnd_430880 : Nat := 4983230072969 + 3 ^ 40 * 430880 * 2
def baseEnd_430880 : Nat := 24583171601042157079825

theorem tailTrace_430880 : CollatzResearch.WordTrace tailWord_430880 prefixEnd_430880 24583171601042157079825 := by
  unfold tailWord_430880
  simp only [CollatzResearch.WordTrace]
  refine ⟨7857742339501411645217047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10476989786001882193622729 7857742339501411645217047)
  ·
    refine ⟨11786613509252117467825571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7857742339501411645217047 11786613509252117467825571)
    ·
      refine ⟨17679920263878176201738357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11786613509252117467825571 17679920263878176201738357)
      ·
        refine ⟨1657492524738579018912971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17679920263878176201738357 1657492524738579018912971)
        ·
          refine ⟨2486238787107868528369457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1657492524738579018912971 2486238787107868528369457)
          ·
            refine ⟨1864679090330901396277093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2486238787107868528369457 1864679090330901396277093)
            ·
              refine ⟨349627329437044011801955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1864679090330901396277093 349627329437044011801955)
              ·
                refine ⟨524440994155566017702933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349627329437044011801955 524440994155566017702933)
                ·
                  refine ⟨24583171601042157079825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 524440994155566017702933 24583171601042157079825)
                  ·
                    rfl

theorem cell23_430880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 6].length) (baseStart_430880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430880 prefixEnd_430880 := by exact prefixLift 430880
  have htrace : WordTrace (prefixWord ++ tailWord_430880) baseStart_430880 baseEnd_430880 := by
    simpa [prefixWord, tailWord_430880, baseEnd_430880] using wordTrace_append hprefix tailTrace_430880
  have hstable : (prefixWord ++ tailWord_430880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430880).length < 2 ^ (prefixWord ++ tailWord_430880).sum := by decide
  have hdescent : baseEnd_430880 < baseStart_430880 := by decide
  rcases family_descends (prefixWord ++ tailWord_430880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430924 : List Nat := [2, 2, 1, 3, 3, 2, 1, 4, 1, 1, 3]
def baseStart_430924 : Nat := 118140960795 + 430924 * 2 ^ 59
def prefixEnd_430924 : Nat := 4983230072969 + 3 ^ 40 * 430924 * 2
def baseEnd_430924 : Nat := 221271137558177241568223

theorem tailTrace_430924 : CollatzResearch.WordTrace tailWord_430924 prefixEnd_430924 221271137558177241568223 := by
  unfold tailWord_430924
  simp only [CollatzResearch.WordTrace]
  refine ⟨7858544745421709402517913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10478059660562279203357217 7858544745421709402517913)
  ·
    refine ⟨5893908559066282051888435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7858544745421709402517913 5893908559066282051888435)
    ·
      refine ⟨8840862838599423077832653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5893908559066282051888435 8840862838599423077832653)
      ·
        refine ⟨3315323564474783654187245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8840862838599423077832653 3315323564474783654187245)
        ·
          refine ⟨1243246336678043870320217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3315323564474783654187245 1243246336678043870320217)
          ·
            refine ⟨932434752508532902740163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1243246336678043870320217 932434752508532902740163)
            ·
              refine ⟨1398652128762799354110245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 932434752508532902740163 1398652128762799354110245)
              ·
                refine ⟨262247274143024878895671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1398652128762799354110245 262247274143024878895671)
                ·
                  refine ⟨393370911214537318343507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262247274143024878895671 393370911214537318343507)
                  ·
                    refine ⟨590056366821805977515261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 393370911214537318343507 590056366821805977515261)
                    ·
                      refine ⟨221271137558177241568223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 590056366821805977515261 221271137558177241568223)
                      ·
                        rfl

theorem cell23_430924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_430924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430924 prefixEnd_430924 := by exact prefixLift 430924
  have htrace : WordTrace (prefixWord ++ tailWord_430924) baseStart_430924 baseEnd_430924 := by
    simpa [prefixWord, tailWord_430924, baseEnd_430924] using wordTrace_append hprefix tailTrace_430924
  have hstable : (prefixWord ++ tailWord_430924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430924).length < 2 ^ (prefixWord ++ tailWord_430924).sum := by decide
  have hdescent : baseEnd_430924 < baseStart_430924 := by decide
  rcases family_descends (prefixWord ++ tailWord_430924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430933 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 3, 1, 5]
def baseStart_430933 : Nat := 118140960795 + 430933 * 2 ^ 59
def prefixEnd_430933 : Nat := 4983230072969 + 3 ^ 40 * 430933 * 2
def baseEnd_430933 : Nat := 221275758884067706355681

theorem tailTrace_430933 : CollatzResearch.WordTrace tailWord_430933 prefixEnd_430933 221275758884067706355681 := by
  unfold tailWord_430933
  simp only [CollatzResearch.WordTrace]
  refine ⟨15717417747810813342113453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10478278498540542228075635 15717417747810813342113453)
  ·
    refine ⟨5894031655429055003292545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15717417747810813342113453 5894031655429055003292545)
    ·
      refine ⟨4420523741571791252469409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5894031655429055003292545 4420523741571791252469409)
      ·
        refine ⟨3315392806178843439352057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4420523741571791252469409 3315392806178843439352057)
        ·
          refine ⟨2486544604634132579514043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3315392806178843439352057 2486544604634132579514043)
          ·
            refine ⟨3729816906951198869271065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2486544604634132579514043 3729816906951198869271065)
            ·
              refine ⟨2797362680213399151953299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3729816906951198869271065 2797362680213399151953299)
              ·
                refine ⟨4196044020320098727929949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2797362680213399151953299 4196044020320098727929949)
                ·
                  refine ⟨1573516507620037022973731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4196044020320098727929949 1573516507620037022973731)
                  ·
                    refine ⟨2360274761430055534460597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1573516507620037022973731 2360274761430055534460597)
                    ·
                      refine ⟨221275758884067706355681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2360274761430055534460597 221275758884067706355681)
                      ·
                        rfl

theorem cell23_430933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_430933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430933 prefixEnd_430933 := by exact prefixLift 430933
  have htrace : WordTrace (prefixWord ++ tailWord_430933) baseStart_430933 baseEnd_430933 := by
    simpa [prefixWord, tailWord_430933, baseEnd_430933] using wordTrace_append hprefix tailTrace_430933
  have hstable : (prefixWord ++ tailWord_430933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430933).length < 2 ^ (prefixWord ++ tailWord_430933).sum := by decide
  have hdescent : baseEnd_430933 < baseStart_430933 := by decide
  rcases family_descends (prefixWord ++ tailWord_430933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430940 : List Nat := [2, 2, 4, 2, 1, 1, 1, 3, 1, 6]
def baseStart_430940 : Nat := 118140960795 + 430940 * 2 ^ 59
def prefixEnd_430940 : Nat := 4983230072969 + 3 ^ 40 * 430940 * 2
def baseEnd_430940 : Nat := 73759784416216392989383

theorem tailTrace_430940 : CollatzResearch.WordTrace tailWord_430940 prefixEnd_430940 73759784416216392989383 := by
  unfold tailWord_430940
  simp only [CollatzResearch.WordTrace]
  refine ⟨7858836529392726768809137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10478448705856969025078849 7858836529392726768809137)
  ·
    refine ⟨5894127397044545076606853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7858836529392726768809137 5894127397044545076606853)
    ·
      refine ⟨1105148886945852201863785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5894127397044545076606853 1105148886945852201863785)
      ·
        refine ⟨828861665209389151397839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1105148886945852201863785 828861665209389151397839)
        ·
          refine ⟨1243292497814083727096759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 828861665209389151397839 1243292497814083727096759)
          ·
            refine ⟨1864938746721125590645139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1243292497814083727096759 1864938746721125590645139)
            ·
              refine ⟨2797408120081688385967709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1864938746721125590645139 2797408120081688385967709)
              ·
                refine ⟨1049028045030633144737891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2797408120081688385967709 1049028045030633144737891)
                ·
                  refine ⟨1573542067545949717106837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1049028045030633144737891 1573542067545949717106837)
                  ·
                    refine ⟨73759784416216392989383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1573542067545949717106837 73759784416216392989383)
                    ·
                      rfl

theorem cell23_430940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_430940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430940 prefixEnd_430940 := by exact prefixLift 430940
  have htrace : WordTrace (prefixWord ++ tailWord_430940) baseStart_430940 baseEnd_430940 := by
    simpa [prefixWord, tailWord_430940, baseEnd_430940] using wordTrace_append hprefix tailTrace_430940
  have hstable : (prefixWord ++ tailWord_430940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430940).length < 2 ^ (prefixWord ++ tailWord_430940).sum := by decide
  have hdescent : baseEnd_430940 < baseStart_430940 := by decide
  rcases family_descends (prefixWord ++ tailWord_430940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430947 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 5, 2, 2]
def baseStart_430947 : Nat := 118140960795 + 430947 * 2 ^ 59
def prefixEnd_430947 : Nat := 4983230072969 + 3 ^ 40 * 430947 * 2
def baseEnd_430947 : Nat := 221282947613230651580617

theorem tailTrace_430947 : CollatzResearch.WordTrace tailWord_430947 prefixEnd_430947 221282947613230651580617 := by
  unfold tailWord_430947
  simp only [CollatzResearch.WordTrace]
  refine ⟨15717928369760093733123095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10478618913173395822082063 15717928369760093733123095)
  ·
    refine ⟨23576892554640140599684643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15717928369760093733123095 23576892554640140599684643)
    ·
      refine ⟨35365338831960210899526965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23576892554640140599684643 35365338831960210899526965)
      ·
        refine ⟨3315500515496269771830653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35365338831960210899526965 3315500515496269771830653)
        ·
          refine ⟨1243312693311101164436495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3315500515496269771830653 1243312693311101164436495)
          ·
            refine ⟨1864969039966651746654743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1243312693311101164436495 1864969039966651746654743)
            ·
              refine ⟨2797453559949977619982115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1864969039966651746654743 2797453559949977619982115)
              ·
                refine ⟨4196180339924966429973173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2797453559949977619982115 4196180339924966429973173)
                ·
                  refine ⟨393391906867965602809985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4196180339924966429973173 393391906867965602809985)
                  ·
                    refine ⟨295043930150974202107489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 393391906867965602809985 295043930150974202107489)
                    ·
                      refine ⟨221282947613230651580617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 295043930150974202107489 221282947613230651580617)
                      ·
                        rfl

theorem cell23_430947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_430947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430947 prefixEnd_430947 := by exact prefixLift 430947
  have htrace : WordTrace (prefixWord ++ tailWord_430947) baseStart_430947 baseEnd_430947 := by
    simpa [prefixWord, tailWord_430947, baseEnd_430947] using wordTrace_append hprefix tailTrace_430947
  have hstable : (prefixWord ++ tailWord_430947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430947).length < 2 ^ (prefixWord ++ tailWord_430947).sum := by decide
  have hdescent : baseEnd_430947 < baseStart_430947 := by decide
  rcases family_descends (prefixWord ++ tailWord_430947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430974 : List Nat := [4, 2, 3, 1, 2, 1, 1, 1, 4, 4]
def baseStart_430974 : Nat := 118140960795 + 430974 * 2 ^ 59
def prefixEnd_430974 : Nat := 4983230072969 + 3 ^ 40 * 430974 * 2
def baseEnd_430974 : Nat := 73765603863634015314331

theorem tailTrace_430974 : CollatzResearch.WordTrace tailWord_430974 prefixEnd_430974 73765603863634015314331 := by
  unfold tailWord_430974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1964864142582784668044497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10479275427108184896237317 1964864142582784668044497)
  ·
    refine ⟨1473648106937088501033373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1964864142582784668044497 1473648106937088501033373)
    ·
      refine ⟨552618040101408187887515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1473648106937088501033373 552618040101408187887515)
      ·
        refine ⟨828927060152112281831273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552618040101408187887515 828927060152112281831273)
        ·
          refine ⟨621695295114084211373455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 828927060152112281831273 621695295114084211373455)
          ·
            refine ⟨932542942671126317060183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621695295114084211373455 932542942671126317060183)
            ·
              refine ⟨1398814414006689475590275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 932542942671126317060183 1398814414006689475590275)
              ·
                refine ⟨2098221621010034213385413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1398814414006689475590275 2098221621010034213385413)
                ·
                  refine ⟨393416553939381415009765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2098221621010034213385413 393416553939381415009765)
                  ·
                    refine ⟨73765603863634015314331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 393416553939381415009765 73765603863634015314331)
                    ·
                      rfl

theorem cell23_430974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_430974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430974 prefixEnd_430974 := by exact prefixLift 430974
  have htrace : WordTrace (prefixWord ++ tailWord_430974) baseStart_430974 baseEnd_430974 := by
    simpa [prefixWord, tailWord_430974, baseEnd_430974] using wordTrace_append hprefix tailTrace_430974
  have hstable : (prefixWord ++ tailWord_430974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430974).length < 2 ^ (prefixWord ++ tailWord_430974).sum := by decide
  have hdescent : baseEnd_430974 < baseStart_430974 := by decide
  rcases family_descends (prefixWord ++ tailWord_430974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430994 : List Nat := [3, 2, 3, 2, 2, 2, 1, 1, 1, 2, 4]
def baseStart_430994 : Nat := 118140960795 + 430994 * 2 ^ 59
def prefixEnd_430994 : Nat := 4983230072969 + 3 ^ 40 * 430994 * 2
def baseEnd_430994 : Nat := 221307081203991967692901

theorem tailTrace_430994 : CollatzResearch.WordTrace tailWord_430994 prefixEnd_430994 221307081203991967692901 := by
  unfold tailWord_430994
  simp only [CollatzResearch.WordTrace]
  refine ⟨3929910650147455190021009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10479761733726547173389357 3929910650147455190021009)
  ·
    refine ⟨2947432987610591392515757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3929910650147455190021009 2947432987610591392515757)
    ·
      refine ⟨1105287370353971772193409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2947432987610591392515757 1105287370353971772193409)
      ·
        refine ⟨828965527765478829145057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1105287370353971772193409 828965527765478829145057)
        ·
          refine ⟨621724145824109121858793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 828965527765478829145057 621724145824109121858793)
          ·
            refine ⟨466293109368081841394095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 621724145824109121858793 466293109368081841394095)
            ·
              refine ⟨699439664052122762091143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466293109368081841394095 699439664052122762091143)
              ·
                refine ⟨1049159496078184143136715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 699439664052122762091143 1049159496078184143136715)
                ·
                  refine ⟨1573739244117276214705073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1049159496078184143136715 1573739244117276214705073)
                  ·
                    refine ⟨1180304433087957161028805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1573739244117276214705073 1180304433087957161028805)
                    ·
                      refine ⟨221307081203991967692901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1180304433087957161028805 221307081203991967692901)
                      ·
                        rfl

theorem cell23_430994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_430994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430994 prefixEnd_430994 := by exact prefixLift 430994
  have htrace : WordTrace (prefixWord ++ tailWord_430994) baseStart_430994 baseEnd_430994 := by
    simpa [prefixWord, tailWord_430994, baseEnd_430994] using wordTrace_append hprefix tailTrace_430994
  have hstable : (prefixWord ++ tailWord_430994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430994).length < 2 ^ (prefixWord ++ tailWord_430994).sum := by decide
  have hdescent : baseEnd_430994 < baseStart_430994 := by decide
  rcases family_descends (prefixWord ++ tailWord_430994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430997 : List Nat := [1, 3, 2, 1, 1, 6, 1, 1, 1, 3, 3]
def baseStart_430997 : Nat := 118140960795 + 430997 * 2 ^ 59
def prefixEnd_430997 : Nat := 4983230072969 + 3 ^ 40 * 430997 * 2
def baseEnd_430997 : Nat := 221308621645955455955387

theorem tailTrace_430997 : CollatzResearch.WordTrace tailWord_430997 prefixEnd_430997 221308621645955455955387 := by
  unfold tailWord_430997
  simp only [CollatzResearch.WordTrace]
  refine ⟨15719752019578952272443245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10479834679719301514962163 15719752019578952272443245)
  ·
    refine ⟨5894907007342107102166217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15719752019578952272443245 5894907007342107102166217)
    ·
      refine ⟨4421180255506580326624663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5894907007342107102166217 4421180255506580326624663)
      ·
        refine ⟨6631770383259870489936995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4421180255506580326624663 6631770383259870489936995)
        ·
          refine ⟨9947655574889805734905493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6631770383259870489936995 9947655574889805734905493)
          ·
            refine ⟨466296355072959643823695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9947655574889805734905493 466296355072959643823695)
            ·
              refine ⟨699444532609439465735543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466296355072959643823695 699444532609439465735543)
              ·
                refine ⟨1049166798914159198603315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 699444532609439465735543 1049166798914159198603315)
                ·
                  refine ⟨1573750198371238797904973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1049166798914159198603315 1573750198371238797904973)
                  ·
                    refine ⟨590156324389214549214365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1573750198371238797904973 590156324389214549214365)
                    ·
                      refine ⟨221308621645955455955387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 590156324389214549214365 221308621645955455955387)
                      ·
                        rfl

theorem cell23_430997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_430997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430997 prefixEnd_430997 := by exact prefixLift 430997
  have htrace : WordTrace (prefixWord ++ tailWord_430997) baseStart_430997 baseEnd_430997 := by
    simpa [prefixWord, tailWord_430997, baseEnd_430997] using wordTrace_append hprefix tailTrace_430997
  have hstable : (prefixWord ++ tailWord_430997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430997).length < 2 ^ (prefixWord ++ tailWord_430997).sum := by decide
  have hdescent : baseEnd_430997 < baseStart_430997 := by decide
  rcases family_descends (prefixWord ++ tailWord_430997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430998 : List Nat := [5, 3, 1, 1, 1, 1, 2, 2, 3, 2, 2]
def baseStart_430998 : Nat := 118140960795 + 430998 * 2 ^ 59
def prefixEnd_430998 : Nat := 4983230072969 + 3 ^ 40 * 430998 * 2
def baseEnd_430998 : Nat := 221309135126609952042883

theorem tailTrace_430998 : CollatzResearch.WordTrace tailWord_430998 prefixEnd_430998 221309135126609952042883 := by
  unfold tailWord_430998
  simp only [CollatzResearch.WordTrace]
  refine ⟨982486780785958090201853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10479858995050219628819765 982486780785958090201853)
  ·
    refine ⟨368432542794734283825695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 982486780785958090201853 368432542794734283825695)
    ·
      refine ⟨552648814192101425738543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368432542794734283825695 552648814192101425738543)
      ·
        refine ⟨828973221288152138607815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552648814192101425738543 828973221288152138607815)
        ·
          refine ⟨1243459831932228207911723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 828973221288152138607815 1243459831932228207911723)
          ·
            refine ⟨1865189747898342311867585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1243459831932228207911723 1865189747898342311867585)
            ·
              refine ⟨1398892310923756733900689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1865189747898342311867585 1398892310923756733900689)
              ·
                refine ⟨1049169233192817550425517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1398892310923756733900689 1049169233192817550425517)
                ·
                  refine ⟨393438462447306581409569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1049169233192817550425517 393438462447306581409569)
                  ·
                    refine ⟨295078846835479936057177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 393438462447306581409569 295078846835479936057177)
                    ·
                      refine ⟨221309135126609952042883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 295078846835479936057177 221309135126609952042883)
                      ·
                        rfl

theorem cell23_430998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_430998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_430998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_430998 prefixEnd_430998 := by exact prefixLift 430998
  have htrace : WordTrace (prefixWord ++ tailWord_430998) baseStart_430998 baseEnd_430998 := by
    simpa [prefixWord, tailWord_430998, baseEnd_430998] using wordTrace_append hprefix tailTrace_430998
  have hstable : (prefixWord ++ tailWord_430998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430998).length < 2 ^ (prefixWord ++ tailWord_430998).sum := by decide
  have hdescent : baseEnd_430998 < baseStart_430998 := by decide
  rcases family_descends (prefixWord ++ tailWord_430998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431004 : List Nat := [2, 2, 3, 3, 3, 1, 2, 7]
def baseStart_431004 : Nat := 118140960795 + 431004 * 2 ^ 59
def prefixEnd_431004 : Nat := 4983230072969 + 3 ^ 40 * 431004 * 2
def baseEnd_431004 : Nat := 8196748741130997354365

theorem tailTrace_431004 : CollatzResearch.WordTrace tailWord_431004 prefixEnd_431004 8196748741130997354365 := by
  unfold tailWord_431004
  simp only [CollatzResearch.WordTrace]
  refine ⟨7860003665276796233974033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10480004887035728311965377 7860003665276796233974033)
  ·
    refine ⟨5895002748957597175480525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7860003665276796233974033 5895002748957597175480525)
    ·
      refine ⟨2210626030859098940805197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5895002748957597175480525 2210626030859098940805197)
      ·
        refine ⟨828984761572162102801949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2210626030859098940805197 828984761572162102801949)
        ·
          refine ⟨310869285589560788550731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 828984761572162102801949 310869285589560788550731)
          ·
            refine ⟨466303928384341182826097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310869285589560788550731 466303928384341182826097)
            ·
              refine ⟨349727946288255887119573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466303928384341182826097 349727946288255887119573)
              ·
                refine ⟨8196748741130997354365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 349727946288255887119573 8196748741130997354365)
                ·
                  rfl

theorem cell23_431004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 7].length) (baseStart_431004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431004 prefixEnd_431004 := by exact prefixLift 431004
  have htrace : WordTrace (prefixWord ++ tailWord_431004) baseStart_431004 baseEnd_431004 := by
    simpa [prefixWord, tailWord_431004, baseEnd_431004] using wordTrace_append hprefix tailTrace_431004
  have hstable : (prefixWord ++ tailWord_431004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431004).length < 2 ^ (prefixWord ++ tailWord_431004).sum := by decide
  have hdescent : baseEnd_431004 < baseStart_431004 := by decide
  rcases family_descends (prefixWord ++ tailWord_431004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431010 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 2, 2, 5]
def baseStart_431010 : Nat := 118140960795 + 431010 * 2 ^ 59
def prefixEnd_431010 : Nat := 4983230072969 + 3 ^ 40 * 431010 * 2
def baseEnd_431010 : Nat := 221315296894463905092827

theorem tailTrace_431010 : CollatzResearch.WordTrace tailWord_431010 prefixEnd_431010 221315296894463905092827 := by
  unfold tailWord_431010
  simp only [CollatzResearch.WordTrace]
  refine ⟨3930056542132963873166621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10480150779021236995110989 3930056542132963873166621)
  ·
    refine ⟨1473771203299861452437483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3930056542132963873166621 1473771203299861452437483)
    ·
      refine ⟨2210656804949792178656225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1473771203299861452437483 2210656804949792178656225)
      ·
        refine ⟨1657992603712344133992169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2210656804949792178656225 1657992603712344133992169)
        ·
          refine ⟨1243494452784258100494127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1657992603712344133992169 1243494452784258100494127)
          ·
            refine ⟨1865241679176387150741191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1243494452784258100494127 1865241679176387150741191)
            ·
              refine ⟨2797862518764580726111787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1865241679176387150741191 2797862518764580726111787)
              ·
                refine ⟨4196793778146871089167681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2797862518764580726111787 4196793778146871089167681)
                ·
                  refine ⟨3147595333610153316875761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4196793778146871089167681 3147595333610153316875761)
                  ·
                    refine ⟨2360696500207614987656821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3147595333610153316875761 2360696500207614987656821)
                    ·
                      refine ⟨221315296894463905092827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2360696500207614987656821 221315296894463905092827)
                      ·
                        rfl

theorem cell23_431010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_431010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431010 prefixEnd_431010 := by exact prefixLift 431010
  have htrace : WordTrace (prefixWord ++ tailWord_431010) baseStart_431010 baseEnd_431010 := by
    simpa [prefixWord, tailWord_431010, baseEnd_431010] using wordTrace_append hprefix tailTrace_431010
  have hstable : (prefixWord ++ tailWord_431010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431010).length < 2 ^ (prefixWord ++ tailWord_431010).sum := by decide
  have hdescent : baseEnd_431010 < baseStart_431010 := by decide
  rcases family_descends (prefixWord ++ tailWord_431010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431015 : List Nat := [1, 1, 6, 1, 4, 1, 1, 3, 1, 2, 2]
def baseStart_431015 : Nat := 118140960795 + 431015 * 2 ^ 59
def prefixEnd_431015 : Nat := 4983230072969 + 3 ^ 40 * 431015 * 2
def baseEnd_431015 : Nat := 221317864297736385530305

theorem tailTrace_431015 : CollatzResearch.WordTrace tailWord_431015 prefixEnd_431015 221317864297736385530305 := by
  unfold tailWord_431015
  simp only [CollatzResearch.WordTrace]
  refine ⟨15720408533513741346598499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10480272355675827564398999 15720408533513741346598499)
  ·
    refine ⟨23580612800270612019897749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15720408533513741346598499 23580612800270612019897749)
    ·
      refine ⟨1105341225012684938432707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23580612800270612019897749 1105341225012684938432707)
      ·
        refine ⟨1658011837519027407649061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1105341225012684938432707 1658011837519027407649061)
        ·
          refine ⟨310877219534817638934199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1658011837519027407649061 310877219534817638934199)
          ·
            refine ⟨466315829302226458401299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310877219534817638934199 466315829302226458401299)
            ·
              refine ⟨699473743953339687601949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466315829302226458401299 699473743953339687601949)
              ·
                refine ⟨262302653982502382850731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 699473743953339687601949 262302653982502382850731)
                ·
                  refine ⟨393453980973753574276097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262302653982502382850731 393453980973753574276097)
                  ·
                    refine ⟨295090485730315180707073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 393453980973753574276097 295090485730315180707073)
                    ·
                      refine ⟨221317864297736385530305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 295090485730315180707073 221317864297736385530305)
                      ·
                        rfl

theorem cell23_431015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_431015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431015 prefixEnd_431015 := by exact prefixLift 431015
  have htrace : WordTrace (prefixWord ++ tailWord_431015) baseStart_431015 baseEnd_431015 := by
    simpa [prefixWord, tailWord_431015, baseEnd_431015] using wordTrace_append hprefix tailTrace_431015
  have hstable : (prefixWord ++ tailWord_431015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431015).length < 2 ^ (prefixWord ++ tailWord_431015).sum := by decide
  have hdescent : baseEnd_431015 < baseStart_431015 := by decide
  rcases family_descends (prefixWord ++ tailWord_431015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431048 : List Nat := [2, 1, 3, 1, 6, 1, 2, 1, 2, 1, 3]
def baseStart_431048 : Nat := 118140960795 + 431048 * 2 ^ 59
def prefixEnd_431048 : Nat := 4983230072969 + 3 ^ 40 * 431048 * 2
def baseEnd_431048 : Nat := 221334809159334756417653

theorem tailTrace_431048 : CollatzResearch.WordTrace tailWord_431048 prefixEnd_431048 221334809159334756417653 := by
  unfold tailWord_431048
  simp only [CollatzResearch.WordTrace]
  refine ⟨7860806071197093991274899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10481074761596125321699865 7860806071197093991274899)
  ·
    refine ⟨11791209106795640986912349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7860806071197093991274899 11791209106795640986912349)
    ·
      refine ⟨4421703415048365370092131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11791209106795640986912349 4421703415048365370092131)
      ·
        refine ⟨6632555122572548055138197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4421703415048365370092131 6632555122572548055138197)
        ·
          refine ⟨310901021370588190084603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6632555122572548055138197 310901021370588190084603)
          ·
            refine ⟨466351532055882285126905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310901021370588190084603 466351532055882285126905)
            ·
              refine ⟨349763649041911713845179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466351532055882285126905 349763649041911713845179)
              ·
                refine ⟨524645473562867570767769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349763649041911713845179 524645473562867570767769)
                ·
                  refine ⟨393484105172150678075827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 524645473562867570767769 393484105172150678075827)
                  ·
                    refine ⟨590226157758226017113741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 393484105172150678075827 590226157758226017113741)
                    ·
                      refine ⟨221334809159334756417653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 590226157758226017113741 221334809159334756417653)
                      ·
                        rfl

theorem cell23_431048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 2, 1, 3].length) (baseStart_431048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431048 prefixEnd_431048 := by exact prefixLift 431048
  have htrace : WordTrace (prefixWord ++ tailWord_431048) baseStart_431048 baseEnd_431048 := by
    simpa [prefixWord, tailWord_431048, baseEnd_431048] using wordTrace_append hprefix tailTrace_431048
  have hstable : (prefixWord ++ tailWord_431048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431048).length < 2 ^ (prefixWord ++ tailWord_431048).sum := by decide
  have hdescent : baseEnd_431048 < baseStart_431048 := by decide
  rcases family_descends (prefixWord ++ tailWord_431048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431094 : List Nat := [5, 1, 1, 1, 3, 2, 1, 4, 5]
def baseStart_431094 : Nat := 118140960795 + 431094 * 2 ^ 59
def prefixEnd_431094 : Nat := 4983230072969 + 3 ^ 40 * 431094 * 2
def baseEnd_431094 : Nat := 24595381029937952938049

theorem tailTrace_431094 : CollatzResearch.WordTrace tailWord_431094 prefixEnd_431094 24595381029937952938049 := by
  unfold tailWord_431094
  simp only [CollatzResearch.WordTrace]
  refine ⟨982705618764221114920271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10482193266818358559149557 982705618764221114920271)
  ·
    refine ⟨1474058428146331672380407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 982705618764221114920271 1474058428146331672380407)
    ·
      refine ⟨2211087642219497508570611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1474058428146331672380407 2211087642219497508570611)
      ·
        refine ⟨3316631463329246262855917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2211087642219497508570611 3316631463329246262855917)
        ·
          refine ⟨1243736798748467348570969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3316631463329246262855917 1243736798748467348570969)
          ·
            refine ⟨932802599061350511428227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1243736798748467348570969 932802599061350511428227)
            ·
              refine ⟨1399203898592025767142341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 932802599061350511428227 1399203898592025767142341)
              ·
                refine ⟨262350730986004831339189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1399203898592025767142341 262350730986004831339189)
                ·
                  refine ⟨24595381029937952938049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 262350730986004831339189 24595381029937952938049)
                  ·
                    rfl

theorem cell23_431094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_431094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431094 prefixEnd_431094 := by exact prefixLift 431094
  have htrace : WordTrace (prefixWord ++ tailWord_431094) baseStart_431094 baseEnd_431094 := by
    simpa [prefixWord, tailWord_431094, baseEnd_431094] using wordTrace_append hprefix tailTrace_431094
  have hstable : (prefixWord ++ tailWord_431094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431094).length < 2 ^ (prefixWord ++ tailWord_431094).sum := by decide
  have hdescent : baseEnd_431094 < baseStart_431094 := by decide
  rcases family_descends (prefixWord ++ tailWord_431094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431100 : List Nat := [2, 2, 2, 1, 2, 3, 2, 1, 1, 2, 5]
def baseStart_431100 : Nat := 118140960795 + 431100 * 2 ^ 59
def prefixEnd_431100 : Nat := 4983230072969 + 3 ^ 40 * 431100 * 2
def baseEnd_431100 : Nat := 221361510153368552967413

theorem tailTrace_431100 : CollatzResearch.WordTrace tailWord_431100 prefixEnd_431100 221361510153368552967413 := by
  unfold tailWord_431100
  simp only [CollatzResearch.WordTrace]
  refine ⟨7861754369102900431721377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10482339158803867242295169 7861754369102900431721377)
  ·
    refine ⟨5896315776827175323791033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7861754369102900431721377 5896315776827175323791033)
    ·
      refine ⟨4422236832620381492843275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5896315776827175323791033 4422236832620381492843275)
      ·
        refine ⟨6633355248930572239264913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4422236832620381492843275 6633355248930572239264913)
        ·
          refine ⟨4975016436697929179448685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6633355248930572239264913 4975016436697929179448685)
          ·
            refine ⟨1865631163761723442293257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4975016436697929179448685 1865631163761723442293257)
            ·
              refine ⟨1399223372821292581719943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1865631163761723442293257 1399223372821292581719943)
              ·
                refine ⟨2098835059231938872579915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1399223372821292581719943 2098835059231938872579915)
                ·
                  refine ⟨3148252588847908308869873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2098835059231938872579915 3148252588847908308869873)
                  ·
                    refine ⟨2361189441635931231652405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3148252588847908308869873 2361189441635931231652405)
                    ·
                      refine ⟨221361510153368552967413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2361189441635931231652405 221361510153368552967413)
                      ·
                        rfl

theorem cell23_431100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_431100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431100 prefixEnd_431100 := by exact prefixLift 431100
  have htrace : WordTrace (prefixWord ++ tailWord_431100) baseStart_431100 baseEnd_431100 := by
    simpa [prefixWord, tailWord_431100, baseEnd_431100] using wordTrace_append hprefix tailTrace_431100
  have hstable : (prefixWord ++ tailWord_431100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431100).length < 2 ^ (prefixWord ++ tailWord_431100).sum := by decide
  have hdescent : baseEnd_431100 < baseStart_431100 := by decide
  rcases family_descends (prefixWord ++ tailWord_431100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431103 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 4, 8]
def baseStart_431103 : Nat := 118140960795 + 431103 * 2 ^ 59
def prefixEnd_431103 : Nat := 4983230072969 + 3 ^ 40 * 431103 * 2
def baseEnd_431103 : Nat := 73787683531777347076633

theorem tailTrace_431103 : CollatzResearch.WordTrace tailWord_431103 prefixEnd_431103 73787683531777347076633 := by
  unfold tailWord_431103
  simp only [CollatzResearch.WordTrace]
  refine ⟨15723618157194932375801963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10482412104796621583867975 15723618157194932375801963)
  ·
    refine ⟨23585427235792398563702945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15723618157194932375801963 23585427235792398563702945)
    ·
      refine ⟨17689070426844298922777209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23585427235792398563702945 17689070426844298922777209)
      ·
        refine ⟨13266802820133224192082907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17689070426844298922777209 13266802820133224192082907)
        ·
          refine ⟨19900204230199836288124361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13266802820133224192082907 19900204230199836288124361)
          ·
            refine ⟨14925153172649877216093271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19900204230199836288124361 14925153172649877216093271)
            ·
              refine ⟨22387729758974815824139907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14925153172649877216093271 22387729758974815824139907)
              ·
                refine ⟨33581594638462223736209861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22387729758974815824139907 33581594638462223736209861)
                ·
                  refine ⟨6296548994711666950539349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33581594638462223736209861 6296548994711666950539349)
                  ·
                    refine ⟨73787683531777347076633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6296548994711666950539349 73787683531777347076633)
                    ·
                      rfl

theorem cell23_431103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 8].length) (baseStart_431103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431103 prefixEnd_431103 := by exact prefixLift 431103
  have htrace : WordTrace (prefixWord ++ tailWord_431103) baseStart_431103 baseEnd_431103 := by
    simpa [prefixWord, tailWord_431103, baseEnd_431103] using wordTrace_append hprefix tailTrace_431103
  have hstable : (prefixWord ++ tailWord_431103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431103).length < 2 ^ (prefixWord ++ tailWord_431103).sum := by decide
  have hdescent : baseEnd_431103 < baseStart_431103 := by decide
  rcases family_descends (prefixWord ++ tailWord_431103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431127 : List Nat := [1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 4]
def baseStart_431127 : Nat := 118140960795 + 431127 * 2 ^ 59
def prefixEnd_431127 : Nat := 4983230072969 + 3 ^ 40 * 431127 * 2
def baseEnd_431127 : Nat := 221375374131039947329789

theorem tailTrace_431127 : CollatzResearch.WordTrace tailWord_431127 prefixEnd_431127 221375374131039947329789 := by
  unfold tailWord_431127
  simp only [CollatzResearch.WordTrace]
  refine ⟨15724493509107984474675635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10482995672738656316450423 15724493509107984474675635)
  ·
    refine ⟨23586740263661976712013453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15724493509107984474675635 23586740263661976712013453)
    ·
      refine ⟨8845027598873241267005045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23586740263661976712013453 8845027598873241267005045)
      ·
        refine ⟨829221337394366368781723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8845027598873241267005045 829221337394366368781723)
        ·
          refine ⟨1243832006091549553172585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 829221337394366368781723 1243832006091549553172585)
          ·
            refine ⟨932874004568662164879439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1243832006091549553172585 932874004568662164879439)
            ·
              refine ⟨1399311006852993247319159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 932874004568662164879439 1399311006852993247319159)
              ·
                refine ⟨2098966510279489870978739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1399311006852993247319159 2098966510279489870978739)
                ·
                  refine ⟨3148449765419234806468109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2098966510279489870978739 3148449765419234806468109)
                  ·
                    refine ⟨1180668662032213052425541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3148449765419234806468109 1180668662032213052425541)
                    ·
                      refine ⟨221375374131039947329789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1180668662032213052425541 221375374131039947329789)
                      ·
                        rfl

theorem cell23_431127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_431127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431127 prefixEnd_431127 := by exact prefixLift 431127
  have htrace : WordTrace (prefixWord ++ tailWord_431127) baseStart_431127 baseEnd_431127 := by
    simpa [prefixWord, tailWord_431127, baseEnd_431127] using wordTrace_append hprefix tailTrace_431127
  have hstable : (prefixWord ++ tailWord_431127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431127).length < 2 ^ (prefixWord ++ tailWord_431127).sum := by decide
  have hdescent : baseEnd_431127 < baseStart_431127 := by decide
  rcases family_descends (prefixWord ++ tailWord_431127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431154 : List Nat := [3, 2, 1, 1, 2, 2, 1, 6, 1, 4]
def baseStart_431154 : Nat := 118140960795 + 431154 * 2 ^ 59
def prefixEnd_431154 : Nat := 4983230072969 + 3 ^ 40 * 431154 * 2
def baseEnd_431154 : Nat := 73796412702903780564055

theorem tailTrace_431154 : CollatzResearch.WordTrace tailWord_431154 prefixEnd_431154 73796412702903780564055 := by
  unfold tailWord_431154
  simp only [CollatzResearch.WordTrace]
  refine ⟨3931369570002542021477129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10483652186673445390605677 3931369570002542021477129)
  ·
    refine ⟨2948527177501906516107847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3931369570002542021477129 2948527177501906516107847)
    ·
      refine ⟨4422790766252859774161771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2948527177501906516107847 4422790766252859774161771)
      ·
        refine ⟨6634186149379289661242657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4422790766252859774161771 6634186149379289661242657)
        ·
          refine ⟨4975639612034467245931993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6634186149379289661242657 4975639612034467245931993)
          ·
            refine ⟨3731729709025850434448995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4975639612034467245931993 3731729709025850434448995)
            ·
              refine ⟨5597594563538775651673493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3731729709025850434448995 5597594563538775651673493)
              ·
                refine ⟨262387245165880108672195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5597594563538775651673493 262387245165880108672195)
                ·
                  refine ⟨393580867748820163008293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262387245165880108672195 393580867748820163008293)
                  ·
                    refine ⟨73796412702903780564055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 393580867748820163008293 73796412702903780564055)
                    ·
                      rfl

theorem cell23_431154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_431154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431154 prefixEnd_431154 := by exact prefixLift 431154
  have htrace : WordTrace (prefixWord ++ tailWord_431154) baseStart_431154 baseEnd_431154 := by
    simpa [prefixWord, tailWord_431154, baseEnd_431154] using wordTrace_append hprefix tailTrace_431154
  have hstable : (prefixWord ++ tailWord_431154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431154).length < 2 ^ (prefixWord ++ tailWord_431154).sum := by decide
  have hdescent : baseEnd_431154 < baseStart_431154 := by decide
  rcases family_descends (prefixWord ++ tailWord_431154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431177 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 5, 1, 3]
def baseStart_431177 : Nat := 118140960795 + 431177 * 2 ^ 59
def prefixEnd_431177 : Nat := 4983230072969 + 3 ^ 40 * 431177 * 2
def baseEnd_431177 : Nat := 221401048163764751704559

theorem tailTrace_431177 : CollatzResearch.WordTrace tailWord_431177 prefixEnd_431177 221401048163764751704559 := by
  unfold tailWord_431177
  simp only [CollatzResearch.WordTrace]
  refine ⟨15726317158926843013995785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10484211439284562009330523 15726317158926843013995785)
  ·
    refine ⟨11794737869195132260496839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15726317158926843013995785 11794737869195132260496839)
    ·
      refine ⟨17692106803792698390745259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11794737869195132260496839 17692106803792698390745259)
      ·
        refine ⟨26538160205689047586117889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17692106803792698390745259 26538160205689047586117889)
        ·
          refine ⟨19903620154266785689588417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26538160205689047586117889 19903620154266785689588417)
          ·
            refine ⟨14927715115700089267191313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19903620154266785689588417 14927715115700089267191313)
            ·
              refine ⟨11195786336775066950393485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14927715115700089267191313 11195786336775066950393485)
              ·
                refine ⟨4198419876290650106397557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11195786336775066950393485 4198419876290650106397557)
                ·
                  refine ⟨393601863402248447474771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4198419876290650106397557 393601863402248447474771)
                  ·
                    refine ⟨590402795103372671212157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 393601863402248447474771 590402795103372671212157)
                    ·
                      refine ⟨221401048163764751704559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 590402795103372671212157 221401048163764751704559)
                      ·
                        rfl

theorem cell23_431177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 5, 1, 3].length) (baseStart_431177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431177 prefixEnd_431177 := by exact prefixLift 431177
  have htrace : WordTrace (prefixWord ++ tailWord_431177) baseStart_431177 baseEnd_431177 := by
    simpa [prefixWord, tailWord_431177, baseEnd_431177] using wordTrace_append hprefix tailTrace_431177
  have hstable : (prefixWord ++ tailWord_431177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431177).length < 2 ^ (prefixWord ++ tailWord_431177).sum := by decide
  have hdescent : baseEnd_431177 < baseStart_431177 := by decide
  rcases family_descends (prefixWord ++ tailWord_431177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431198 : List Nat := [4, 4, 1, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_431198 : Nat := 118140960795 + 431198 * 2 ^ 59
def prefixEnd_431198 : Nat := 4983230072969 + 3 ^ 40 * 431198 * 2
def baseEnd_431198 : Nat := 221411831257509169541963

theorem tailTrace_431198 : CollatzResearch.WordTrace tailWord_431198 prefixEnd_431198 221411831257509169541963 := by
  unfold tailWord_431198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1965885386481345450063781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10484722061233842400340165 1965885386481345450063781)
  ·
    refine ⟨368603509965252271886959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1965885386481345450063781 368603509965252271886959)
    ·
      refine ⟨552905264947878407830439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368603509965252271886959 552905264947878407830439)
      ·
        refine ⟨829357897421817611745659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552905264947878407830439 829357897421817611745659)
        ·
          refine ⟨1244036846132726417618489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 829357897421817611745659 1244036846132726417618489)
          ·
            refine ⟨933027634599544813213867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1244036846132726417618489 933027634599544813213867)
            ·
              refine ⟨1399541451899317219820801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 933027634599544813213867 1399541451899317219820801)
              ·
                refine ⟨1049656088924487914865601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1399541451899317219820801 1049656088924487914865601)
                ·
                  refine ⟨787242066693365936149201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1049656088924487914865601 787242066693365936149201)
                  ·
                    refine ⟨590431550020024452111901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 787242066693365936149201 590431550020024452111901)
                    ·
                      refine ⟨221411831257509169541963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 590431550020024452111901 221411831257509169541963)
                      ·
                        rfl

theorem cell23_431198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_431198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431198 prefixEnd_431198 := by exact prefixLift 431198
  have htrace : WordTrace (prefixWord ++ tailWord_431198) baseStart_431198 baseEnd_431198 := by
    simpa [prefixWord, tailWord_431198, baseEnd_431198] using wordTrace_append hprefix tailTrace_431198
  have hstable : (prefixWord ++ tailWord_431198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431198).length < 2 ^ (prefixWord ++ tailWord_431198).sum := by decide
  have hdescent : baseEnd_431198 < baseStart_431198 := by decide
  rcases family_descends (prefixWord ++ tailWord_431198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431217 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 2, 6, 2]
def baseStart_431217 : Nat := 118140960795 + 431217 * 2 ^ 59
def prefixEnd_431217 : Nat := 4983230072969 + 3 ^ 40 * 431217 * 2
def baseEnd_431217 : Nat := 221421587389944595204375

theorem tailTrace_431217 : CollatzResearch.WordTrace tailWord_431217 prefixEnd_431217 221421587389944595204375 := by
  unfold tailWord_431217
  simp only [CollatzResearch.WordTrace]
  refine ⟨15727776078781929845451905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10485184052521286563634603 15727776078781929845451905)
  ·
    refine ⟨11795832059086447384088929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15727776078781929845451905 11795832059086447384088929)
    ·
      refine ⟨8846874044314835538066697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11795832059086447384088929 8846874044314835538066697)
      ·
        refine ⟨6635155533236126653550023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8846874044314835538066697 6635155533236126653550023)
        ·
          refine ⟨9952733299854189980325035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6635155533236126653550023 9952733299854189980325035)
          ·
            refine ⟨14929099949781284970487553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9952733299854189980325035 14929099949781284970487553)
            ·
              refine ⟨11196824962335963727865665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14929099949781284970487553 11196824962335963727865665)
              ·
                refine ⟨8397618721751972795899249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11196824962335963727865665 8397618721751972795899249)
                ·
                  refine ⟨6298214041313979596924437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8397618721751972795899249 6298214041313979596924437)
                  ·
                    refine ⟨295228783186592793605833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6298214041313979596924437 295228783186592793605833)
                    ·
                      refine ⟨221421587389944595204375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 295228783186592793605833 221421587389944595204375)
                      ·
                        rfl

theorem cell23_431217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 6, 2].length) (baseStart_431217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431217 prefixEnd_431217 := by exact prefixLift 431217
  have htrace : WordTrace (prefixWord ++ tailWord_431217) baseStart_431217 baseEnd_431217 := by
    simpa [prefixWord, tailWord_431217, baseEnd_431217] using wordTrace_append hprefix tailTrace_431217
  have hstable : (prefixWord ++ tailWord_431217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431217).length < 2 ^ (prefixWord ++ tailWord_431217).sum := by decide
  have hdescent : baseEnd_431217 < baseStart_431217 := by decide
  rcases family_descends (prefixWord ++ tailWord_431217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431262 : List Nat := [4, 3, 1, 1, 2, 3, 2, 2, 1, 1, 3]
def baseStart_431262 : Nat := 118140960795 + 431262 * 2 ^ 59
def prefixEnd_431262 : Nat := 4983230072969 + 3 ^ 40 * 431262 * 2
def baseEnd_431262 : Nat := 221444694019396919141669

theorem tailTrace_431262 : CollatzResearch.WordTrace tailWord_431262 prefixEnd_431262 221444694019396919141669 := by
  unfold tailWord_431262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1966177170452362816355005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10486278242412601687226693 1966177170452362816355005)
  ·
    refine ⟨737316438919636056133127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1966177170452362816355005 737316438919636056133127)
    ·
      refine ⟨1105974658379454084199691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 737316438919636056133127 1105974658379454084199691)
      ·
        refine ⟨1658961987569181126299537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1105974658379454084199691 1658961987569181126299537)
        ·
          refine ⟨1244221490676885844724653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1658961987569181126299537 1244221490676885844724653)
          ·
            refine ⟨466583059003832191771745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1244221490676885844724653 466583059003832191771745)
            ·
              refine ⟨349937294252874143828809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466583059003832191771745 349937294252874143828809)
              ·
                refine ⟨262452970689655607871607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349937294252874143828809 262452970689655607871607)
                ·
                  refine ⟨393679456034483411807411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262452970689655607871607 393679456034483411807411)
                  ·
                    refine ⟨590519184051725117711117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 393679456034483411807411 590519184051725117711117)
                    ·
                      refine ⟨221444694019396919141669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 590519184051725117711117 221444694019396919141669)
                      ·
                        rfl

theorem cell23_431262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_431262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431262 prefixEnd_431262 := by exact prefixLift 431262
  have htrace : WordTrace (prefixWord ++ tailWord_431262) baseStart_431262 baseEnd_431262 := by
    simpa [prefixWord, tailWord_431262, baseEnd_431262] using wordTrace_append hprefix tailTrace_431262
  have hstable : (prefixWord ++ tailWord_431262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431262).length < 2 ^ (prefixWord ++ tailWord_431262).sum := by decide
  have hdescent : baseEnd_431262 < baseStart_431262 := by decide
  rcases family_descends (prefixWord ++ tailWord_431262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431274 : List Nat := [3, 1, 5, 1, 1, 1, 3, 8]
def baseStart_431274 : Nat := 118140960795 + 431274 * 2 ^ 59
def prefixEnd_431274 : Nat := 4983230072969 + 3 ^ 40 * 431274 * 2
def baseEnd_431274 : Nat := 8201883547675958229319

theorem tailTrace_431274 : CollatzResearch.WordTrace tailWord_431274 prefixEnd_431274 8201883547675958229319 := by
  unfold tailWord_431274
  simp only [CollatzResearch.WordTrace]
  refine ⟨3932463759893857145069219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10486570026383619053517917 3932463759893857145069219)
  ·
    refine ⟨5898695639840785717603829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3932463759893857145069219 5898695639840785717603829)
    ·
      refine ⟨553002716235073661025359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5898695639840785717603829 553002716235073661025359)
      ·
        refine ⟨829504074352610491538039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553002716235073661025359 829504074352610491538039)
        ·
          refine ⟨1244256111528915737307059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 829504074352610491538039 1244256111528915737307059)
          ·
            refine ⟨1866384167293373605960589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1244256111528915737307059 1866384167293373605960589)
            ·
              refine ⟨699894062735015102235221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1866384167293373605960589 699894062735015102235221)
              ·
                refine ⟨8201883547675958229319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 699894062735015102235221 8201883547675958229319)
                ·
                  rfl

theorem cell23_431274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 8].length) (baseStart_431274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431274 prefixEnd_431274 := by exact prefixLift 431274
  have htrace : WordTrace (prefixWord ++ tailWord_431274) baseStart_431274 baseEnd_431274 := by
    simpa [prefixWord, tailWord_431274, baseEnd_431274] using wordTrace_append hprefix tailTrace_431274
  have hstable : (prefixWord ++ tailWord_431274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431274).length < 2 ^ (prefixWord ++ tailWord_431274).sum := by decide
  have hdescent : baseEnd_431274 < baseStart_431274 := by decide
  rcases family_descends (prefixWord ++ tailWord_431274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431327 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 1, 6, 3]
def baseStart_431327 : Nat := 118140960795 + 431327 * 2 ^ 59
def prefixEnd_431327 : Nat := 4983230072969 + 3 ^ 40 * 431327 * 2
def baseEnd_431327 : Nat := 221478070261939164828869

theorem tailTrace_431327 : CollatzResearch.WordTrace tailWord_431327 prefixEnd_431327 221478070261939164828869 := by
  unfold tailWord_431327
  simp only [CollatzResearch.WordTrace]
  refine ⟨15731788108383418631956235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10487858738922279087970823 15731788108383418631956235)
  ·
    refine ⟨23597682162575127947934353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15731788108383418631956235 23597682162575127947934353)
    ·
      refine ⟨17698261621931345960950765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23597682162575127947934353 17698261621931345960950765)
      ·
        refine ⟨6636848108224254735356537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17698261621931345960950765 6636848108224254735356537)
        ·
          refine ⟨4977636081168191051517403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6636848108224254735356537 4977636081168191051517403)
          ·
            refine ⟨7466454121752286577276105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4977636081168191051517403 7466454121752286577276105)
            ·
              refine ⟨5599840591314214932957079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7466454121752286577276105 5599840591314214932957079)
              ·
                refine ⟨8399760886971322399435619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5599840591314214932957079 8399760886971322399435619)
                ·
                  refine ⟨12599641330456983599153429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8399760886971322399435619 12599641330456983599153429)
                  ·
                    refine ⟨590608187365171106210317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12599641330456983599153429 590608187365171106210317)
                    ·
                      refine ⟨221478070261939164828869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 590608187365171106210317 221478070261939164828869)
                      ·
                        rfl

theorem cell23_431327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_431327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431327 prefixEnd_431327 := by exact prefixLift 431327
  have htrace : WordTrace (prefixWord ++ tailWord_431327) baseStart_431327 baseEnd_431327 := by
    simpa [prefixWord, tailWord_431327, baseEnd_431327] using wordTrace_append hprefix tailTrace_431327
  have hstable : (prefixWord ++ tailWord_431327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431327).length < 2 ^ (prefixWord ++ tailWord_431327).sum := by decide
  have hdescent : baseEnd_431327 < baseStart_431327 := by decide
  rcases family_descends (prefixWord ++ tailWord_431327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431335 : List Nat := [1, 1, 5, 3, 2, 1, 3, 1, 2, 1, 3]
def baseStart_431335 : Nat := 118140960795 + 431335 * 2 ^ 59
def prefixEnd_431335 : Nat := 4983230072969 + 3 ^ 40 * 431335 * 2
def baseEnd_431335 : Nat := 221482178107175133528833

theorem tailTrace_431335 : CollatzResearch.WordTrace tailWord_431335 prefixEnd_431335 221482178107175133528833 := by
  unfold tailWord_431335
  simp only [CollatzResearch.WordTrace]
  refine ⟨15732079892354435998247459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10488053261569623998831639 15732079892354435998247459)
  ·
    refine ⟨23598119838531653997371189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15732079892354435998247459 23598119838531653997371189)
    ·
      refine ⟨2212323734862342562253549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23598119838531653997371189 2212323734862342562253549)
      ·
        refine ⟨829621400573378460845081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2212323734862342562253549 829621400573378460845081)
        ·
          refine ⟨622216050430033845633811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 829621400573378460845081 622216050430033845633811)
          ·
            refine ⟨933324075645050768450717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622216050430033845633811 933324075645050768450717)
            ·
              refine ⟨349996528366894038169019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 933324075645050768450717 349996528366894038169019)
              ·
                refine ⟨524994792550341057253529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349996528366894038169019 524994792550341057253529)
                ·
                  refine ⟨393746094412755792940147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 524994792550341057253529 393746094412755792940147)
                  ·
                    refine ⟨590619141619133689410221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 393746094412755792940147 590619141619133689410221)
                    ·
                      refine ⟨221482178107175133528833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 590619141619133689410221 221482178107175133528833)
                      ·
                        rfl

theorem cell23_431335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_431335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431335 prefixEnd_431335 := by exact prefixLift 431335
  have htrace : WordTrace (prefixWord ++ tailWord_431335) baseStart_431335 baseEnd_431335 := by
    simpa [prefixWord, tailWord_431335, baseEnd_431335] using wordTrace_append hprefix tailTrace_431335
  have hstable : (prefixWord ++ tailWord_431335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431335).length < 2 ^ (prefixWord ++ tailWord_431335).sum := by decide
  have hdescent : baseEnd_431335 < baseStart_431335 := by decide
  rcases family_descends (prefixWord ++ tailWord_431335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431347 : List Nat := [1, 1, 1, 2, 2, 5, 2, 2, 7]
def baseStart_431347 : Nat := 118140960795 + 431347 * 2 ^ 59
def prefixEnd_431347 : Nat := 4983230072969 + 3 ^ 40 * 431347 * 2
def baseEnd_431347 : Nat := 24609815541669898508753

theorem tailTrace_431347 : CollatzResearch.WordTrace tailWord_431347 prefixEnd_431347 24609815541669898508753 := by
  unfold tailWord_431347
  simp only [CollatzResearch.WordTrace]
  refine ⟨15732517568310962047684295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10488345045540641365122863 15732517568310962047684295)
  ·
    refine ⟨23598776352466443071526443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15732517568310962047684295 23598776352466443071526443)
    ·
      refine ⟨35398164528699664607289665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23598776352466443071526443 35398164528699664607289665)
      ·
        refine ⟨26548623396524748455467249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35398164528699664607289665 26548623396524748455467249)
        ·
          refine ⟨19911467547393561341600437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26548623396524748455467249 19911467547393561341600437)
          ·
            refine ⟨1866700082568146375775041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19911467547393561341600437 1866700082568146375775041)
            ·
              refine ⟨1400025061926109781831281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1866700082568146375775041 1400025061926109781831281)
              ·
                refine ⟨1050018796444582336373461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1400025061926109781831281 1050018796444582336373461)
                ·
                  refine ⟨24609815541669898508753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1050018796444582336373461 24609815541669898508753)
                  ·
                    rfl

theorem cell23_431347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 7].length) (baseStart_431347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431347 prefixEnd_431347 := by exact prefixLift 431347
  have htrace : WordTrace (prefixWord ++ tailWord_431347) baseStart_431347 baseEnd_431347 := by
    simpa [prefixWord, tailWord_431347, baseEnd_431347] using wordTrace_append hprefix tailTrace_431347
  have hstable : (prefixWord ++ tailWord_431347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431347).length < 2 ^ (prefixWord ++ tailWord_431347).sum := by decide
  have hdescent : baseEnd_431347 < baseStart_431347 := by decide
  rcases family_descends (prefixWord ++ tailWord_431347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431358 : List Nat := [4, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2]
def baseStart_431358 : Nat := 118140960795 + 431358 * 2 ^ 59
def prefixEnd_431358 : Nat := 4983230072969 + 3 ^ 40 * 431358 * 2
def baseEnd_431358 : Nat := 221493988162228543541227

theorem tailTrace_431358 : CollatzResearch.WordTrace tailWord_431358 prefixEnd_431358 221493988162228543541227 := by
  unfold tailWord_431358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1966614846408888865791841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10488612514180740617556485 1966614846408888865791841)
  ·
    refine ⟨1474961134806666649343881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1966614846408888865791841 1474961134806666649343881)
    ·
      refine ⟨1106220851104999987007911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1474961134806666649343881 1106220851104999987007911)
      ·
        refine ⟨1659331276657499980511867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1106220851104999987007911 1659331276657499980511867)
        ·
          refine ⟨2488996914986249970767801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1659331276657499980511867 2488996914986249970767801)
          ·
            refine ⟨1866747686239687478075851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2488996914986249970767801 1866747686239687478075851)
            ·
              refine ⟨2800121529359531217113777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1866747686239687478075851 2800121529359531217113777)
              ·
                refine ⟨2100091147019648412835333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2800121529359531217113777 2100091147019648412835333)
                ·
                  refine ⟨393767090066184077406625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2100091147019648412835333 393767090066184077406625)
                  ·
                    refine ⟨295325317549638058054969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 393767090066184077406625 295325317549638058054969)
                    ·
                      refine ⟨221493988162228543541227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 295325317549638058054969 221493988162228543541227)
                      ·
                        rfl

theorem cell23_431358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_431358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431358 prefixEnd_431358 := by exact prefixLift 431358
  have htrace : WordTrace (prefixWord ++ tailWord_431358) baseStart_431358 baseEnd_431358 := by
    simpa [prefixWord, tailWord_431358, baseEnd_431358] using wordTrace_append hprefix tailTrace_431358
  have hstable : (prefixWord ++ tailWord_431358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431358).length < 2 ^ (prefixWord ++ tailWord_431358).sum := by decide
  have hdescent : baseEnd_431358 < baseStart_431358 := by decide
  rcases family_descends (prefixWord ++ tailWord_431358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431392 : List Nat := [2, 1, 1, 5, 3, 2, 2, 1, 2, 2, 2]
def baseStart_431392 : Nat := 118140960795 + 431392 * 2 ^ 59
def prefixEnd_431392 : Nat := 4983230072969 + 3 ^ 40 * 431392 * 2
def baseEnd_431392 : Nat := 221511446504481410516071

theorem tailTrace_431392 : CollatzResearch.WordTrace tailWord_431392 prefixEnd_431392 221511446504481410516071 := by
  unfold tailWord_431392
  simp only [CollatzResearch.WordTrace]
  refine ⟨7867079426573967366536215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10489439235431956488714953 7867079426573967366536215)
  ·
    refine ⟨11800619139860951049804323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7867079426573967366536215 11800619139860951049804323)
    ·
      refine ⟨17700928709791426574706485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11800619139860951049804323 17700928709791426574706485)
      ·
        refine ⟨1659462066542946241378733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17700928709791426574706485 1659462066542946241378733)
        ·
          refine ⟨622298274953604840517025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1659462066542946241378733 622298274953604840517025)
          ·
            refine ⟨466723706215203630387769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 622298274953604840517025 466723706215203630387769)
            ·
              refine ⟨350042779661402722790827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466723706215203630387769 350042779661402722790827)
              ·
                refine ⟨525064169492104084186241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350042779661402722790827 525064169492104084186241)
                ·
                  refine ⟨393798127119078063139681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 525064169492104084186241 393798127119078063139681)
                  ·
                    refine ⟨295348595339308547354761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 393798127119078063139681 295348595339308547354761)
                    ·
                      refine ⟨221511446504481410516071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 295348595339308547354761 221511446504481410516071)
                      ·
                        rfl

theorem cell23_431392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_431392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431392 prefixEnd_431392 := by exact prefixLift 431392
  have htrace : WordTrace (prefixWord ++ tailWord_431392) baseStart_431392 baseEnd_431392 := by
    simpa [prefixWord, tailWord_431392, baseEnd_431392] using wordTrace_append hprefix tailTrace_431392
  have hstable : (prefixWord ++ tailWord_431392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431392).length < 2 ^ (prefixWord ++ tailWord_431392).sum := by decide
  have hdescent : baseEnd_431392 < baseStart_431392 := by decide
  rcases family_descends (prefixWord ++ tailWord_431392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431427 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 6]
def baseStart_431427 : Nat := 118140960795 + 431427 * 2 ^ 59
def prefixEnd_431427 : Nat := 4983230072969 + 3 ^ 40 * 431427 * 2
def baseEnd_431427 : Nat := 221529418327388773578409

theorem tailTrace_431427 : CollatzResearch.WordTrace tailWord_431427 prefixEnd_431427 221529418327388773578409 := by
  unfold tailWord_431427
  simp only [CollatzResearch.WordTrace]
  refine ⟨15735435408021135710596535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10490290272014090473731023 15735435408021135710596535)
  ·
    refine ⟨23603153112031703565894803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15735435408021135710596535 23603153112031703565894803)
    ·
      refine ⟨35404729668047555348842205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23603153112031703565894803 35404729668047555348842205)
      ·
        refine ⟨13276773625517833255815827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35404729668047555348842205 13276773625517833255815827)
        ·
          refine ⟨19915160438276749883723741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13276773625517833255815827 19915160438276749883723741)
          ·
            refine ⟨7468185164353781206396403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19915160438276749883723741 7468185164353781206396403)
            ·
              refine ⟨11202277746530671809594605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7468185164353781206396403 11202277746530671809594605)
              ·
                refine ⟨4200854154949001928597977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11202277746530671809594605 4200854154949001928597977)
                ·
                  refine ⟨3150640616211751446448483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4200854154949001928597977 3150640616211751446448483)
                  ·
                    refine ⟨4725960924317627169672725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3150640616211751446448483 4725960924317627169672725)
                    ·
                      refine ⟨221529418327388773578409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4725960924317627169672725 221529418327388773578409)
                      ·
                        rfl

theorem cell23_431427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_431427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431427 prefixEnd_431427 := by exact prefixLift 431427
  have htrace : WordTrace (prefixWord ++ tailWord_431427) baseStart_431427 baseEnd_431427 := by
    simpa [prefixWord, tailWord_431427, baseEnd_431427] using wordTrace_append hprefix tailTrace_431427
  have hstable : (prefixWord ++ tailWord_431427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431427).length < 2 ^ (prefixWord ++ tailWord_431427).sum := by decide
  have hdescent : baseEnd_431427 < baseStart_431427 := by decide
  rcases family_descends (prefixWord ++ tailWord_431427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431468 : List Nat := [2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 3]
def baseStart_431468 : Nat := 118140960795 + 431468 * 2 ^ 59
def prefixEnd_431468 : Nat := 4983230072969 + 3 ^ 40 * 431468 * 2
def baseEnd_431468 : Nat := 221550471034223113165721

theorem tailTrace_431468 : CollatzResearch.WordTrace tailWord_431468 prefixEnd_431468 221550471034223113165721 := by
  unfold tailWord_431468
  simp only [CollatzResearch.WordTrace]
  refine ⟨7868465400436299856419529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10491287200581733141892705 7868465400436299856419529)
  ·
    refine ⟨5901349050327224892314647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7868465400436299856419529 5901349050327224892314647)
    ·
      refine ⟨8852023575490837338471971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5901349050327224892314647 8852023575490837338471971)
      ·
        refine ⟨13278035363236256007707957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8852023575490837338471971 13278035363236256007707957)
        ·
          refine ⟨1244815815303399000722621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13278035363236256007707957 1244815815303399000722621)
          ·
            refine ⟨466805930738774625270983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1244815815303399000722621 466805930738774625270983)
            ·
              refine ⟨700208896108161937906475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466805930738774625270983 700208896108161937906475)
              ·
                refine ⟨1050313344162242906859713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 700208896108161937906475 1050313344162242906859713)
                ·
                  refine ⟨787735008121682180144785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1050313344162242906859713 787735008121682180144785)
                  ·
                    refine ⟨590801256091261635108589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 787735008121682180144785 590801256091261635108589)
                    ·
                      refine ⟨221550471034223113165721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 590801256091261635108589 221550471034223113165721)
                      ·
                        rfl

theorem cell23_431468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 3].length) (baseStart_431468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431468 prefixEnd_431468 := by exact prefixLift 431468
  have htrace : WordTrace (prefixWord ++ tailWord_431468) baseStart_431468 baseEnd_431468 := by
    simpa [prefixWord, tailWord_431468, baseEnd_431468] using wordTrace_append hprefix tailTrace_431468
  have hstable : (prefixWord ++ tailWord_431468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431468).length < 2 ^ (prefixWord ++ tailWord_431468).sum := by decide
  have hdescent : baseEnd_431468 < baseStart_431468 := by decide
  rcases family_descends (prefixWord ++ tailWord_431468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431508 : List Nat := [2, 4, 2, 1, 2, 1, 1, 2, 1, 5, 2]
def baseStart_431508 : Nat := 118140960795 + 431508 * 2 ^ 59
def prefixEnd_431508 : Nat := 4983230072969 + 3 ^ 40 * 431508 * 2
def baseEnd_431508 : Nat := 221571010260402956665537

theorem tailTrace_431508 : CollatzResearch.WordTrace tailWord_431508 prefixEnd_431508 221571010260402956665537 := by
  unfold tailWord_431508
  simp only [CollatzResearch.WordTrace]
  refine ⟨7869194860363843272147589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10492259813818457696196785 7869194860363843272147589)
  ·
    refine ⟨1475474036318220613527673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7869194860363843272147589 1475474036318220613527673)
    ·
      refine ⟨1106605527238665460145755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1475474036318220613527673 1106605527238665460145755)
      ·
        refine ⟨1659908290857998190218633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1106605527238665460145755 1659908290857998190218633)
        ·
          refine ⟨1244931218143498642663975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1659908290857998190218633 1244931218143498642663975)
          ·
            refine ⟨1867396827215247963995963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1244931218143498642663975 1867396827215247963995963)
            ·
              refine ⟨2801095240822871945993945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1867396827215247963995963 2801095240822871945993945)
              ·
                refine ⟨2100821430617153959495459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2801095240822871945993945 2100821430617153959495459)
                ·
                  refine ⟨3151232145925730939243189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2100821430617153959495459 3151232145925730939243189)
                  ·
                    refine ⟨295428013680537275554049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3151232145925730939243189 295428013680537275554049)
                    ·
                      refine ⟨221571010260402956665537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 295428013680537275554049 221571010260402956665537)
                      ·
                        rfl

theorem cell23_431508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_431508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431508 prefixEnd_431508 := by exact prefixLift 431508
  have htrace : WordTrace (prefixWord ++ tailWord_431508) baseStart_431508 baseEnd_431508 := by
    simpa [prefixWord, tailWord_431508, baseEnd_431508] using wordTrace_append hprefix tailTrace_431508
  have hstable : (prefixWord ++ tailWord_431508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431508).length < 2 ^ (prefixWord ++ tailWord_431508).sum := by decide
  have hdescent : baseEnd_431508 < baseStart_431508 := by decide
  rcases family_descends (prefixWord ++ tailWord_431508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431524 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 5, 1, 5]
def baseStart_431524 : Nat := 118140960795 + 431524 * 2 ^ 59
def prefixEnd_431524 : Nat := 4983230072969 + 3 ^ 40 * 431524 * 2
def baseEnd_431524 : Nat := 221579225950874894065463

theorem tailTrace_431524 : CollatzResearch.WordTrace tailWord_431524 prefixEnd_431524 221579225950874894065463 := by
  unfold tailWord_431524
  simp only [CollatzResearch.WordTrace]
  refine ⟨7869486644334860638438813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10492648859113147517918417 7869486644334860638438813)
  ·
    refine ⟨2951057491625572739414555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7869486644334860638438813 2951057491625572739414555)
    ·
      refine ⟨4426586237438359109121833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2951057491625572739414555 4426586237438359109121833)
      ·
        refine ⟨3319939678078769331841375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4426586237438359109121833 3319939678078769331841375)
        ·
          refine ⟨4979909517118153997762063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3319939678078769331841375 4979909517118153997762063)
          ·
            refine ⟨7469864275677230996643095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4979909517118153997762063 7469864275677230996643095)
            ·
              refine ⟨11204796413515846494964643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7469864275677230996643095 11204796413515846494964643)
              ·
                refine ⟨16807194620273769742446965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11204796413515846494964643 16807194620273769742446965)
                ·
                  refine ⟨1575674495650665913354403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16807194620273769742446965 1575674495650665913354403)
                  ·
                    refine ⟨2363511743475998870031605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1575674495650665913354403 2363511743475998870031605)
                    ·
                      refine ⟨221579225950874894065463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2363511743475998870031605 221579225950874894065463)
                      ·
                        rfl

theorem cell23_431524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_431524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431524 prefixEnd_431524 := by exact prefixLift 431524
  have htrace : WordTrace (prefixWord ++ tailWord_431524) baseStart_431524 baseEnd_431524 := by
    simpa [prefixWord, tailWord_431524, baseEnd_431524] using wordTrace_append hprefix tailTrace_431524
  have hstable : (prefixWord ++ tailWord_431524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431524).length < 2 ^ (prefixWord ++ tailWord_431524).sum := by decide
  have hdescent : baseEnd_431524 < baseStart_431524 := by decide
  rcases family_descends (prefixWord ++ tailWord_431524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431541 : List Nat := [1, 3, 3, 2, 2, 1, 1, 3, 1, 1, 5]
def baseStart_431541 : Nat := 118140960795 + 431541 * 2 ^ 59
def prefixEnd_431541 : Nat := 4983230072969 + 3 ^ 40 * 431541 * 2
def baseEnd_431541 : Nat := 221587955122001327552885

theorem tailTrace_431541 : CollatzResearch.WordTrace tailWord_431541 prefixEnd_431541 221587955122001327552885 := by
  unfold tailWord_431541
  simp only [CollatzResearch.WordTrace]
  refine ⟨15739593329608133180246477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10493062219738755453497651 15739593329608133180246477)
  ·
    refine ⟨5902347498603049942592429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15739593329608133180246477 5902347498603049942592429)
    ·
      refine ⟨2213380311976143728472161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5902347498603049942592429 2213380311976143728472161)
      ·
        refine ⟨1660035233982107796354121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2213380311976143728472161 1660035233982107796354121)
        ·
          refine ⟨1245026425486580847265591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1660035233982107796354121 1245026425486580847265591)
          ·
            refine ⟨1867539638229871270898387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1245026425486580847265591 1867539638229871270898387)
            ·
              refine ⟨2801309457344806906347581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1867539638229871270898387 2801309457344806906347581)
              ·
                refine ⟨1050491046504302589880343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2801309457344806906347581 1050491046504302589880343)
                ·
                  refine ⟨1575736569756453884820515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1050491046504302589880343 1575736569756453884820515)
                  ·
                    refine ⟨2363604854634680827230773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1575736569756453884820515 2363604854634680827230773)
                    ·
                      refine ⟨221587955122001327552885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2363604854634680827230773 221587955122001327552885)
                      ·
                        rfl

theorem cell23_431541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_431541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431541 prefixEnd_431541 := by exact prefixLift 431541
  have htrace : WordTrace (prefixWord ++ tailWord_431541) baseStart_431541 baseEnd_431541 := by
    simpa [prefixWord, tailWord_431541, baseEnd_431541] using wordTrace_append hprefix tailTrace_431541
  have hstable : (prefixWord ++ tailWord_431541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431541).length < 2 ^ (prefixWord ++ tailWord_431541).sum := by decide
  have hdescent : baseEnd_431541 < baseStart_431541 := by decide
  rcases family_descends (prefixWord ++ tailWord_431541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431555 : List Nat := [1, 1, 1, 3, 1, 1, 4, 6, 1, 2, 2]
def baseStart_431555 : Nat := 118140960795 + 431555 * 2 ^ 59
def prefixEnd_431555 : Nat := 4983230072969 + 3 ^ 40 * 431555 * 2
def baseEnd_431555 : Nat := 221595143851164272777821

theorem tailTrace_431555 : CollatzResearch.WordTrace tailWord_431555 prefixEnd_431555 221595143851164272777821 := by
  unfold tailWord_431555
  simp only [CollatzResearch.WordTrace]
  refine ⟨15740103951557413571256119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10493402634371609047504079 15740103951557413571256119)
  ·
    refine ⟨23610155927336120356884179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15740103951557413571256119 23610155927336120356884179)
    ·
      refine ⟨35415233891004180535326269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23610155927336120356884179 35415233891004180535326269)
      ·
        refine ⟨13280712709126567700747351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35415233891004180535326269 13280712709126567700747351)
        ·
          refine ⟨19921069063689851551121027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13280712709126567700747351 19921069063689851551121027)
          ·
            refine ⟨29881603595534777326681541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19921069063689851551121027 29881603595534777326681541)
            ·
              refine ⟨5602800674162770748752789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29881603595534777326681541 5602800674162770748752789)
              ·
                refine ⟨262631281601379878847787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5602800674162770748752789 262631281601379878847787)
                ·
                  refine ⟨393946922402069818271681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262631281601379878847787 393946922402069818271681)
                  ·
                    refine ⟨295460191801552363703761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 393946922402069818271681 295460191801552363703761)
                    ·
                      refine ⟨221595143851164272777821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 295460191801552363703761 221595143851164272777821)
                      ·
                        rfl

theorem cell23_431555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 6, 1, 2, 2].length) (baseStart_431555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431555 prefixEnd_431555 := by exact prefixLift 431555
  have htrace : WordTrace (prefixWord ++ tailWord_431555) baseStart_431555 baseEnd_431555 := by
    simpa [prefixWord, tailWord_431555, baseEnd_431555] using wordTrace_append hprefix tailTrace_431555
  have hstable : (prefixWord ++ tailWord_431555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431555).length < 2 ^ (prefixWord ++ tailWord_431555).sum := by decide
  have hdescent : baseEnd_431555 < baseStart_431555 := by decide
  rcases family_descends (prefixWord ++ tailWord_431555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431572 : List Nat := [2, 4, 1, 2, 4, 1, 1, 2, 1, 1, 4]
def baseStart_431572 : Nat := 118140960795 + 431572 * 2 ^ 59
def prefixEnd_431572 : Nat := 4983230072969 + 3 ^ 40 * 431572 * 2
def baseEnd_431572 : Nat := 221603873022290706265243

theorem tailTrace_431572 : CollatzResearch.WordTrace tailWord_431572 prefixEnd_431572 221603873022290706265243 := by
  unfold tailWord_431572
  simp only [CollatzResearch.WordTrace]
  refine ⟨7870361996247912737312485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10493815994997216983083313 7870361996247912737312485)
  ·
    refine ⟨1475692874296483638246091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7870361996247912737312485 1475692874296483638246091)
    ·
      refine ⟨2213539311444725457369137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1475692874296483638246091 2213539311444725457369137)
      ·
        refine ⟨1660154483583544093026853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2213539311444725457369137 1660154483583544093026853)
        ·
          refine ⟨311278965671914517442535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1660154483583544093026853 311278965671914517442535)
          ·
            refine ⟨466918448507871776163803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311278965671914517442535 466918448507871776163803)
            ·
              refine ⟨700377672761807664245705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466918448507871776163803 700377672761807664245705)
              ·
                refine ⟨525283254571355748184279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 700377672761807664245705 525283254571355748184279)
                ·
                  refine ⟨787924881857033622276419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 525283254571355748184279 787924881857033622276419)
                  ·
                    refine ⟨1181887322785550433414629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 787924881857033622276419 1181887322785550433414629)
                    ·
                      refine ⟨221603873022290706265243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1181887322785550433414629 221603873022290706265243)
                      ·
                        rfl

theorem cell23_431572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_431572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431572 prefixEnd_431572 := by exact prefixLift 431572
  have htrace : WordTrace (prefixWord ++ tailWord_431572) baseStart_431572 baseEnd_431572 := by
    simpa [prefixWord, tailWord_431572, baseEnd_431572] using wordTrace_append hprefix tailTrace_431572
  have hstable : (prefixWord ++ tailWord_431572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431572).length < 2 ^ (prefixWord ++ tailWord_431572).sum := by decide
  have hdescent : baseEnd_431572 < baseStart_431572 := by decide
  rcases family_descends (prefixWord ++ tailWord_431572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431584 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 5]
def baseStart_431584 : Nat := 118140960795 + 431584 * 2 ^ 59
def prefixEnd_431584 : Nat := 4983230072969 + 3 ^ 40 * 431584 * 2
def baseEnd_431584 : Nat := 221610034790144659315187

theorem tailTrace_431584 : CollatzResearch.WordTrace tailWord_431584 prefixEnd_431584 221610034790144659315187 := by
  unfold tailWord_431584
  simp only [CollatzResearch.WordTrace]
  refine ⟨7870580834226175762030903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10494107778968234349374537 7870580834226175762030903)
  ·
    refine ⟨11805871251339263643046355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7870580834226175762030903 11805871251339263643046355)
    ·
      refine ⟨17708806877008895464569533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11805871251339263643046355 17708806877008895464569533)
      ·
        refine ⟨6640802578878335799213575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17708806877008895464569533 6640802578878335799213575)
        ·
          refine ⟨9961203868317503698820363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6640802578878335799213575 9961203868317503698820363)
          ·
            refine ⟨14941805802476255548230545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9961203868317503698820363 14941805802476255548230545)
            ·
              refine ⟨11206354351857191661172909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14941805802476255548230545 11206354351857191661172909)
              ·
                refine ⟨4202382881946446872939841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11206354351857191661172909 4202382881946446872939841)
                ·
                  refine ⟨3151787161459835154704881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4202382881946446872939841 3151787161459835154704881)
                  ·
                    refine ⟨2363840371094876366028661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3151787161459835154704881 2363840371094876366028661)
                    ·
                      refine ⟨221610034790144659315187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2363840371094876366028661 221610034790144659315187)
                      ·
                        rfl

theorem cell23_431584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_431584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431584 prefixEnd_431584 := by exact prefixLift 431584
  have htrace : WordTrace (prefixWord ++ tailWord_431584) baseStart_431584 baseEnd_431584 := by
    simpa [prefixWord, tailWord_431584, baseEnd_431584] using wordTrace_append hprefix tailTrace_431584
  have hstable : (prefixWord ++ tailWord_431584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431584).length < 2 ^ (prefixWord ++ tailWord_431584).sum := by decide
  have hdescent : baseEnd_431584 < baseStart_431584 := by decide
  rcases family_descends (prefixWord ++ tailWord_431584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431606 : List Nat := [5, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2]
def baseStart_431606 : Nat := 118140960795 + 431606 * 2 ^ 59
def prefixEnd_431606 : Nat := 4983230072969 + 3 ^ 40 * 431606 * 2
def baseEnd_431606 : Nat := 221621331364543573240087

theorem tailTrace_431606 : CollatzResearch.WordTrace tailWord_431606 prefixEnd_431606 221621331364543573240087 := by
  unfold tailWord_431606
  simp only [CollatzResearch.WordTrace]
  refine ⟨983872754648290580085167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10494642716248432854241781 983872754648290580085167)
  ·
    refine ⟨1475809131972435870127751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 983872754648290580085167 1475809131972435870127751)
    ·
      refine ⟨2213713697958653805191627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1475809131972435870127751 2213713697958653805191627)
      ·
        refine ⟨3320570546937980707787441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2213713697958653805191627 3320570546937980707787441)
        ·
          refine ⟨2490427910203485530840581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3320570546937980707787441 2490427910203485530840581)
          ·
            refine ⟨466955233163153537032609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2490427910203485530840581 466955233163153537032609)
            ·
              refine ⟨350216424872365152774457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466955233163153537032609 350216424872365152774457)
              ·
                refine ⟨262662318654273864580843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350216424872365152774457 262662318654273864580843)
                ·
                  refine ⟨393993477981410796871265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262662318654273864580843 393993477981410796871265)
                  ·
                    refine ⟨295495108486058097653449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 393993477981410796871265 295495108486058097653449)
                    ·
                      refine ⟨221621331364543573240087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 295495108486058097653449 221621331364543573240087)
                      ·
                        rfl

theorem cell23_431606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_431606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431606 prefixEnd_431606 := by exact prefixLift 431606
  have htrace : WordTrace (prefixWord ++ tailWord_431606) baseStart_431606 baseEnd_431606 := by
    simpa [prefixWord, tailWord_431606, baseEnd_431606] using wordTrace_append hprefix tailTrace_431606
  have hstable : (prefixWord ++ tailWord_431606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431606).length < 2 ^ (prefixWord ++ tailWord_431606).sum := by decide
  have hdescent : baseEnd_431606 < baseStart_431606 := by decide
  rcases family_descends (prefixWord ++ tailWord_431606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431645 : List Nat := [1, 4, 2, 2, 1, 1, 2, 2, 4, 2, 2]
def baseStart_431645 : Nat := 118140960795 + 431645 * 2 ^ 59
def prefixEnd_431645 : Nat := 4983230072969 + 3 ^ 40 * 431645 * 2
def baseEnd_431645 : Nat := 221641357110068920652407

theorem tailTrace_431645 : CollatzResearch.WordTrace tailWord_431645 prefixEnd_431645 221641357110068920652407 := by
  unfold tailWord_431645
  simp only [CollatzResearch.WordTrace]
  refine ⟨15743386521231358942032389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10495591014154239294688259 15743386521231358942032389)
  ·
    refine ⟨2951884972730879801631073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15743386521231358942032389 2951884972730879801631073)
    ·
      refine ⟨2213913729548159851223305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2951884972730879801631073 2213913729548159851223305)
      ·
        refine ⟨1660435297161119888417479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2213913729548159851223305 1660435297161119888417479)
        ·
          refine ⟨2490652945741679832626219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1660435297161119888417479 2490652945741679832626219)
          ·
            refine ⟨3735979418612519748939329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2490652945741679832626219 3735979418612519748939329)
            ·
              refine ⟨2801984563959389811704497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3735979418612519748939329 2801984563959389811704497)
              ·
                refine ⟨2101488422969542358778373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2801984563959389811704497 2101488422969542358778373)
                ·
                  refine ⟨394029079306789192270945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2101488422969542358778373 394029079306789192270945)
                  ·
                    refine ⟨295521809480091894203209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 394029079306789192270945 295521809480091894203209)
                    ·
                      refine ⟨221641357110068920652407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 295521809480091894203209 221641357110068920652407)
                      ·
                        rfl

theorem cell23_431645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_431645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431645 prefixEnd_431645 := by exact prefixLift 431645
  have htrace : WordTrace (prefixWord ++ tailWord_431645) baseStart_431645 baseEnd_431645 := by
    simpa [prefixWord, tailWord_431645, baseEnd_431645] using wordTrace_append hprefix tailTrace_431645
  have hstable : (prefixWord ++ tailWord_431645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431645).length < 2 ^ (prefixWord ++ tailWord_431645).sum := by decide
  have hdescent : baseEnd_431645 < baseStart_431645 := by decide
  rcases family_descends (prefixWord ++ tailWord_431645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431662 : List Nat := [4, 1, 3, 1, 2, 2, 1, 1, 4, 2, 2]
def baseStart_431662 : Nat := 118140960795 + 431662 * 2 ^ 59
def prefixEnd_431662 : Nat := 4983230072969 + 3 ^ 40 * 431662 * 2
def baseEnd_431662 : Nat := 221650086281195354139829

theorem tailTrace_431662 : CollatzResearch.WordTrace tailWord_431662 prefixEnd_431662 221650086281195354139829 := by
  unfold tailWord_431662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1968000820271221355675155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10496004374779847230267493 1968000820271221355675155)
  ·
    refine ⟨2952001230406832033512733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1968000820271221355675155 2952001230406832033512733)
    ·
      refine ⟨1107000461402562012567275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2952001230406832033512733 1107000461402562012567275)
      ·
        refine ⟨1660500692103843018850913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1107000461402562012567275 1660500692103843018850913)
        ·
          refine ⟨1245375519077882264138185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1660500692103843018850913 1245375519077882264138185)
          ·
            refine ⟨934031639308411698103639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1245375519077882264138185 934031639308411698103639)
            ·
              refine ⟨1401047458962617547155459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 934031639308411698103639 1401047458962617547155459)
              ·
                refine ⟨2101571188443926320733189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1401047458962617547155459 2101571188443926320733189)
                ·
                  refine ⟨394044597833236185137473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2101571188443926320733189 394044597833236185137473)
                  ·
                    refine ⟨295533448374927138853105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 394044597833236185137473 295533448374927138853105)
                    ·
                      refine ⟨221650086281195354139829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 295533448374927138853105 221650086281195354139829)
                      ·
                        rfl

theorem cell23_431662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_431662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431662 prefixEnd_431662 := by exact prefixLift 431662
  have htrace : WordTrace (prefixWord ++ tailWord_431662) baseStart_431662 baseEnd_431662 := by
    simpa [prefixWord, tailWord_431662, baseEnd_431662] using wordTrace_append hprefix tailTrace_431662
  have hstable : (prefixWord ++ tailWord_431662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431662).length < 2 ^ (prefixWord ++ tailWord_431662).sum := by decide
  have hdescent : baseEnd_431662 < baseStart_431662 := by decide
  rcases family_descends (prefixWord ++ tailWord_431662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431681 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 3, 7]
def baseStart_431681 : Nat := 118140960795 + 431681 * 2 ^ 59
def prefixEnd_431681 : Nat := 4983230072969 + 3 ^ 40 * 431681 * 2
def baseEnd_431681 : Nat := 73886614137876926600747

theorem tailTrace_431681 : CollatzResearch.WordTrace tailWord_431681 prefixEnd_431681 73886614137876926600747 := by
  unfold tailWord_431681
  simp only [CollatzResearch.WordTrace]
  refine ⟨15744699549100937090342897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10496466366067291393561931 15744699549100937090342897)
  ·
    refine ⟨11808524661825702817757173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15744699549100937090342897 11808524661825702817757173)
    ·
      refine ⟨1107049187046159639164735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11808524661825702817757173 1107049187046159639164735)
      ·
        refine ⟨1660573780569239458747103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1107049187046159639164735 1660573780569239458747103)
        ·
          refine ⟨2490860670853859188120655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1660573780569239458747103 2490860670853859188120655)
          ·
            refine ⟨3736291006280788782180983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2490860670853859188120655 3736291006280788782180983)
            ·
              refine ⟨5604436509421183173271475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3736291006280788782180983 5604436509421183173271475)
              ·
                refine ⟨8406654764131774759907213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5604436509421183173271475 8406654764131774759907213)
                ·
                  refine ⟨3152495536549415534965205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8406654764131774759907213 3152495536549415534965205)
                  ·
                    refine ⟨73886614137876926600747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3152495536549415534965205 73886614137876926600747)
                    ·
                      rfl

theorem cell23_431681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_431681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431681 prefixEnd_431681 := by exact prefixLift 431681
  have htrace : WordTrace (prefixWord ++ tailWord_431681) baseStart_431681 baseEnd_431681 := by
    simpa [prefixWord, tailWord_431681, baseEnd_431681] using wordTrace_append hprefix tailTrace_431681
  have hstable : (prefixWord ++ tailWord_431681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431681).length < 2 ^ (prefixWord ++ tailWord_431681).sum := by decide
  have hdescent : baseEnd_431681 < baseStart_431681 := by decide
  rcases family_descends (prefixWord ++ tailWord_431681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431752 : List Nat := [2, 1, 3, 5, 1, 1, 2, 1, 2, 1, 4]
def baseStart_431752 : Nat := 118140960795 + 431752 * 2 ^ 59
def prefixEnd_431752 : Nat := 4983230072969 + 3 ^ 40 * 431752 * 2
def baseEnd_431752 : Nat := 221696299540100002014415

theorem tailTrace_431752 : CollatzResearch.WordTrace tailWord_431752 prefixEnd_431752 221696299540100002014415 := by
  unfold tailWord_431752
  simp only [CollatzResearch.WordTrace]
  refine ⟨7873644565921858108088755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10498192754562477477451673 7873644565921858108088755)
  ·
    refine ⟨11810466848882787162133133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7873644565921858108088755 11810466848882787162133133)
    ·
      refine ⟨4428925068331045185799925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11810466848882787162133133 4428925068331045185799925)
      ·
        refine ⟨415211725156035486168743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4428925068331045185799925 415211725156035486168743)
        ·
          refine ⟨622817587734053229253115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415211725156035486168743 622817587734053229253115)
          ·
            refine ⟨934226381601079843879673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622817587734053229253115 934226381601079843879673)
            ·
              refine ⟨700669786200809882909755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 934226381601079843879673 700669786200809882909755)
              ·
                refine ⟨1051004679301214824364633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 700669786200809882909755 1051004679301214824364633)
                ·
                  refine ⟨788253509475911118273475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1051004679301214824364633 788253509475911118273475)
                  ·
                    refine ⟨1182380264213866677410213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 788253509475911118273475 1182380264213866677410213)
                    ·
                      refine ⟨221696299540100002014415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1182380264213866677410213 221696299540100002014415)
                      ·
                        rfl

theorem cell23_431752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_431752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431752 prefixEnd_431752 := by exact prefixLift 431752
  have htrace : WordTrace (prefixWord ++ tailWord_431752) baseStart_431752 baseEnd_431752 := by
    simpa [prefixWord, tailWord_431752, baseEnd_431752] using wordTrace_append hprefix tailTrace_431752
  have hstable : (prefixWord ++ tailWord_431752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431752).length < 2 ^ (prefixWord ++ tailWord_431752).sum := by decide
  have hdescent : baseEnd_431752 < baseStart_431752 := by decide
  rcases family_descends (prefixWord ++ tailWord_431752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431808 : List Nat := [2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 4]
def baseStart_431808 : Nat := 118140960795 + 431808 * 2 ^ 59
def prefixEnd_431808 : Nat := 4983230072969 + 3 ^ 40 * 431808 * 2
def baseEnd_431808 : Nat := 221725054456751782914157

theorem tailTrace_431808 : CollatzResearch.WordTrace tailWord_431808 prefixEnd_431808 221725054456751782914157 := by
  unfold tailWord_431808
  simp only [CollatzResearch.WordTrace]
  refine ⟨7874665809820418890108039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10499554413093891853477385 7874665809820418890108039)
  ·
    refine ⟨11811998714730628335162059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7874665809820418890108039 11811998714730628335162059)
    ·
      refine ⟨17717998072095942502743089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11811998714730628335162059 17717998072095942502743089)
      ·
        refine ⟨13288498554071956877057317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17717998072095942502743089 13288498554071956877057317)
        ·
          refine ⟨2491593478888491914448247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13288498554071956877057317 2491593478888491914448247)
          ·
            refine ⟨3737390218332737871672371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2491593478888491914448247 3737390218332737871672371)
            ·
              refine ⟨5606085327499106807508557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3737390218332737871672371 5606085327499106807508557)
              ·
                refine ⟨2102281997812165052815709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5606085327499106807508557 2102281997812165052815709)
                ·
                  refine ⟨788355749179561894805891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2102281997812165052815709 788355749179561894805891)
                  ·
                    refine ⟨1182533623769342842208837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 788355749179561894805891 1182533623769342842208837)
                    ·
                      refine ⟨221725054456751782914157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1182533623769342842208837 221725054456751782914157)
                      ·
                        rfl

theorem cell23_431808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_431808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431808 prefixEnd_431808 := by exact prefixLift 431808
  have htrace : WordTrace (prefixWord ++ tailWord_431808) baseStart_431808 baseEnd_431808 := by
    simpa [prefixWord, tailWord_431808, baseEnd_431808] using wordTrace_append hprefix tailTrace_431808
  have hstable : (prefixWord ++ tailWord_431808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431808).length < 2 ^ (prefixWord ++ tailWord_431808).sum := by decide
  have hdescent : baseEnd_431808 < baseStart_431808 := by decide
  rcases family_descends (prefixWord ++ tailWord_431808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431825 : List Nat := [1, 2, 2, 1, 2, 5, 1, 3, 1, 1, 4]
def baseStart_431825 : Nat := 118140960795 + 431825 * 2 ^ 59
def prefixEnd_431825 : Nat := 4983230072969 + 3 ^ 40 * 431825 * 2
def baseEnd_431825 : Nat := 221733783627878216401579

theorem tailTrace_431825 : CollatzResearch.WordTrace tailWord_431825 prefixEnd_431825 221733783627878216401579 := by
  unfold tailWord_431825
  simp only [CollatzResearch.WordTrace]
  refine ⟨15749951660579249683584929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10499967773719499789056619 15749951660579249683584929)
  ·
    refine ⟨11812463745434437262688697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15749951660579249683584929 11812463745434437262688697)
    ·
      refine ⟨8859347809075827947016523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11812463745434437262688697 8859347809075827947016523)
      ·
        refine ⟨13289021713613741920524785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8859347809075827947016523 13289021713613741920524785)
        ·
          refine ⟨9966766285210306440393589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13289021713613741920524785 9966766285210306440393589)
          ·
            refine ⟨934384339238466228786899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9966766285210306440393589 934384339238466228786899)
            ·
              refine ⟨1401576508857699343180349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 934384339238466228786899 1401576508857699343180349)
              ·
                refine ⟨525591190821637253692631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1401576508857699343180349 525591190821637253692631)
                ·
                  refine ⟨788386786232455880538947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 525591190821637253692631 788386786232455880538947)
                  ·
                    refine ⟨1182580179348683820808421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 788386786232455880538947 1182580179348683820808421)
                    ·
                      refine ⟨221733783627878216401579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1182580179348683820808421 221733783627878216401579)
                      ·
                        rfl

theorem cell23_431825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 1, 4].length) (baseStart_431825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431825 prefixEnd_431825 := by exact prefixLift 431825
  have htrace : WordTrace (prefixWord ++ tailWord_431825) baseStart_431825 baseEnd_431825 := by
    simpa [prefixWord, tailWord_431825, baseEnd_431825] using wordTrace_append hprefix tailTrace_431825
  have hstable : (prefixWord ++ tailWord_431825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431825).length < 2 ^ (prefixWord ++ tailWord_431825).sum := by decide
  have hdescent : baseEnd_431825 < baseStart_431825 := by decide
  rcases family_descends (prefixWord ++ tailWord_431825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431831 : List Nat := [1, 1, 3, 2, 1, 3, 12]
def baseStart_431831 : Nat := 118140960795 + 431831 * 2 ^ 59
def prefixEnd_431831 : Nat := 4983230072969 + 3 ^ 40 * 431831 * 2
def baseEnd_431831 : Nat := 2737492154466730776871

theorem tailTrace_431831 : CollatzResearch.WordTrace tailWord_431831 prefixEnd_431831 2737492154466730776871 := by
  unfold tailWord_431831
  simp only [CollatzResearch.WordTrace]
  refine ⟨15750170498557512708303347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10500113665705008472202231 15750170498557512708303347)
  ·
    refine ⟨23625255747836269062455021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15750170498557512708303347 23625255747836269062455021)
    ·
      refine ⟨8859470905438600898420633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23625255747836269062455021 8859470905438600898420633)
      ·
        refine ⟨6644603179078950673815475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8859470905438600898420633 6644603179078950673815475)
        ·
          refine ⟨9966904768618426010723213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6644603179078950673815475 9966904768618426010723213)
          ·
            refine ⟨3737589288231909754021205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9966904768618426010723213 3737589288231909754021205)
            ·
              refine ⟨2737492154466730776871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 3737589288231909754021205 2737492154466730776871)
              ·
                rfl

theorem cell23_431831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 12].length) (baseStart_431831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431831 prefixEnd_431831 := by exact prefixLift 431831
  have htrace : WordTrace (prefixWord ++ tailWord_431831) baseStart_431831 baseEnd_431831 := by
    simpa [prefixWord, tailWord_431831, baseEnd_431831] using wordTrace_append hprefix tailTrace_431831
  have hstable : (prefixWord ++ tailWord_431831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431831).length < 2 ^ (prefixWord ++ tailWord_431831).sum := by decide
  have hdescent : baseEnd_431831 < baseStart_431831 := by decide
  rcases family_descends (prefixWord ++ tailWord_431831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431862 : List Nat := [5, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3]
def baseStart_431862 : Nat := 118140960795 + 431862 * 2 ^ 59
def prefixEnd_431862 : Nat := 4983230072969 + 3 ^ 40 * 431862 * 2
def baseEnd_431862 : Nat := 221752782412094571638909

theorem tailTrace_431862 : CollatzResearch.WordTrace tailWord_431862 prefixEnd_431862 221752782412094571638909 := by
  unfold tailWord_431862
  simp only [CollatzResearch.WordTrace]
  refine ⟨984456322590325312667615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10500867440963470001787893 984456322590325312667615)
  ·
    refine ⟨1476684483885487969001423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 984456322590325312667615 1476684483885487969001423)
    ·
      refine ⟨2215026725828231953502135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1476684483885487969001423 2215026725828231953502135)
      ·
        refine ⟨3322540088742347930253203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2215026725828231953502135 3322540088742347930253203)
        ·
          refine ⟨4983810133113521895379805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3322540088742347930253203 4983810133113521895379805)
          ·
            refine ⟨1868928799917570710767427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4983810133113521895379805 1868928799917570710767427)
            ·
              refine ⟨2803393199876356066151141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1868928799917570710767427 2803393199876356066151141)
              ·
                refine ⟨525636224976816762403339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2803393199876356066151141 525636224976816762403339)
                ·
                  refine ⟨788454337465225143605009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 525636224976816762403339 788454337465225143605009)
                  ·
                    refine ⟨591340753098918857703757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 788454337465225143605009 591340753098918857703757)
                    ·
                      refine ⟨221752782412094571638909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 591340753098918857703757 221752782412094571638909)
                      ·
                        rfl

theorem cell23_431862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_431862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431862 prefixEnd_431862 := by exact prefixLift 431862
  have htrace : WordTrace (prefixWord ++ tailWord_431862) baseStart_431862 baseEnd_431862 := by
    simpa [prefixWord, tailWord_431862, baseEnd_431862] using wordTrace_append hprefix tailTrace_431862
  have hstable : (prefixWord ++ tailWord_431862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431862).length < 2 ^ (prefixWord ++ tailWord_431862).sum := by decide
  have hdescent : baseEnd_431862 < baseStart_431862 := by decide
  rcases family_descends (prefixWord ++ tailWord_431862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431875 : List Nat := [1, 1, 1, 3, 2, 2, 3, 2, 4, 1, 3]
def baseStart_431875 : Nat := 118140960795 + 431875 * 2 ^ 59
def prefixEnd_431875 : Nat := 4983230072969 + 3 ^ 40 * 431875 * 2
def baseEnd_431875 : Nat := 221759457660603020776349

theorem tailTrace_431875 : CollatzResearch.WordTrace tailWord_431875 prefixEnd_431875 221759457660603020776349 := by
  unfold tailWord_431875
  simp only [CollatzResearch.WordTrace]
  refine ⟨15751775310398108222905079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10501183540265405481936719 15751775310398108222905079)
  ·
    refine ⟨23627662965597162334357619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15751775310398108222905079 23627662965597162334357619)
    ·
      refine ⟨35441494448395743501536429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23627662965597162334357619 35441494448395743501536429)
      ·
        refine ⟨13290560418148403813076161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35441494448395743501536429 13290560418148403813076161)
        ·
          refine ⟨9967920313611302859807121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13290560418148403813076161 9967920313611302859807121)
          ·
            refine ⟨7475940235208477144855341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9967920313611302859807121 7475940235208477144855341)
            ·
              refine ⟨2803477588203178929320753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7475940235208477144855341 2803477588203178929320753)
              ·
                refine ⟨2102608191152384196990565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2803477588203178929320753 2102608191152384196990565)
                ·
                  refine ⟨394239035841072036935731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2102608191152384196990565 394239035841072036935731)
                  ·
                    refine ⟨591358553761608055403597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 394239035841072036935731 591358553761608055403597)
                    ·
                      refine ⟨221759457660603020776349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 591358553761608055403597 221759457660603020776349)
                      ·
                        rfl

theorem cell23_431875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 4, 1, 3].length) (baseStart_431875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431875 prefixEnd_431875 := by exact prefixLift 431875
  have htrace : WordTrace (prefixWord ++ tailWord_431875) baseStart_431875 baseEnd_431875 := by
    simpa [prefixWord, tailWord_431875, baseEnd_431875] using wordTrace_append hprefix tailTrace_431875
  have hstable : (prefixWord ++ tailWord_431875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431875).length < 2 ^ (prefixWord ++ tailWord_431875).sum := by decide
  have hdescent : baseEnd_431875 < baseStart_431875 := by decide
  rcases family_descends (prefixWord ++ tailWord_431875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431876 : List Nat := [2, 3, 2, 2, 1, 2, 3, 3, 1, 2, 2]
def baseStart_431876 : Nat := 118140960795 + 431876 * 2 ^ 59
def prefixEnd_431876 : Nat := 4983230072969 + 3 ^ 40 * 431876 * 2
def baseEnd_431876 : Nat := 221759971141257516863845

theorem tailTrace_431876 : CollatzResearch.WordTrace tailWord_431876 prefixEnd_431876 221759971141257516863845 := by
  unfold tailWord_431876
  simp only [CollatzResearch.WordTrace]
  refine ⟨7875905891697242696845741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10501207855596323595794321 7875905891697242696845741)
  ·
    refine ⟨2953464709386466011317153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7875905891697242696845741 2953464709386466011317153)
    ·
      refine ⟨2215098532039849508487865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2953464709386466011317153 2215098532039849508487865)
      ·
        refine ⟨1661323899029887131365899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2215098532039849508487865 1661323899029887131365899)
        ·
          refine ⟨2491985848544830697048849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1661323899029887131365899 2491985848544830697048849)
          ·
            refine ⟨1868989386408623022786637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2491985848544830697048849 1868989386408623022786637)
            ·
              refine ⟨700871019903233633544989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1868989386408623022786637 700871019903233633544989)
              ·
                refine ⟨262826632463712612579371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 700871019903233633544989 262826632463712612579371)
                ·
                  refine ⟨394239948695568918869057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262826632463712612579371 394239948695568918869057)
                  ·
                    refine ⟨295679961521676689151793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 394239948695568918869057 295679961521676689151793)
                    ·
                      refine ⟨221759971141257516863845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 295679961521676689151793 221759971141257516863845)
                      ·
                        rfl

theorem cell23_431876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_431876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431876 prefixEnd_431876 := by exact prefixLift 431876
  have htrace : WordTrace (prefixWord ++ tailWord_431876) baseStart_431876 baseEnd_431876 := by
    simpa [prefixWord, tailWord_431876, baseEnd_431876] using wordTrace_append hprefix tailTrace_431876
  have hstable : (prefixWord ++ tailWord_431876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431876).length < 2 ^ (prefixWord ++ tailWord_431876).sum := by decide
  have hdescent : baseEnd_431876 < baseStart_431876 := by decide
  rcases family_descends (prefixWord ++ tailWord_431876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431909 : List Nat := [1, 3, 1, 2, 3, 2, 4, 1, 2, 1, 3]
def baseStart_431909 : Nat := 118140960795 + 431909 * 2 ^ 59
def prefixEnd_431909 : Nat := 4983230072969 + 3 ^ 40 * 431909 * 2
def baseEnd_431909 : Nat := 221776916002855887751193

theorem tailTrace_431909 : CollatzResearch.WordTrace tailWord_431909 prefixEnd_431909 221776916002855887751193 := by
  unfold tailWord_431909
  simp only [CollatzResearch.WordTrace]
  refine ⟨15753015392274932029642781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10502010261516621353095187 15753015392274932029642781)
  ·
    refine ⟨5907380772103099511116043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15753015392274932029642781 5907380772103099511116043)
    ·
      refine ⟨8861071158154649266674065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5907380772103099511116043 8861071158154649266674065)
      ·
        refine ⟨6645803368615986950005549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8861071158154649266674065 6645803368615986950005549)
        ·
          refine ⟨2492176263230995106252081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6645803368615986950005549 2492176263230995106252081)
          ·
            refine ⟨1869132197423246329689061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2492176263230995106252081 1869132197423246329689061)
            ·
              refine ⟨350462287016858686816699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1869132197423246329689061 350462287016858686816699)
              ·
                refine ⟨525693430525288030225049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350462287016858686816699 525693430525288030225049)
                ·
                  refine ⟨394270072893966022668787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 525693430525288030225049 394270072893966022668787)
                  ·
                    refine ⟨591405109340949034003181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 394270072893966022668787 591405109340949034003181)
                    ·
                      refine ⟨221776916002855887751193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 591405109340949034003181 221776916002855887751193)
                      ·
                        rfl

theorem cell23_431909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 2, 1, 3].length) (baseStart_431909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431909 prefixEnd_431909 := by exact prefixLift 431909
  have htrace : WordTrace (prefixWord ++ tailWord_431909) baseStart_431909 baseEnd_431909 := by
    simpa [prefixWord, tailWord_431909, baseEnd_431909] using wordTrace_append hprefix tailTrace_431909
  have hstable : (prefixWord ++ tailWord_431909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431909).length < 2 ^ (prefixWord ++ tailWord_431909).sum := by decide
  have hdescent : baseEnd_431909 < baseStart_431909 := by decide
  rcases family_descends (prefixWord ++ tailWord_431909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431932 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 6, 2, 2]
def baseStart_431932 : Nat := 118140960795 + 431932 * 2 ^ 59
def prefixEnd_431932 : Nat := 4983230072969 + 3 ^ 40 * 431932 * 2
def baseEnd_431932 : Nat := 221788726057909297763587

theorem tailTrace_431932 : CollatzResearch.WordTrace tailWord_431932 prefixEnd_431932 221788726057909297763587 := by
  unfold tailWord_431932
  simp only [CollatzResearch.WordTrace]
  refine ⟨7876927135595803478865025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10502569514127737971820033 7876927135595803478865025)
  ·
    refine ⟨5907695351696852609148769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7876927135595803478865025 5907695351696852609148769)
    ·
      refine ⟨4430771513772639456861577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5907695351696852609148769 4430771513772639456861577)
      ·
        refine ⟨3323078635329479592646183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4430771513772639456861577 3323078635329479592646183)
        ·
          refine ⟨4984617952994219388969275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3323078635329479592646183 4984617952994219388969275)
          ·
            refine ⟨7476926929491329083453913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4984617952994219388969275 7476926929491329083453913)
            ·
              refine ⟨5607695197118496812590435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7476926929491329083453913 5607695197118496812590435)
              ·
                refine ⟨8411542795677745218885653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5607695197118496812590435 8411542795677745218885653)
                ·
                  refine ⟨394291068547394307135265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8411542795677745218885653 394291068547394307135265)
                  ·
                    refine ⟨295718301410545730351449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 394291068547394307135265 295718301410545730351449)
                    ·
                      refine ⟨221788726057909297763587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 295718301410545730351449 221788726057909297763587)
                      ·
                        rfl

theorem cell23_431932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_431932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_431932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_431932 prefixEnd_431932 := by exact prefixLift 431932
  have htrace : WordTrace (prefixWord ++ tailWord_431932) baseStart_431932 baseEnd_431932 := by
    simpa [prefixWord, tailWord_431932, baseEnd_431932] using wordTrace_append hprefix tailTrace_431932
  have hstable : (prefixWord ++ tailWord_431932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431932).length < 2 ^ (prefixWord ++ tailWord_431932).sum := by decide
  have hdescent : baseEnd_431932 < baseStart_431932 := by decide
  rcases family_descends (prefixWord ++ tailWord_431932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432005 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 4, 1, 4]
def baseStart_432005 : Nat := 118140960795 + 432005 * 2 ^ 59
def prefixEnd_432005 : Nat := 4983230072969 + 3 ^ 40 * 432005 * 2
def baseEnd_432005 : Nat := 221826210145687512150751

theorem tailTrace_432005 : CollatzResearch.WordTrace tailWord_432005 prefixEnd_432005 221826210145687512150751 := by
  unfold tailWord_432005
  simp only [CollatzResearch.WordTrace]
  refine ⟨15756516799927140425137469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10504344533284760283424979 15756516799927140425137469)
  ·
    refine ⟨5908693799972677659426551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15756516799927140425137469 5908693799972677659426551)
    ·
      refine ⟨8863040699959016489139827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5908693799972677659426551 8863040699959016489139827)
      ·
        refine ⟨13294561049938524733709741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8863040699959016489139827 13294561049938524733709741)
        ·
          refine ⟨4985460393726946775141153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13294561049938524733709741 4985460393726946775141153)
          ·
            refine ⟨3739095295295210081355865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4985460393726946775141153 3739095295295210081355865)
            ·
              refine ⟨2804321471471407561016899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3739095295295210081355865 2804321471471407561016899)
              ·
                refine ⟨4206482207207111341525349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2804321471471407561016899 4206482207207111341525349)
                ·
                  refine ⟨788715413851333376536003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4206482207207111341525349 788715413851333376536003)
                  ·
                    refine ⟨1183073120777000064804005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 788715413851333376536003 1183073120777000064804005)
                    ·
                      refine ⟨221826210145687512150751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1183073120777000064804005 221826210145687512150751)
                      ·
                        rfl

theorem cell23_432005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_432005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432005 prefixEnd_432005 := by exact prefixLift 432005
  have htrace : WordTrace (prefixWord ++ tailWord_432005) baseStart_432005 baseEnd_432005 := by
    simpa [prefixWord, tailWord_432005, baseEnd_432005] using wordTrace_append hprefix tailTrace_432005
  have hstable : (prefixWord ++ tailWord_432005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432005).length < 2 ^ (prefixWord ++ tailWord_432005).sum := by decide
  have hdescent : baseEnd_432005 < baseStart_432005 := by decide
  rcases family_descends (prefixWord ++ tailWord_432005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432025 : List Nat := [1, 2, 1, 2, 1, 3, 3, 2, 1, 4, 3]
def baseStart_432025 : Nat := 118140960795 + 432025 * 2 ^ 59
def prefixEnd_432025 : Nat := 4983230072969 + 3 ^ 40 * 432025 * 2
def baseEnd_432025 : Nat := 221836479758777433900659

theorem tailTrace_432025 : CollatzResearch.WordTrace tailWord_432025 prefixEnd_432025 221836479758777433900659 := by
  unfold tailWord_432025
  simp only [CollatzResearch.WordTrace]
  refine ⟨15757246259854683840865529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10504830839903122560577019 15757246259854683840865529)
  ·
    refine ⟨11817934694891012880649147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15757246259854683840865529 11817934694891012880649147)
    ·
      refine ⟨17726902042336519320973721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11817934694891012880649147 17726902042336519320973721)
      ·
        refine ⟨13295176531752389490730291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17726902042336519320973721 13295176531752389490730291)
        ·
          refine ⟨19942764797628584236095437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13295176531752389490730291 19942764797628584236095437)
          ·
            refine ⟨7478536799110719088535789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19942764797628584236095437 7478536799110719088535789)
            ·
              refine ⟨2804451299666519658200921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7478536799110719088535789 2804451299666519658200921)
              ·
                refine ⟨2103338474749889743650691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2804451299666519658200921 2103338474749889743650691)
                ·
                  refine ⟨3155007712124834615476037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2103338474749889743650691 3155007712124834615476037)
                  ·
                    refine ⟨591563946023406490401757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3155007712124834615476037 591563946023406490401757)
                    ·
                      refine ⟨221836479758777433900659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 591563946023406490401757 221836479758777433900659)
                      ·
                        rfl

theorem cell23_432025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 4, 3].length) (baseStart_432025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432025 prefixEnd_432025 := by exact prefixLift 432025
  have htrace : WordTrace (prefixWord ++ tailWord_432025) baseStart_432025 baseEnd_432025 := by
    simpa [prefixWord, tailWord_432025, baseEnd_432025] using wordTrace_append hprefix tailTrace_432025
  have hstable : (prefixWord ++ tailWord_432025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432025).length < 2 ^ (prefixWord ++ tailWord_432025).sum := by decide
  have hdescent : baseEnd_432025 < baseStart_432025 := by decide
  rcases family_descends (prefixWord ++ tailWord_432025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432075 : List Nat := [1, 1, 1, 1, 3, 4, 2, 2, 3, 5]
def baseStart_432075 : Nat := 118140960795 + 432075 * 2 ^ 59
def prefixEnd_432075 : Nat := 4983230072969 + 3 ^ 40 * 432075 * 2
def baseEnd_432075 : Nat := 73954051263834079425143

theorem tailTrace_432075 : CollatzResearch.WordTrace tailWord_432075 prefixEnd_432075 73954051263834079425143 := by
  unfold tailWord_432075
  simp only [CollatzResearch.WordTrace]
  refine ⟨15759069909673542380185679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10506046606449028253457119 15759069909673542380185679)
  ·
    refine ⟨23638604864510313570278519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15759069909673542380185679 23638604864510313570278519)
    ·
      refine ⟨35457907296765470355417779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23638604864510313570278519 35457907296765470355417779)
      ·
        refine ⟨53186860945148205533126669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35457907296765470355417779 53186860945148205533126669)
        ·
          refine ⟨19945072854430577074922501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53186860945148205533126669 19945072854430577074922501)
          ·
            refine ⟨3739701160205733201547969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19945072854430577074922501 3739701160205733201547969)
            ·
              refine ⟨2804775870154299901160977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3739701160205733201547969 2804775870154299901160977)
              ·
                refine ⟨2103581902615724925870733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2804775870154299901160977 2103581902615724925870733)
                ·
                  refine ⟨788843213480896847201525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2103581902615724925870733 788843213480896847201525)
                  ·
                    refine ⟨73954051263834079425143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 788843213480896847201525 73954051263834079425143)
                    ·
                      rfl

theorem cell23_432075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 5].length) (baseStart_432075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432075 prefixEnd_432075 := by exact prefixLift 432075
  have htrace : WordTrace (prefixWord ++ tailWord_432075) baseStart_432075 baseEnd_432075 := by
    simpa [prefixWord, tailWord_432075, baseEnd_432075] using wordTrace_append hprefix tailTrace_432075
  have hstable : (prefixWord ++ tailWord_432075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432075).length < 2 ^ (prefixWord ++ tailWord_432075).sum := by decide
  have hdescent : baseEnd_432075 < baseStart_432075 := by decide
  rcases family_descends (prefixWord ++ tailWord_432075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432099 : List Nat := [1, 1, 1, 6, 1, 2, 1, 3, 2, 3, 2]
def baseStart_432099 : Nat := 118140960795 + 432099 * 2 ^ 59
def prefixEnd_432099 : Nat := 4983230072969 + 3 ^ 40 * 432099 * 2
def baseEnd_432099 : Nat := 221874477327210144375319

theorem tailTrace_432099 : CollatzResearch.WordTrace tailWord_432099 prefixEnd_432099 221874477327210144375319 := by
  unfold tailWord_432099
  simp only [CollatzResearch.WordTrace]
  refine ⟨15759945261586594479059351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10506630174391062986039567 15759945261586594479059351)
  ·
    refine ⟨23639917892379891718589027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15759945261586594479059351 23639917892379891718589027)
    ·
      refine ⟨35459876838569837577883541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23639917892379891718589027 35459876838569837577883541)
      ·
        refine ⟨1662181726807961136463291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35459876838569837577883541 1662181726807961136463291)
        ·
          refine ⟨2493272590211941704694937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1662181726807961136463291 2493272590211941704694937)
          ·
            refine ⟨1869954442658956278521203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2493272590211941704694937 1869954442658956278521203)
            ·
              refine ⟨2804931663988434417781805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1869954442658956278521203 2804931663988434417781805)
              ·
                refine ⟨1051849373995662906668177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2804931663988434417781805 1051849373995662906668177)
                ·
                  refine ⟨788887030496747180001133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1051849373995662906668177 788887030496747180001133)
                  ·
                    refine ⟨295832636436280192500425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 788887030496747180001133 295832636436280192500425)
                    ·
                      refine ⟨221874477327210144375319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 295832636436280192500425 221874477327210144375319)
                      ·
                        rfl

theorem cell23_432099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_432099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432099 prefixEnd_432099 := by exact prefixLift 432099
  have htrace : WordTrace (prefixWord ++ tailWord_432099) baseStart_432099 baseEnd_432099 := by
    simpa [prefixWord, tailWord_432099, baseEnd_432099] using wordTrace_append hprefix tailTrace_432099
  have hstable : (prefixWord ++ tailWord_432099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432099).length < 2 ^ (prefixWord ++ tailWord_432099).sum := by decide
  have hdescent : baseEnd_432099 < baseStart_432099 := by decide
  rcases family_descends (prefixWord ++ tailWord_432099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432106 : List Nat := [3, 1, 3, 1, 2, 1, 2, 5, 1, 1, 3]
def baseStart_432106 : Nat := 118140960795 + 432106 * 2 ^ 59
def prefixEnd_432106 : Nat := 4983230072969 + 3 ^ 40 * 432106 * 2
def baseEnd_432106 : Nat := 221878071691791616987787

theorem tailTrace_432106 : CollatzResearch.WordTrace tailWord_432106 prefixEnd_432106 221878071691791616987787 := by
  unfold tailWord_432106
  simp only [CollatzResearch.WordTrace]
  refine ⟨3940050143140308668641043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10506800381707489783042781 3940050143140308668641043)
  ·
    refine ⟨5910075214710463002961565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3940050143140308668641043 5910075214710463002961565)
    ·
      refine ⟨2216278205516423626110587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5910075214710463002961565 2216278205516423626110587)
      ·
        refine ⟨3324417308274635439165881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2216278205516423626110587 3324417308274635439165881)
        ·
          refine ⟨2493312981205976579374411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3324417308274635439165881 2493312981205976579374411)
          ·
            refine ⟨3739969471808964869061617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2493312981205976579374411 3739969471808964869061617)
            ·
              refine ⟨2804977103856723651796213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3739969471808964869061617 2804977103856723651796213)
              ·
                refine ⟨262966603486567842355895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2804977103856723651796213 262966603486567842355895)
                ·
                  refine ⟨394449905229851763533843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262966603486567842355895 394449905229851763533843)
                  ·
                    refine ⟨591674857844777645300765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 394449905229851763533843 591674857844777645300765)
                    ·
                      refine ⟨221878071691791616987787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 591674857844777645300765 221878071691791616987787)
                      ·
                        rfl

theorem cell23_432106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_432106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432106 prefixEnd_432106 := by exact prefixLift 432106
  have htrace : WordTrace (prefixWord ++ tailWord_432106) baseStart_432106 baseEnd_432106 := by
    simpa [prefixWord, tailWord_432106, baseEnd_432106] using wordTrace_append hprefix tailTrace_432106
  have hstable : (prefixWord ++ tailWord_432106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432106).length < 2 ^ (prefixWord ++ tailWord_432106).sum := by decide
  have hdescent : baseEnd_432106 < baseStart_432106 := by decide
  rcases family_descends (prefixWord ++ tailWord_432106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432112 : List Nat := [2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 4]
def baseStart_432112 : Nat := 118140960795 + 432112 * 2 ^ 59
def prefixEnd_432112 : Nat := 4983230072969 + 3 ^ 40 * 432112 * 2
def baseEnd_432112 : Nat := 221881152575718593512759

theorem tailTrace_432112 : CollatzResearch.WordTrace tailWord_432112 prefixEnd_432112 221881152575718593512759 := by
  unfold tailWord_432112
  simp only [CollatzResearch.WordTrace]
  refine ⟨7880209705269748849641295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10506946273692998466188393 7880209705269748849641295)
  ·
    refine ⟨11820314557904623274461943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7880209705269748849641295 11820314557904623274461943)
    ·
      refine ⟨17730471836856934911692915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11820314557904623274461943 17730471836856934911692915)
      ·
        refine ⟨26595707755285402367539373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17730471836856934911692915 26595707755285402367539373)
        ·
          refine ⟨9973390408232025887827265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26595707755285402367539373 9973390408232025887827265)
          ·
            refine ⟨7480042806174019415870449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9973390408232025887827265 7480042806174019415870449)
            ·
              refine ⟨5610032104630514561902837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7480042806174019415870449 5610032104630514561902837)
              ·
                refine ⟨525940509809110740178391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5610032104630514561902837 525940509809110740178391)
                ·
                  refine ⟨788910764713666110267587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 525940509809110740178391 788910764713666110267587)
                  ·
                    refine ⟨1183366147070499165401381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 788910764713666110267587 1183366147070499165401381)
                    ·
                      refine ⟨221881152575718593512759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1183366147070499165401381 221881152575718593512759)
                      ·
                        rfl

theorem cell23_432112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 4].length) (baseStart_432112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432112 prefixEnd_432112 := by exact prefixLift 432112
  have htrace : WordTrace (prefixWord ++ tailWord_432112) baseStart_432112 baseEnd_432112 := by
    simpa [prefixWord, tailWord_432112, baseEnd_432112] using wordTrace_append hprefix tailTrace_432112
  have hstable : (prefixWord ++ tailWord_432112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432112).length < 2 ^ (prefixWord ++ tailWord_432112).sum := by decide
  have hdescent : baseEnd_432112 < baseStart_432112 := by decide
  rcases family_descends (prefixWord ++ tailWord_432112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432125 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 3, 1, 6]
def baseStart_432125 : Nat := 118140960795 + 432125 * 2 ^ 59
def prefixEnd_432125 : Nat := 4983230072969 + 3 ^ 40 * 432125 * 2
def baseEnd_432125 : Nat := 221887827824227042650199

theorem tailTrace_432125 : CollatzResearch.WordTrace tailWord_432125 prefixEnd_432125 221887827824227042650199 := by
  unfold tailWord_432125
  simp only [CollatzResearch.WordTrace]
  refine ⟨15760893559492400919505829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10507262372994933946337219 15760893559492400919505829)
  ·
    refine ⟨2955167542404825172407343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15760893559492400919505829 2955167542404825172407343)
    ·
      refine ⟨4432751313607237758611015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2955167542404825172407343 4432751313607237758611015)
      ·
        refine ⟨6649126970410856637916523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4432751313607237758611015 6649126970410856637916523)
        ·
          refine ⟨9973690455616284956874785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6649126970410856637916523 9973690455616284956874785)
          ·
            refine ⟨7480267841712213717656089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9973690455616284956874785 7480267841712213717656089)
            ·
              refine ⟨5610200881284160288242067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7480267841712213717656089 5610200881284160288242067)
              ·
                refine ⟨8415301321926240432363101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5610200881284160288242067 8415301321926240432363101)
                ·
                  refine ⟨3155737995722340162136163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8415301321926240432363101 3155737995722340162136163)
                  ·
                    refine ⟨4733606993583510243204245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3155737995722340162136163 4733606993583510243204245)
                    ·
                      refine ⟨221887827824227042650199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4733606993583510243204245 221887827824227042650199)
                      ·
                        rfl

theorem cell23_432125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_432125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432125 prefixEnd_432125 := by exact prefixLift 432125
  have htrace : WordTrace (prefixWord ++ tailWord_432125) baseStart_432125 baseEnd_432125 := by
    simpa [prefixWord, tailWord_432125, baseEnd_432125] using wordTrace_append hprefix tailTrace_432125
  have hstable : (prefixWord ++ tailWord_432125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432125).length < 2 ^ (prefixWord ++ tailWord_432125).sum := by decide
  have hdescent : baseEnd_432125 < baseStart_432125 := by decide
  rcases family_descends (prefixWord ++ tailWord_432125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432152 : List Nat := [2, 1, 2, 3, 2, 1, 5, 7]
def baseStart_432152 : Nat := 118140960795 + 432152 * 2 ^ 59
def prefixEnd_432152 : Nat := 4983230072969 + 3 ^ 40 * 432152 * 2
def baseEnd_432152 : Nat := 8218581177848090259725

theorem tailTrace_432152 : CollatzResearch.WordTrace tailWord_432152 prefixEnd_432152 8218581177848090259725 := by
  unfold tailWord_432152
  simp only [CollatzResearch.WordTrace]
  refine ⟨7880939165197292265369355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10507918886929723020492473 7880939165197292265369355)
  ·
    refine ⟨11821408747795938398054033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7880939165197292265369355 11821408747795938398054033)
    ·
      refine ⟨8866056560846953798540525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11821408747795938398054033 8866056560846953798540525)
      ·
        refine ⟨3324771210317607674452697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8866056560846953798540525 3324771210317607674452697)
        ·
          refine ⟨2493578407738205755839523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3324771210317607674452697 2493578407738205755839523)
          ·
            refine ⟨3740367611607308633759285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2493578407738205755839523 3740367611607308633759285)
            ·
              refine ⟨350659463588185184414933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3740367611607308633759285 350659463588185184414933)
              ·
                refine ⟨8218581177848090259725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 350659463588185184414933 8218581177848090259725)
                ·
                  rfl

theorem cell23_432152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 7].length) (baseStart_432152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432152 prefixEnd_432152 := by exact prefixLift 432152
  have htrace : WordTrace (prefixWord ++ tailWord_432152) baseStart_432152 baseEnd_432152 := by
    simpa [prefixWord, tailWord_432152, baseEnd_432152] using wordTrace_append hprefix tailTrace_432152
  have hstable : (prefixWord ++ tailWord_432152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432152).length < 2 ^ (prefixWord ++ tailWord_432152).sum := by decide
  have hdescent : baseEnd_432152 < baseStart_432152 := by decide
  rcases family_descends (prefixWord ++ tailWord_432152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432163 : List Nat := [1, 1, 1, 4, 3, 1, 4, 3, 1, 2, 2]
def baseStart_432163 : Nat := 118140960795 + 432163 * 2 ^ 59
def prefixEnd_432163 : Nat := 4983230072969 + 3 ^ 40 * 432163 * 2
def baseEnd_432163 : Nat := 221907340089097893975025

theorem tailTrace_432163 : CollatzResearch.WordTrace tailWord_432163 prefixEnd_432163 221907340089097893975025 := by
  unfold tailWord_432163
  simp only [CollatzResearch.WordTrace]
  refine ⟨15762279533354733409389143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10508186355569822272926095 15762279533354733409389143)
  ·
    refine ⟨23643419300032100114083715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15762279533354733409389143 23643419300032100114083715)
    ·
      refine ⟨35465128950048150171125573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23643419300032100114083715 35465128950048150171125573)
      ·
        refine ⟨6649711678134028157086045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35465128950048150171125573 6649711678134028157086045)
        ·
          refine ⟨2493641879300260558907267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6649711678134028157086045 2493641879300260558907267)
          ·
            refine ⟨3740462818950390838360901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2493641879300260558907267 3740462818950390838360901)
            ·
              refine ⟨701336778553198282192669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3740462818950390838360901 701336778553198282192669)
              ·
                refine ⟨263001291957449355822251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 701336778553198282192669 263001291957449355822251)
                ·
                  refine ⟨394501937936174033733377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 263001291957449355822251 394501937936174033733377)
                  ·
                    refine ⟨295876453452130525300033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 394501937936174033733377 295876453452130525300033)
                    ·
                      refine ⟨221907340089097893975025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 295876453452130525300033 221907340089097893975025)
                      ·
                        rfl

theorem cell23_432163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 3, 1, 2, 2].length) (baseStart_432163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432163 prefixEnd_432163 := by exact prefixLift 432163
  have htrace : WordTrace (prefixWord ++ tailWord_432163) baseStart_432163 baseEnd_432163 := by
    simpa [prefixWord, tailWord_432163, baseEnd_432163] using wordTrace_append hprefix tailTrace_432163
  have hstable : (prefixWord ++ tailWord_432163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432163).length < 2 ^ (prefixWord ++ tailWord_432163).sum := by decide
  have hdescent : baseEnd_432163 < baseStart_432163 := by decide
  rcases family_descends (prefixWord ++ tailWord_432163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432175 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 5]
def baseStart_432175 : Nat := 118140960795 + 432175 * 2 ^ 59
def prefixEnd_432175 : Nat := 4983230072969 + 3 ^ 40 * 432175 * 2
def baseEnd_432175 : Nat := 221913501856951847024969

theorem tailTrace_432175 : CollatzResearch.WordTrace tailWord_432175 prefixEnd_432175 221913501856951847024969 := by
  unfold tailWord_432175
  simp only [CollatzResearch.WordTrace]
  refine ⟨15762717209311259458825979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10508478139540839639217319 15762717209311259458825979)
  ·
    refine ⟨23644075813966889188238969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15762717209311259458825979 23644075813966889188238969)
    ·
      refine ⟨17733056860475166891179227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23644075813966889188238969 17733056860475166891179227)
      ·
        refine ⟨26599585290712750336768841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17733056860475166891179227 26599585290712750336768841)
        ·
          refine ⟨19949688968034562752576631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26599585290712750336768841 19949688968034562752576631)
          ·
            refine ⟨29924533452051844128864947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19949688968034562752576631 29924533452051844128864947)
            ·
              refine ⟨44886800178077766193297421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29924533452051844128864947 44886800178077766193297421)
              ·
                refine ⟨16832550066779162322486533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44886800178077766193297421 16832550066779162322486533)
                ·
                  refine ⟨3156103137521092935466225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16832550066779162322486533 3156103137521092935466225)
                  ·
                    refine ⟨2367077353140819701599669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3156103137521092935466225 2367077353140819701599669)
                    ·
                      refine ⟨221913501856951847024969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2367077353140819701599669 221913501856951847024969)
                      ·
                        rfl

theorem cell23_432175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 5].length) (baseStart_432175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432175 prefixEnd_432175 := by exact prefixLift 432175
  have htrace : WordTrace (prefixWord ++ tailWord_432175) baseStart_432175 baseEnd_432175 := by
    simpa [prefixWord, tailWord_432175, baseEnd_432175] using wordTrace_append hprefix tailTrace_432175
  have hstable : (prefixWord ++ tailWord_432175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432175).length < 2 ^ (prefixWord ++ tailWord_432175).sum := by decide
  have hdescent : baseEnd_432175 < baseStart_432175 := by decide
  rcases family_descends (prefixWord ++ tailWord_432175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432180 : List Nat := [2, 5, 1, 2, 2, 1, 2, 1, 3, 2, 2]
def baseStart_432180 : Nat := 118140960795 + 432180 * 2 ^ 59
def prefixEnd_432180 : Nat := 4983230072969 + 3 ^ 40 * 432180 * 2
def baseEnd_432180 : Nat := 221916069260224327462447

theorem tailTrace_432180 : CollatzResearch.WordTrace tailWord_432180 prefixEnd_432180 221916069260224327462447 := by
  unfold tailWord_432180
  simp only [CollatzResearch.WordTrace]
  refine ⟨7881449787146572656378997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10508599716195430208505329 7881449787146572656378997)
  ·
    refine ⟨738885917544991186535531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7881449787146572656378997 738885917544991186535531)
    ·
      refine ⟨1108328876317486779803297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 738885917544991186535531 1108328876317486779803297)
      ·
        refine ⟨831246657238115084852473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1108328876317486779803297 831246657238115084852473)
        ·
          refine ⟨623434992928586313639355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 831246657238115084852473 623434992928586313639355)
          ·
            refine ⟨935152489392879470459033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623434992928586313639355 935152489392879470459033)
            ·
              refine ⟨701364367044659602844275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 935152489392879470459033 701364367044659602844275)
              ·
                refine ⟨1052046550566989404266413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 701364367044659602844275 1052046550566989404266413)
                ·
                  refine ⟨394517456462621026599905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1052046550566989404266413 394517456462621026599905)
                  ·
                    refine ⟨295888092346965769949929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 394517456462621026599905 295888092346965769949929)
                    ·
                      refine ⟨221916069260224327462447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 295888092346965769949929 221916069260224327462447)
                      ·
                        rfl

theorem cell23_432180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_432180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432180 prefixEnd_432180 := by exact prefixLift 432180
  have htrace : WordTrace (prefixWord ++ tailWord_432180) baseStart_432180 baseEnd_432180 := by
    simpa [prefixWord, tailWord_432180, baseEnd_432180] using wordTrace_append hprefix tailTrace_432180
  have hstable : (prefixWord ++ tailWord_432180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432180).length < 2 ^ (prefixWord ++ tailWord_432180).sum := by decide
  have hdescent : baseEnd_432180 < baseStart_432180 := by decide
  rcases family_descends (prefixWord ++ tailWord_432180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432195 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 1, 8]
def baseStart_432195 : Nat := 118140960795 + 432195 * 2 ^ 59
def prefixEnd_432195 : Nat := 4983230072969 + 3 ^ 40 * 432195 * 2
def baseEnd_432195 : Nat := 73974590490013922924959

theorem tailTrace_432195 : CollatzResearch.WordTrace tailWord_432195 prefixEnd_432195 73974590490013922924959 := by
  unfold tailWord_432195
  simp only [CollatzResearch.WordTrace]
  refine ⟨15763446669238802874554039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10508964446159201916369359 15763446669238802874554039)
  ·
    refine ⟨23645170003858204311831059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15763446669238802874554039 23645170003858204311831059)
    ·
      refine ⟨35467755005787306467746589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23645170003858204311831059 35467755005787306467746589)
      ·
        refine ⟨13300408127170239925404971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35467755005787306467746589 13300408127170239925404971)
        ·
          refine ⟨19950612190755359888107457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13300408127170239925404971 19950612190755359888107457)
          ·
            refine ⟨14962959143066519916080593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19950612190755359888107457 14962959143066519916080593)
            ·
              refine ⟨11222219357299889937060445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14962959143066519916080593 11222219357299889937060445)
              ·
                refine ⟨4208332258987458726397667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11222219357299889937060445 4208332258987458726397667)
                ·
                  refine ⟨6312498388481188089596501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4208332258987458726397667 6312498388481188089596501)
                  ·
                    refine ⟨73974590490013922924959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6312498388481188089596501 73974590490013922924959)
                    ·
                      rfl

theorem cell23_432195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 8].length) (baseStart_432195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432195 prefixEnd_432195 := by exact prefixLift 432195
  have htrace : WordTrace (prefixWord ++ tailWord_432195) baseStart_432195 baseEnd_432195 := by
    simpa [prefixWord, tailWord_432195, baseEnd_432195] using wordTrace_append hprefix tailTrace_432195
  have hstable : (prefixWord ++ tailWord_432195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432195).length < 2 ^ (prefixWord ++ tailWord_432195).sum := by decide
  have hdescent : baseEnd_432195 < baseStart_432195 := by decide
  rcases family_descends (prefixWord ++ tailWord_432195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432206 : List Nat := [4, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2]
def baseStart_432206 : Nat := 118140960795 + 432206 * 2 ^ 59
def prefixEnd_432206 : Nat := 4983230072969 + 3 ^ 40 * 432206 * 2
def baseEnd_432206 : Nat := 221929419757241225737327

theorem tailTrace_432206 : CollatzResearch.WordTrace tailWord_432206 prefixEnd_432206 221929419757241225737327 := by
  unfold tailWord_432206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1970480984024868969150559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10509231914799301168802981 1970480984024868969150559)
  ·
    refine ⟨2955721476037303453725839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1970480984024868969150559 2955721476037303453725839)
    ·
      refine ⟨4433582214055955180588759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2955721476037303453725839 4433582214055955180588759)
      ·
        refine ⟨6650373321083932770883139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4433582214055955180588759 6650373321083932770883139)
        ·
          refine ⟨9975559981625899156324709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6650373321083932770883139 9975559981625899156324709)
          ·
            refine ⟨1870417496554856091810883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9975559981625899156324709 1870417496554856091810883)
            ·
              refine ⟨2805626244832284137716325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1870417496554856091810883 2805626244832284137716325)
              ·
                refine ⟨526054920906053275821811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2805626244832284137716325 526054920906053275821811)
                ·
                  refine ⟨789082381359079913732717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 526054920906053275821811 789082381359079913732717)
                  ·
                    refine ⟨295905893009654967649769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 789082381359079913732717 295905893009654967649769)
                    ·
                      refine ⟨221929419757241225737327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 295905893009654967649769 221929419757241225737327)
                      ·
                        rfl

theorem cell23_432206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2].length) (baseStart_432206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432206 prefixEnd_432206 := by exact prefixLift 432206
  have htrace : WordTrace (prefixWord ++ tailWord_432206) baseStart_432206 baseEnd_432206 := by
    simpa [prefixWord, tailWord_432206, baseEnd_432206] using wordTrace_append hprefix tailTrace_432206
  have hstable : (prefixWord ++ tailWord_432206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432206).length < 2 ^ (prefixWord ++ tailWord_432206).sum := by decide
  have hdescent : baseEnd_432206 < baseStart_432206 := by decide
  rcases family_descends (prefixWord ++ tailWord_432206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432214 : List Nat := [5, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2]
def baseStart_432214 : Nat := 118140960795 + 432214 * 2 ^ 59
def prefixEnd_432214 : Nat := 4983230072969 + 3 ^ 40 * 432214 * 2
def baseEnd_432214 : Nat := 221933527602477194437291

theorem tailTrace_432214 : CollatzResearch.WordTrace tailWord_432214 prefixEnd_432214 221933527602477194437291 := by
  unfold tailWord_432214
  simp only [CollatzResearch.WordTrace]
  refine ⟨985258728510623069968481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10509426437446646079663797 985258728510623069968481)
  ·
    refine ⟨738944046382967302476361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 985258728510623069968481 738944046382967302476361)
    ·
      refine ⟨554208034787225476857271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 738944046382967302476361 554208034787225476857271)
      ·
        refine ⟨831312052180838215285907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554208034787225476857271 831312052180838215285907)
        ·
          refine ⟨1246968078271257322928861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 831312052180838215285907 1246968078271257322928861)
          ·
            refine ⟨467613029351721496098323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1246968078271257322928861 467613029351721496098323)
            ·
              refine ⟨701419544027582244147485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467613029351721496098323 701419544027582244147485)
              ·
                refine ⟨263032329010343341555307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 701419544027582244147485 263032329010343341555307)
                ·
                  refine ⟨394548493515515012332961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 263032329010343341555307 394548493515515012332961)
                  ·
                    refine ⟨295911370136636259249721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 394548493515515012332961 295911370136636259249721)
                    ·
                      refine ⟨221933527602477194437291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 295911370136636259249721 221933527602477194437291)
                      ·
                        rfl

theorem cell23_432214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_432214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432214 prefixEnd_432214 := by exact prefixLift 432214
  have htrace : WordTrace (prefixWord ++ tailWord_432214) baseStart_432214 baseEnd_432214 := by
    simpa [prefixWord, tailWord_432214, baseEnd_432214] using wordTrace_append hprefix tailTrace_432214
  have hstable : (prefixWord ++ tailWord_432214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432214).length < 2 ^ (prefixWord ++ tailWord_432214).sum := by decide
  have hdescent : baseEnd_432214 < baseStart_432214 := by decide
  rcases family_descends (prefixWord ++ tailWord_432214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432236 : List Nat := [2, 2, 1, 1, 3, 3, 2, 1, 4, 2, 2]
def baseStart_432236 : Nat := 118140960795 + 432236 * 2 ^ 59
def prefixEnd_432236 : Nat := 4983230072969 + 3 ^ 40 * 432236 * 2
def baseEnd_432236 : Nat := 221944824176876108362189

theorem tailTrace_432236 : CollatzResearch.WordTrace tailWord_432236 prefixEnd_432236 221944824176876108362189 := by
  unfold tailWord_432236
  simp only [CollatzResearch.WordTrace]
  refine ⟨7882471031045133438398281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10509961374726844584531041 7882471031045133438398281)
  ·
    refine ⟨5911853273283850078798711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7882471031045133438398281 5911853273283850078798711)
    ·
      refine ⟨8867779909925775118198067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5911853273283850078798711 8867779909925775118198067)
      ·
        refine ⟨13301669864888662677297101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8867779909925775118198067 13301669864888662677297101)
        ·
          refine ⟨4988126199333248503986413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13301669864888662677297101 4988126199333248503986413)
          ·
            refine ⟨1870547324749968188994905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4988126199333248503986413 1870547324749968188994905)
            ·
              refine ⟨1402910493562476141746179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1870547324749968188994905 1402910493562476141746179)
              ·
                refine ⟨2104365740343714212619269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1402910493562476141746179 2104365740343714212619269)
                ·
                  refine ⟨394568576314446414866113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2104365740343714212619269 394568576314446414866113)
                  ·
                    refine ⟨295926432235834811149585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 394568576314446414866113 295926432235834811149585)
                    ·
                      refine ⟨221944824176876108362189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 295926432235834811149585 221944824176876108362189)
                      ·
                        rfl

theorem cell23_432236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 2, 2].length) (baseStart_432236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432236 prefixEnd_432236 := by exact prefixLift 432236
  have htrace : WordTrace (prefixWord ++ tailWord_432236) baseStart_432236 baseEnd_432236 := by
    simpa [prefixWord, tailWord_432236, baseEnd_432236] using wordTrace_append hprefix tailTrace_432236
  have hstable : (prefixWord ++ tailWord_432236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432236).length < 2 ^ (prefixWord ++ tailWord_432236).sum := by decide
  have hdescent : baseEnd_432236 < baseStart_432236 := by decide
  rcases family_descends (prefixWord ++ tailWord_432236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432253 : List Nat := [1, 4, 1, 1, 3, 3, 1, 3, 2, 2, 2]
def baseStart_432253 : Nat := 118140960795 + 432253 * 2 ^ 59
def prefixEnd_432253 : Nat := 4983230072969 + 3 ^ 40 * 432253 * 2
def baseEnd_432253 : Nat := 221953553348002541849611

theorem tailTrace_432253 : CollatzResearch.WordTrace tailWord_432253 prefixEnd_432253 221953553348002541849611 := by
  unfold tailWord_432253
  simp only [CollatzResearch.WordTrace]
  refine ⟨15765562103028678780165413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10510374735352452520110275 15765562103028678780165413)
  ·
    refine ⟨2956042894317877271281015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15765562103028678780165413 2956042894317877271281015)
    ·
      refine ⟨4434064341476815906921523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2956042894317877271281015 4434064341476815906921523)
      ·
        refine ⟨6651096512215223860382285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4434064341476815906921523 6651096512215223860382285)
        ·
          refine ⟨2494161192080708947643357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6651096512215223860382285 2494161192080708947643357)
          ·
            refine ⟨935310447030265855366259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2494161192080708947643357 935310447030265855366259)
            ·
              refine ⟨1402965670545398783049389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 935310447030265855366259 1402965670545398783049389)
              ·
                refine ⟨526112126454524543643521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1402965670545398783049389 526112126454524543643521)
                ·
                  refine ⟨394584094840893407732641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 526112126454524543643521 394584094840893407732641)
                  ·
                    refine ⟨295938071130670055799481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 394584094840893407732641 295938071130670055799481)
                    ·
                      refine ⟨221953553348002541849611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 295938071130670055799481 221953553348002541849611)
                      ·
                        rfl

theorem cell23_432253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 2, 2, 2].length) (baseStart_432253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432253 prefixEnd_432253 := by exact prefixLift 432253
  have htrace : WordTrace (prefixWord ++ tailWord_432253) baseStart_432253 baseEnd_432253 := by
    simpa [prefixWord, tailWord_432253, baseEnd_432253] using wordTrace_append hprefix tailTrace_432253
  have hstable : (prefixWord ++ tailWord_432253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432253).length < 2 ^ (prefixWord ++ tailWord_432253).sum := by decide
  have hdescent : baseEnd_432253 < baseStart_432253 := by decide
  rcases family_descends (prefixWord ++ tailWord_432253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432289 : List Nat := [1, 2, 3, 3, 1, 2, 2, 2, 2, 5]
def baseStart_432289 : Nat := 118140960795 + 432289 * 2 ^ 59
def prefixEnd_432289 : Nat := 4983230072969 + 3 ^ 40 * 432289 * 2
def baseEnd_432289 : Nat := 73990679550521466999815

theorem tailTrace_432289 : CollatzResearch.WordTrace tailWord_432289 prefixEnd_432289 73990679550521466999815 := by
  unfold tailWord_432289
  simp only [CollatzResearch.WordTrace]
  refine ⟨15766875130898256928475921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10511250087265504618983947 15766875130898256928475921)
  ·
    refine ⟨11825156348173692696356941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15766875130898256928475921 11825156348173692696356941)
    ·
      refine ⟨4434433630565134761133853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11825156348173692696356941 4434433630565134761133853)
      ·
        refine ⟨1662912611461925535425195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4434433630565134761133853 1662912611461925535425195)
        ·
          refine ⟨2494368917192888303137793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1662912611461925535425195 2494368917192888303137793)
          ·
            refine ⟨1870776687894666227353345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2494368917192888303137793 1870776687894666227353345)
            ·
              refine ⟨1403082515920999670515009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1870776687894666227353345 1403082515920999670515009)
              ·
                refine ⟨1052311886940749752886257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1403082515920999670515009 1052311886940749752886257)
                ·
                  refine ⟨789233915205562314664693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1052311886940749752886257 789233915205562314664693)
                  ·
                    refine ⟨73990679550521466999815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 789233915205562314664693 73990679550521466999815)
                    ·
                      rfl

theorem cell23_432289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_432289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432289 prefixEnd_432289 := by exact prefixLift 432289
  have htrace : WordTrace (prefixWord ++ tailWord_432289) baseStart_432289 baseEnd_432289 := by
    simpa [prefixWord, tailWord_432289, baseEnd_432289] using wordTrace_append hprefix tailTrace_432289
  have hstable : (prefixWord ++ tailWord_432289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432289).length < 2 ^ (prefixWord ++ tailWord_432289).sum := by decide
  have hdescent : baseEnd_432289 < baseStart_432289 := by decide
  rcases family_descends (prefixWord ++ tailWord_432289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432329 : List Nat := [1, 2, 1, 1, 2, 1, 1, 7, 2, 2, 3]
def baseStart_432329 : Nat := 118140960795 + 432329 * 2 ^ 59
def prefixEnd_432329 : Nat := 4983230072969 + 3 ^ 40 * 432329 * 2
def baseEnd_432329 : Nat := 221992577877744244499261

theorem tailTrace_432329 : CollatzResearch.WordTrace tailWord_432329 prefixEnd_432329 221992577877744244499261 := by
  unfold tailWord_432329
  simp only [CollatzResearch.WordTrace]
  refine ⟨15768334050753343759932041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10512222700502229173288027 15768334050753343759932041)
  ·
    refine ⟨11826250538065007819949031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15768334050753343759932041 11826250538065007819949031)
    ·
      refine ⟨17739375807097511729923547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11826250538065007819949031 17739375807097511729923547)
      ·
        refine ⟨26609063710646267594885321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17739375807097511729923547 26609063710646267594885321)
        ·
          refine ⟨19956797782984700696163991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26609063710646267594885321 19956797782984700696163991)
          ·
            refine ⟨29935196674477051044245987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19956797782984700696163991 29935196674477051044245987)
            ·
              refine ⟨44902795011715576566368981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29935196674477051044245987 44902795011715576566368981)
              ·
                refine ⟨1052409258087083825774273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 44902795011715576566368981 1052409258087083825774273)
                ·
                  refine ⟨789306943565312869330705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1052409258087083825774273 789306943565312869330705)
                  ·
                    refine ⟨591980207673984651998029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 789306943565312869330705 591980207673984651998029)
                    ·
                      refine ⟨221992577877744244499261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 591980207673984651998029 221992577877744244499261)
                      ·
                        rfl

theorem cell23_432329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 2, 3].length) (baseStart_432329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432329 prefixEnd_432329 := by exact prefixLift 432329
  have htrace : WordTrace (prefixWord ++ tailWord_432329) baseStart_432329 baseEnd_432329 := by
    simpa [prefixWord, tailWord_432329, baseEnd_432329] using wordTrace_append hprefix tailTrace_432329
  have hstable : (prefixWord ++ tailWord_432329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432329).length < 2 ^ (prefixWord ++ tailWord_432329).sum := by decide
  have hdescent : baseEnd_432329 < baseStart_432329 := by decide
  rcases family_descends (prefixWord ++ tailWord_432329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432352 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 8]
def baseStart_432352 : Nat := 118140960795 + 432352 * 2 ^ 59
def prefixEnd_432352 : Nat := 4983230072969 + 3 ^ 40 * 432352 * 2
def baseEnd_432352 : Nat := 222004387932797654511655

theorem tailTrace_432352 : CollatzResearch.WordTrace tailWord_432352 prefixEnd_432352 222004387932797654511655 := by
  unfold tailWord_432352
  simp only [CollatzResearch.WordTrace]
  refine ⟨7884586464835009344009655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10512781953113345792012873 7884586464835009344009655)
  ·
    refine ⟨11826879697252514016014483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7884586464835009344009655 11826879697252514016014483)
    ·
      refine ⟨17740319545878771024021725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11826879697252514016014483 17740319545878771024021725)
      ·
        refine ⟨6652619829704539134008147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17740319545878771024021725 6652619829704539134008147)
        ·
          refine ⟨9978929744556808701012221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6652619829704539134008147 9978929744556808701012221)
          ·
            refine ⟨3742098654208803262879583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9978929744556808701012221 3742098654208803262879583)
            ·
              refine ⟨5613147981313204894319375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3742098654208803262879583 5613147981313204894319375)
              ·
                refine ⟨8419721971969807341479063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5613147981313204894319375 8419721971969807341479063)
                ·
                  refine ⟨12629582957954711012218595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8419721971969807341479063 12629582957954711012218595)
                  ·
                    refine ⟨18944374436932066518327893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12629582957954711012218595 18944374436932066518327893)
                    ·
                      refine ⟨222004387932797654511655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 18944374436932066518327893 222004387932797654511655)
                      ·
                        rfl

theorem cell23_432352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_432352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432352 prefixEnd_432352 := by exact prefixLift 432352
  have htrace : WordTrace (prefixWord ++ tailWord_432352) baseStart_432352 baseEnd_432352 := by
    simpa [prefixWord, tailWord_432352, baseEnd_432352] using wordTrace_append hprefix tailTrace_432352
  have hstable : (prefixWord ++ tailWord_432352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432352).length < 2 ^ (prefixWord ++ tailWord_432352).sum := by decide
  have hdescent : baseEnd_432352 < baseStart_432352 := by decide
  rcases family_descends (prefixWord ++ tailWord_432352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432410 : List Nat := [3, 1, 1, 3, 4, 2, 1, 1, 3, 1, 3]
def baseStart_432410 : Nat := 118140960795 + 432410 * 2 ^ 59
def prefixEnd_432410 : Nat := 4983230072969 + 3 ^ 40 * 432410 * 2
def baseEnd_432410 : Nat := 222034169810758427586389

theorem tailTrace_432410 : CollatzResearch.WordTrace tailWord_432410 prefixEnd_432410 222034169810758427586389 := by
  unfold tailWord_432410
  simp only [CollatzResearch.WordTrace]
  refine ⟨3942822090864973648407671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10514192242306596395753789 3942822090864973648407671)
  ·
    refine ⟨5914233136297460472611507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3942822090864973648407671 5914233136297460472611507)
    ·
      refine ⟨8871349704446190708917261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5914233136297460472611507 8871349704446190708917261)
      ·
        refine ⟨3326756139167321515843973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8871349704446190708917261 3326756139167321515843973)
        ·
          refine ⟨623766776093872784220745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3326756139167321515843973 623766776093872784220745)
          ·
            refine ⟨467825082070404588165559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 623766776093872784220745 467825082070404588165559)
            ·
              refine ⟨701737623105606882248339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467825082070404588165559 701737623105606882248339)
              ·
                refine ⟨1052606434658410323372509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 701737623105606882248339 1052606434658410323372509)
                ·
                  refine ⟨394727412996903871264691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1052606434658410323372509 394727412996903871264691)
                  ·
                    refine ⟨592091119495355806897037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 394727412996903871264691 592091119495355806897037)
                    ·
                      refine ⟨222034169810758427586389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 592091119495355806897037 222034169810758427586389)
                      ·
                        rfl

theorem cell23_432410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_432410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432410 prefixEnd_432410 := by exact prefixLift 432410
  have htrace : WordTrace (prefixWord ++ tailWord_432410) baseStart_432410 baseEnd_432410 := by
    simpa [prefixWord, tailWord_432410, baseEnd_432410] using wordTrace_append hprefix tailTrace_432410
  have hstable : (prefixWord ++ tailWord_432410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432410).length < 2 ^ (prefixWord ++ tailWord_432410).sum := by decide
  have hdescent : baseEnd_432410 < baseStart_432410 := by decide
  rcases family_descends (prefixWord ++ tailWord_432410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432419 : List Nat := [1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 5]
def baseStart_432419 : Nat := 118140960795 + 432419 * 2 ^ 59
def prefixEnd_432419 : Nat := 4983230072969 + 3 ^ 40 * 432419 * 2
def baseEnd_432419 : Nat := 222038791136648892373847

theorem tailTrace_432419 : CollatzResearch.WordTrace tailWord_432419 prefixEnd_432419 222038791136648892373847 := by
  unfold tailWord_432419
  simp only [CollatzResearch.WordTrace]
  refine ⟨15771616620427289130708311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10514411080284859420472207 15771616620427289130708311)
  ·
    refine ⟨23657424930640933696062467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15771616620427289130708311 23657424930640933696062467)
    ·
      refine ⟨35486137395961400544093701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23657424930640933696062467 35486137395961400544093701)
      ·
        refine ⟨6653650761742762602017569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35486137395961400544093701 6653650761742762602017569)
        ·
          refine ⟨4990238071307071951513177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6653650761742762602017569 4990238071307071951513177)
          ·
            refine ⟨3742678553480303963634883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4990238071307071951513177 3742678553480303963634883)
            ·
              refine ⟨5614017830220455945452325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3742678553480303963634883 5614017830220455945452325)
              ·
                refine ⟨1052628343166335489772311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5614017830220455945452325 1052628343166335489772311)
                ·
                  refine ⟨1578942514749503234658467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1052628343166335489772311 1578942514749503234658467)
                  ·
                    refine ⟨2368413772124254851987701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1578942514749503234658467 2368413772124254851987701)
                    ·
                      refine ⟨222038791136648892373847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2368413772124254851987701 222038791136648892373847)
                      ·
                        rfl

theorem cell23_432419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_432419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432419 prefixEnd_432419 := by exact prefixLift 432419
  have htrace : WordTrace (prefixWord ++ tailWord_432419) baseStart_432419 baseEnd_432419 := by
    simpa [prefixWord, tailWord_432419, baseEnd_432419] using wordTrace_append hprefix tailTrace_432419
  have hstable : (prefixWord ++ tailWord_432419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432419).length < 2 ^ (prefixWord ++ tailWord_432419).sum := by decide
  have hdescent : baseEnd_432419 < baseStart_432419 := by decide
  rcases family_descends (prefixWord ++ tailWord_432419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432446 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 3, 2, 4]
def baseStart_432446 : Nat := 118140960795 + 432446 * 2 ^ 59
def prefixEnd_432446 : Nat := 4983230072969 + 3 ^ 40 * 432446 * 2
def baseEnd_432446 : Nat := 222052655114320286736223

theorem tailTrace_432446 : CollatzResearch.WordTrace tailWord_432446 prefixEnd_432446 222052655114320286736223 := by
  unfold tailWord_432446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1971575173916184092742649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10515067594219648494627461 1971575173916184092742649)
  ·
    refine ⟨1478681380437138069556987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1971575173916184092742649 1478681380437138069556987)
    ·
      refine ⟨2218022070655707104335481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1478681380437138069556987 2218022070655707104335481)
      ·
        refine ⟨1663516552991780328251611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2218022070655707104335481 1663516552991780328251611)
        ·
          refine ⟨2495274829487670492377417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1663516552991780328251611 2495274829487670492377417)
          ·
            refine ⟨1871456122115752869283063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2495274829487670492377417 1871456122115752869283063)
            ·
              refine ⟨2807184183173629303924595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1871456122115752869283063 2807184183173629303924595)
              ·
                refine ⟨4210776274760443955886893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2807184183173629303924595 4210776274760443955886893)
                ·
                  refine ⟨1579041103035166483457585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4210776274760443955886893 1579041103035166483457585)
                  ·
                    refine ⟨1184280827276374862593189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1579041103035166483457585 1184280827276374862593189)
                    ·
                      refine ⟨222052655114320286736223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1184280827276374862593189 222052655114320286736223)
                      ·
                        rfl

theorem cell23_432446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_432446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432446 prefixEnd_432446 := by exact prefixLift 432446
  have htrace : WordTrace (prefixWord ++ tailWord_432446) baseStart_432446 baseEnd_432446 := by
    simpa [prefixWord, tailWord_432446, baseEnd_432446] using wordTrace_append hprefix tailTrace_432446
  have hstable : (prefixWord ++ tailWord_432446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432446).length < 2 ^ (prefixWord ++ tailWord_432446).sum := by decide
  have hdescent : baseEnd_432446 < baseStart_432446 := by decide
  rcases family_descends (prefixWord ++ tailWord_432446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432483 : List Nat := [1, 1, 1, 5, 2, 1, 1, 5, 2, 1, 3]
def baseStart_432483 : Nat := 118140960795 + 432483 * 2 ^ 59
def prefixEnd_432483 : Nat := 4983230072969 + 3 ^ 40 * 432483 * 2
def baseEnd_432483 : Nat := 222071653898536641973553

theorem tailTrace_432483 : CollatzResearch.WordTrace tailWord_432483 prefixEnd_432483 222071653898536641973553 := by
  unfold tailWord_432483
  simp only [CollatzResearch.WordTrace]
  refine ⟨15773950892195428061038103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10515967261463618707358735 15773950892195428061038103)
  ·
    refine ⟨23660926338293142091557155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15773950892195428061038103 23660926338293142091557155)
    ·
      refine ⟨35491389507439713137335733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23660926338293142091557155 35491389507439713137335733)
      ·
        refine ⟨3327317766322473106625225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35491389507439713137335733 3327317766322473106625225)
        ·
          refine ⟨2495488324741854829968919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3327317766322473106625225 2495488324741854829968919)
          ·
            refine ⟨3743232487112782244953379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2495488324741854829968919 3743232487112782244953379)
            ·
              refine ⟨5614848730669173367430069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3743232487112782244953379 5614848730669173367430069)
              ·
                refine ⟨526392068500235003196569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5614848730669173367430069 526392068500235003196569)
                ·
                  refine ⟨394794051375176252397427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 526392068500235003196569 394794051375176252397427)
                  ·
                    refine ⟨592191077062764378596141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 394794051375176252397427 592191077062764378596141)
                    ·
                      refine ⟨222071653898536641973553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 592191077062764378596141 222071653898536641973553)
                      ·
                        rfl

theorem cell23_432483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_432483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432483 prefixEnd_432483 := by exact prefixLift 432483
  have htrace : WordTrace (prefixWord ++ tailWord_432483) baseStart_432483 baseEnd_432483 := by
    simpa [prefixWord, tailWord_432483, baseEnd_432483] using wordTrace_append hprefix tailTrace_432483
  have hstable : (prefixWord ++ tailWord_432483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432483).length < 2 ^ (prefixWord ++ tailWord_432483).sum := by decide
  have hdescent : baseEnd_432483 < baseStart_432483 := by decide
  rcases family_descends (prefixWord ++ tailWord_432483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432489 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 2, 3, 4]
def baseStart_432489 : Nat := 118140960795 + 432489 * 2 ^ 59
def prefixEnd_432489 : Nat := 4983230072969 + 3 ^ 40 * 432489 * 2
def baseEnd_432489 : Nat := 222074734782463618498525

theorem tailTrace_432489 : CollatzResearch.WordTrace tailWord_432489 prefixEnd_432489 222074734782463618498525 := by
  unfold tailWord_432489
  simp only [CollatzResearch.WordTrace]
  refine ⟨15774169730173691085756521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10516113153449127390504347 15774169730173691085756521)
  ·
    refine ⟨11830627297630268314317391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15774169730173691085756521 11830627297630268314317391)
    ·
      refine ⟨17745940946445402471476087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11830627297630268314317391 17745940946445402471476087)
      ·
        refine ⟨26618911419668103707214131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17745940946445402471476087 26618911419668103707214131)
        ·
          refine ⟨39928367129502155560821197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26618911419668103707214131 39928367129502155560821197)
          ·
            refine ⟨14973137673563308335307949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39928367129502155560821197 14973137673563308335307949)
            ·
              refine ⟨5614926627586240625740481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14973137673563308335307949 5614926627586240625740481)
              ·
                refine ⟨4211194970689680469305361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5614926627586240625740481 4211194970689680469305361)
                ·
                  refine ⟨3158396228017260351979021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4211194970689680469305361 3158396228017260351979021)
                  ·
                    refine ⟨1184398585506472631992133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3158396228017260351979021 1184398585506472631992133)
                    ·
                      refine ⟨222074734782463618498525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1184398585506472631992133 222074734782463618498525)
                      ·
                        rfl

theorem cell23_432489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 3, 4].length) (baseStart_432489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432489 prefixEnd_432489 := by exact prefixLift 432489
  have htrace : WordTrace (prefixWord ++ tailWord_432489) baseStart_432489 baseEnd_432489 := by
    simpa [prefixWord, tailWord_432489, baseEnd_432489] using wordTrace_append hprefix tailTrace_432489
  have hstable : (prefixWord ++ tailWord_432489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432489).length < 2 ^ (prefixWord ++ tailWord_432489).sum := by decide
  have hdescent : baseEnd_432489 < baseStart_432489 := by decide
  rcases family_descends (prefixWord ++ tailWord_432489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432493 : List Nat := [1, 5, 1, 1, 1, 2, 1, 3, 3, 3, 2]
def baseStart_432493 : Nat := 118140960795 + 432493 * 2 ^ 59
def prefixEnd_432493 : Nat := 4983230072969 + 3 ^ 40 * 432493 * 2
def baseEnd_432493 : Nat := 222076788705081602848507

theorem tailTrace_432493 : CollatzResearch.WordTrace tailWord_432493 prefixEnd_432493 222076788705081602848507 := by
  unfold tailWord_432493
  simp only [CollatzResearch.WordTrace]
  refine ⟨15774315622159199768902133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10516210414772799845934755 15774315622159199768902133)
  ·
    refine ⟨1478842089577424978334575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15774315622159199768902133 1478842089577424978334575)
    ·
      refine ⟨2218263134366137467501863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1478842089577424978334575 2218263134366137467501863)
      ·
        refine ⟨3327394701549206201252795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2218263134366137467501863 3327394701549206201252795)
        ·
          refine ⟨4991092052323809301879193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3327394701549206201252795 4991092052323809301879193)
          ·
            refine ⟨3743319039242856976409395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4991092052323809301879193 3743319039242856976409395)
            ·
              refine ⟨5614978558864285464614093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3743319039242856976409395 5614978558864285464614093)
              ·
                refine ⟨2105616959574107049230285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5614978558864285464614093 2105616959574107049230285)
                ·
                  refine ⟨789606359840290143461357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2105616959574107049230285 789606359840290143461357)
                  ·
                    refine ⟨296102384940108803798009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 789606359840290143461357 296102384940108803798009)
                    ·
                      refine ⟨222076788705081602848507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 296102384940108803798009 222076788705081602848507)
                      ·
                        rfl

theorem cell23_432493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_432493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432493 prefixEnd_432493 := by exact prefixLift 432493
  have htrace : WordTrace (prefixWord ++ tailWord_432493) baseStart_432493 baseEnd_432493 := by
    simpa [prefixWord, tailWord_432493, baseEnd_432493] using wordTrace_append hprefix tailTrace_432493
  have hstable : (prefixWord ++ tailWord_432493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432493).length < 2 ^ (prefixWord ++ tailWord_432493).sum := by decide
  have hdescent : baseEnd_432493 < baseStart_432493 := by decide
  rcases family_descends (prefixWord ++ tailWord_432493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432546 : List Nat := [3, 3, 1, 2, 1, 1, 1, 4, 7]
def baseStart_432546 : Nat := 118140960795 + 432546 * 2 ^ 59
def prefixEnd_432546 : Nat := 4983230072969 + 3 ^ 40 * 432546 * 2
def baseEnd_432546 : Nat := 24678222575529988387307

theorem tailTrace_432546 : CollatzResearch.WordTrace tailWord_432546 prefixEnd_432546 24678222575529988387307 := by
  unfold tailWord_432546
  simp only [CollatzResearch.WordTrace]
  refine ⟨3944062172741797455145373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10517499127311459880387661 3944062172741797455145373)
  ·
    refine ⟨1479023314778174045679515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3944062172741797455145373 1479023314778174045679515)
    ·
      refine ⟨2218534972167261068519273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1479023314778174045679515 2218534972167261068519273)
      ·
        refine ⟨1663901229125445801389455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2218534972167261068519273 1663901229125445801389455)
        ·
          refine ⟨2495851843688168702084183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1663901229125445801389455 2495851843688168702084183)
          ·
            refine ⟨3743777765532253053126275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2495851843688168702084183 3743777765532253053126275)
            ·
              refine ⟨5615666648298379579689413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3743777765532253053126275 5615666648298379579689413)
              ·
                refine ⟨1052937496555946171191765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5615666648298379579689413 1052937496555946171191765)
                ·
                  refine ⟨24678222575529988387307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1052937496555946171191765 24678222575529988387307)
                  ·
                    rfl

theorem cell23_432546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_432546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432546 prefixEnd_432546 := by exact prefixLift 432546
  have htrace : WordTrace (prefixWord ++ tailWord_432546) baseStart_432546 baseEnd_432546 := by
    simpa [prefixWord, tailWord_432546, baseEnd_432546] using wordTrace_append hprefix tailTrace_432546
  have hstable : (prefixWord ++ tailWord_432546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432546).length < 2 ^ (prefixWord ++ tailWord_432546).sum := by decide
  have hdescent : baseEnd_432546 < baseStart_432546 := by decide
  rcases family_descends (prefixWord ++ tailWord_432546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432580 : List Nat := [2, 3, 3, 2, 2, 2, 1, 1, 7]
def baseStart_432580 : Nat := 118140960795 + 432580 * 2 ^ 59
def prefixEnd_432580 : Nat := 4983230072969 + 3 ^ 40 * 432580 * 2
def baseEnd_432580 : Nat := 24680162391335862495623

theorem tailTrace_432580 : CollatzResearch.WordTrace tailWord_432580 prefixEnd_432580 24680162391335862495623 := by
  unfold tailWord_432580
  simp only [CollatzResearch.WordTrace]
  refine ⟨7888744386422006813659597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10518325848562675751546129 7888744386422006813659597)
  ·
    refine ⟨2958279144908252555122349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7888744386422006813659597 2958279144908252555122349)
    ·
      refine ⟨1109354679340594708170881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2958279144908252555122349 1109354679340594708170881)
      ·
        refine ⟨832016009505446031128161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1109354679340594708170881 832016009505446031128161)
        ·
          refine ⟨624012007129084523346121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 832016009505446031128161 624012007129084523346121)
          ·
            refine ⟨468009005346813392509591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 624012007129084523346121 468009005346813392509591)
            ·
              refine ⟨702013508020220088764387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468009005346813392509591 702013508020220088764387)
              ·
                refine ⟨1053020262030330133146581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 702013508020220088764387 1053020262030330133146581)
                ·
                  refine ⟨24680162391335862495623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1053020262030330133146581 24680162391335862495623)
                  ·
                    rfl

theorem cell23_432580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 7].length) (baseStart_432580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432580 prefixEnd_432580 := by exact prefixLift 432580
  have htrace : WordTrace (prefixWord ++ tailWord_432580) baseStart_432580 baseEnd_432580 := by
    simpa [prefixWord, tailWord_432580, baseEnd_432580] using wordTrace_append hprefix tailTrace_432580
  have hstable : (prefixWord ++ tailWord_432580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432580).length < 2 ^ (prefixWord ++ tailWord_432580).sum := by decide
  have hdescent : baseEnd_432580 < baseStart_432580 := by decide
  rcases family_descends (prefixWord ++ tailWord_432580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432586 : List Nat := [3, 1, 2, 1, 2, 2, 3, 1, 1, 2, 5]
def baseStart_432586 : Nat := 118140960795 + 432586 * 2 ^ 59
def prefixEnd_432586 : Nat := 4983230072969 + 3 ^ 40 * 432586 * 2
def baseEnd_432586 : Nat := 222124542405949738985579

theorem tailTrace_432586 : CollatzResearch.WordTrace tailWord_432586 prefixEnd_432586 222124542405949738985579 := by
  unfold tailWord_432586
  simp only [CollatzResearch.WordTrace]
  refine ⟨3944426902705569163009403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10518471740548184434691741 3944426902705569163009403)
  ·
    refine ⟨5916640354058353744514105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3944426902705569163009403 5916640354058353744514105)
    ·
      refine ⟨4437480265543765308385579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5916640354058353744514105 4437480265543765308385579)
      ·
        refine ⟨6656220398315647962578369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4437480265543765308385579 6656220398315647962578369)
        ·
          refine ⟨4992165298736735971933777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6656220398315647962578369 4992165298736735971933777)
          ·
            refine ⟨3744123974052551978950333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4992165298736735971933777 3744123974052551978950333)
            ·
              refine ⟨1404046490269706992106375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3744123974052551978950333 1404046490269706992106375)
              ·
                refine ⟨2106069735404560488159563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1404046490269706992106375 2106069735404560488159563)
                ·
                  refine ⟨3159104603106840732239345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2106069735404560488159563 3159104603106840732239345)
                  ·
                    refine ⟨2369328452330130549179509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3159104603106840732239345 2369328452330130549179509)
                    ·
                      refine ⟨222124542405949738985579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2369328452330130549179509 222124542405949738985579)
                      ·
                        rfl

theorem cell23_432586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_432586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432586 prefixEnd_432586 := by exact prefixLift 432586
  have htrace : WordTrace (prefixWord ++ tailWord_432586) baseStart_432586 baseEnd_432586 := by
    simpa [prefixWord, tailWord_432586, baseEnd_432586] using wordTrace_append hprefix tailTrace_432586
  have hstable : (prefixWord ++ tailWord_432586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432586).length < 2 ^ (prefixWord ++ tailWord_432586).sum := by decide
  have hdescent : baseEnd_432586 < baseStart_432586 := by decide
  rcases family_descends (prefixWord ++ tailWord_432586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432630 : List Nat := [5, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2]
def baseStart_432630 : Nat := 118140960795 + 432630 * 2 ^ 59
def prefixEnd_432630 : Nat := 4983230072969 + 3 ^ 40 * 432630 * 2
def baseEnd_432630 : Nat := 222147135554747566835377

theorem tailTrace_432630 : CollatzResearch.WordTrace tailWord_432630 prefixEnd_432630 222147135554747566835377 := by
  unfold tailWord_432630
  simp only [CollatzResearch.WordTrace]
  refine ⟨986207026416429510414959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10519541615108581444426229 986207026416429510414959)
  ·
    refine ⟨1479310539624644265622439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 986207026416429510414959 1479310539624644265622439)
    ·
      refine ⟨2218965809436966398433659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1479310539624644265622439 2218965809436966398433659)
      ·
        refine ⟨3328448714155449597650489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2218965809436966398433659 3328448714155449597650489)
        ·
          refine ⟨2496336535616587198237867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3328448714155449597650489 2496336535616587198237867)
          ·
            refine ⟨3744504803424880797356801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2496336535616587198237867 3744504803424880797356801)
            ·
              refine ⟨2808378602568660598017601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3744504803424880797356801 2808378602568660598017601)
              ·
                refine ⟨2106283951926495448513201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2808378602568660598017601 2106283951926495448513201)
                ·
                  refine ⟨1579712963944871586384901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2106283951926495448513201 1579712963944871586384901)
                  ·
                    refine ⟨296196180739663422447169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1579712963944871586384901 296196180739663422447169)
                    ·
                      refine ⟨222147135554747566835377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 296196180739663422447169 222147135554747566835377)
                      ·
                        rfl

theorem cell23_432630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_432630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432630 prefixEnd_432630 := by exact prefixLift 432630
  have htrace : WordTrace (prefixWord ++ tailWord_432630) baseStart_432630 baseEnd_432630 := by
    simpa [prefixWord, tailWord_432630, baseEnd_432630] using wordTrace_append hprefix tailTrace_432630
  have hstable : (prefixWord ++ tailWord_432630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432630).length < 2 ^ (prefixWord ++ tailWord_432630).sum := by decide
  have hdescent : baseEnd_432630 < baseStart_432630 := by decide
  rcases family_descends (prefixWord ++ tailWord_432630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432633 : List Nat := [1, 2, 1, 3, 1, 2, 4, 2, 2, 2, 3]
def baseStart_432633 : Nat := 118140960795 + 432633 * 2 ^ 59
def prefixEnd_432633 : Nat := 4983230072969 + 3 ^ 40 * 432633 * 2
def baseEnd_432633 : Nat := 222148675996711055097863

theorem tailTrace_432633 : CollatzResearch.WordTrace tailWord_432633 prefixEnd_432633 222148675996711055097863 := by
  unfold tailWord_432633
  simp only [CollatzResearch.WordTrace]
  refine ⟨15779421841652003678998553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10519614561101335785999035 15779421841652003678998553)
  ·
    refine ⟨11834566381239002759248915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15779421841652003678998553 11834566381239002759248915)
    ·
      refine ⟨17751849571858504138873373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11834566381239002759248915 17751849571858504138873373)
      ·
        refine ⟨6656943589446939052077515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17751849571858504138873373 6656943589446939052077515)
        ·
          refine ⟨9985415384170408578116273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6656943589446939052077515 9985415384170408578116273)
          ·
            refine ⟨7489061538127806433587205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9985415384170408578116273 7489061538127806433587205)
            ·
              refine ⟨1404199038398963706297601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7489061538127806433587205 1404199038398963706297601)
              ·
                refine ⟨1053149278799222779723201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1404199038398963706297601 1053149278799222779723201)
                ·
                  refine ⟨789861959099417084792401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1053149278799222779723201 789861959099417084792401)
                  ·
                    refine ⟨592396469324562813594301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 789861959099417084792401 592396469324562813594301)
                    ·
                      refine ⟨222148675996711055097863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 592396469324562813594301 222148675996711055097863)
                      ·
                        rfl

theorem cell23_432633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_432633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432633 prefixEnd_432633 := by exact prefixLift 432633
  have htrace : WordTrace (prefixWord ++ tailWord_432633) baseStart_432633 baseEnd_432633 := by
    simpa [prefixWord, tailWord_432633, baseEnd_432633] using wordTrace_append hprefix tailTrace_432633
  have hstable : (prefixWord ++ tailWord_432633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432633).length < 2 ^ (prefixWord ++ tailWord_432633).sum := by decide
  have hdescent : baseEnd_432633 < baseStart_432633 := by decide
  rcases family_descends (prefixWord ++ tailWord_432633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432690 : List Nat := [3, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2]
def baseStart_432690 : Nat := 118140960795 + 432690 * 2 ^ 59
def prefixEnd_432690 : Nat := 4983230072969 + 3 ^ 40 * 432690 * 2
def baseEnd_432690 : Nat := 222177944394017332085101

theorem tailTrace_432690 : CollatzResearch.WordTrace tailWord_432690 prefixEnd_432690 222177944394017332085101 := by
  unfold tailWord_432690
  simp only [CollatzResearch.WordTrace]
  refine ⟨3945375200611375603455881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10521000534963668275882349 3945375200611375603455881)
  ·
    refine ⟨2959031400458531702591911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3945375200611375603455881 2959031400458531702591911)
    ·
      refine ⟨4438547100687797553887867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2959031400458531702591911 4438547100687797553887867)
      ·
        refine ⟨6657820651031696330831801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4438547100687797553887867 6657820651031696330831801)
        ·
          refine ⟨4993365488273772248123851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6657820651031696330831801 4993365488273772248123851)
          ·
            refine ⟨7490048232410658372185777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4993365488273772248123851 7490048232410658372185777)
            ·
              refine ⟨5617536174307993779139333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7490048232410658372185777 5617536174307993779139333)
              ·
                refine ⟨1053288032682748833588625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5617536174307993779139333 1053288032682748833588625)
                ·
                  refine ⟨789966024512061625191469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1053288032682748833588625 789966024512061625191469)
                  ·
                    refine ⟨296237259192023109446801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 789966024512061625191469 296237259192023109446801)
                    ·
                      refine ⟨222177944394017332085101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 296237259192023109446801 222177944394017332085101)
                      ·
                        rfl

theorem cell23_432690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2].length) (baseStart_432690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432690 prefixEnd_432690 := by exact prefixLift 432690
  have htrace : WordTrace (prefixWord ++ tailWord_432690) baseStart_432690 baseEnd_432690 := by
    simpa [prefixWord, tailWord_432690, baseEnd_432690] using wordTrace_append hprefix tailTrace_432690
  have hstable : (prefixWord ++ tailWord_432690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432690).length < 2 ^ (prefixWord ++ tailWord_432690).sum := by decide
  have hdescent : baseEnd_432690 < baseStart_432690 := by decide
  rcases family_descends (prefixWord ++ tailWord_432690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432697 : List Nat := [1, 2, 1, 5, 1, 1, 1, 6, 1, 1, 3]
def baseStart_432697 : Nat := 118140960795 + 432697 * 2 ^ 59
def prefixEnd_432697 : Nat := 4983230072969 + 3 ^ 40 * 432697 * 2
def baseEnd_432697 : Nat := 222181538758598804697569

theorem tailTrace_432697 : CollatzResearch.WordTrace tailWord_432697 prefixEnd_432697 222181538758598804697569 := by
  unfold tailWord_432697
  simp only [CollatzResearch.WordTrace]
  refine ⟨15781756113420142609328345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10521170742280095072885563 15781756113420142609328345)
  ·
    refine ⟨11836317085065106956996259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15781756113420142609328345 11836317085065106956996259)
    ·
      refine ⟨17754475627597660435494389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11836317085065106956996259 17754475627597660435494389)
      ·
        refine ⟨1664482090087280665827599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17754475627597660435494389 1664482090087280665827599)
        ·
          refine ⟨2496723135130920998741399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1664482090087280665827599 2496723135130920998741399)
          ·
            refine ⟨3745084702696381498112099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2496723135130920998741399 3745084702696381498112099)
            ·
              refine ⟨5617627054044572247168149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3745084702696381498112099 5617627054044572247168149)
              ·
                refine ⟨263326268158339324086007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5617627054044572247168149 263326268158339324086007)
                ·
                  refine ⟨394989402237508986129011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 263326268158339324086007 394989402237508986129011)
                  ·
                    refine ⟨592484103356263479193517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 394989402237508986129011 592484103356263479193517)
                    ·
                      refine ⟨222181538758598804697569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 592484103356263479193517 222181538758598804697569)
                      ·
                        rfl

theorem cell23_432697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_432697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432697 prefixEnd_432697 := by exact prefixLift 432697
  have htrace : WordTrace (prefixWord ++ tailWord_432697) baseStart_432697 baseEnd_432697 := by
    simpa [prefixWord, tailWord_432697, baseEnd_432697] using wordTrace_append hprefix tailTrace_432697
  have hstable : (prefixWord ++ tailWord_432697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432697).length < 2 ^ (prefixWord ++ tailWord_432697).sum := by decide
  have hdescent : baseEnd_432697 < baseStart_432697 := by decide
  rcases family_descends (prefixWord ++ tailWord_432697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432717 : List Nat := [1, 6, 1, 1, 2, 2, 2, 2, 1, 5]
def baseStart_432717 : Nat := 118140960795 + 432717 * 2 ^ 59
def prefixEnd_432717 : Nat := 4983230072969 + 3 ^ 40 * 432717 * 2
def baseEnd_432717 : Nat := 74063936123896242149159

theorem tailTrace_432717 : CollatzResearch.WordTrace tailWord_432717 prefixEnd_432717 74063936123896242149159 := by
  unfold tailWord_432717
  simp only [CollatzResearch.WordTrace]
  refine ⟨15782485573347686025056405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10521657048898457350037603 15782485573347686025056405)
  ·
    refine ⟨739804011250672782424519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15782485573347686025056405 739804011250672782424519)
    ·
      refine ⟨1109706016876009173636779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 739804011250672782424519 1109706016876009173636779)
      ·
        refine ⟨1664559025314013760455169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1109706016876009173636779 1664559025314013760455169)
        ·
          refine ⟨1248419268985510320341377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1664559025314013760455169 1248419268985510320341377)
          ·
            refine ⟨936314451739132740256033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1248419268985510320341377 936314451739132740256033)
            ·
              refine ⟨702235838804349555192025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 936314451739132740256033 702235838804349555192025)
              ·
                refine ⟨526676879103262166394019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 702235838804349555192025 526676879103262166394019)
                ·
                  refine ⟨790015318654893249591029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 526676879103262166394019 790015318654893249591029)
                  ·
                    refine ⟨74063936123896242149159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 790015318654893249591029 74063936123896242149159)
                    ·
                      rfl

theorem cell23_432717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_432717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432717 prefixEnd_432717 := by exact prefixLift 432717
  have htrace : WordTrace (prefixWord ++ tailWord_432717) baseStart_432717 baseEnd_432717 := by
    simpa [prefixWord, tailWord_432717, baseEnd_432717] using wordTrace_append hprefix tailTrace_432717
  have hstable : (prefixWord ++ tailWord_432717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432717).length < 2 ^ (prefixWord ++ tailWord_432717).sum := by decide
  have hdescent : baseEnd_432717 < baseStart_432717 := by decide
  rcases family_descends (prefixWord ++ tailWord_432717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432720 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 5, 2, 2]
def baseStart_432720 : Nat := 118140960795 + 432720 * 2 ^ 59
def prefixEnd_432720 : Nat := 4983230072969 + 3 ^ 40 * 432720 * 2
def baseEnd_432720 : Nat := 222193348813652214709963

theorem tailTrace_432720 : CollatzResearch.WordTrace tailWord_432720 prefixEnd_432720 222193348813652214709963 := by
  unfold tailWord_432720
  simp only [CollatzResearch.WordTrace]
  refine ⟨7891297496168408768707807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10521729994891211691610409 7891297496168408768707807)
  ·
    refine ⟨11836946244252613153061711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7891297496168408768707807 11836946244252613153061711)
    ·
      refine ⟨17755419366378919729592567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11836946244252613153061711 17755419366378919729592567)
      ·
        refine ⟨26633129049568379594388851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17755419366378919729592567 26633129049568379594388851)
        ·
          refine ⟨39949693574352569391583277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26633129049568379594388851 39949693574352569391583277)
          ·
            refine ⟨14981135090382213521843729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39949693574352569391583277 14981135090382213521843729)
            ·
              refine ⟨11235851317786660141382797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14981135090382213521843729 11235851317786660141382797)
              ·
                refine ⟨4213444244169997553018549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11235851317786660141382797 4213444244169997553018549)
                ·
                  refine ⟨395010397890937270595489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4213444244169997553018549 395010397890937270595489)
                  ·
                    refine ⟨296257798418202952946617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 395010397890937270595489 296257798418202952946617)
                    ·
                      refine ⟨222193348813652214709963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 296257798418202952946617 222193348813652214709963)
                      ·
                        rfl

theorem cell23_432720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 5, 2, 2].length) (baseStart_432720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432720 prefixEnd_432720 := by exact prefixLift 432720
  have htrace : WordTrace (prefixWord ++ tailWord_432720) baseStart_432720 baseEnd_432720 := by
    simpa [prefixWord, tailWord_432720, baseEnd_432720] using wordTrace_append hprefix tailTrace_432720
  have hstable : (prefixWord ++ tailWord_432720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432720).length < 2 ^ (prefixWord ++ tailWord_432720).sum := by decide
  have hdescent : baseEnd_432720 < baseStart_432720 := by decide
  rcases family_descends (prefixWord ++ tailWord_432720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432740 : List Nat := [2, 3, 1, 1, 2, 2, 1, 5, 1, 2, 3]
def baseStart_432740 : Nat := 118140960795 + 432740 * 2 ^ 59
def prefixEnd_432740 : Nat := 4983230072969 + 3 ^ 40 * 432740 * 2
def baseEnd_432740 : Nat := 222203618426742136459871

theorem tailTrace_432740 : CollatzResearch.WordTrace tailWord_432740 prefixEnd_432740 222203618426742136459871 := by
  unfold tailWord_432740
  simp only [CollatzResearch.WordTrace]
  refine ⟨7891662226132180476571837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10522216301509573968762449 7891662226132180476571837)
  ·
    refine ⟨2959373334799567678714439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7891662226132180476571837 2959373334799567678714439)
    ·
      refine ⟨4439060002199351518071659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2959373334799567678714439 4439060002199351518071659)
      ·
        refine ⟨6658590003299027277107489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4439060002199351518071659 6658590003299027277107489)
        ·
          refine ⟨4993942502474270457830617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6658590003299027277107489 4993942502474270457830617)
          ·
            refine ⟨3745456876855702843372963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4993942502474270457830617 3745456876855702843372963)
            ·
              refine ⟨5618185315283554265059445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3745456876855702843372963 5618185315283554265059445)
              ·
                refine ⟨526704873307833212349323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5618185315283554265059445 526704873307833212349323)
                ·
                  refine ⟨790057309961749818523985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 526704873307833212349323 790057309961749818523985)
                  ·
                    refine ⟨592542982471312363892989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 790057309961749818523985 592542982471312363892989)
                    ·
                      refine ⟨222203618426742136459871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 592542982471312363892989 222203618426742136459871)
                      ·
                        rfl

theorem cell23_432740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_432740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432740 prefixEnd_432740 := by exact prefixLift 432740
  have htrace : WordTrace (prefixWord ++ tailWord_432740) baseStart_432740 baseEnd_432740 := by
    simpa [prefixWord, tailWord_432740, baseEnd_432740] using wordTrace_append hprefix tailTrace_432740
  have hstable : (prefixWord ++ tailWord_432740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432740).length < 2 ^ (prefixWord ++ tailWord_432740).sum := by decide
  have hdescent : baseEnd_432740 < baseStart_432740 := by decide
  rcases family_descends (prefixWord ++ tailWord_432740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432797 : List Nat := [1, 4, 2, 1, 1, 1, 2, 5, 1, 3, 2]
def baseStart_432797 : Nat := 118140960795 + 432797 * 2 ^ 59
def prefixEnd_432797 : Nat := 4983230072969 + 3 ^ 40 * 432797 * 2
def baseEnd_432797 : Nat := 222232886824048413447109

theorem tailTrace_432797 : CollatzResearch.WordTrace tailWord_432797 prefixEnd_432797 222232886824048413447109 := by
  unfold tailWord_432797
  simp only [CollatzResearch.WordTrace]
  refine ⟨15785403413057859687968645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10523602275371906458645763 15785403413057859687968645)
  ·
    refine ⟨2959763139948348691494121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15785403413057859687968645 2959763139948348691494121)
    ·
      refine ⟨2219822354961261518620591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2959763139948348691494121 2219822354961261518620591)
      ·
        refine ⟨3329733532441892277930887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2219822354961261518620591 3329733532441892277930887)
        ·
          refine ⟨4994600298662838416896331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3329733532441892277930887 4994600298662838416896331)
          ·
            refine ⟨7491900447994257625344497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4994600298662838416896331 7491900447994257625344497)
            ·
              refine ⟨5618925335995693219008373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7491900447994257625344497 5618925335995693219008373)
              ·
                refine ⟨526774250249596239282035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5618925335995693219008373 526774250249596239282035)
                ·
                  refine ⟨790161375374394358923053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 526774250249596239282035 790161375374394358923053)
                  ·
                    refine ⟨296310515765397884596145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 790161375374394358923053 296310515765397884596145)
                    ·
                      refine ⟨222232886824048413447109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 296310515765397884596145 222232886824048413447109)
                      ·
                        rfl

theorem cell23_432797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_432797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432797 prefixEnd_432797 := by exact prefixLift 432797
  have htrace : WordTrace (prefixWord ++ tailWord_432797) baseStart_432797 baseEnd_432797 := by
    simpa [prefixWord, tailWord_432797, baseEnd_432797] using wordTrace_append hprefix tailTrace_432797
  have hstable : (prefixWord ++ tailWord_432797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432797).length < 2 ^ (prefixWord ++ tailWord_432797).sum := by decide
  have hdescent : baseEnd_432797 < baseStart_432797 := by decide
  rcases family_descends (prefixWord ++ tailWord_432797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432814 : List Nat := [4, 1, 4, 1, 1, 1, 1, 2, 3, 3, 2]
def baseStart_432814 : Nat := 118140960795 + 432814 * 2 ^ 59
def prefixEnd_432814 : Nat := 4983230072969 + 3 ^ 40 * 432814 * 2
def baseEnd_432814 : Nat := 222241615995174846934531

theorem tailTrace_432814 : CollatzResearch.WordTrace tailWord_432814 prefixEnd_432814 222241615995174846934531 := by
  unfold tailWord_432814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1973252931749533948917187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10524015635997514394224997 1973252931749533948917187)
  ·
    refine ⟨2959879397624300923375781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1973252931749533948917187 2959879397624300923375781)
    ·
      refine ⟨554977387054556423132959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2959879397624300923375781 554977387054556423132959)
      ·
        refine ⟨832466080581834634699439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554977387054556423132959 832466080581834634699439)
        ·
          refine ⟨1248699120872751952049159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 832466080581834634699439 1248699120872751952049159)
          ·
            refine ⟨1873048681309127928073739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1248699120872751952049159 1873048681309127928073739)
            ·
              refine ⟨2809573021963691892110609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1873048681309127928073739 2809573021963691892110609)
              ·
                refine ⟨2107179766472768919082957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2809573021963691892110609 2107179766472768919082957)
                ·
                  refine ⟨790192412427288344656109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2107179766472768919082957 790192412427288344656109)
                  ·
                    refine ⟨296322154660233129246041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 790192412427288344656109 296322154660233129246041)
                    ·
                      refine ⟨222241615995174846934531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 296322154660233129246041 222241615995174846934531)
                      ·
                        rfl

theorem cell23_432814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_432814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432814 prefixEnd_432814 := by exact prefixLift 432814
  have htrace : WordTrace (prefixWord ++ tailWord_432814) baseStart_432814 baseEnd_432814 := by
    simpa [prefixWord, tailWord_432814, baseEnd_432814] using wordTrace_append hprefix tailTrace_432814
  have hstable : (prefixWord ++ tailWord_432814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432814).length < 2 ^ (prefixWord ++ tailWord_432814).sum := by decide
  have hdescent : baseEnd_432814 < baseStart_432814 := by decide
  rcases family_descends (prefixWord ++ tailWord_432814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432830 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3]
def baseStart_432830 : Nat := 118140960795 + 432830 * 2 ^ 59
def prefixEnd_432830 : Nat := 4983230072969 + 3 ^ 40 * 432830 * 2
def baseEnd_432830 : Nat := 222249831685646784334457

theorem tailTrace_432830 : CollatzResearch.WordTrace tailWord_432830 prefixEnd_432830 222249831685646784334457 := by
  unfold tailWord_432830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1973325877742288290489993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10524404681292204215946629 1973325877742288290489993)
  ·
    refine ⟨1479994408306716217867495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1973325877742288290489993 1479994408306716217867495)
    ·
      refine ⟨2219991612460074326801243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1479994408306716217867495 2219991612460074326801243)
      ·
        refine ⟨3329987418690111490201865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2219991612460074326801243 3329987418690111490201865)
        ·
          refine ⟨2497490564017583617651399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3329987418690111490201865 2497490564017583617651399)
          ·
            refine ⟨3746235846026375426477099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2497490564017583617651399 3746235846026375426477099)
            ·
              refine ⟨5619353769039563139715649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3746235846026375426477099 5619353769039563139715649)
              ·
                refine ⟨4214515326779672354786737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5619353769039563139715649 4214515326779672354786737)
                ·
                  refine ⟨3160886495084754266090053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4214515326779672354786737 3160886495084754266090053)
                  ·
                    refine ⟨592666217828391424891885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3160886495084754266090053 592666217828391424891885)
                    ·
                      refine ⟨222249831685646784334457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 592666217828391424891885 222249831685646784334457)
                      ·
                        rfl

theorem cell23_432830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_432830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432830 prefixEnd_432830 := by exact prefixLift 432830
  have htrace : WordTrace (prefixWord ++ tailWord_432830) baseStart_432830 baseEnd_432830 := by
    simpa [prefixWord, tailWord_432830, baseEnd_432830] using wordTrace_append hprefix tailTrace_432830
  have hstable : (prefixWord ++ tailWord_432830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432830).length < 2 ^ (prefixWord ++ tailWord_432830).sum := by decide
  have hdescent : baseEnd_432830 < baseStart_432830 := by decide
  rcases family_descends (prefixWord ++ tailWord_432830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432867 : List Nat := [1, 1, 1, 7, 1, 1, 2, 4, 5]
def baseStart_432867 : Nat := 118140960795 + 432867 * 2 ^ 59
def prefixEnd_432867 : Nat := 4983230072969 + 3 ^ 40 * 432867 * 2
def baseEnd_432867 : Nat := 24696536718873682174643

theorem tailTrace_432867 : CollatzResearch.WordTrace tailWord_432867 prefixEnd_432867 24696536718873682174643 := by
  unfold tailWord_432867
  simp only [CollatzResearch.WordTrace]
  refine ⟨15787956522804261643016855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10525304348536174428677903 15787956522804261643016855)
  ·
    refine ⟨23681934784206392464525283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15787956522804261643016855 23681934784206392464525283)
    ·
      refine ⟨35522902176309588696787925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23681934784206392464525283 35522902176309588696787925)
      ·
        refine ⟨832568019757255985080967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 35522902176309588696787925 832568019757255985080967)
        ·
          refine ⟨1248852029635883977621451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 832568019757255985080967 1248852029635883977621451)
          ·
            refine ⟨1873278044453825966432177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1248852029635883977621451 1873278044453825966432177)
            ·
              refine ⟨1404958533340369474824133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1873278044453825966432177 1404958533340369474824133)
              ·
                refine ⟨263429725001319276529525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1404958533340369474824133 263429725001319276529525)
                ·
                  refine ⟨24696536718873682174643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 263429725001319276529525 24696536718873682174643)
                  ·
                    rfl

theorem cell23_432867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 4, 5].length) (baseStart_432867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432867 prefixEnd_432867 := by exact prefixLift 432867
  have htrace : WordTrace (prefixWord ++ tailWord_432867) baseStart_432867 baseEnd_432867 := by
    simpa [prefixWord, tailWord_432867, baseEnd_432867] using wordTrace_append hprefix tailTrace_432867
  have hstable : (prefixWord ++ tailWord_432867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432867).length < 2 ^ (prefixWord ++ tailWord_432867).sum := by decide
  have hdescent : baseEnd_432867 < baseStart_432867 := by decide
  rcases family_descends (prefixWord ++ tailWord_432867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432873 : List Nat := [1, 2, 1, 1, 1, 2, 4, 3, 1, 2, 5]
def baseStart_432873 : Nat := 118140960795 + 432873 * 2 ^ 59
def prefixEnd_432873 : Nat := 4983230072969 + 3 ^ 40 * 432873 * 2
def baseEnd_432873 : Nat := 222271911353790116096759

theorem tailTrace_432873 : CollatzResearch.WordTrace tailWord_432873 prefixEnd_432873 222271911353790116096759 := by
  unfold tailWord_432873
  simp only [CollatzResearch.WordTrace]
  refine ⟨15788175360782524667735273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10525450240521683111823515 15788175360782524667735273)
  ·
    refine ⟨11841131520586893500801455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15788175360782524667735273 11841131520586893500801455)
    ·
      refine ⟨17761697280880340251202183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11841131520586893500801455 17761697280880340251202183)
      ·
        refine ⟨26642545921320510376803275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17761697280880340251202183 26642545921320510376803275)
        ·
          refine ⟨39963818881980765565204913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26642545921320510376803275 39963818881980765565204913)
          ·
            refine ⟨29972864161485574173903685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39963818881980765565204913 29972864161485574173903685)
            ·
              refine ⟨5619912030278545157606941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29972864161485574173903685 5619912030278545157606941)
              ·
                refine ⟨2107467011354454434102603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5619912030278545157606941 2107467011354454434102603)
                ·
                  refine ⟨3161200517031681651153905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2107467011354454434102603 3161200517031681651153905)
                  ·
                    refine ⟨2370900387773761238365429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3161200517031681651153905 2370900387773761238365429)
                    ·
                      refine ⟨222271911353790116096759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2370900387773761238365429 222271911353790116096759)
                      ·
                        rfl

theorem cell23_432873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 2, 5].length) (baseStart_432873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432873 prefixEnd_432873 := by exact prefixLift 432873
  have htrace : WordTrace (prefixWord ++ tailWord_432873) baseStart_432873 baseEnd_432873 := by
    simpa [prefixWord, tailWord_432873, baseEnd_432873] using wordTrace_append hprefix tailTrace_432873
  have hstable : (prefixWord ++ tailWord_432873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432873).length < 2 ^ (prefixWord ++ tailWord_432873).sum := by decide
  have hdescent : baseEnd_432873 < baseStart_432873 := by decide
  rcases family_descends (prefixWord ++ tailWord_432873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432893 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 2, 8]
def baseStart_432893 : Nat := 118140960795 + 432893 * 2 ^ 59
def prefixEnd_432893 : Nat := 4983230072969 + 3 ^ 40 * 432893 * 2
def baseEnd_432893 : Nat := 74094060322293345948889

theorem tailTrace_432893 : CollatzResearch.WordTrace tailWord_432893 prefixEnd_432893 74094060322293345948889 := by
  unfold tailWord_432893
  simp only [CollatzResearch.WordTrace]
  refine ⟨15788904820710068083463333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10525936547140045388975555 15788904820710068083463333)
  ·
    refine ⟨2960419653883137765649375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15788904820710068083463333 2960419653883137765649375)
    ·
      refine ⟨4440629480824706648474063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2960419653883137765649375 4440629480824706648474063)
      ·
        refine ⟨6660944221237059972711095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4440629480824706648474063 6660944221237059972711095)
        ·
          refine ⟨9991416331855589959066643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6660944221237059972711095 9991416331855589959066643)
          ·
            refine ⟨14987124497783384938599965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9991416331855589959066643 14987124497783384938599965)
            ·
              refine ⟨5620171686668769351974987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14987124497783384938599965 5620171686668769351974987)
              ·
                refine ⟨8430257530003154027962481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5620171686668769351974987 8430257530003154027962481)
                ·
                  refine ⟨6322693147502365520971861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8430257530003154027962481 6322693147502365520971861)
                  ·
                    refine ⟨74094060322293345948889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6322693147502365520971861 74094060322293345948889)
                    ·
                      rfl

theorem cell23_432893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_432893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432893 prefixEnd_432893 := by exact prefixLift 432893
  have htrace : WordTrace (prefixWord ++ tailWord_432893) baseStart_432893 baseEnd_432893 := by
    simpa [prefixWord, tailWord_432893, baseEnd_432893] using wordTrace_append hprefix tailTrace_432893
  have hstable : (prefixWord ++ tailWord_432893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432893).length < 2 ^ (prefixWord ++ tailWord_432893).sum := by decide
  have hdescent : baseEnd_432893 < baseStart_432893 := by decide
  rcases family_descends (prefixWord ++ tailWord_432893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432900 : List Nat := [2, 3, 2, 2, 1, 1, 1, 3, 1, 3, 4]
def baseStart_432900 : Nat := 118140960795 + 432900 * 2 ^ 59
def prefixEnd_432900 : Nat := 4983230072969 + 3 ^ 40 * 432900 * 2
def baseEnd_432900 : Nat := 222285775331461510459135

theorem tailTrace_432900 : CollatzResearch.WordTrace tailWord_432900 prefixEnd_432900 222285775331461510459135 := by
  unfold tailWord_432900
  simp only [CollatzResearch.WordTrace]
  refine ⟨7894580065842354139484077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10526106754456472185978769 7894580065842354139484077)
  ·
    refine ⟨2960467524690882802306529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7894580065842354139484077 2960467524690882802306529)
    ·
      refine ⟨2220350643518162101729897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2960467524690882802306529 2220350643518162101729897)
      ·
        refine ⟨1665262982638621576297423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2220350643518162101729897 1665262982638621576297423)
        ·
          refine ⟨2497894473957932364446135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1665262982638621576297423 2497894473957932364446135)
          ·
            refine ⟨3746841710936898546669203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2497894473957932364446135 3746841710936898546669203)
            ·
              refine ⟨5620262566405347820003805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3746841710936898546669203 5620262566405347820003805)
              ·
                refine ⟨2107598462402005432501427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5620262566405347820003805 2107598462402005432501427)
                ·
                  refine ⟨3161397693603008148752141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2107598462402005432501427 3161397693603008148752141)
                  ·
                    refine ⟨1185524135101128055782053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3161397693603008148752141 1185524135101128055782053)
                    ·
                      refine ⟨222285775331461510459135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1185524135101128055782053 222285775331461510459135)
                      ·
                        rfl

theorem cell23_432900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_432900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432900 prefixEnd_432900 := by exact prefixLift 432900
  have htrace : WordTrace (prefixWord ++ tailWord_432900) baseStart_432900 baseEnd_432900 := by
    simpa [prefixWord, tailWord_432900, baseEnd_432900] using wordTrace_append hprefix tailTrace_432900
  have hstable : (prefixWord ++ tailWord_432900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432900).length < 2 ^ (prefixWord ++ tailWord_432900).sum := by decide
  have hdescent : baseEnd_432900 < baseStart_432900 := by decide
  rcases family_descends (prefixWord ++ tailWord_432900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432913 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 6]
def baseStart_432913 : Nat := 118140960795 + 432913 * 2 ^ 59
def prefixEnd_432913 : Nat := 4983230072969 + 3 ^ 40 * 432913 * 2
def baseEnd_432913 : Nat := 222292450579969959596575

theorem tailTrace_432913 : CollatzResearch.WordTrace tailWord_432913 prefixEnd_432913 222292450579969959596575 := by
  unfold tailWord_432913
  simp only [CollatzResearch.WordTrace]
  refine ⟨15789634280637611499191393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10526422853758407666127595 15789634280637611499191393)
  ·
    refine ⟨11842225710478208624393545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15789634280637611499191393 11842225710478208624393545)
    ·
      refine ⟨8881669282858656468295159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11842225710478208624393545 8881669282858656468295159)
      ·
        refine ⟨13322503924287984702442739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8881669282858656468295159 13322503924287984702442739)
        ·
          refine ⟨19983755886431977053664109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13322503924287984702442739 19983755886431977053664109)
          ·
            refine ⟨7493908457411991395124041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19983755886431977053664109 7493908457411991395124041)
            ·
              refine ⟨5620431343058993546343031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7493908457411991395124041 5620431343058993546343031)
              ·
                refine ⟨8430647014588490319514547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5620431343058993546343031 8430647014588490319514547)
                ·
                  refine ⟨12645970521882735479271821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8430647014588490319514547 12645970521882735479271821)
                  ·
                    refine ⟨4742238945706025804726933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12645970521882735479271821 4742238945706025804726933)
                    ·
                      refine ⟨222292450579969959596575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4742238945706025804726933 222292450579969959596575)
                      ·
                        rfl

theorem cell23_432913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_432913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432913 prefixEnd_432913 := by exact prefixLift 432913
  have htrace : WordTrace (prefixWord ++ tailWord_432913) baseStart_432913 baseEnd_432913 := by
    simpa [prefixWord, tailWord_432913, baseEnd_432913] using wordTrace_append hprefix tailTrace_432913
  have hstable : (prefixWord ++ tailWord_432913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432913).length < 2 ^ (prefixWord ++ tailWord_432913).sum := by decide
  have hdescent : baseEnd_432913 < baseStart_432913 := by decide
  rcases family_descends (prefixWord ++ tailWord_432913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432914 : List Nat := [3, 2, 4, 1, 2, 1, 1, 2, 2, 5]
def baseStart_432914 : Nat := 118140960795 + 432914 * 2 ^ 59
def prefixEnd_432914 : Nat := 4983230072969 + 3 ^ 40 * 432914 * 2
def baseEnd_432914 : Nat := 74097654686874818561357

theorem tailTrace_432914 : CollatzResearch.WordTrace tailWord_432914 prefixEnd_432914 74097654686874818561357 := by
  unfold tailWord_432914
  simp only [CollatzResearch.WordTrace]
  refine ⟨3947417688408497167494449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10526447169089325779985197 3947417688408497167494449)
  ·
    refine ⟨2960563266306372875620837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3947417688408497167494449 2960563266306372875620837)
    ·
      refine ⟨555105612432444914178907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2960563266306372875620837 555105612432444914178907)
      ·
        refine ⟨832658418648667371268361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555105612432444914178907 832658418648667371268361)
        ·
          refine ⟨624493813986500528451271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 832658418648667371268361 624493813986500528451271)
          ·
            refine ⟨936740720979750792676907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624493813986500528451271 936740720979750792676907)
            ·
              refine ⟨1405111081469626189015361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 936740720979750792676907 1405111081469626189015361)
              ·
                refine ⟨1053833311102219641761521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1405111081469626189015361 1053833311102219641761521)
                ·
                  refine ⟨790374983326664731321141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1053833311102219641761521 790374983326664731321141)
                  ·
                    refine ⟨74097654686874818561357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 790374983326664731321141 74097654686874818561357)
                    ·
                      rfl

theorem cell23_432914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_432914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432914 prefixEnd_432914 := by exact prefixLift 432914
  have htrace : WordTrace (prefixWord ++ tailWord_432914) baseStart_432914 baseEnd_432914 := by
    simpa [prefixWord, tailWord_432914, baseEnd_432914] using wordTrace_append hprefix tailTrace_432914
  have hstable : (prefixWord ++ tailWord_432914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432914).length < 2 ^ (prefixWord ++ tailWord_432914).sum := by decide
  have hdescent : baseEnd_432914 < baseStart_432914 := by decide
  rcases family_descends (prefixWord ++ tailWord_432914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432927 : List Nat := [1, 1, 2, 4, 2, 2, 3, 1, 3, 4]
def baseStart_432927 : Nat := 118140960795 + 432927 * 2 ^ 59
def prefixEnd_432927 : Nat := 4983230072969 + 3 ^ 40 * 432927 * 2
def baseEnd_432927 : Nat := 74099879769710968273837

theorem tailTrace_432927 : CollatzResearch.WordTrace tailWord_432927 prefixEnd_432927 74099879769710968273837 := by
  unfold tailWord_432927
  simp only [CollatzResearch.WordTrace]
  refine ⟨15790144902586891890201035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10526763268391261260134023 15790144902586891890201035)
  ·
    refine ⟨23685217353880337835301553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15790144902586891890201035 23685217353880337835301553)
    ·
      refine ⟨17763913015410253376476165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23685217353880337835301553 17763913015410253376476165)
      ·
        refine ⟨3330733690389422508089281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17763913015410253376476165 3330733690389422508089281)
        ·
          refine ⟨2498050267792066881066961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3330733690389422508089281 2498050267792066881066961)
          ·
            refine ⟨1873537700844050160800221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2498050267792066881066961 1873537700844050160800221)
            ·
              refine ⟨702576637816518810300083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1873537700844050160800221 702576637816518810300083)
              ·
                refine ⟨1053864956724778215450125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 702576637816518810300083 1053864956724778215450125)
                ·
                  refine ⟨395199358771791830793797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1053864956724778215450125 395199358771791830793797)
                  ·
                    refine ⟨74099879769710968273837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 395199358771791830793797 74099879769710968273837)
                    ·
                      rfl

theorem cell23_432927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 3, 4].length) (baseStart_432927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432927 prefixEnd_432927 := by exact prefixLift 432927
  have htrace : WordTrace (prefixWord ++ tailWord_432927) baseStart_432927 baseEnd_432927 := by
    simpa [prefixWord, tailWord_432927, baseEnd_432927] using wordTrace_append hprefix tailTrace_432927
  have hstable : (prefixWord ++ tailWord_432927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432927).length < 2 ^ (prefixWord ++ tailWord_432927).sum := by decide
  have hdescent : baseEnd_432927 < baseStart_432927 := by decide
  rcases family_descends (prefixWord ++ tailWord_432927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432940 : List Nat := [2, 2, 1, 1, 1, 4, 3, 3, 6]
def baseStart_432940 : Nat := 118140960795 + 432940 * 2 ^ 59
def prefixEnd_432940 : Nat := 4983230072969 + 3 ^ 40 * 432940 * 2
def baseEnd_432940 : Nat := 24700701617515705995439

theorem tailTrace_432940 : CollatzResearch.WordTrace tailWord_432940 prefixEnd_432940 24700701617515705995439 := by
  unfold tailWord_432940
  simp only [CollatzResearch.WordTrace]
  refine ⟨7895309525769897555212137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10527079367693196740282849 7895309525769897555212137)
  ·
    refine ⟨5921482144327423166409103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7895309525769897555212137 5921482144327423166409103)
    ·
      refine ⟨8882223216491134749613655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5921482144327423166409103 8882223216491134749613655)
      ·
        refine ⟨13323334824736702124420483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8882223216491134749613655 13323334824736702124420483)
        ·
          refine ⟨19985002237105053186630725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13323334824736702124420483 19985002237105053186630725)
          ·
            refine ⟨3747187919457197472493261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19985002237105053186630725 3747187919457197472493261)
            ·
              refine ⟨1405195469796449052184973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3747187919457197472493261 1405195469796449052184973)
              ·
                refine ⟨526948301173668394569365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1405195469796449052184973 526948301173668394569365)
                ·
                  refine ⟨24700701617515705995439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 526948301173668394569365 24700701617515705995439)
                  ·
                    rfl

theorem cell23_432940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 6].length) (baseStart_432940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432940 prefixEnd_432940 := by exact prefixLift 432940
  have htrace : WordTrace (prefixWord ++ tailWord_432940) baseStart_432940 baseEnd_432940 := by
    simpa [prefixWord, tailWord_432940, baseEnd_432940] using wordTrace_append hprefix tailTrace_432940
  have hstable : (prefixWord ++ tailWord_432940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432940).length < 2 ^ (prefixWord ++ tailWord_432940).sum := by decide
  have hdescent : baseEnd_432940 < baseStart_432940 := by decide
  rcases family_descends (prefixWord ++ tailWord_432940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432954 : List Nat := [3, 1, 1, 1, 6, 1, 2, 1, 2, 2, 3]
def baseStart_432954 : Nat := 118140960795 + 432954 * 2 ^ 59
def prefixEnd_432954 : Nat := 4983230072969 + 3 ^ 40 * 432954 * 2
def baseEnd_432954 : Nat := 222313503286804299183887

theorem tailTrace_432954 : CollatzResearch.WordTrace tailWord_432954 prefixEnd_432954 222313503286804299183887 := by
  unfold tailWord_432954
  simp only [CollatzResearch.WordTrace]
  refine ⟨3947782418372268875358479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10527419782326050334289277 3947782418372268875358479)
  ·
    refine ⟨5921673627558403313037719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3947782418372268875358479 5921673627558403313037719)
    ·
      refine ⟨8882510441337604969556579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5921673627558403313037719 8882510441337604969556579)
      ·
        refine ⟨13323765662006407454334869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8882510441337604969556579 13323765662006407454334869)
        ·
          refine ⟨624551515406550349421947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13323765662006407454334869 624551515406550349421947)
          ·
            refine ⟨936827273109825524132921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624551515406550349421947 936827273109825524132921)
            ·
              refine ⟨702620454832369143099691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 936827273109825524132921 702620454832369143099691)
              ·
                refine ⟨1053930682248553714649537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 702620454832369143099691 1053930682248553714649537)
                ·
                  refine ⟨790448011686415285987153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1053930682248553714649537 790448011686415285987153)
                  ·
                    refine ⟨592836008764811464490365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 790448011686415285987153 592836008764811464490365)
                    ·
                      refine ⟨222313503286804299183887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 592836008764811464490365 222313503286804299183887)
                      ·
                        rfl

theorem cell23_432954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 2, 2, 3].length) (baseStart_432954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_432954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_432954 prefixEnd_432954 := by exact prefixLift 432954
  have htrace : WordTrace (prefixWord ++ tailWord_432954) baseStart_432954 baseEnd_432954 := by
    simpa [prefixWord, tailWord_432954, baseEnd_432954] using wordTrace_append hprefix tailTrace_432954
  have hstable : (prefixWord ++ tailWord_432954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432954).length < 2 ^ (prefixWord ++ tailWord_432954).sum := by decide
  have hdescent : baseEnd_432954 < baseStart_432954 := by decide
  rcases family_descends (prefixWord ++ tailWord_432954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433034 : List Nat := [3, 1, 2, 4, 1, 2, 1, 1, 4, 4]
def baseStart_433034 : Nat := 118140960795 + 433034 * 2 ^ 59
def prefixEnd_433034 : Nat := 4983230072969 + 3 ^ 40 * 433034 * 2
def baseEnd_433034 : Nat := 74118193913054662061173

theorem tailTrace_433034 : CollatzResearch.WordTrace tailWord_433034 prefixEnd_433034 74118193913054662061173 := by
  unfold tailWord_433034
  simp only [CollatzResearch.WordTrace]
  refine ⟨3948511878299812291086539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10529365008799499442897437 3948511878299812291086539)
  ·
    refine ⟨5922767817449718436629809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3948511878299812291086539 5922767817449718436629809)
    ·
      refine ⟨4442075863087288827472357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5922767817449718436629809 4442075863087288827472357)
      ·
        refine ⟨832889224328866655151067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4442075863087288827472357 832889224328866655151067)
        ·
          refine ⟨1249333836493299982726601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 832889224328866655151067 1249333836493299982726601)
          ·
            refine ⟨937000377369974987044951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1249333836493299982726601 937000377369974987044951)
            ·
              refine ⟨1405500566054962480567427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 937000377369974987044951 1405500566054962480567427)
              ·
                refine ⟨2108250849082443720851141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1405500566054962480567427 2108250849082443720851141)
                ·
                  refine ⟨395297034202958197659589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2108250849082443720851141 395297034202958197659589)
                  ·
                    refine ⟨74118193913054662061173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 395297034202958197659589 74118193913054662061173)
                    ·
                      rfl

theorem cell23_433034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_433034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433034 prefixEnd_433034 := by exact prefixLift 433034
  have htrace : WordTrace (prefixWord ++ tailWord_433034) baseStart_433034 baseEnd_433034 := by
    simpa [prefixWord, tailWord_433034, baseEnd_433034] using wordTrace_append hprefix tailTrace_433034
  have hstable : (prefixWord ++ tailWord_433034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433034).length < 2 ^ (prefixWord ++ tailWord_433034).sum := by decide
  have hdescent : baseEnd_433034 < baseStart_433034 := by decide
  rcases family_descends (prefixWord ++ tailWord_433034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433092 : List Nat := [2, 3, 3, 3, 2, 1, 1, 1, 3, 2, 2]
def baseStart_433092 : Nat := 118140960795 + 433092 * 2 ^ 59
def prefixEnd_433092 : Nat := 4983230072969 + 3 ^ 40 * 433092 * 2
def baseEnd_433092 : Nat := 222384363617124759258253

theorem tailTrace_433092 : CollatzResearch.WordTrace tailWord_433092 prefixEnd_433092 222384363617124759258253 := by
  unfold tailWord_433092
  simp only [CollatzResearch.WordTrace]
  refine ⟨7898081473494562534978765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10530775297992750046638353 7898081473494562534978765)
  ·
    refine ⟨2961780552560460950617037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7898081473494562534978765 2961780552560460950617037)
    ·
      refine ⟨1110667707210172856481389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2961780552560460950617037 1110667707210172856481389)
      ·
        refine ⟨416500390203814821180521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1110667707210172856481389 416500390203814821180521)
        ·
          refine ⟨312375292652861115885391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416500390203814821180521 312375292652861115885391)
          ·
            refine ⟨468562938979291673828087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312375292652861115885391 468562938979291673828087)
            ·
              refine ⟨702844408468937510742131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468562938979291673828087 702844408468937510742131)
              ·
                refine ⟨1054266612703406266113197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 702844408468937510742131 1054266612703406266113197)
                ·
                  refine ⟨395349979763777349792449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1054266612703406266113197 395349979763777349792449)
                  ·
                    refine ⟨296512484822833012344337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 395349979763777349792449 296512484822833012344337)
                    ·
                      refine ⟨222384363617124759258253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 296512484822833012344337 222384363617124759258253)
                      ·
                        rfl

theorem cell23_433092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_433092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433092 prefixEnd_433092 := by exact prefixLift 433092
  have htrace : WordTrace (prefixWord ++ tailWord_433092) baseStart_433092 baseEnd_433092 := by
    simpa [prefixWord, tailWord_433092, baseEnd_433092] using wordTrace_append hprefix tailTrace_433092
  have hstable : (prefixWord ++ tailWord_433092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433092).length < 2 ^ (prefixWord ++ tailWord_433092).sum := by decide
  have hdescent : baseEnd_433092 < baseStart_433092 := by decide
  rcases family_descends (prefixWord ++ tailWord_433092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433097 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 2, 8, 2]
def baseStart_433097 : Nat := 118140960795 + 433097 * 2 ^ 59
def prefixEnd_433097 : Nat := 4983230072969 + 3 ^ 40 * 433097 * 2
def baseEnd_433097 : Nat := 222386931020397239695729

theorem tailTrace_433097 : CollatzResearch.WordTrace tailWord_433097 prefixEnd_433097 222386931020397239695729 := by
  unfold tailWord_433097
  simp only [CollatzResearch.WordTrace]
  refine ⟨15796345311971010923889545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10530896874647340615926363 15796345311971010923889545)
  ·
    refine ⟨11847258983978258192917159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15796345311971010923889545 11847258983978258192917159)
    ·
      refine ⟨17770888475967387289375739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11847258983978258192917159 17770888475967387289375739)
      ·
        refine ⟨26656332713951080934063609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17770888475967387289375739 26656332713951080934063609)
        ·
          refine ⟨19992249535463310700547707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26656332713951080934063609 19992249535463310700547707)
          ·
            refine ⟨29988374303194966050821561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19992249535463310700547707 29988374303194966050821561)
            ·
              refine ⟨22491280727396224538116171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29988374303194966050821561 22491280727396224538116171)
              ·
                refine ⟨33736921091094336807174257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22491280727396224538116171 33736921091094336807174257)
                ·
                  refine ⟨25302690818320752605380693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33736921091094336807174257 25302690818320752605380693)
                  ·
                    refine ⟨296515908027196319594305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25302690818320752605380693 296515908027196319594305)
                    ·
                      refine ⟨222386931020397239695729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 296515908027196319594305 222386931020397239695729)
                      ·
                        rfl

theorem cell23_433097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 8, 2].length) (baseStart_433097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433097 prefixEnd_433097 := by exact prefixLift 433097
  have htrace : WordTrace (prefixWord ++ tailWord_433097) baseStart_433097 baseEnd_433097 := by
    simpa [prefixWord, tailWord_433097, baseEnd_433097] using wordTrace_append hprefix tailTrace_433097
  have hstable : (prefixWord ++ tailWord_433097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433097).length < 2 ^ (prefixWord ++ tailWord_433097).sum := by decide
  have hdescent : baseEnd_433097 < baseStart_433097 := by decide
  rcases family_descends (prefixWord ++ tailWord_433097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433108 : List Nat := [2, 4, 1, 2, 1, 2, 4, 1, 2, 1, 3]
def baseStart_433108 : Nat := 118140960795 + 433108 * 2 ^ 59
def prefixEnd_433108 : Nat := 4983230072969 + 3 ^ 40 * 433108 * 2
def baseEnd_433108 : Nat := 222392579307596696658179

theorem tailTrace_433108 : CollatzResearch.WordTrace tailWord_433108 prefixEnd_433108 222392579307596696658179 := by
  unfold tailWord_433108
  simp only [CollatzResearch.WordTrace]
  refine ⟨7898373257465579901269989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10531164343287439868359985 7898373257465579901269989)
  ·
    refine ⟨1480944985774796231488123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7898373257465579901269989 1480944985774796231488123)
    ·
      refine ⟨2221417478662194347232185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1480944985774796231488123 2221417478662194347232185)
      ·
        refine ⟨1666063108996645760424139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2221417478662194347232185 1666063108996645760424139)
        ·
          refine ⟨2499094663494968640636209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1666063108996645760424139 2499094663494968640636209)
          ·
            refine ⟨1874320997621226480477157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2499094663494968640636209 1874320997621226480477157)
            ·
              refine ⟨351435187053979965089467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1874320997621226480477157 351435187053979965089467)
              ·
                refine ⟨527152780580969947634201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351435187053979965089467 527152780580969947634201)
                ·
                  refine ⟨395364585435727460725651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 527152780580969947634201 395364585435727460725651)
                  ·
                    refine ⟨593046878153591191088477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 395364585435727460725651 593046878153591191088477)
                    ·
                      refine ⟨222392579307596696658179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 593046878153591191088477 222392579307596696658179)
                      ·
                        rfl

theorem cell23_433108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_433108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433108 prefixEnd_433108 := by exact prefixLift 433108
  have htrace : WordTrace (prefixWord ++ tailWord_433108) baseStart_433108 baseEnd_433108 := by
    simpa [prefixWord, tailWord_433108, baseEnd_433108] using wordTrace_append hprefix tailTrace_433108
  have hstable : (prefixWord ++ tailWord_433108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433108).length < 2 ^ (prefixWord ++ tailWord_433108).sum := by decide
  have hdescent : baseEnd_433108 < baseStart_433108 := by decide
  rcases family_descends (prefixWord ++ tailWord_433108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433147 : List Nat := [1, 1, 1, 1, 1, 3, 3, 4, 2, 3, 3]
def baseStart_433147 : Nat := 118140960795 + 433147 * 2 ^ 59
def prefixEnd_433147 : Nat := 4983230072969 + 3 ^ 40 * 433147 * 2
def baseEnd_433147 : Nat := 222412605053122044070499

theorem tailTrace_433147 : CollatzResearch.WordTrace tailWord_433147 prefixEnd_433147 222412605053122044070499 := by
  unfold tailWord_433147
  simp only [CollatzResearch.WordTrace]
  refine ⟨15798168961789869463209695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10532112641193246308806463 15798168961789869463209695)
  ·
    refine ⟨23697253442684804194814543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15798168961789869463209695 23697253442684804194814543)
    ·
      refine ⟨35545880164027206292221815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23697253442684804194814543 35545880164027206292221815)
      ·
        refine ⟨53318820246040809438332723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35545880164027206292221815 53318820246040809438332723)
        ·
          refine ⟨79978230369061214157499085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53318820246040809438332723 79978230369061214157499085)
          ·
            refine ⟨29991836388397955309062157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79978230369061214157499085 29991836388397955309062157)
            ·
              refine ⟨11246938645649233240898309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29991836388397955309062157 11246938645649233240898309)
              ·
                refine ⟨2108800996059231232668433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11246938645649233240898309 2108800996059231232668433)
                ·
                  refine ⟨1581600747044423424501325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2108800996059231232668433 1581600747044423424501325)
                  ·
                    refine ⟨593100280141658784187997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1581600747044423424501325 593100280141658784187997)
                    ·
                      refine ⟨222412605053122044070499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 593100280141658784187997 222412605053122044070499)
                      ·
                        rfl

theorem cell23_433147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 3, 3].length) (baseStart_433147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433147 prefixEnd_433147 := by exact prefixLift 433147
  have htrace : WordTrace (prefixWord ++ tailWord_433147) baseStart_433147 baseEnd_433147 := by
    simpa [prefixWord, tailWord_433147, baseEnd_433147] using wordTrace_append hprefix tailTrace_433147
  have hstable : (prefixWord ++ tailWord_433147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433147).length < 2 ^ (prefixWord ++ tailWord_433147).sum := by decide
  have hdescent : baseEnd_433147 < baseStart_433147 := by decide
  rcases family_descends (prefixWord ++ tailWord_433147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433148 : List Nat := [2, 2, 2, 1, 2, 4, 2, 2, 2, 2, 2]
def baseStart_433148 : Nat := 118140960795 + 433148 * 2 ^ 59
def prefixEnd_433148 : Nat := 4983230072969 + 3 ^ 40 * 433148 * 2
def baseEnd_433148 : Nat := 222413118533776540157995

theorem tailTrace_433148 : CollatzResearch.WordTrace tailWord_433148 prefixEnd_433148 222413118533776540157995 := by
  unfold tailWord_433148
  simp only [CollatzResearch.WordTrace]
  refine ⟨7899102717393123316998049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10532136956524164422664065 7899102717393123316998049)
  ·
    refine ⟨5924327038044842487748537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7899102717393123316998049 5924327038044842487748537)
    ·
      refine ⟨4443245278533631865811403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5924327038044842487748537 4443245278533631865811403)
      ·
        refine ⟨6664867917800447798717105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4443245278533631865811403 6664867917800447798717105)
        ·
          refine ⟨4998650938350335849037829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6664867917800447798717105 4998650938350335849037829)
          ·
            refine ⟨937247050940687971694593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4998650938350335849037829 937247050940687971694593)
            ·
              refine ⟨702935288205515978770945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 937247050940687971694593 702935288205515978770945)
              ·
                refine ⟨527201466154136984078209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 702935288205515978770945 527201466154136984078209)
                ·
                  refine ⟨395401099615602738058657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 527201466154136984078209 395401099615602738058657)
                  ·
                    refine ⟨296550824711702053543993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 395401099615602738058657 296550824711702053543993)
                    ·
                      refine ⟨222413118533776540157995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 296550824711702053543993 222413118533776540157995)
                      ·
                        rfl

theorem cell23_433148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 2, 2, 2].length) (baseStart_433148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433148 prefixEnd_433148 := by exact prefixLift 433148
  have htrace : WordTrace (prefixWord ++ tailWord_433148) baseStart_433148 baseEnd_433148 := by
    simpa [prefixWord, tailWord_433148, baseEnd_433148] using wordTrace_append hprefix tailTrace_433148
  have hstable : (prefixWord ++ tailWord_433148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433148).length < 2 ^ (prefixWord ++ tailWord_433148).sum := by decide
  have hdescent : baseEnd_433148 < baseStart_433148 := by decide
  rcases family_descends (prefixWord ++ tailWord_433148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433164 : List Nat := [2, 2, 1, 2, 3, 3, 1, 1, 2, 3, 3]
def baseStart_433164 : Nat := 118140960795 + 433164 * 2 ^ 59
def prefixEnd_433164 : Nat := 4983230072969 + 3 ^ 40 * 433164 * 2
def baseEnd_433164 : Nat := 222421334224248477557921

theorem tailTrace_433164 : CollatzResearch.WordTrace tailWord_433164 prefixEnd_433164 222421334224248477557921 := by
  unfold tailWord_433164
  simp only [CollatzResearch.WordTrace]
  refine ⟨7899394501364140683289273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10532526001818854244385697 7899394501364140683289273)
  ·
    refine ⟨5924545876023105512466955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7899394501364140683289273 5924545876023105512466955)
    ·
      refine ⟨8886818814034658268700433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5924545876023105512466955 8886818814034658268700433)
      ·
        refine ⟨6665114110525993701525325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8886818814034658268700433 6665114110525993701525325)
        ·
          refine ⟨2499417791447247638071997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6665114110525993701525325 2499417791447247638071997)
          ·
            refine ⟨937281671792717864276999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2499417791447247638071997 937281671792717864276999)
            ·
              refine ⟨1405922507689076796415499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 937281671792717864276999 1405922507689076796415499)
              ·
                refine ⟨2108883761533615194623249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1405922507689076796415499 2108883761533615194623249)
                ·
                  refine ⟨1581662821150211395967437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2108883761533615194623249 1581662821150211395967437)
                  ·
                    refine ⟨593123557931329273487789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1581662821150211395967437 593123557931329273487789)
                    ·
                      refine ⟨222421334224248477557921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 593123557931329273487789 222421334224248477557921)
                      ·
                        rfl

theorem cell23_433164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_433164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433164 prefixEnd_433164 := by exact prefixLift 433164
  have htrace : WordTrace (prefixWord ++ tailWord_433164) baseStart_433164 baseEnd_433164 := by
    simpa [prefixWord, tailWord_433164, baseEnd_433164] using wordTrace_append hprefix tailTrace_433164
  have hstable : (prefixWord ++ tailWord_433164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433164).length < 2 ^ (prefixWord ++ tailWord_433164).sum := by decide
  have hdescent : baseEnd_433164 < baseStart_433164 := by decide
  rcases family_descends (prefixWord ++ tailWord_433164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433297 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 5]
def baseStart_433297 : Nat := 118140960795 + 433297 * 2 ^ 59
def prefixEnd_433297 : Nat := 4983230072969 + 3 ^ 40 * 433297 * 2
def baseEnd_433297 : Nat := 222489627151296457194809

theorem tailTrace_433297 : CollatzResearch.WordTrace tailWord_433297 prefixEnd_433297 222489627151296457194809 := by
  unfold tailWord_433297
  simp only [CollatzResearch.WordTrace]
  refine ⟨15803639911246445081170145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10535759940830963387446763 15803639911246445081170145)
  ·
    refine ⟨11852729933434833810877609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15803639911246445081170145 11852729933434833810877609)
    ·
      refine ⟨8889547450076125358158207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11852729933434833810877609 8889547450076125358158207)
      ·
        refine ⟨13334321175114188037237311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8889547450076125358158207 13334321175114188037237311)
        ·
          refine ⟨20001481762671282055855967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13334321175114188037237311 20001481762671282055855967)
          ·
            refine ⟨30002222644006923083783951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20001481762671282055855967 30002222644006923083783951)
            ·
              refine ⟨45003333966010384625675927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30002222644006923083783951 45003333966010384625675927)
              ·
                refine ⟨67505000949015576938513891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45003333966010384625675927 67505000949015576938513891)
                ·
                  refine ⟨101257501423523365407770837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67505000949015576938513891 101257501423523365407770837)
                  ·
                    refine ⟨2373222689613828876744629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 101257501423523365407770837 2373222689613828876744629)
                    ·
                      refine ⟨222489627151296457194809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2373222689613828876744629 222489627151296457194809)
                      ·
                        rfl

theorem cell23_433297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_433297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433297 prefixEnd_433297 := by exact prefixLift 433297
  have htrace : WordTrace (prefixWord ++ tailWord_433297) baseStart_433297 baseEnd_433297 := by
    simpa [prefixWord, tailWord_433297, baseEnd_433297] using wordTrace_append hprefix tailTrace_433297
  have hstable : (prefixWord ++ tailWord_433297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433297).length < 2 ^ (prefixWord ++ tailWord_433297).sum := by decide
  have hdescent : baseEnd_433297 < baseStart_433297 := by decide
  rcases family_descends (prefixWord ++ tailWord_433297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433298 : List Nat := [3, 2, 3, 1, 1, 2, 1, 3, 2, 3, 2]
def baseStart_433298 : Nat := 118140960795 + 433298 * 2 ^ 59
def prefixEnd_433298 : Nat := 4983230072969 + 3 ^ 40 * 433298 * 2
def baseEnd_433298 : Nat := 222490140631950953282305

theorem tailTrace_433298 : CollatzResearch.WordTrace tailWord_433298 prefixEnd_433298 222490140631950953282305 := by
  unfold tailWord_433298
  simp only [CollatzResearch.WordTrace]
  refine ⟨3950919096060705562989137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10535784256161881501304365 3950919096060705562989137)
  ·
    refine ⟨2963189322045529172241853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3950919096060705562989137 2963189322045529172241853)
    ·
      refine ⟨1111195995767073439590695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2963189322045529172241853 1111195995767073439590695)
      ·
        refine ⟨1666793993650610159386043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1111195995767073439590695 1666793993650610159386043)
        ·
          refine ⟨2500190990475915239079065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1666793993650610159386043 2500190990475915239079065)
          ·
            refine ⟨1875143242856936429309299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2500190990475915239079065 1875143242856936429309299)
            ·
              refine ⟨2812714864285404643963949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1875143242856936429309299 2812714864285404643963949)
              ·
                refine ⟨1054768074107026741486481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2812714864285404643963949 1054768074107026741486481)
                ·
                  refine ⟨791076055580270056114861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1054768074107026741486481 791076055580270056114861)
                  ·
                    refine ⟨296653520842601271043073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 791076055580270056114861 296653520842601271043073)
                    ·
                      refine ⟨222490140631950953282305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 296653520842601271043073 222490140631950953282305)
                      ·
                        rfl

theorem cell23_433298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_433298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433298 prefixEnd_433298 := by exact prefixLift 433298
  have htrace : WordTrace (prefixWord ++ tailWord_433298) baseStart_433298 baseEnd_433298 := by
    simpa [prefixWord, tailWord_433298, baseEnd_433298] using wordTrace_append hprefix tailTrace_433298
  have hstable : (prefixWord ++ tailWord_433298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433298).length < 2 ^ (prefixWord ++ tailWord_433298).sum := by decide
  have hdescent : baseEnd_433298 < baseStart_433298 := by decide
  rcases family_descends (prefixWord ++ tailWord_433298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433304 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 3, 6]
def baseStart_433304 : Nat := 118140960795 + 433304 * 2 ^ 59
def prefixEnd_433304 : Nat := 4983230072969 + 3 ^ 40 * 433304 * 2
def baseEnd_433304 : Nat := 74164407171959309935759

theorem tailTrace_433304 : CollatzResearch.WordTrace tailWord_433304 prefixEnd_433304 74164407171959309935759 := by
  unfold tailWord_433304
  simp only [CollatzResearch.WordTrace]
  refine ⟨7901947611110542638337483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10535930148147390184449977 7901947611110542638337483)
  ·
    refine ⟨11852921416665813957506225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7901947611110542638337483 11852921416665813957506225)
    ·
      refine ⟨8889691062499360468129669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11852921416665813957506225 8889691062499360468129669)
      ·
        refine ⟨1666817074218630087774313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8889691062499360468129669 1666817074218630087774313)
        ·
          refine ⟨1250112805663972565830735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1666817074218630087774313 1250112805663972565830735)
          ·
            refine ⟨1875169208495958848746103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1250112805663972565830735 1875169208495958848746103)
            ·
              refine ⟨2812753812743938273119155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1875169208495958848746103 2812753812743938273119155)
              ·
                refine ⟨4219130719115907409678733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2812753812743938273119155 4219130719115907409678733)
                ·
                  refine ⟨1582174019668465278629525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4219130719115907409678733 1582174019668465278629525)
                  ·
                    refine ⟨74164407171959309935759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1582174019668465278629525 74164407171959309935759)
                    ·
                      rfl

theorem cell23_433304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 3, 6].length) (baseStart_433304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433304 prefixEnd_433304 := by exact prefixLift 433304
  have htrace : WordTrace (prefixWord ++ tailWord_433304) baseStart_433304 baseEnd_433304 := by
    simpa [prefixWord, tailWord_433304, baseEnd_433304] using wordTrace_append hprefix tailTrace_433304
  have hstable : (prefixWord ++ tailWord_433304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433304).length < 2 ^ (prefixWord ++ tailWord_433304).sum := by decide
  have hdescent : baseEnd_433304 < baseStart_433304 := by decide
  rcases family_descends (prefixWord ++ tailWord_433304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433307 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 6]
def baseStart_433307 : Nat := 118140960795 + 433307 * 2 ^ 59
def prefixEnd_433307 : Nat := 4983230072969 + 3 ^ 40 * 433307 * 2
def baseEnd_433307 : Nat := 222494761957841418069763

theorem tailTrace_433307 : CollatzResearch.WordTrace tailWord_433307 prefixEnd_433307 222494761957841418069763 := by
  unfold tailWord_433307
  simp only [CollatzResearch.WordTrace]
  refine ⟨15804004641210216789034175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10536003094140144526022783 15804004641210216789034175)
  ·
    refine ⟨23706006961815325183551263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15804004641210216789034175 23706006961815325183551263)
    ·
      refine ⟨35559010442722987775326895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23706006961815325183551263 35559010442722987775326895)
      ·
        refine ⟨53338515664084481662990343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35559010442722987775326895 53338515664084481662990343)
        ·
          refine ⟨80007773496126722494485515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53338515664084481662990343 80007773496126722494485515)
          ·
            refine ⟨120011660244190083741728273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80007773496126722494485515 120011660244190083741728273)
            ·
              refine ⟨90008745183142562806296205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120011660244190083741728273 90008745183142562806296205)
              ·
                refine ⟨33753279443678461052361077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90008745183142562806296205 33753279443678461052361077)
                ·
                  refine ⟨3164369947844855723658851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33753279443678461052361077 3164369947844855723658851)
                  ·
                    refine ⟨4746554921767283585488277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3164369947844855723658851 4746554921767283585488277)
                    ·
                      refine ⟨222494761957841418069763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4746554921767283585488277 222494761957841418069763)
                      ·
                        rfl

theorem cell23_433307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 6].length) (baseStart_433307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433307 prefixEnd_433307 := by exact prefixLift 433307
  have htrace : WordTrace (prefixWord ++ tailWord_433307) baseStart_433307 baseEnd_433307 := by
    simpa [prefixWord, tailWord_433307, baseEnd_433307] using wordTrace_append hprefix tailTrace_433307
  have hstable : (prefixWord ++ tailWord_433307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433307).length < 2 ^ (prefixWord ++ tailWord_433307).sum := by decide
  have hdescent : baseEnd_433307 < baseStart_433307 := by decide
  rcases family_descends (prefixWord ++ tailWord_433307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433308 : List Nat := [2, 2, 3, 2, 1, 3, 3, 1, 1, 5]
def baseStart_433308 : Nat := 118140960795 + 433308 * 2 ^ 59
def prefixEnd_433308 : Nat := 4983230072969 + 3 ^ 40 * 433308 * 2
def baseEnd_433308 : Nat := 74165091812831971385753

theorem tailTrace_433308 : CollatzResearch.WordTrace tailWord_433308 prefixEnd_433308 74165091812831971385753 := by
  unfold tailWord_433308
  simp only [CollatzResearch.WordTrace]
  refine ⟨7902020557103296979910289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10536027409471062639880385 7902020557103296979910289)
  ·
    refine ⟨5926515417827472734932717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7902020557103296979910289 5926515417827472734932717)
    ·
      refine ⟨2222443281685302275599769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5926515417827472734932717 2222443281685302275599769)
      ·
        refine ⟨1666832461263976706699827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2222443281685302275599769 1666832461263976706699827)
        ·
          refine ⟨2500248691895965060049741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1666832461263976706699827 2500248691895965060049741)
          ·
            refine ⟨937593259460986897518653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2500248691895965060049741 937593259460986897518653)
            ·
              refine ⟨351597472297870086569495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 937593259460986897518653 351597472297870086569495)
              ·
                refine ⟨527396208446805129854243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351597472297870086569495 527396208446805129854243)
                ·
                  refine ⟨791094312670207694781365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 527396208446805129854243 791094312670207694781365)
                  ·
                    refine ⟨74165091812831971385753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 791094312670207694781365 74165091812831971385753)
                    ·
                      rfl

theorem cell23_433308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_433308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433308 prefixEnd_433308 := by exact prefixLift 433308
  have htrace : WordTrace (prefixWord ++ tailWord_433308) baseStart_433308 baseEnd_433308 := by
    simpa [prefixWord, tailWord_433308, baseEnd_433308] using wordTrace_append hprefix tailTrace_433308
  have hstable : (prefixWord ++ tailWord_433308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433308).length < 2 ^ (prefixWord ++ tailWord_433308).sum := by decide
  have hdescent : baseEnd_433308 < baseStart_433308 := by decide
  rcases family_descends (prefixWord ++ tailWord_433308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433317 : List Nat := [1, 3, 1, 2, 1, 15]
def baseStart_433317 : Nat := 118140960795 + 433317 * 2 ^ 59
def prefixEnd_433317 : Nat := 4983230072969 + 3 ^ 40 * 433317 * 2
def baseEnd_433317 : Nat := 915637435244388390719

theorem tailTrace_433317 : CollatzResearch.WordTrace tailWord_433317 prefixEnd_433317 915637435244388390719 := by
  unfold tailWord_433317
  simp only [CollatzResearch.WordTrace]
  refine ⟨15804369371173988496898205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10536246247449325664598803 15804369371173988496898205)
  ·
    refine ⟨5926638514190245686336827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15804369371173988496898205 5926638514190245686336827)
    ·
      refine ⟨8889957771285368529505241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5926638514190245686336827 8889957771285368529505241)
      ·
        refine ⟨6667468328464026397128931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8889957771285368529505241 6667468328464026397128931)
        ·
          refine ⟨10001202492696039595693397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6667468328464026397128931 10001202492696039595693397)
          ·
            refine ⟨915637435244388390719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 10001202492696039595693397 915637435244388390719)
            ·
              rfl

theorem cell23_433317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 15].length) (baseStart_433317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433317 prefixEnd_433317 := by exact prefixLift 433317
  have htrace : WordTrace (prefixWord ++ tailWord_433317) baseStart_433317 baseEnd_433317 := by
    simpa [prefixWord, tailWord_433317, baseEnd_433317] using wordTrace_append hprefix tailTrace_433317
  have hstable : (prefixWord ++ tailWord_433317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433317).length < 2 ^ (prefixWord ++ tailWord_433317).sum := by decide
  have hdescent : baseEnd_433317 < baseStart_433317 := by decide
  rcases family_descends (prefixWord ++ tailWord_433317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433322 : List Nat := [3, 1, 5, 1, 1, 2, 1, 4, 1, 1, 3]
def baseStart_433322 : Nat := 118140960795 + 433322 * 2 ^ 59
def prefixEnd_433322 : Nat := 4983230072969 + 3 ^ 40 * 433322 * 2
def baseEnd_433322 : Nat := 222502464167658859382195

theorem tailTrace_433322 : CollatzResearch.WordTrace tailWord_433322 prefixEnd_433322 222502464167658859382195 := by
  unfold tailWord_433322
  simp only [CollatzResearch.WordTrace]
  refine ⟨3951137934038968587707555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10536367824103916233886813 3951137934038968587707555)
  ·
    refine ⟨5926706901058452881561333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3951137934038968587707555 5926706901058452881561333)
    ·
      refine ⟨555628771974229957646375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5926706901058452881561333 555628771974229957646375)
      ·
        refine ⟨833443157961344936469563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555628771974229957646375 833443157961344936469563)
        ·
          refine ⟨1250164736942017404704345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 833443157961344936469563 1250164736942017404704345)
          ·
            refine ⟨937623552706513053528259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1250164736942017404704345 937623552706513053528259)
            ·
              refine ⟨1406435329059769580292389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 937623552706513053528259 1406435329059769580292389)
              ·
                refine ⟨263706624198706796304823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1406435329059769580292389 263706624198706796304823)
                ·
                  refine ⟨395559936298060194457235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 263706624198706796304823 395559936298060194457235)
                  ·
                    refine ⟨593339904447090291685853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 395559936298060194457235 593339904447090291685853)
                    ·
                      refine ⟨222502464167658859382195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 593339904447090291685853 222502464167658859382195)
                      ·
                        rfl

theorem cell23_433322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_433322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433322 prefixEnd_433322 := by exact prefixLift 433322
  have htrace : WordTrace (prefixWord ++ tailWord_433322) baseStart_433322 baseEnd_433322 := by
    simpa [prefixWord, tailWord_433322, baseEnd_433322] using wordTrace_append hprefix tailTrace_433322
  have hstable : (prefixWord ++ tailWord_433322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433322).length < 2 ^ (prefixWord ++ tailWord_433322).sum := by decide
  have hdescent : baseEnd_433322 < baseStart_433322 := by decide
  rcases family_descends (prefixWord ++ tailWord_433322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433345 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 5, 2, 2]
def baseStart_433345 : Nat := 118140960795 + 433345 * 2 ^ 59
def prefixEnd_433345 : Nat := 4983230072969 + 3 ^ 40 * 433345 * 2
def baseEnd_433345 : Nat := 222514274222712269394589

theorem tailTrace_433345 : CollatzResearch.WordTrace tailWord_433345 prefixEnd_433345 222514274222712269394589 := by
  unfold tailWord_433345
  simp only [CollatzResearch.WordTrace]
  refine ⟨15805390615072549278917489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10536927076715032852611659 15805390615072549278917489)
  ·
    refine ⟨11854042961304411959188117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15805390615072549278917489 11854042961304411959188117)
    ·
      refine ⟨555658263811144310586943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11854042961304411959188117 555658263811144310586943)
      ·
        refine ⟨833487395716716465880415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555658263811144310586943 833487395716716465880415)
        ·
          refine ⟨1250231093575074698820623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 833487395716716465880415 1250231093575074698820623)
          ·
            refine ⟨1875346640362612048230935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1250231093575074698820623 1875346640362612048230935)
            ·
              refine ⟨2813019960543918072346403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1875346640362612048230935 2813019960543918072346403)
              ·
                refine ⟨4219529940815877108519605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2813019960543918072346403 4219529940815877108519605)
                ·
                  refine ⟨395580931951488478923713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4219529940815877108519605 395580931951488478923713)
                  ·
                    refine ⟨296685698963616359192785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 395580931951488478923713 296685698963616359192785)
                    ·
                      refine ⟨222514274222712269394589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 296685698963616359192785 222514274222712269394589)
                      ·
                        rfl

theorem cell23_433345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_433345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433345 prefixEnd_433345 := by exact prefixLift 433345
  have htrace : WordTrace (prefixWord ++ tailWord_433345) baseStart_433345 baseEnd_433345 := by
    simpa [prefixWord, tailWord_433345, baseEnd_433345] using wordTrace_append hprefix tailTrace_433345
  have hstable : (prefixWord ++ tailWord_433345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433345).length < 2 ^ (prefixWord ++ tailWord_433345).sum := by decide
  have hdescent : baseEnd_433345 < baseStart_433345 := by decide
  rcases family_descends (prefixWord ++ tailWord_433345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433361 : List Nat := [1, 2, 2, 1, 2, 2, 1, 4, 4, 1, 3]
def baseStart_433361 : Nat := 118140960795 + 433361 * 2 ^ 59
def prefixEnd_433361 : Nat := 4983230072969 + 3 ^ 40 * 433361 * 2
def baseEnd_433361 : Nat := 222522489913184206794515

theorem tailTrace_433361 : CollatzResearch.WordTrace tailWord_433361 prefixEnd_433361 222522489913184206794515 := by
  unfold tailWord_433361
  simp only [CollatzResearch.WordTrace]
  refine ⟨15805974183014584011499937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10537316122009722674333291 15805974183014584011499937)
  ·
    refine ⟨11854480637260938008624953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15805974183014584011499937 11854480637260938008624953)
    ·
      refine ⟨8890860477945703506468715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11854480637260938008624953 8890860477945703506468715)
      ·
        refine ⟨13336290716918555259703073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8890860477945703506468715 13336290716918555259703073)
        ·
          refine ⟨10002218037688916444777305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13336290716918555259703073 10002218037688916444777305)
          ·
            refine ⟨7501663528266687333582979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10002218037688916444777305 7501663528266687333582979)
            ·
              refine ⟨11252495292400031000374469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7501663528266687333582979 11252495292400031000374469)
              ·
                refine ⟨2109842867325005812570213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11252495292400031000374469 2109842867325005812570213)
                ·
                  refine ⟨395595537623438589856915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2109842867325005812570213 395595537623438589856915)
                  ·
                    refine ⟨593393306435157884785373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 395595537623438589856915 593393306435157884785373)
                    ·
                      refine ⟨222522489913184206794515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 593393306435157884785373 222522489913184206794515)
                      ·
                        rfl

theorem cell23_433361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 4, 1, 3].length) (baseStart_433361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433361 prefixEnd_433361 := by exact prefixLift 433361
  have htrace : WordTrace (prefixWord ++ tailWord_433361) baseStart_433361 baseEnd_433361 := by
    simpa [prefixWord, tailWord_433361, baseEnd_433361] using wordTrace_append hprefix tailTrace_433361
  have hstable : (prefixWord ++ tailWord_433361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433361).length < 2 ^ (prefixWord ++ tailWord_433361).sum := by decide
  have hdescent : baseEnd_433361 < baseStart_433361 := by decide
  rcases family_descends (prefixWord ++ tailWord_433361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433362 : List Nat := [3, 2, 2, 2, 1, 1, 4, 3, 1, 2, 2]
def baseStart_433362 : Nat := 118140960795 + 433362 * 2 ^ 59
def prefixEnd_433362 : Nat := 4983230072969 + 3 ^ 40 * 433362 * 2
def baseEnd_433362 : Nat := 222523003393838702882011

theorem tailTrace_433362 : CollatzResearch.WordTrace tailWord_433362 prefixEnd_433362 222523003393838702882011 := by
  unfold tailWord_433362
  simp only [CollatzResearch.WordTrace]
  refine ⟨3951502664002740295571585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10537340437340640788190893 3951502664002740295571585)
  ·
    refine ⟨2963626998002055221678689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3951502664002740295571585 2963626998002055221678689)
    ·
      refine ⟨2222720248501541416259017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2963626998002055221678689 2222720248501541416259017)
      ·
        refine ⟨1667040186376156062194263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2222720248501541416259017 1667040186376156062194263)
        ·
          refine ⟨2500560279564234093291395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1667040186376156062194263 2500560279564234093291395)
          ·
            refine ⟨3750840419346351139937093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2500560279564234093291395 3750840419346351139937093)
            ·
              refine ⟨703282578627440838738205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3750840419346351139937093 703282578627440838738205)
              ·
                refine ⟨263730966985290314526827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 703282578627440838738205 263730966985290314526827)
                ·
                  refine ⟨395596450477935471790241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 263730966985290314526827 395596450477935471790241)
                  ·
                    refine ⟨296697337858451603842681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 395596450477935471790241 296697337858451603842681)
                    ·
                      refine ⟨222523003393838702882011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 296697337858451603842681 222523003393838702882011)
                      ·
                        rfl

theorem cell23_433362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_433362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433362 prefixEnd_433362 := by exact prefixLift 433362
  have htrace : WordTrace (prefixWord ++ tailWord_433362) baseStart_433362 baseEnd_433362 := by
    simpa [prefixWord, tailWord_433362, baseEnd_433362] using wordTrace_append hprefix tailTrace_433362
  have hstable : (prefixWord ++ tailWord_433362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433362).length < 2 ^ (prefixWord ++ tailWord_433362).sum := by decide
  have hdescent : baseEnd_433362 < baseStart_433362 := by decide
  rcases family_descends (prefixWord ++ tailWord_433362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433365 : List Nat := [1, 3, 2, 4, 1, 1, 4, 1, 1, 2, 3]
def baseStart_433365 : Nat := 118140960795 + 433365 * 2 ^ 59
def prefixEnd_433365 : Nat := 4983230072969 + 3 ^ 40 * 433365 * 2
def baseEnd_433365 : Nat := 222524543835802191144497

theorem tailTrace_433365 : CollatzResearch.WordTrace tailWord_433365 prefixEnd_433365 222524543835802191144497 := by
  unfold tailWord_433365
  simp only [CollatzResearch.WordTrace]
  refine ⟨15806120075000092694645549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10537413383333395129763699 15806120075000092694645549)
  ·
    refine ⟨5927295028125034760492081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15806120075000092694645549 5927295028125034760492081)
    ·
      refine ⟨4445471271093776070369061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5927295028125034760492081 4445471271093776070369061)
      ·
        refine ⟨833525863330083013194199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4445471271093776070369061 833525863330083013194199)
        ·
          refine ⟨1250288794995124519791299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 833525863330083013194199 1250288794995124519791299)
          ·
            refine ⟨1875433192492686779686949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1250288794995124519791299 1875433192492686779686949)
            ·
              refine ⟨351643723592378771191303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1875433192492686779686949 351643723592378771191303)
              ·
                refine ⟨527465585388568156786955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351643723592378771191303 527465585388568156786955)
                ·
                  refine ⟨791198378082852235180433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 527465585388568156786955 791198378082852235180433)
                  ·
                    refine ⟨593398783562139176385325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 791198378082852235180433 593398783562139176385325)
                    ·
                      refine ⟨222524543835802191144497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 593398783562139176385325 222524543835802191144497)
                      ·
                        rfl

theorem cell23_433365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_433365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433365 prefixEnd_433365 := by exact prefixLift 433365
  have htrace : WordTrace (prefixWord ++ tailWord_433365) baseStart_433365 baseEnd_433365 := by
    simpa [prefixWord, tailWord_433365, baseEnd_433365] using wordTrace_append hprefix tailTrace_433365
  have hstable : (prefixWord ++ tailWord_433365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433365).length < 2 ^ (prefixWord ++ tailWord_433365).sum := by decide
  have hdescent : baseEnd_433365 < baseStart_433365 := by decide
  rcases family_descends (prefixWord ++ tailWord_433365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433395 : List Nat := [1, 1, 1, 2, 2, 6, 3, 1, 2, 1, 3]
def baseStart_433395 : Nat := 118140960795 + 433395 * 2 ^ 59
def prefixEnd_433395 : Nat := 4983230072969 + 3 ^ 40 * 433395 * 2
def baseEnd_433395 : Nat := 222539948255437073769359

theorem tailTrace_433395 : CollatzResearch.WordTrace tailWord_433395 prefixEnd_433395 222539948255437073769359 := by
  unfold tailWord_433395
  simp only [CollatzResearch.WordTrace]
  refine ⟨15807214264891407818237639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10538142843260938545491759 15807214264891407818237639)
  ·
    refine ⟨23710821397337111727356459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15807214264891407818237639 23710821397337111727356459)
    ·
      refine ⟨35566232096005667591034689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23710821397337111727356459 35566232096005667591034689)
      ·
        refine ⟨26674674072004250693276017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35566232096005667591034689 26674674072004250693276017)
        ·
          refine ⟨20006005554003188019957013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26674674072004250693276017 20006005554003188019957013)
          ·
            refine ⟨937781510343899438435485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20006005554003188019957013 937781510343899438435485)
            ·
              refine ⟨351668066378962289413307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 937781510343899438435485 351668066378962289413307)
              ·
                refine ⟨527502099568443434119961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351668066378962289413307 527502099568443434119961)
                ·
                  refine ⟨395626574676332575589971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 527502099568443434119961 395626574676332575589971)
                  ·
                    refine ⟨593439862014498863384957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 395626574676332575589971 593439862014498863384957)
                    ·
                      refine ⟨222539948255437073769359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 593439862014498863384957 222539948255437073769359)
                      ·
                        rfl

theorem cell23_433395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 2, 1, 3].length) (baseStart_433395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433395 prefixEnd_433395 := by exact prefixLift 433395
  have htrace : WordTrace (prefixWord ++ tailWord_433395) baseStart_433395 baseEnd_433395 := by
    simpa [prefixWord, tailWord_433395, baseEnd_433395] using wordTrace_append hprefix tailTrace_433395
  have hstable : (prefixWord ++ tailWord_433395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433395).length < 2 ^ (prefixWord ++ tailWord_433395).sum := by decide
  have hdescent : baseEnd_433395 < baseStart_433395 := by decide
  rcases family_descends (prefixWord ++ tailWord_433395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433464 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 3, 1, 7]
def baseStart_433464 : Nat := 118140960795 + 433464 * 2 ^ 59
def prefixEnd_433464 : Nat := 4983230072969 + 3 ^ 40 * 433464 * 2
def baseEnd_433464 : Nat := 222575378420597303806541

theorem tailTrace_433464 : CollatzResearch.WordTrace tailWord_433464 prefixEnd_433464 222575378420597303806541 := by
  unfold tailWord_433464
  simp only [CollatzResearch.WordTrace]
  refine ⟨7904865450820716301249723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10539820601094288401666297 7904865450820716301249723)
  ·
    refine ⟨11857298176231074451874585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7904865450820716301249723 11857298176231074451874585)
    ·
      refine ⟨8892973632173305838905939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11857298176231074451874585 8892973632173305838905939)
      ·
        refine ⟨13339460448259958758358909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8892973632173305838905939 13339460448259958758358909)
        ·
          refine ⟨5002297668097484534384591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13339460448259958758358909 5002297668097484534384591)
          ·
            refine ⟨7503446502146226801576887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5002297668097484534384591 7503446502146226801576887)
            ·
              refine ⟨11255169753219340202365331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7503446502146226801576887 11255169753219340202365331)
              ·
                refine ⟨16882754629829010303547997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11255169753219340202365331 16882754629829010303547997)
                ·
                  refine ⟨6331032986185878863830499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16882754629829010303547997 6331032986185878863830499)
                  ·
                    refine ⟨9496549479278818295745749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6331032986185878863830499 9496549479278818295745749)
                    ·
                      refine ⟨222575378420597303806541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 9496549479278818295745749 222575378420597303806541)
                      ·
                        rfl

theorem cell23_433464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_433464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433464 prefixEnd_433464 := by exact prefixLift 433464
  have htrace : WordTrace (prefixWord ++ tailWord_433464) baseStart_433464 baseEnd_433464 := by
    simpa [prefixWord, tailWord_433464, baseEnd_433464] using wordTrace_append hprefix tailTrace_433464
  have hstable : (prefixWord ++ tailWord_433464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433464).length < 2 ^ (prefixWord ++ tailWord_433464).sum := by decide
  have hdescent : baseEnd_433464 < baseStart_433464 := by decide
  rcases family_descends (prefixWord ++ tailWord_433464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433471 : List Nat := [1, 1, 2, 2, 4, 2, 1, 3, 2, 5]
def baseStart_433471 : Nat := 118140960795 + 433471 * 2 ^ 59
def prefixEnd_433471 : Nat := 4983230072969 + 3 ^ 40 * 433471 * 2
def baseEnd_433471 : Nat := 74192990928392925473003

theorem tailTrace_433471 : CollatzResearch.WordTrace tailWord_433471 prefixEnd_433471 74192990928392925473003 := by
  unfold tailWord_433471
  simp only [CollatzResearch.WordTrace]
  refine ⟨15809986212616072798004267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10539990808410715198669511 15809986212616072798004267)
  ·
    refine ⟨23714979318924109197006401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15809986212616072798004267 23714979318924109197006401)
    ·
      refine ⟨17786234489193081897754801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23714979318924109197006401 17786234489193081897754801)
      ·
        refine ⟨13339675866894811423316101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17786234489193081897754801 13339675866894811423316101)
        ·
          refine ⟨2501189225042777141871769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13339675866894811423316101 2501189225042777141871769)
          ·
            refine ⟨1875891918782082856403827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2501189225042777141871769 1875891918782082856403827)
            ·
              refine ⟨2813837878173124284605741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1875891918782082856403827 2813837878173124284605741)
              ·
                refine ⟨1055189204314921606727153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2813837878173124284605741 1055189204314921606727153)
                ·
                  refine ⟨791391903236191205045365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1055189204314921606727153 791391903236191205045365)
                  ·
                    refine ⟨74192990928392925473003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 791391903236191205045365 74192990928392925473003)
                    ·
                      rfl

theorem cell23_433471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 5].length) (baseStart_433471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433471 prefixEnd_433471 := by exact prefixLift 433471
  have htrace : WordTrace (prefixWord ++ tailWord_433471) baseStart_433471 baseEnd_433471 := by
    simpa [prefixWord, tailWord_433471, baseEnd_433471] using wordTrace_append hprefix tailTrace_433471
  have hstable : (prefixWord ++ tailWord_433471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433471).length < 2 ^ (prefixWord ++ tailWord_433471).sum := by decide
  have hdescent : baseEnd_433471 < baseStart_433471 := by decide
  rcases family_descends (prefixWord ++ tailWord_433471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433491 : List Nat := [1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 4]
def baseStart_433491 : Nat := 118140960795 + 433491 * 2 ^ 59
def prefixEnd_433491 : Nat := 4983230072969 + 3 ^ 40 * 433491 * 2
def baseEnd_433491 : Nat := 222589242398268698168917

theorem tailTrace_433491 : CollatzResearch.WordTrace tailWord_433491 prefixEnd_433491 222589242398268698168917 := by
  unfold tailWord_433491
  simp only [CollatzResearch.WordTrace]
  refine ⟨15810715672543616213732327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10540477115029077475821551 15810715672543616213732327)
  ·
    refine ⟨23716073508815424320598491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15810715672543616213732327 23716073508815424320598491)
    ·
      refine ⟨35574110263223136480897737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23716073508815424320598491 35574110263223136480897737)
      ·
        refine ⟨26680582697417352360673303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35574110263223136480897737 26680582697417352360673303)
        ·
          refine ⟨40020874046126028541009955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26680582697417352360673303 40020874046126028541009955)
          ·
            refine ⟨60031311069189042811514933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40020874046126028541009955 60031311069189042811514933)
            ·
              refine ⟨5627935412736472763579525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60031311069189042811514933 5627935412736472763579525)
              ·
                refine ⟨1055237889888088643171161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5627935412736472763579525 1055237889888088643171161)
                ·
                  refine ⟨791428417416066482378371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1055237889888088643171161 791428417416066482378371)
                  ·
                    refine ⟨1187142626124099723567557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 791428417416066482378371 1187142626124099723567557)
                    ·
                      refine ⟨222589242398268698168917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1187142626124099723567557 222589242398268698168917)
                      ·
                        rfl

theorem cell23_433491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 4].length) (baseStart_433491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433491 prefixEnd_433491 := by exact prefixLift 433491
  have htrace : WordTrace (prefixWord ++ tailWord_433491) baseStart_433491 baseEnd_433491 := by
    simpa [prefixWord, tailWord_433491, baseEnd_433491] using wordTrace_append hprefix tailTrace_433491
  have hstable : (prefixWord ++ tailWord_433491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433491).length < 2 ^ (prefixWord ++ tailWord_433491).sum := by decide
  have hdescent : baseEnd_433491 < baseStart_433491 := by decide
  rcases family_descends (prefixWord ++ tailWord_433491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433508 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 1, 6, 2]
def baseStart_433508 : Nat := 118140960795 + 433508 * 2 ^ 59
def prefixEnd_433508 : Nat := 4983230072969 + 3 ^ 40 * 433508 * 2
def baseEnd_433508 : Nat := 222597971569395131656339

theorem tailTrace_433508 : CollatzResearch.WordTrace tailWord_433508 prefixEnd_433508 222597971569395131656339 := by
  unfold tailWord_433508
  simp only [CollatzResearch.WordTrace]
  refine ⟨7905667856741014058550589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10540890475654685411400785 7905667856741014058550589)
  ·
    refine ⟨2964625446277880271956471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7905667856741014058550589 2964625446277880271956471)
    ·
      refine ⟨4446938169416820407934707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2964625446277880271956471 4446938169416820407934707)
      ·
        refine ⟨6670407254125230611902061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4446938169416820407934707 6670407254125230611902061)
        ·
          refine ⟨2501402720296961479463273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6670407254125230611902061 2501402720296961479463273)
          ·
            refine ⟨1876052040222721109597455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2501402720296961479463273 1876052040222721109597455)
            ·
              refine ⟨2814078060334081664396183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1876052040222721109597455 2814078060334081664396183)
              ·
                refine ⟨4221117090501122496594275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2814078060334081664396183 4221117090501122496594275)
                ·
                  refine ⟨6331675635751683744891413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4221117090501122496594275 6331675635751683744891413)
                  ·
                    refine ⟨296797295425860175541785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6331675635751683744891413 296797295425860175541785)
                    ·
                      refine ⟨222597971569395131656339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 296797295425860175541785 222597971569395131656339)
                      ·
                        rfl

theorem cell23_433508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 1, 6, 2].length) (baseStart_433508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433508 prefixEnd_433508 := by exact prefixLift 433508
  have htrace : WordTrace (prefixWord ++ tailWord_433508) baseStart_433508 baseEnd_433508 := by
    simpa [prefixWord, tailWord_433508, baseEnd_433508] using wordTrace_append hprefix tailTrace_433508
  have hstable : (prefixWord ++ tailWord_433508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433508).length < 2 ^ (prefixWord ++ tailWord_433508).sum := by decide
  have hdescent : baseEnd_433508 < baseStart_433508 := by decide
  rcases family_descends (prefixWord ++ tailWord_433508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433565 : List Nat := [1, 4, 2, 1, 3, 2, 3, 1, 6]
def baseStart_433565 : Nat := 118140960795 + 433565 * 2 ^ 59
def prefixEnd_433565 : Nat := 4983230072969 + 3 ^ 40 * 433565 * 2
def baseEnd_433565 : Nat := 24736359996300156515953

theorem tailTrace_433565 : CollatzResearch.WordTrace tailWord_433565 prefixEnd_433565 24736359996300156515953 := by
  unfold tailWord_433565
  simp only [CollatzResearch.WordTrace]
  refine ⟨15813414674275526851926149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10542276449517017901284099 15813414674275526851926149)
  ·
    refine ⟨2965015251426661284736153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15813414674275526851926149 2965015251426661284736153)
    ·
      refine ⟨2223761438569995963552115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2965015251426661284736153 2223761438569995963552115)
      ·
        refine ⟨3335642157854993945328173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2223761438569995963552115 3335642157854993945328173)
        ·
          refine ⟨1250865809195622729498065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3335642157854993945328173 1250865809195622729498065)
          ·
            refine ⟨938149356896717047123549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1250865809195622729498065 938149356896717047123549)
            ·
              refine ⟨351806008836268892671331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 938149356896717047123549 351806008836268892671331)
              ·
                refine ⟨527709013254403339006997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351806008836268892671331 527709013254403339006997)
                ·
                  refine ⟨24736359996300156515953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 527709013254403339006997 24736359996300156515953)
                  ·
                    rfl

theorem cell23_433565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 6].length) (baseStart_433565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433565 prefixEnd_433565 := by exact prefixLift 433565
  have htrace : WordTrace (prefixWord ++ tailWord_433565) baseStart_433565 baseEnd_433565 := by
    simpa [prefixWord, tailWord_433565, baseEnd_433565] using wordTrace_append hprefix tailTrace_433565
  have hstable : (prefixWord ++ tailWord_433565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433565).length < 2 ^ (prefixWord ++ tailWord_433565).sum := by decide
  have hdescent : baseEnd_433565 < baseStart_433565 := by decide
  rcases family_descends (prefixWord ++ tailWord_433565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433568 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 3, 5, 2]
def baseStart_433568 : Nat := 118140960795 + 433568 * 2 ^ 59
def prefixEnd_433568 : Nat := 4983230072969 + 3 ^ 40 * 433568 * 2
def baseEnd_433568 : Nat := 222628780408664896906063

theorem tailTrace_433568 : CollatzResearch.WordTrace tailWord_433568 prefixEnd_433568 222628780408664896906063 := by
  unfold tailWord_433568
  simp only [CollatzResearch.WordTrace]
  refine ⟨7906762046632329182142679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10542349395509772242856905 7906762046632329182142679)
  ·
    refine ⟨11860143069948493773214019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7906762046632329182142679 11860143069948493773214019)
    ·
      refine ⟨17790214604922740659821029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11860143069948493773214019 17790214604922740659821029)
      ·
        refine ⟨3335665238423013873716443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17790214604922740659821029 3335665238423013873716443)
        ·
          refine ⟨5003497857634520810574665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3335665238423013873716443 5003497857634520810574665)
          ·
            refine ⟨3752623393225890607930999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5003497857634520810574665 3752623393225890607930999)
            ·
              refine ⟨5628935089838835911896499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3752623393225890607930999 5628935089838835911896499)
              ·
                refine ⟨8443402634758253867844749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5628935089838835911896499 8443402634758253867844749)
                ·
                  refine ⟨3166275988034345200441781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8443402634758253867844749 3166275988034345200441781)
                  ·
                    refine ⟨296838373878219862541417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3166275988034345200441781 296838373878219862541417)
                    ·
                      refine ⟨222628780408664896906063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 296838373878219862541417 222628780408664896906063)
                      ·
                        rfl

theorem cell23_433568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_433568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433568 prefixEnd_433568 := by exact prefixLift 433568
  have htrace : WordTrace (prefixWord ++ tailWord_433568) baseStart_433568 baseEnd_433568 := by
    simpa [prefixWord, tailWord_433568, baseEnd_433568] using wordTrace_append hprefix tailTrace_433568
  have hstable : (prefixWord ++ tailWord_433568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433568).length < 2 ^ (prefixWord ++ tailWord_433568).sum := by decide
  have hdescent : baseEnd_433568 < baseStart_433568 := by decide
  rcases family_descends (prefixWord ++ tailWord_433568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433575 : List Nat := [1, 1, 6, 1, 1, 1, 1, 4, 3, 1, 3]
def baseStart_433575 : Nat := 118140960795 + 433575 * 2 ^ 59
def prefixEnd_433575 : Nat := 4983230072969 + 3 ^ 40 * 433575 * 2
def baseEnd_433575 : Nat := 222632374773246369518531

theorem tailTrace_433575 : CollatzResearch.WordTrace tailWord_433575 prefixEnd_433575 222632374773246369518531 := by
  unfold tailWord_433575
  simp only [CollatzResearch.WordTrace]
  refine ⟨15813779404239298559790179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10542519602826199039860119 15813779404239298559790179)
  ·
    refine ⟨23720669106358947839685269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15813779404239298559790179 23720669106358947839685269)
    ·
      refine ⟨1111906364360575679985247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23720669106358947839685269 1111906364360575679985247)
      ·
        refine ⟨1667859546540863519977871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1111906364360575679985247 1667859546540863519977871)
        ·
          refine ⟨2501789319811295279966807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1667859546540863519977871 2501789319811295279966807)
          ·
            refine ⟨3752683979716942919950211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2501789319811295279966807 3752683979716942919950211)
            ·
              refine ⟨5629025969575414379925317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3752683979716942919950211 5629025969575414379925317)
              ·
                refine ⟨1055442369295390196235997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5629025969575414379925317 1055442369295390196235997)
                ·
                  refine ⟨395790888485771323588499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1055442369295390196235997 395790888485771323588499)
                  ·
                    refine ⟨593686332728656985382749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 395790888485771323588499 593686332728656985382749)
                    ·
                      refine ⟨222632374773246369518531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 593686332728656985382749 222632374773246369518531)
                      ·
                        rfl

theorem cell23_433575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_433575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433575 prefixEnd_433575 := by exact prefixLift 433575
  have htrace : WordTrace (prefixWord ++ tailWord_433575) baseStart_433575 baseEnd_433575 := by
    simpa [prefixWord, tailWord_433575, baseEnd_433575] using wordTrace_append hprefix tailTrace_433575
  have hstable : (prefixWord ++ tailWord_433575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433575).length < 2 ^ (prefixWord ++ tailWord_433575).sum := by decide
  have hdescent : baseEnd_433575 < baseStart_433575 := by decide
  rcases family_descends (prefixWord ++ tailWord_433575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433585 : List Nat := [1, 2, 2, 4, 1, 1, 2, 3, 2, 3, 2]
def baseStart_433585 : Nat := 118140960795 + 433585 * 2 ^ 59
def prefixEnd_433585 : Nat := 4983230072969 + 3 ^ 40 * 433585 * 2
def baseEnd_433585 : Nat := 222637509579791330393485

theorem tailTrace_433585 : CollatzResearch.WordTrace tailWord_433585 prefixEnd_433585 222637509579791330393485 := by
  unfold tailWord_433585
  simp only [CollatzResearch.WordTrace]
  refine ⟨15814144134203070267654209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10542762756135380178436139 15814144134203070267654209)
  ·
    refine ⟨11860608100652302700740657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15814144134203070267654209 11860608100652302700740657)
    ·
      refine ⟨8895456075489227025555493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11860608100652302700740657 8895456075489227025555493)
      ·
        refine ⟨1667898014154230067291655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8895456075489227025555493 1667898014154230067291655)
        ·
          refine ⟨2501847021231345100937483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1667898014154230067291655 2501847021231345100937483)
          ·
            refine ⟨3752770531847017651406225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2501847021231345100937483 3752770531847017651406225)
            ·
              refine ⟨2814577898885263238554669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3752770531847017651406225 2814577898885263238554669)
              ·
                refine ⟨1055466712081973714458001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2814577898885263238554669 1055466712081973714458001)
                ·
                  refine ⟨791600034061480285843501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1055466712081973714458001 791600034061480285843501)
                  ·
                    refine ⟨296850012773055107191313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 791600034061480285843501 296850012773055107191313)
                    ·
                      refine ⟨222637509579791330393485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 296850012773055107191313 222637509579791330393485)
                      ·
                        rfl

theorem cell23_433585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_433585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433585 prefixEnd_433585 := by exact prefixLift 433585
  have htrace : WordTrace (prefixWord ++ tailWord_433585) baseStart_433585 baseEnd_433585 := by
    simpa [prefixWord, tailWord_433585, baseEnd_433585] using wordTrace_append hprefix tailTrace_433585
  have hstable : (prefixWord ++ tailWord_433585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433585).length < 2 ^ (prefixWord ++ tailWord_433585).sum := by decide
  have hdescent : baseEnd_433585 < baseStart_433585 := by decide
  rcases family_descends (prefixWord ++ tailWord_433585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433591 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 3, 6]
def baseStart_433591 : Nat := 118140960795 + 433591 * 2 ^ 59
def prefixEnd_433591 : Nat := 4983230072969 + 3 ^ 40 * 433591 * 2
def baseEnd_433591 : Nat := 74213530154572768972819

theorem tailTrace_433591 : CollatzResearch.WordTrace tailWord_433591 prefixEnd_433591 74213530154572768972819 := by
  unfold tailWord_433591
  simp only [CollatzResearch.WordTrace]
  refine ⟨15814362972181333292372627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10542908648120888861581751 15814362972181333292372627)
  ·
    refine ⟨23721544458271999938558941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15814362972181333292372627 23721544458271999938558941)
    ·
      refine ⟨8895579171851999976959603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23721544458271999938558941 8895579171851999976959603)
      ·
        refine ⟨13343368757777999965439405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8895579171851999976959603 13343368757777999965439405)
        ·
          refine ⟨5003763284166749987039777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13343368757777999965439405 5003763284166749987039777)
          ·
            refine ⟨3752822463125062490279833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5003763284166749987039777 3752822463125062490279833)
            ·
              refine ⟨2814616847343796867709875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3752822463125062490279833 2814616847343796867709875)
              ·
                refine ⟨4221925271015695301564813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2814616847343796867709875 4221925271015695301564813)
                ·
                  refine ⟨1583221976630885738086805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4221925271015695301564813 1583221976630885738086805)
                  ·
                    refine ⟨74213530154572768972819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1583221976630885738086805 74213530154572768972819)
                    ·
                      rfl

theorem cell23_433591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 6].length) (baseStart_433591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433591 prefixEnd_433591 := by exact prefixLift 433591
  have htrace : WordTrace (prefixWord ++ tailWord_433591) baseStart_433591 baseEnd_433591 := by
    simpa [prefixWord, tailWord_433591, baseEnd_433591] using wordTrace_append hprefix tailTrace_433591
  have hstable : (prefixWord ++ tailWord_433591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433591).length < 2 ^ (prefixWord ++ tailWord_433591).sum := by decide
  have hdescent : baseEnd_433591 < baseStart_433591 := by decide
  rcases family_descends (prefixWord ++ tailWord_433591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433592 : List Nat := [2, 1, 2, 1, 2, 2, 5, 3, 1, 1, 3]
def baseStart_433592 : Nat := 118140960795 + 433592 * 2 ^ 59
def prefixEnd_433592 : Nat := 4983230072969 + 3 ^ 40 * 433592 * 2
def baseEnd_433592 : Nat := 222641103944372803005953

theorem tailTrace_433592 : CollatzResearch.WordTrace tailWord_433592 prefixEnd_433592 222641103944372803005953 := by
  unfold tailWord_433592
  simp only [CollatzResearch.WordTrace]
  refine ⟨7907199722588855231579515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10542932963451806975439353 7907199722588855231579515)
  ·
    refine ⟨11860799583883282847369273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7907199722588855231579515 11860799583883282847369273)
    ·
      refine ⟨8895599687912462135526955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11860799583883282847369273 8895599687912462135526955)
      ·
        refine ⟨13343399531868693203290433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8895599687912462135526955 13343399531868693203290433)
        ·
          refine ⟨10007549648901519902467825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13343399531868693203290433 10007549648901519902467825)
          ·
            refine ⟨7505662236676139926850869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10007549648901519902467825 7505662236676139926850869)
            ·
              refine ⟨703655834688388118142269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7505662236676139926850869 703655834688388118142269)
              ·
                refine ⟨263870938008145544303351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 703655834688388118142269 263870938008145544303351)
                ·
                  refine ⟨395806407012218316455027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 263870938008145544303351 395806407012218316455027)
                  ·
                    refine ⟨593709610518327474682541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 395806407012218316455027 593709610518327474682541)
                    ·
                      refine ⟨222641103944372803005953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 593709610518327474682541 222641103944372803005953)
                      ·
                        rfl

theorem cell23_433592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 3, 1, 1, 3].length) (baseStart_433592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433592 prefixEnd_433592 := by exact prefixLift 433592
  have htrace : WordTrace (prefixWord ++ tailWord_433592) baseStart_433592 baseEnd_433592 := by
    simpa [prefixWord, tailWord_433592, baseEnd_433592] using wordTrace_append hprefix tailTrace_433592
  have hstable : (prefixWord ++ tailWord_433592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433592).length < 2 ^ (prefixWord ++ tailWord_433592).sum := by decide
  have hdescent : baseEnd_433592 < baseStart_433592 := by decide
  rcases family_descends (prefixWord ++ tailWord_433592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433598 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4]
def baseStart_433598 : Nat := 118140960795 + 433598 * 2 ^ 59
def prefixEnd_433598 : Nat := 4983230072969 + 3 ^ 40 * 433598 * 2
def baseEnd_433598 : Nat := 222644184828299779530925

theorem tailTrace_433598 : CollatzResearch.WordTrace tailWord_433598 prefixEnd_433598 222644184828299779530925 := by
  unfold tailWord_433598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1976827285394496685984681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10543078855437315658584965 1976827285394496685984681)
  ·
    refine ⟨1482620464045872514488511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1976827285394496685984681 1482620464045872514488511)
    ·
      refine ⟨2223930696068808771732767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1482620464045872514488511 2223930696068808771732767)
      ·
        refine ⟨3335896044103213157599151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2223930696068808771732767 3335896044103213157599151)
        ·
          refine ⟨5003844066154819736398727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3335896044103213157599151 5003844066154819736398727)
          ·
            refine ⟨7505766099232229604598091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5003844066154819736398727 7505766099232229604598091)
            ·
              refine ⟨11258649148848344406897137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7505766099232229604598091 11258649148848344406897137)
              ·
                refine ⟨8443986861636258305172853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11258649148848344406897137 8443986861636258305172853)
                ·
                  refine ⟨791623768278399216109955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8443986861636258305172853 791623768278399216109955)
                  ·
                    refine ⟨1187435652417598824164933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 791623768278399216109955 1187435652417598824164933)
                    ·
                      refine ⟨222644184828299779530925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1187435652417598824164933 222644184828299779530925)
                      ·
                        rfl

theorem cell23_433598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_433598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433598 prefixEnd_433598 := by exact prefixLift 433598
  have htrace : WordTrace (prefixWord ++ tailWord_433598) baseStart_433598 baseEnd_433598 := by
    simpa [prefixWord, tailWord_433598, baseEnd_433598] using wordTrace_append hprefix tailTrace_433598
  have hstable : (prefixWord ++ tailWord_433598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433598).length < 2 ^ (prefixWord ++ tailWord_433598).sum := by decide
  have hdescent : baseEnd_433598 < baseStart_433598 := by decide
  rcases family_descends (prefixWord ++ tailWord_433598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433608 : List Nat := [2, 1, 3, 1, 3, 1, 1, 3, 4, 4]
def baseStart_433608 : Nat := 118140960795 + 433608 * 2 ^ 59
def prefixEnd_433608 : Nat := 4983230072969 + 3 ^ 40 * 433608 * 2
def baseEnd_433608 : Nat := 74216439878281580135293

theorem tailTrace_433608 : CollatzResearch.WordTrace tailWord_433608 prefixEnd_433608 74216439878281580135293 := by
  unfold tailWord_433608
  simp only [CollatzResearch.WordTrace]
  refine ⟨7907491506559872597870739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10543322008746496797160985 7907491506559872597870739)
  ·
    refine ⟨11861237259839808896806109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7907491506559872597870739 11861237259839808896806109)
    ·
      refine ⟨4447963972439928336302291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11861237259839808896806109 4447963972439928336302291)
      ·
        refine ⟨6671945958659892504453437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4447963972439928336302291 6671945958659892504453437)
        ·
          refine ⟨2501979734497459689170039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6671945958659892504453437 2501979734497459689170039)
          ·
            refine ⟨3752969601746189533755059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2501979734497459689170039 3752969601746189533755059)
            ·
              refine ⟨5629454402619284300632589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3752969601746189533755059 5629454402619284300632589)
              ·
                refine ⟨2111045400982231612737221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5629454402619284300632589 2111045400982231612737221)
                ·
                  refine ⟨395821012684168427388229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2111045400982231612737221 395821012684168427388229)
                  ·
                    refine ⟨74216439878281580135293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 395821012684168427388229 74216439878281580135293)
                    ·
                      rfl

theorem cell23_433608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_433608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433608 prefixEnd_433608 := by exact prefixLift 433608
  have htrace : WordTrace (prefixWord ++ tailWord_433608) baseStart_433608 baseEnd_433608 := by
    simpa [prefixWord, tailWord_433608, baseEnd_433608] using wordTrace_append hprefix tailTrace_433608
  have hstable : (prefixWord ++ tailWord_433608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433608).length < 2 ^ (prefixWord ++ tailWord_433608).sum := by decide
  have hdescent : baseEnd_433608 < baseStart_433608 := by decide
  rcases family_descends (prefixWord ++ tailWord_433608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433611 : List Nat := [1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 6]
def baseStart_433611 : Nat := 118140960795 + 433611 * 2 ^ 59
def prefixEnd_433611 : Nat := 4983230072969 + 3 ^ 40 * 433611 * 2
def baseEnd_433611 : Nat := 222650860076808228668365

theorem tailTrace_433611 : CollatzResearch.WordTrace tailWord_433611 prefixEnd_433611 222650860076808228668365 := by
  unfold tailWord_433611
  simp only [CollatzResearch.WordTrace]
  refine ⟨15815092432108876708100687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10543394954739251138733791 15815092432108876708100687)
  ·
    refine ⟨23722638648163315062151031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15815092432108876708100687 23722638648163315062151031)
    ·
      refine ⟨35583957972244972593226547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23722638648163315062151031 35583957972244972593226547)
      ·
        refine ⟨53375936958367458889839821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35583957972244972593226547 53375936958367458889839821)
        ·
          refine ⟨20015976359387797083689933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53375936958367458889839821 20015976359387797083689933)
          ·
            refine ⟨7505991134770423906383725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20015976359387797083689933 7505991134770423906383725)
            ·
              refine ⟨2814746675538908964893897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7505991134770423906383725 2814746675538908964893897)
              ·
                refine ⟨2111060006654181723670423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2814746675538908964893897 2111060006654181723670423)
                ·
                  refine ⟨3166590009981272585505635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2111060006654181723670423 3166590009981272585505635)
                  ·
                    refine ⟨4749885014971908878258453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3166590009981272585505635 4749885014971908878258453)
                    ·
                      refine ⟨222650860076808228668365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4749885014971908878258453 222650860076808228668365)
                      ·
                        rfl

theorem cell23_433611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 6].length) (baseStart_433611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433611 prefixEnd_433611 := by exact prefixLift 433611
  have htrace : WordTrace (prefixWord ++ tailWord_433611) baseStart_433611 baseEnd_433611 := by
    simpa [prefixWord, tailWord_433611, baseEnd_433611] using wordTrace_append hprefix tailTrace_433611
  have hstable : (prefixWord ++ tailWord_433611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433611).length < 2 ^ (prefixWord ++ tailWord_433611).sum := by decide
  have hdescent : baseEnd_433611 < baseStart_433611 := by decide
  rcases family_descends (prefixWord ++ tailWord_433611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433625 : List Nat := [1, 2, 1, 2, 4, 3, 1, 3, 2, 4]
def baseStart_433625 : Nat := 118140960795 + 433625 * 2 ^ 59
def prefixEnd_433625 : Nat := 4983230072969 + 3 ^ 40 * 433625 * 2
def baseEnd_433625 : Nat := 74219349601990391297767

theorem tailTrace_433625 : CollatzResearch.WordTrace tailWord_433625 prefixEnd_433625 74219349601990391297767 := by
  unfold tailWord_433625
  simp only [CollatzResearch.WordTrace]
  refine ⟨15815603054058157099110329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10543735369372104732740219 15815603054058157099110329)
  ·
    refine ⟨11861702290543617824332747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15815603054058157099110329 11861702290543617824332747)
    ·
      refine ⟨17792553435815426736499121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11861702290543617824332747 17792553435815426736499121)
      ·
        refine ⟨13344415076861570052374341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17792553435815426736499121 13344415076861570052374341)
        ·
          refine ⟨2502077826911544384820189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13344415076861570052374341 2502077826911544384820189)
          ·
            refine ⟨938279185091829144307571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2502077826911544384820189 938279185091829144307571)
            ·
              refine ⟨1407418777637743716461357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 938279185091829144307571 1407418777637743716461357)
              ·
                refine ⟨527782041614153893673009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1407418777637743716461357 527782041614153893673009)
                ·
                  refine ⟨395836531210615420254757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 527782041614153893673009 395836531210615420254757)
                  ·
                    refine ⟨74219349601990391297767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 395836531210615420254757 74219349601990391297767)
                    ·
                      rfl

theorem cell23_433625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 2, 4].length) (baseStart_433625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433625 prefixEnd_433625 := by exact prefixLift 433625
  have htrace : WordTrace (prefixWord ++ tailWord_433625) baseStart_433625 baseEnd_433625 := by
    simpa [prefixWord, tailWord_433625, baseEnd_433625] using wordTrace_append hprefix tailTrace_433625
  have hstable : (prefixWord ++ tailWord_433625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433625).length < 2 ^ (prefixWord ++ tailWord_433625).sum := by decide
  have hdescent : baseEnd_433625 < baseStart_433625 := by decide
  rcases family_descends (prefixWord ++ tailWord_433625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433635 : List Nat := [1, 1, 1, 6, 2, 2, 1, 1, 3, 2, 3]
def baseStart_433635 : Nat := 118140960795 + 433635 * 2 ^ 59
def prefixEnd_433635 : Nat := 4983230072969 + 3 ^ 40 * 433635 * 2
def baseEnd_433635 : Nat := 222663183612516134768255

theorem tailTrace_433635 : CollatzResearch.WordTrace tailWord_433635 prefixEnd_433635 222663183612516134768255 := by
  unfold tailWord_433635
  simp only [CollatzResearch.WordTrace]
  refine ⟨15815967784021928806974359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10543978522681285871316239 15815967784021928806974359)
  ·
    refine ⟨23723951676032893210461539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15815967784021928806974359 23723951676032893210461539)
    ·
      refine ⟨35585927514049339815692309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23723951676032893210461539 35585927514049339815692309)
      ·
        refine ⟨1668090352221062803860577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35585927514049339815692309 1668090352221062803860577)
        ·
          refine ⟨1251067764165797102895433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1668090352221062803860577 1251067764165797102895433)
          ·
            refine ⟨938300823124347827171575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1251067764165797102895433 938300823124347827171575)
            ·
              refine ⟨1407451234686521740757363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 938300823124347827171575 1407451234686521740757363)
              ·
                refine ⟨2111176852029782611136045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1407451234686521740757363 2111176852029782611136045)
                ·
                  refine ⟨791691319511168479176017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2111176852029782611136045 791691319511168479176017)
                  ·
                    refine ⟨593768489633376359382013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 791691319511168479176017 593768489633376359382013)
                    ·
                      refine ⟨222663183612516134768255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 593768489633376359382013 222663183612516134768255)
                      ·
                        rfl

theorem cell23_433635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_433635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433635 prefixEnd_433635 := by exact prefixLift 433635
  have htrace : WordTrace (prefixWord ++ tailWord_433635) baseStart_433635 baseEnd_433635 := by
    simpa [prefixWord, tailWord_433635, baseEnd_433635] using wordTrace_append hprefix tailTrace_433635
  have hstable : (prefixWord ++ tailWord_433635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433635).length < 2 ^ (prefixWord ++ tailWord_433635).sum := by decide
  have hdescent : baseEnd_433635 < baseStart_433635 := by decide
  rcases family_descends (prefixWord ++ tailWord_433635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433648 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 3]
def baseStart_433648 : Nat := 118140960795 + 433648 * 2 ^ 59
def prefixEnd_433648 : Nat := 4983230072969 + 3 ^ 40 * 433648 * 2
def baseEnd_433648 : Nat := 222669858861024583905695

theorem tailTrace_433648 : CollatzResearch.WordTrace tailWord_433648 prefixEnd_433648 222669858861024583905695 := by
  unfold tailWord_433648
  simp only [CollatzResearch.WordTrace]
  refine ⟨7908220966487416013598799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10544294621983221351465065 7908220966487416013598799)
  ·
    refine ⟨11862331449731124020398199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7908220966487416013598799 11862331449731124020398199)
    ·
      refine ⟨17793497174596686030597299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11862331449731124020398199 17793497174596686030597299)
      ·
        refine ⟨26690245761895029045895949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17793497174596686030597299 26690245761895029045895949)
        ·
          refine ⟨10008842160710635892210981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26690245761895029045895949 10008842160710635892210981)
          ·
            refine ⟨1876657905133244229789559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10008842160710635892210981 1876657905133244229789559)
            ·
              refine ⟨2814986857699866344684339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1876657905133244229789559 2814986857699866344684339)
              ·
                refine ⟨4222480286549799517026509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2814986857699866344684339 4222480286549799517026509)
                ·
                  refine ⟨1583430107456174818884941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4222480286549799517026509 1583430107456174818884941)
                  ·
                    refine ⟨593786290296065557081853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1583430107456174818884941 593786290296065557081853)
                    ·
                      refine ⟨222669858861024583905695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 593786290296065557081853 222669858861024583905695)
                      ·
                        rfl

theorem cell23_433648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 3].length) (baseStart_433648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433648 prefixEnd_433648 := by exact prefixLift 433648
  have htrace : WordTrace (prefixWord ++ tailWord_433648) baseStart_433648 baseEnd_433648 := by
    simpa [prefixWord, tailWord_433648, baseEnd_433648] using wordTrace_append hprefix tailTrace_433648
  have hstable : (prefixWord ++ tailWord_433648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433648).length < 2 ^ (prefixWord ++ tailWord_433648).sum := by decide
  have hdescent : baseEnd_433648 < baseStart_433648 := by decide
  rcases family_descends (prefixWord ++ tailWord_433648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433692 : List Nat := [2, 2, 3, 1, 2, 1, 2, 4, 1, 3, 2]
def baseStart_433692 : Nat := 118140960795 + 433692 * 2 ^ 59
def prefixEnd_433692 : Nat := 4983230072969 + 3 ^ 40 * 433692 * 2
def baseEnd_433692 : Nat := 222692452009822411755493

theorem tailTrace_433692 : CollatzResearch.WordTrace tailWord_433692 prefixEnd_433692 222692452009822411755493 := by
  unfold tailWord_433692
  simp only [CollatzResearch.WordTrace]
  refine ⟨7909023372407713770899665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10545364496543618361199553 7909023372407713770899665)
  ·
    refine ⟨5931767529305785328174749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7909023372407713770899665 5931767529305785328174749)
    ·
      refine ⟨2224412823489669498065531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5931767529305785328174749 2224412823489669498065531)
      ·
        refine ⟨3336619235234504247098297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2224412823489669498065531 3336619235234504247098297)
        ·
          refine ⟨2502464426425878185323723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3336619235234504247098297 2502464426425878185323723)
          ·
            refine ⟨3753696639638817277985585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2502464426425878185323723 3753696639638817277985585)
            ·
              refine ⟨2815272479729112958489189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3753696639638817277985585 2815272479729112958489189)
              ·
                refine ⟨527863589949208679716723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2815272479729112958489189 527863589949208679716723)
                ·
                  refine ⟨791795384923813019575085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 527863589949208679716723 791795384923813019575085)
                  ·
                    refine ⟨296923269346429882340657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 791795384923813019575085 296923269346429882340657)
                    ·
                      refine ⟨222692452009822411755493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 296923269346429882340657 222692452009822411755493)
                      ·
                        rfl

theorem cell23_433692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_433692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433692 prefixEnd_433692 := by exact prefixLift 433692
  have htrace : WordTrace (prefixWord ++ tailWord_433692) baseStart_433692 baseEnd_433692 := by
    simpa [prefixWord, tailWord_433692, baseEnd_433692] using wordTrace_append hprefix tailTrace_433692
  have hstable : (prefixWord ++ tailWord_433692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433692).length < 2 ^ (prefixWord ++ tailWord_433692).sum := by decide
  have hdescent : baseEnd_433692 < baseStart_433692 := by decide
  rcases family_descends (prefixWord ++ tailWord_433692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433722 : List Nat := [3, 1, 1, 1, 3, 2, 3, 1, 4, 2, 2]
def baseStart_433722 : Nat := 118140960795 + 433722 * 2 ^ 59
def prefixEnd_433722 : Nat := 4983230072969 + 3 ^ 40 * 433722 * 2
def baseEnd_433722 : Nat := 222707856429457294380355

theorem tailTrace_433722 : CollatzResearch.WordTrace tailWord_433722 prefixEnd_433722 222707856429457294380355 := by
  unfold tailWord_433722
  simp only [CollatzResearch.WordTrace]
  refine ⟨3954785233676685666347855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10546093956471161776927613 3954785233676685666347855)
  ·
    refine ⟨5932177850515028499521783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3954785233676685666347855 5932177850515028499521783)
    ·
      refine ⟨8898266775772542749282675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5932177850515028499521783 8898266775772542749282675)
      ·
        refine ⟨13347400163658814123924013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8898266775772542749282675 13347400163658814123924013)
        ·
          refine ⟨5005275061372055296471505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13347400163658814123924013 5005275061372055296471505)
          ·
            refine ⟨3753956296029041472353629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5005275061372055296471505 3753956296029041472353629)
            ·
              refine ⟨1407733611010890552132611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3753956296029041472353629 1407733611010890552132611)
              ·
                refine ⟨2111600416516335828198917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1407733611010890552132611 2111600416516335828198917)
                ·
                  refine ⟨395925078096812967787297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2111600416516335828198917 395925078096812967787297)
                  ·
                    refine ⟨296943808572609725840473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 395925078096812967787297 296943808572609725840473)
                    ·
                      refine ⟨222707856429457294380355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 296943808572609725840473 222707856429457294380355)
                      ·
                        rfl

theorem cell23_433722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 4, 2, 2].length) (baseStart_433722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433722 prefixEnd_433722 := by exact prefixLift 433722
  have htrace : WordTrace (prefixWord ++ tailWord_433722) baseStart_433722 baseEnd_433722 := by
    simpa [prefixWord, tailWord_433722, baseEnd_433722] using wordTrace_append hprefix tailTrace_433722
  have hstable : (prefixWord ++ tailWord_433722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433722).length < 2 ^ (prefixWord ++ tailWord_433722).sum := by decide
  have hdescent : baseEnd_433722 < baseStart_433722 := by decide
  rcases family_descends (prefixWord ++ tailWord_433722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433795 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 1, 6, 2]
def baseStart_433795 : Nat := 118140960795 + 433795 * 2 ^ 59
def prefixEnd_433795 : Nat := 4983230072969 + 3 ^ 40 * 433795 * 2
def baseEnd_433795 : Nat := 222745340517235508767519

theorem tailTrace_433795 : CollatzResearch.WordTrace tailWord_433795 prefixEnd_433795 222745340517235508767519 := by
  unfold tailWord_433795
  simp only [CollatzResearch.WordTrace]
  refine ⟨15821803463442276132798839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10547868975628184088532559 15821803463442276132798839)
  ·
    refine ⟨23732705195163414199198259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15821803463442276132798839 23732705195163414199198259)
    ·
      refine ⟨35599057792745121298797389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23732705195163414199198259 35599057792745121298797389)
      ·
        refine ⟨13349646672279420487049021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35599057792745121298797389 13349646672279420487049021)
        ·
          refine ⟨5006117502104782682643383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13349646672279420487049021 5006117502104782682643383)
          ·
            refine ⟨7509176253157174023965075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5006117502104782682643383 7509176253157174023965075)
            ·
              refine ⟨11263764379735761035947613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7509176253157174023965075 11263764379735761035947613)
              ·
                refine ⟨4223911642400910388480355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11263764379735761035947613 4223911642400910388480355)
                ·
                  refine ⟨6335867463601365582720533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4223911642400910388480355 6335867463601365582720533)
                  ·
                    refine ⟨296993787356314011690025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6335867463601365582720533 296993787356314011690025)
                    ·
                      refine ⟨222745340517235508767519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 296993787356314011690025 222745340517235508767519)
                      ·
                        rfl

theorem cell23_433795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 6, 2].length) (baseStart_433795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433795 prefixEnd_433795 := by exact prefixLift 433795
  have htrace : WordTrace (prefixWord ++ tailWord_433795) baseStart_433795 baseEnd_433795 := by
    simpa [prefixWord, tailWord_433795, baseEnd_433795] using wordTrace_append hprefix tailTrace_433795
  have hstable : (prefixWord ++ tailWord_433795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433795).length < 2 ^ (prefixWord ++ tailWord_433795).sum := by decide
  have hdescent : baseEnd_433795 < baseStart_433795 := by decide
  rcases family_descends (prefixWord ++ tailWord_433795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433808 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 4]
def baseStart_433808 : Nat := 118140960795 + 433808 * 2 ^ 59
def prefixEnd_433808 : Nat := 4983230072969 + 3 ^ 40 * 433808 * 2
def baseEnd_433808 : Nat := 222752015765743957904959

theorem tailTrace_433808 : CollatzResearch.WordTrace tailWord_433808 prefixEnd_433808 222752015765743957904959 := by
  unfold tailWord_433808
  simp only [CollatzResearch.WordTrace]
  refine ⟨7911138806197589676511039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10548185074930119568681385 7911138806197589676511039)
  ·
    refine ⟨11866708209296384514766559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7911138806197589676511039 11866708209296384514766559)
    ·
      refine ⟨17800062313944576772149839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11866708209296384514766559 17800062313944576772149839)
      ·
        refine ⟨26700093470916865158224759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17800062313944576772149839 26700093470916865158224759)
        ·
          refine ⟨40050140206375297737337139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26700093470916865158224759 40050140206375297737337139)
          ·
            refine ⟨60075210309562946606005709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40050140206375297737337139 60075210309562946606005709)
            ·
              refine ⟨22528203866086104977252141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60075210309562946606005709 22528203866086104977252141)
              ·
                refine ⟨8448076449782289366469553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22528203866086104977252141 8448076449782289366469553)
                ·
                  refine ⟨6336057337336717024852165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8448076449782289366469553 6336057337336717024852165)
                  ·
                    refine ⟨1188010750750634442159781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6336057337336717024852165 1188010750750634442159781)
                    ·
                      refine ⟨222752015765743957904959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1188010750750634442159781 222752015765743957904959)
                      ·
                        rfl

theorem cell23_433808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 4].length) (baseStart_433808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433808 prefixEnd_433808 := by exact prefixLift 433808
  have htrace : WordTrace (prefixWord ++ tailWord_433808) baseStart_433808 baseEnd_433808 := by
    simpa [prefixWord, tailWord_433808, baseEnd_433808] using wordTrace_append hprefix tailTrace_433808
  have hstable : (prefixWord ++ tailWord_433808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433808).length < 2 ^ (prefixWord ++ tailWord_433808).sum := by decide
  have hdescent : baseEnd_433808 < baseStart_433808 := by decide
  rcases family_descends (prefixWord ++ tailWord_433808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433846 : List Nat := [5, 1, 3, 1, 1, 2, 1, 1, 2, 4, 2]
def baseStart_433846 : Nat := 118140960795 + 433846 * 2 ^ 59
def prefixEnd_433846 : Nat := 4983230072969 + 3 ^ 40 * 433846 * 2
def baseEnd_433846 : Nat := 222771528030614809229785

theorem tailTrace_433846 : CollatzResearch.WordTrace tailWord_433846 prefixEnd_433846 222771528030614809229785 := by
  unfold tailWord_433846
  simp only [CollatzResearch.WordTrace]
  refine ⟨988978974141094490181587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10549109057505007895270261 988978974141094490181587)
  ·
    refine ⟨1483468461211641735272381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 988978974141094490181587 1483468461211641735272381)
    ·
      refine ⟨556300672954365650727143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1483468461211641735272381 556300672954365650727143)
      ·
        refine ⟨834451009431548476090715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556300672954365650727143 834451009431548476090715)
        ·
          refine ⟨1251676514147322714136073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 834451009431548476090715 1251676514147322714136073)
          ·
            refine ⟨938757385610492035602055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1251676514147322714136073 938757385610492035602055)
            ·
              refine ⟨1408136078415738053403083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 938757385610492035602055 1408136078415738053403083)
              ·
                refine ⟨2112204117623607080104625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1408136078415738053403083 2112204117623607080104625)
                ·
                  refine ⟨1584153088217705310078469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2112204117623607080104625 1584153088217705310078469)
                  ·
                    refine ⟨297028704040819745639713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1584153088217705310078469 297028704040819745639713)
                    ·
                      refine ⟨222771528030614809229785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 297028704040819745639713 222771528030614809229785)
                      ·
                        rfl

theorem cell23_433846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_433846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433846 prefixEnd_433846 := by exact prefixLift 433846
  have htrace : WordTrace (prefixWord ++ tailWord_433846) baseStart_433846 baseEnd_433846 := by
    simpa [prefixWord, tailWord_433846, baseEnd_433846] using wordTrace_append hprefix tailTrace_433846
  have hstable : (prefixWord ++ tailWord_433846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433846).length < 2 ^ (prefixWord ++ tailWord_433846).sum := by decide
  have hdescent : baseEnd_433846 < baseStart_433846 := by decide
  rcases family_descends (prefixWord ++ tailWord_433846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433866 : List Nat := [3, 1, 2, 1, 6, 1, 1, 1, 2, 2, 3]
def baseStart_433866 : Nat := 118140960795 + 433866 * 2 ^ 59
def prefixEnd_433866 : Nat := 4983230072969 + 3 ^ 40 * 433866 * 2
def baseEnd_433866 : Nat := 222781797643704730979693

theorem tailTrace_433866 : CollatzResearch.WordTrace tailWord_433866 prefixEnd_433866 222781797643704730979693 := by
  unfold tailWord_433866
  simp only [CollatzResearch.WordTrace]
  refine ⟨3956098261546263814658363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10549595364123370172422301 3956098261546263814658363)
  ·
    refine ⟨5934147392319395721987545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3956098261546263814658363 5934147392319395721987545)
    ·
      refine ⟨4450610544239546791490659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5934147392319395721987545 4450610544239546791490659)
      ·
        refine ⟨6675915816359320187235989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4450610544239546791490659 6675915816359320187235989)
        ·
          refine ⟨312933553891843133776687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6675915816359320187235989 312933553891843133776687)
          ·
            refine ⟨469400330837764700665031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312933553891843133776687 469400330837764700665031)
            ·
              refine ⟨704100496256647050997547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469400330837764700665031 704100496256647050997547)
              ·
                refine ⟨1056150744384970576496321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 704100496256647050997547 1056150744384970576496321)
                ·
                  refine ⟨792113058288727932372241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1056150744384970576496321 792113058288727932372241)
                  ·
                    refine ⟨594084793716545949279181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 792113058288727932372241 594084793716545949279181)
                    ·
                      refine ⟨222781797643704730979693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 594084793716545949279181 222781797643704730979693)
                      ·
                        rfl

theorem cell23_433866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 2, 2, 3].length) (baseStart_433866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433866 prefixEnd_433866 := by exact prefixLift 433866
  have htrace : WordTrace (prefixWord ++ tailWord_433866) baseStart_433866 baseEnd_433866 := by
    simpa [prefixWord, tailWord_433866, baseEnd_433866] using wordTrace_append hprefix tailTrace_433866
  have hstable : (prefixWord ++ tailWord_433866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433866).length < 2 ^ (prefixWord ++ tailWord_433866).sum := by decide
  have hdescent : baseEnd_433866 < baseStart_433866 := by decide
  rcases family_descends (prefixWord ++ tailWord_433866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433872 : List Nat := [2, 1, 1, 1, 1, 2, 1, 7, 2, 3, 2]
def baseStart_433872 : Nat := 118140960795 + 433872 * 2 ^ 59
def prefixEnd_433872 : Nat := 4983230072969 + 3 ^ 40 * 433872 * 2
def baseEnd_433872 : Nat := 222784878527631707504665

theorem tailTrace_433872 : CollatzResearch.WordTrace tailWord_433872 prefixEnd_433872 222784878527631707504665 := by
  unfold tailWord_433872
  simp only [CollatzResearch.WordTrace]
  refine ⟨7912305942081659141675935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10549741256108878855567913 7912305942081659141675935)
  ·
    refine ⟨11868458913122488712513903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7912305942081659141675935 11868458913122488712513903)
    ·
      refine ⟨17802688369683733068770855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11868458913122488712513903 17802688369683733068770855)
      ·
        refine ⟨26704032554525599603156283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17802688369683733068770855 26704032554525599603156283)
        ·
          refine ⟨40056048831788399404734425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26704032554525599603156283 40056048831788399404734425)
          ·
            refine ⟨30042036623841299553550819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40056048831788399404734425 30042036623841299553550819)
            ·
              refine ⟨45063054935761949330326229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30042036623841299553550819 45063054935761949330326229)
              ·
                refine ⟨1056165350056920687429521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 45063054935761949330326229 1056165350056920687429521)
                ·
                  refine ⟨792124012542690515572141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1056165350056920687429521 792124012542690515572141)
                  ·
                    refine ⟨297046504703508943339553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 792124012542690515572141 297046504703508943339553)
                    ·
                      refine ⟨222784878527631707504665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 297046504703508943339553 222784878527631707504665)
                      ·
                        rfl

theorem cell23_433872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 2, 3, 2].length) (baseStart_433872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433872 prefixEnd_433872 := by exact prefixLift 433872
  have htrace : WordTrace (prefixWord ++ tailWord_433872) baseStart_433872 baseEnd_433872 := by
    simpa [prefixWord, tailWord_433872, baseEnd_433872] using wordTrace_append hprefix tailTrace_433872
  have hstable : (prefixWord ++ tailWord_433872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433872).length < 2 ^ (prefixWord ++ tailWord_433872).sum := by decide
  have hdescent : baseEnd_433872 < baseStart_433872 := by decide
  rcases family_descends (prefixWord ++ tailWord_433872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433882 : List Nat := [3, 1, 1, 2, 2, 4, 1, 3, 1, 5]
def baseStart_433882 : Nat := 118140960795 + 433882 * 2 ^ 59
def prefixEnd_433882 : Nat := 4983230072969 + 3 ^ 40 * 433882 * 2
def baseEnd_433882 : Nat := 74263337778058889459873

theorem tailTrace_433882 : CollatzResearch.WordTrace tailWord_433882 prefixEnd_433882 74263337778058889459873 := by
  unfold tailWord_433882
  simp only [CollatzResearch.WordTrace]
  refine ⟨3956244153531772497803975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10549984409418059994143933 3956244153531772497803975)
  ·
    refine ⟨5934366230297658746705963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3956244153531772497803975 5934366230297658746705963)
    ·
      refine ⟨8901549345446488120058945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5934366230297658746705963 8901549345446488120058945)
      ·
        refine ⟨6676162009084866090044209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8901549345446488120058945 6676162009084866090044209)
        ·
          refine ⟨5007121506813649567533157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6676162009084866090044209 5007121506813649567533157)
          ·
            refine ⟨938835282527559293912467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5007121506813649567533157 938835282527559293912467)
            ·
              refine ⟨1408252923791338940868701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 938835282527559293912467 1408252923791338940868701)
              ·
                refine ⟨528094846421752102825763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1408252923791338940868701 528094846421752102825763)
                ·
                  refine ⟨792142269632628154238645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 528094846421752102825763 792142269632628154238645)
                  ·
                    refine ⟨74263337778058889459873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 792142269632628154238645 74263337778058889459873)
                    ·
                      rfl

theorem cell23_433882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 1, 5].length) (baseStart_433882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433882 prefixEnd_433882 := by exact prefixLift 433882
  have htrace : WordTrace (prefixWord ++ tailWord_433882) baseStart_433882 baseEnd_433882 := by
    simpa [prefixWord, tailWord_433882, baseEnd_433882] using wordTrace_append hprefix tailTrace_433882
  have hstable : (prefixWord ++ tailWord_433882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433882).length < 2 ^ (prefixWord ++ tailWord_433882).sum := by decide
  have hdescent : baseEnd_433882 < baseStart_433882 := by decide
  rcases family_descends (prefixWord ++ tailWord_433882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433896 : List Nat := [2, 1, 4, 1, 3, 1, 2, 4, 1, 1, 3]
def baseStart_433896 : Nat := 118140960795 + 433896 * 2 ^ 59
def prefixEnd_433896 : Nat := 4983230072969 + 3 ^ 40 * 433896 * 2
def baseEnd_433896 : Nat := 222797202063339613604555

theorem tailTrace_433896 : CollatzResearch.WordTrace tailWord_433896 prefixEnd_433896 222797202063339613604555 := by
  unfold tailWord_433896
  simp only [CollatzResearch.WordTrace]
  refine ⟨7912743618038185191112771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10550324824050913588150361 7912743618038185191112771)
  ·
    refine ⟨11869115427057277786669157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7912743618038185191112771 11869115427057277786669157)
    ·
      refine ⟨2225459142573239585000467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11869115427057277786669157 2225459142573239585000467)
      ·
        refine ⟨3338188713859859377500701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2225459142573239585000467 3338188713859859377500701)
        ·
          refine ⟨1251820767697447266562763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3338188713859859377500701 1251820767697447266562763)
          ·
            refine ⟨1877731151546170899844145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1251820767697447266562763 1877731151546170899844145)
            ·
              refine ⟨1408298363659628174883109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1877731151546170899844145 1408298363659628174883109)
              ·
                refine ⟨264055943186180282790583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1408298363659628174883109 264055943186180282790583)
                ·
                  refine ⟨396083914779270424185875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 264055943186180282790583 396083914779270424185875)
                  ·
                    refine ⟨594125872168905636278813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 396083914779270424185875 594125872168905636278813)
                    ·
                      refine ⟨222797202063339613604555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 594125872168905636278813 222797202063339613604555)
                      ·
                        rfl

theorem cell23_433896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_433896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433896 prefixEnd_433896 := by exact prefixLift 433896
  have htrace : WordTrace (prefixWord ++ tailWord_433896) baseStart_433896 baseEnd_433896 := by
    simpa [prefixWord, tailWord_433896, baseEnd_433896] using wordTrace_append hprefix tailTrace_433896
  have hstable : (prefixWord ++ tailWord_433896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433896).length < 2 ^ (prefixWord ++ tailWord_433896).sum := by decide
  have hdescent : baseEnd_433896 < baseStart_433896 := by decide
  rcases family_descends (prefixWord ++ tailWord_433896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433905 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 3, 1, 5]
def baseStart_433905 : Nat := 118140960795 + 433905 * 2 ^ 59
def prefixEnd_433905 : Nat := 4983230072969 + 3 ^ 40 * 433905 * 2
def baseEnd_433905 : Nat := 222801823389230078392013

theorem tailTrace_433905 : CollatzResearch.WordTrace tailWord_433905 prefixEnd_433905 222801823389230078392013 := by
  unfold tailWord_433905
  simp only [CollatzResearch.WordTrace]
  refine ⟨15825815493043764919303169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10550543662029176612868779 15825815493043764919303169)
  ·
    refine ⟨11869361619782823689477377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15825815493043764919303169 11869361619782823689477377)
    ·
      refine ⟨8902021214837117767108033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11869361619782823689477377 8902021214837117767108033)
      ·
        refine ⟨6676515911127838325331025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8902021214837117767108033 6676515911127838325331025)
        ·
          refine ⟨5007386933345878743998269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6676515911127838325331025 5007386933345878743998269)
          ·
            refine ⟨1877770100004704528999351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5007386933345878743998269 1877770100004704528999351)
            ·
              refine ⟨2816655150007056793499027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1877770100004704528999351 2816655150007056793499027)
              ·
                refine ⟨4224982725010585190248541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2816655150007056793499027 4224982725010585190248541)
                ·
                  refine ⟨1584368521878969446343203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4224982725010585190248541 1584368521878969446343203)
                  ·
                    refine ⟨2376552782818454169514805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1584368521878969446343203 2376552782818454169514805)
                    ·
                      refine ⟨222801823389230078392013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2376552782818454169514805 222801823389230078392013)
                      ·
                        rfl

theorem cell23_433905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_433905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433905 prefixEnd_433905 := by exact prefixLift 433905
  have htrace : WordTrace (prefixWord ++ tailWord_433905) baseStart_433905 baseEnd_433905 := by
    simpa [prefixWord, tailWord_433905, baseEnd_433905] using wordTrace_append hprefix tailTrace_433905
  have hstable : (prefixWord ++ tailWord_433905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433905).length < 2 ^ (prefixWord ++ tailWord_433905).sum := by decide
  have hdescent : baseEnd_433905 < baseStart_433905 := by decide
  rcases family_descends (prefixWord ++ tailWord_433905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433915 : List Nat := [1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 4]
def baseStart_433915 : Nat := 118140960795 + 433915 * 2 ^ 59
def prefixEnd_433915 : Nat := 4983230072969 + 3 ^ 40 * 433915 * 2
def baseEnd_433915 : Nat := 222806958195775039266967

theorem tailTrace_433915 : CollatzResearch.WordTrace tailWord_433915 prefixEnd_433915 222806958195775039266967 := by
  unfold tailWord_433915
  simp only [CollatzResearch.WordTrace]
  refine ⟨15826180223007536627167199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10550786815338357751444799 15826180223007536627167199)
  ·
    refine ⟨23739270334511304940750799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15826180223007536627167199 23739270334511304940750799)
    ·
      refine ⟨35608905501766957411126199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23739270334511304940750799 35608905501766957411126199)
      ·
        refine ⟨53413358252650436116689299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35608905501766957411126199 53413358252650436116689299)
        ·
          refine ⟨80120037378975654175033949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53413358252650436116689299 80120037378975654175033949)
          ·
            refine ⟨30045014017115870315637731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80120037378975654175033949 30045014017115870315637731)
            ·
              refine ⟨45067521025673805473456597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30045014017115870315637731 45067521025673805473456597)
              ·
                refine ⟨1056270024039229815784139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 45067521025673805473456597 1056270024039229815784139)
                ·
                  refine ⟨1584405036058844723676209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1056270024039229815784139 1584405036058844723676209)
                  ·
                    refine ⟨1188303777044133542757157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1584405036058844723676209 1188303777044133542757157)
                    ·
                      refine ⟨222806958195775039266967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1188303777044133542757157 222806958195775039266967)
                      ·
                        rfl

theorem cell23_433915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 4].length) (baseStart_433915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433915 prefixEnd_433915 := by exact prefixLift 433915
  have htrace : WordTrace (prefixWord ++ tailWord_433915) baseStart_433915 baseEnd_433915 := by
    simpa [prefixWord, tailWord_433915, baseEnd_433915] using wordTrace_append hprefix tailTrace_433915
  have hstable : (prefixWord ++ tailWord_433915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433915).length < 2 ^ (prefixWord ++ tailWord_433915).sum := by decide
  have hdescent : baseEnd_433915 < baseStart_433915 := by decide
  rcases family_descends (prefixWord ++ tailWord_433915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433919 : List Nat := [1, 1, 2, 2, 1, 3, 4, 2, 3, 2, 2]
def baseStart_433919 : Nat := 118140960795 + 433919 * 2 ^ 59
def prefixEnd_433919 : Nat := 4983230072969 + 3 ^ 40 * 433919 * 2
def baseEnd_433919 : Nat := 222809012118393023616949

theorem tailTrace_433919 : CollatzResearch.WordTrace tailWord_433919 prefixEnd_433919 222809012118393023616949 := by
  unfold tailWord_433919
  simp only [CollatzResearch.WordTrace]
  refine ⟨15826326114993045310312811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10550884076662030206875207 15826326114993045310312811)
  ·
    refine ⟨23739489172489567965469217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15826326114993045310312811 23739489172489567965469217)
    ·
      refine ⟨17804616879367175974101913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23739489172489567965469217 17804616879367175974101913)
      ·
        refine ⟨13353462659525381980576435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17804616879367175974101913 13353462659525381980576435)
        ·
          refine ⟨20030193989288072970864653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13353462659525381980576435 20030193989288072970864653)
          ·
            refine ⟨7511322745983027364074245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20030193989288072970864653 7511322745983027364074245)
            ·
              refine ⟨1408373014871817630763921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7511322745983027364074245 1408373014871817630763921)
              ·
                refine ⟨1056279761153863223072941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1408373014871817630763921 1056279761153863223072941)
                ·
                  refine ⟨396104910432698708652353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1056279761153863223072941 396104910432698708652353)
                  ·
                    refine ⟨297078682824524031489265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 396104910432698708652353 297078682824524031489265)
                    ·
                      refine ⟨222809012118393023616949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 297078682824524031489265 222809012118393023616949)
                      ·
                        rfl

theorem cell23_433919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 3, 2, 2].length) (baseStart_433919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433919 prefixEnd_433919 := by exact prefixLift 433919
  have htrace : WordTrace (prefixWord ++ tailWord_433919) baseStart_433919 baseEnd_433919 := by
    simpa [prefixWord, tailWord_433919, baseEnd_433919] using wordTrace_append hprefix tailTrace_433919
  have hstable : (prefixWord ++ tailWord_433919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433919).length < 2 ^ (prefixWord ++ tailWord_433919).sum := by decide
  have hdescent : baseEnd_433919 < baseStart_433919 := by decide
  rcases family_descends (prefixWord ++ tailWord_433919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433922 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_433922 : Nat := 118140960795 + 433922 * 2 ^ 59
def prefixEnd_433922 : Nat := 4983230072969 + 3 ^ 40 * 433922 * 2
def baseEnd_433922 : Nat := 222810552560356511879435

theorem tailTrace_433922 : CollatzResearch.WordTrace tailWord_433922 prefixEnd_433922 222810552560356511879435 := by
  unfold tailWord_433922
  simp only [CollatzResearch.WordTrace]
  refine ⟨3956608883495544205668005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10550957022654784548448013 3956608883495544205668005)
  ·
    refine ⟨741864165655414538562751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3956608883495544205668005 741864165655414538562751)
    ·
      refine ⟨1112796248483121807844127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 741864165655414538562751 1112796248483121807844127)
      ·
        refine ⟨1669194372724682711766191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1112796248483121807844127 1669194372724682711766191)
        ·
          refine ⟨2503791559087024067649287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1669194372724682711766191 2503791559087024067649287)
          ·
            refine ⟨3755687338630536101473931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2503791559087024067649287 3755687338630536101473931)
            ·
              refine ⟨5633531007945804152210897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3755687338630536101473931 5633531007945804152210897)
              ·
                refine ⟨4225148255959353114158173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5633531007945804152210897 4225148255959353114158173)
                ·
                  refine ⟨1584430595984757417809315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4225148255959353114158173 1584430595984757417809315)
                  ·
                    refine ⟨2376645893977136126713973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1584430595984757417809315 2376645893977136126713973)
                    ·
                      refine ⟨222810552560356511879435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2376645893977136126713973 222810552560356511879435)
                      ·
                        rfl

theorem cell23_433922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_433922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433922 prefixEnd_433922 := by exact prefixLift 433922
  have htrace : WordTrace (prefixWord ++ tailWord_433922) baseStart_433922 baseEnd_433922 := by
    simpa [prefixWord, tailWord_433922, baseEnd_433922] using wordTrace_append hprefix tailTrace_433922
  have hstable : (prefixWord ++ tailWord_433922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433922).length < 2 ^ (prefixWord ++ tailWord_433922).sum := by decide
  have hdescent : baseEnd_433922 < baseStart_433922 := by decide
  rcases family_descends (prefixWord ++ tailWord_433922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433940 : List Nat := [2, 4, 4, 1, 1, 1, 1, 2, 2, 3, 2]
def baseStart_433940 : Nat := 118140960795 + 433940 * 2 ^ 59
def prefixEnd_433940 : Nat := 4983230072969 + 3 ^ 40 * 433940 * 2
def baseEnd_433940 : Nat := 222819795212137441454353

theorem tailTrace_433940 : CollatzResearch.WordTrace tailWord_433940 prefixEnd_433940 222819795212137441454353 := by
  unfold tailWord_433940
  simp only [CollatzResearch.WordTrace]
  refine ⟨7913546023958482948413637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10551394698611310597884849 7913546023958482948413637)
  ·
    refine ⟨1483789879492215552827557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7913546023958482948413637 1483789879492215552827557)
    ·
      refine ⟨278210602404790416155167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1483789879492215552827557 278210602404790416155167)
      ·
        refine ⟨417315903607185624232751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278210602404790416155167 417315903607185624232751)
        ·
          refine ⟨625973855410778436349127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417315903607185624232751 625973855410778436349127)
          ·
            refine ⟨938960783116167654523691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625973855410778436349127 938960783116167654523691)
            ·
              refine ⟨1408441174674251481785537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 938960783116167654523691 1408441174674251481785537)
              ·
                refine ⟨1056330881005688611339153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1408441174674251481785537 1056330881005688611339153)
                ·
                  refine ⟨792248160754266458504365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1056330881005688611339153 792248160754266458504365)
                  ·
                    refine ⟨297093060282849921939137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 792248160754266458504365 297093060282849921939137)
                    ·
                      refine ⟨222819795212137441454353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 297093060282849921939137 222819795212137441454353)
                      ·
                        rfl

theorem cell23_433940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_433940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433940 prefixEnd_433940 := by exact prefixLift 433940
  have htrace : WordTrace (prefixWord ++ tailWord_433940) baseStart_433940 baseEnd_433940 := by
    simpa [prefixWord, tailWord_433940, baseEnd_433940] using wordTrace_append hprefix tailTrace_433940
  have hstable : (prefixWord ++ tailWord_433940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433940).length < 2 ^ (prefixWord ++ tailWord_433940).sum := by decide
  have hdescent : baseEnd_433940 < baseStart_433940 := by decide
  rcases family_descends (prefixWord ++ tailWord_433940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433973 : List Nat := [1, 3, 3, 1, 5, 1, 1, 2, 1, 2, 3]
def baseStart_433973 : Nat := 118140960795 + 433973 * 2 ^ 59
def prefixEnd_433973 : Nat := 4983230072969 + 3 ^ 40 * 433973 * 2
def baseEnd_433973 : Nat := 222836740073735812341701

theorem tailTrace_433973 : CollatzResearch.WordTrace tailWord_433973 prefixEnd_433973 222836740073735812341701 := by
  unfold tailWord_433973
  simp only [CollatzResearch.WordTrace]
  refine ⟨15828295656797412532778573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10552197104531608355185715 15828295656797412532778573)
  ·
    refine ⟨5935610871299029699791965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15828295656797412532778573 5935610871299029699791965)
    ·
      refine ⟨2225854076737136137421987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5935610871299029699791965 2225854076737136137421987)
      ·
        refine ⟨3338781115105704206132981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2225854076737136137421987 3338781115105704206132981)
        ·
          refine ⟨313010729541159769324967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3338781115105704206132981 313010729541159769324967)
          ·
            refine ⟨469516094311739653987451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313010729541159769324967 469516094311739653987451)
            ·
              refine ⟨704274141467609480981177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469516094311739653987451 704274141467609480981177)
              ·
                refine ⟨528205606100707110735883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 704274141467609480981177 528205606100707110735883)
                ·
                  refine ⟨792308409151060666103825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 528205606100707110735883 792308409151060666103825)
                  ·
                    refine ⟨594231306863295499577869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 792308409151060666103825 594231306863295499577869)
                    ·
                      refine ⟨222836740073735812341701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 594231306863295499577869 222836740073735812341701)
                      ·
                        rfl

theorem cell23_433973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_433973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433973 prefixEnd_433973 := by exact prefixLift 433973
  have htrace : WordTrace (prefixWord ++ tailWord_433973) baseStart_433973 baseEnd_433973 := by
    simpa [prefixWord, tailWord_433973, baseEnd_433973] using wordTrace_append hprefix tailTrace_433973
  have hstable : (prefixWord ++ tailWord_433973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433973).length < 2 ^ (prefixWord ++ tailWord_433973).sum := by decide
  have hdescent : baseEnd_433973 < baseStart_433973 := by decide
  rcases family_descends (prefixWord ++ tailWord_433973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433975 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 4]
def baseStart_433975 : Nat := 118140960795 + 433975 * 2 ^ 59
def prefixEnd_433975 : Nat := 4983230072969 + 3 ^ 40 * 433975 * 2
def baseEnd_433975 : Nat := 222837767035044804516691

theorem tailTrace_433975 : CollatzResearch.WordTrace tailWord_433975 prefixEnd_433975 222837767035044804516691 := by
  unfold tailWord_433975
  simp only [CollatzResearch.WordTrace]
  refine ⟨15828368602790166874351379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10552245735193444582900919 15828368602790166874351379)
  ·
    refine ⟨23742552904185250311527069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15828368602790166874351379 23742552904185250311527069)
    ·
      refine ⟨8903457339069468866822651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23742552904185250311527069 8903457339069468866822651)
      ·
        refine ⟨13355186008604203300233977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8903457339069468866822651 13355186008604203300233977)
        ·
          refine ⟨10016389506453152475175483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13355186008604203300233977 10016389506453152475175483)
          ·
            refine ⟨15024584259679728712763225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10016389506453152475175483 15024584259679728712763225)
            ·
              refine ⟨11268438194759796534572419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15024584259679728712763225 11268438194759796534572419)
              ·
                refine ⟨16902657292139694801858629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11268438194759796534572419 16902657292139694801858629)
                ·
                  refine ⟨3169248242276192775348493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16902657292139694801858629 3169248242276192775348493)
                  ·
                    refine ⟨1188468090853572290755685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3169248242276192775348493 1188468090853572290755685)
                    ·
                      refine ⟨222837767035044804516691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1188468090853572290755685 222837767035044804516691)
                      ·
                        rfl

theorem cell23_433975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_433975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433975 prefixEnd_433975 := by exact prefixLift 433975
  have htrace : WordTrace (prefixWord ++ tailWord_433975) baseStart_433975 baseEnd_433975 := by
    simpa [prefixWord, tailWord_433975, baseEnd_433975] using wordTrace_append hprefix tailTrace_433975
  have hstable : (prefixWord ++ tailWord_433975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433975).length < 2 ^ (prefixWord ++ tailWord_433975).sum := by decide
  have hdescent : baseEnd_433975 < baseStart_433975 := by decide
  rcases family_descends (prefixWord ++ tailWord_433975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433990 : List Nat := [6, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3]
def baseStart_433990 : Nat := 118140960795 + 433990 * 2 ^ 59
def prefixEnd_433990 : Nat := 4983230072969 + 3 ^ 40 * 433990 * 2
def baseEnd_433990 : Nat := 222845469244862245829123

theorem tailTrace_433990 : CollatzResearch.WordTrace tailWord_433990 prefixEnd_433990 222845469244862245829123 := by
  unfold tailWord_433990
  simp only [CollatzResearch.WordTrace]
  refine ⟨494653615554244513629607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10552610465157216290764949 494653615554244513629607)
  ·
    refine ⟨741980423331366770444411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 494653615554244513629607 741980423331366770444411)
    ·
      refine ⟨1112970634997050155666617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 741980423331366770444411 1112970634997050155666617)
      ·
        refine ⟨834727976247787616749963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1112970634997050155666617 834727976247787616749963)
        ·
          refine ⟨1252091964371681425124945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 834727976247787616749963 1252091964371681425124945)
          ·
            refine ⟨939068973278761068843709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1252091964371681425124945 939068973278761068843709)
            ·
              refine ⟨352150864979535400816391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 939068973278761068843709 352150864979535400816391)
              ·
                refine ⟨528226297469303101224587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 352150864979535400816391 528226297469303101224587)
                ·
                  refine ⟨792339446203954651836881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 528226297469303101224587 792339446203954651836881)
                  ·
                    refine ⟨594254584652965988877661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 792339446203954651836881 594254584652965988877661)
                    ·
                      refine ⟨222845469244862245829123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 594254584652965988877661 222845469244862245829123)
                      ·
                        rfl

theorem cell23_433990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_433990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_433990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_433990 prefixEnd_433990 := by exact prefixLift 433990
  have htrace : WordTrace (prefixWord ++ tailWord_433990) baseStart_433990 baseEnd_433990 := by
    simpa [prefixWord, tailWord_433990, baseEnd_433990] using wordTrace_append hprefix tailTrace_433990
  have hstable : (prefixWord ++ tailWord_433990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433990).length < 2 ^ (prefixWord ++ tailWord_433990).sum := by decide
  have hdescent : baseEnd_433990 < baseStart_433990 := by decide
  rcases family_descends (prefixWord ++ tailWord_433990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434066 : List Nat := [3, 2, 3, 2, 1, 1, 2, 4, 5]
def baseStart_434066 : Nat := 118140960795 + 434066 * 2 ^ 59
def prefixEnd_434066 : Nat := 4983230072969 + 3 ^ 40 * 434066 * 2
def baseEnd_434066 : Nat := 24764943752733772053197

theorem tailTrace_434066 : CollatzResearch.WordTrace tailWord_434066 prefixEnd_434066 24764943752733772053197 := by
  unfold tailWord_434066
  simp only [CollatzResearch.WordTrace]
  refine ⟨3957921911365122353978513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10554458430306992943942701 3957921911365122353978513)
  ·
    refine ⟨2968441433523841765483885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3957921911365122353978513 2968441433523841765483885)
    ·
      refine ⟨1113165537571440662056457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2968441433523841765483885 1113165537571440662056457)
      ·
        refine ⟨834874153178580496542343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1113165537571440662056457 834874153178580496542343)
        ·
          refine ⟨1252311229767870744813515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 834874153178580496542343 1252311229767870744813515)
          ·
            refine ⟨1878466844651806117220273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1252311229767870744813515 1878466844651806117220273)
            ·
              refine ⟨1408850133488854587915205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1878466844651806117220273 1408850133488854587915205)
              ·
                refine ⟨264159400029160235234101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1408850133488854587915205 264159400029160235234101)
                ·
                  refine ⟨24764943752733772053197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 264159400029160235234101 24764943752733772053197)
                  ·
                    rfl

theorem cell23_434066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 4, 5].length) (baseStart_434066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434066 prefixEnd_434066 := by exact prefixLift 434066
  have htrace : WordTrace (prefixWord ++ tailWord_434066) baseStart_434066 baseEnd_434066 := by
    simpa [prefixWord, tailWord_434066, baseEnd_434066] using wordTrace_append hprefix tailTrace_434066
  have hstable : (prefixWord ++ tailWord_434066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434066).length < 2 ^ (prefixWord ++ tailWord_434066).sum := by decide
  have hdescent : baseEnd_434066 < baseStart_434066 := by decide
  rcases family_descends (prefixWord ++ tailWord_434066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434100 : List Nat := [2, 5, 2, 1, 2, 2, 1, 3, 5]
def baseStart_434100 : Nat := 118140960795 + 434100 * 2 ^ 59
def prefixEnd_434100 : Nat := 4983230072969 + 3 ^ 40 * 434100 * 2
def baseEnd_434100 : Nat := 24766883568539646161513

theorem tailTrace_434100 : CollatzResearch.WordTrace tailWord_434100 prefixEnd_434100 24766883568539646161513 := by
  unfold tailWord_434100
  simp only [CollatzResearch.WordTrace]
  refine ⟨7916463863668656611325877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10555285151558208815101169 7916463863668656611325877)
  ·
    refine ⟨742168487218936557311801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7916463863668656611325877 742168487218936557311801)
    ·
      refine ⟨556626365414202417983851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 742168487218936557311801 556626365414202417983851)
      ·
        refine ⟨834939548121303626975777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556626365414202417983851 834939548121303626975777)
        ·
          refine ⟨626204661090977720231833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 834939548121303626975777 626204661090977720231833)
          ·
            refine ⟨469653495818233290173875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 626204661090977720231833 469653495818233290173875)
            ·
              refine ⟨704480243727349935260813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469653495818233290173875 704480243727349935260813)
              ·
                refine ⟨264180091397756225722805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 704480243727349935260813 264180091397756225722805)
                ·
                  refine ⟨24766883568539646161513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 264180091397756225722805 24766883568539646161513)
                  ·
                    rfl

theorem cell23_434100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_434100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434100 prefixEnd_434100 := by exact prefixLift 434100
  have htrace : WordTrace (prefixWord ++ tailWord_434100) baseStart_434100 baseEnd_434100 := by
    simpa [prefixWord, tailWord_434100, baseEnd_434100] using wordTrace_append hprefix tailTrace_434100
  have hstable : (prefixWord ++ tailWord_434100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434100).length < 2 ^ (prefixWord ++ tailWord_434100).sum := by decide
  have hdescent : baseEnd_434100 < baseStart_434100 := by decide
  rcases family_descends (prefixWord ++ tailWord_434100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434122 : List Nat := [3, 1, 2, 1, 2, 1, 4, 1, 8]
def baseStart_434122 : Nat := 118140960795 + 434122 * 2 ^ 59
def prefixEnd_434122 : Nat := 4983230072969 + 3 ^ 40 * 434122 * 2
def baseEnd_434122 : Nat := 24768138743472858819835

theorem tailTrace_434122 : CollatzResearch.WordTrace tailWord_434122 prefixEnd_434122 24768138743472858819835 := by
  unfold tailWord_434122
  simp only [CollatzResearch.WordTrace]
  refine ⟨3958432533314402744988155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10555820088838407319968413 3958432533314402744988155)
  ·
    refine ⟨5937648799971604117482233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3958432533314402744988155 5937648799971604117482233)
    ·
      refine ⟨4453236599978703088111675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5937648799971604117482233 4453236599978703088111675)
      ·
        refine ⟨6679854899968054632167513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4453236599978703088111675 6679854899968054632167513)
        ·
          refine ⟨5009891174976040974125635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6679854899968054632167513 5009891174976040974125635)
          ·
            refine ⟨7514836762464061461188453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5009891174976040974125635 7514836762464061461188453)
            ·
              refine ⟨1409031892962011523972835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7514836762464061461188453 1409031892962011523972835)
              ·
                refine ⟨2113547839443017285959253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1409031892962011523972835 2113547839443017285959253)
                ·
                  refine ⟨24768138743472858819835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2113547839443017285959253 24768138743472858819835)
                  ·
                    rfl

theorem cell23_434122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 8].length) (baseStart_434122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434122 prefixEnd_434122 := by exact prefixLift 434122
  have htrace : WordTrace (prefixWord ++ tailWord_434122) baseStart_434122 baseEnd_434122 := by
    simpa [prefixWord, tailWord_434122, baseEnd_434122] using wordTrace_append hprefix tailTrace_434122
  have hstable : (prefixWord ++ tailWord_434122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434122).length < 2 ^ (prefixWord ++ tailWord_434122).sum := by decide
  have hdescent : baseEnd_434122 < baseStart_434122 := by decide
  rcases family_descends (prefixWord ++ tailWord_434122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434239 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 3, 3, 3]
def baseStart_434239 : Nat := 118140960795 + 434239 * 2 ^ 59
def prefixEnd_434239 : Nat := 4983230072969 + 3 ^ 40 * 434239 * 2
def baseEnd_434239 : Nat := 222973325927831771615477

theorem tailTrace_434239 : CollatzResearch.WordTrace tailWord_434239 prefixEnd_434239 222973325927831771615477 := by
  unfold tailWord_434239
  simp only [CollatzResearch.WordTrace]
  refine ⟨15837997473833739961961771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10558664982555826641307847 15837997473833739961961771)
  ·
    refine ⟨23756996210750609942942657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15837997473833739961961771 23756996210750609942942657)
    ·
      refine ⟨17817747158062957457206993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23756996210750609942942657 17817747158062957457206993)
      ·
        refine ⟨13363310368547218092905245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17817747158062957457206993 13363310368547218092905245)
        ·
          refine ⟨5011241388205206784839467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13363310368547218092905245 5011241388205206784839467)
          ·
            refine ⟨7516862082307810177259201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5011241388205206784839467 7516862082307810177259201)
            ·
              refine ⟨5637646561730857632944401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7516862082307810177259201 5637646561730857632944401)
              ·
                refine ⟨4228234921298143224708301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5637646561730857632944401 4228234921298143224708301)
                ·
                  refine ⟨1585588095486803709265613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4228234921298143224708301 1585588095486803709265613)
                  ·
                    refine ⟨594595535807551390974605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1585588095486803709265613 594595535807551390974605)
                    ·
                      refine ⟨222973325927831771615477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 594595535807551390974605 222973325927831771615477)
                      ·
                        rfl

theorem cell23_434239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 3, 3].length) (baseStart_434239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434239 prefixEnd_434239 := by exact prefixLift 434239
  have htrace : WordTrace (prefixWord ++ tailWord_434239) baseStart_434239 baseEnd_434239 := by
    simpa [prefixWord, tailWord_434239, baseEnd_434239] using wordTrace_append hprefix tailTrace_434239
  have hstable : (prefixWord ++ tailWord_434239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434239).length < 2 ^ (prefixWord ++ tailWord_434239).sum := by decide
  have hdescent : baseEnd_434239 < baseStart_434239 := by decide
  rcases family_descends (prefixWord ++ tailWord_434239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434240 : List Nat := [2, 1, 1, 2, 2, 4, 2, 4, 1, 2, 2]
def baseStart_434240 : Nat := 118140960795 + 434240 * 2 ^ 59
def prefixEnd_434240 : Nat := 4983230072969 + 3 ^ 40 * 434240 * 2
def baseEnd_434240 : Nat := 222973839408486267702973

theorem tailTrace_434240 : CollatzResearch.WordTrace tailWord_434240 prefixEnd_434240 222973839408486267702973 := by
  unfold tailWord_434240
  simp only [CollatzResearch.WordTrace]
  refine ⟨7919016973415058566374087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10558689297886744755165449 7919016973415058566374087)
  ·
    refine ⟨11878525460122587849561131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7919016973415058566374087 11878525460122587849561131)
    ·
      refine ⟨17817788190183881774341697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11878525460122587849561131 17817788190183881774341697)
      ·
        refine ⟨13363341142637911330756273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17817788190183881774341697 13363341142637911330756273)
        ·
          refine ⟨10022505856978433498067205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13363341142637911330756273 10022505856978433498067205)
          ·
            refine ⟨1879219848183456280887601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10022505856978433498067205 1879219848183456280887601)
            ·
              refine ⟨1409414886137592210665701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1879219848183456280887601 1409414886137592210665701)
              ·
                refine ⟨264265291150798539499819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1409414886137592210665701 264265291150798539499819)
                ·
                  refine ⟨396397936726197809249729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 264265291150798539499819 396397936726197809249729)
                  ·
                    refine ⟨297298452544648356937297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 396397936726197809249729 297298452544648356937297)
                    ·
                      refine ⟨222973839408486267702973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 297298452544648356937297 222973839408486267702973)
                      ·
                        rfl

theorem cell23_434240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 4, 1, 2, 2].length) (baseStart_434240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_434240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_434240 prefixEnd_434240 := by exact prefixLift 434240
  have htrace : WordTrace (prefixWord ++ tailWord_434240) baseStart_434240 baseEnd_434240 := by
    simpa [prefixWord, tailWord_434240, baseEnd_434240] using wordTrace_append hprefix tailTrace_434240
  have hstable : (prefixWord ++ tailWord_434240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434240).length < 2 ^ (prefixWord ++ tailWord_434240).sum := by decide
  have hdescent : baseEnd_434240 < baseStart_434240 := by decide
  rcases family_descends (prefixWord ++ tailWord_434240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
