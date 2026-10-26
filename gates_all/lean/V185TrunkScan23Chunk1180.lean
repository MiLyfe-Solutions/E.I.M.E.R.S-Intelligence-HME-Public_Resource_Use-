import V185TrunkScan23Chunk1179

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6991743 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 6, 4]
def baseStart_6991743 : Nat := 118140960795 + 6991743 * 2 ^ 59
def prefixEnd_6991743 : Nat := 4983230072969 + 3 ^ 40 * 6991743 * 2
def baseEnd_6991743 : Nat := 1196708257236181169019355

theorem tailTrace_6991743 : CollatzResearch.WordTrace tailWord_6991743 prefixEnd_6991743 1196708257236181169019355 := by
  unfold tailWord_6991743
  simp only [CollatzResearch.WordTrace]
  refine ⟨255009817109116680482779883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170006544739411120321853255 255009817109116680482779883)
  ·
    refine ⟨382514725663675020724169825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255009817109116680482779883 382514725663675020724169825)
    ·
      refine ⟨286886044247756265543127369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382514725663675020724169825 286886044247756265543127369)
      ·
        refine ⟨215164533185817199157345527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286886044247756265543127369 215164533185817199157345527)
        ·
          refine ⟨322746799778725798736018291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215164533185817199157345527 322746799778725798736018291)
          ·
            refine ⟨484120199668088698104027437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322746799778725798736018291 484120199668088698104027437)
            ·
              refine ⟨181545074875533261789010289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 484120199668088698104027437 181545074875533261789010289)
              ·
                refine ⟨136158806156649946341757717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181545074875533261789010289 136158806156649946341757717)
                ·
                  refine ⟨6382444038592966234769893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 136158806156649946341757717 6382444038592966234769893)
                  ·
                    refine ⟨1196708257236181169019355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6382444038592966234769893 1196708257236181169019355)
                    ·
                      rfl

theorem cell23_6991743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 6, 4].length) (baseStart_6991743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991743 prefixEnd_6991743 := by exact prefixLift 6991743
  have htrace : WordTrace (prefixWord ++ tailWord_6991743) baseStart_6991743 baseEnd_6991743 := by
    simpa [prefixWord, tailWord_6991743, baseEnd_6991743] using wordTrace_append hprefix tailTrace_6991743
  have hstable : (prefixWord ++ tailWord_6991743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991743).length < 2 ^ (prefixWord ++ tailWord_6991743).sum := by decide
  have hdescent : baseEnd_6991743 < baseStart_6991743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991764 : List Nat := [2, 4, 2, 1, 1, 4, 2, 1, 1, 5]
def baseStart_6991764 : Nat := 118140960795 + 6991764 * 2 ^ 59
def prefixEnd_6991764 : Nat := 4983230072969 + 3 ^ 40 * 6991764 * 2
def baseEnd_6991764 : Nat := 1196711851600762641631823

theorem tailTrace_6991764 : CollatzResearch.WordTrace tailWord_6991764 prefixEnd_6991764 1196711851600762641631823 := by
  unfold tailWord_6991764
  simp only [CollatzResearch.WordTrace]
  refine ⟨127505291521020300534647173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170007055361360400712862897 127505291521020300534647173)
  ·
    refine ⟨23907242160191306350246345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127505291521020300534647173 23907242160191306350246345)
    ·
      refine ⟨17930431620143479762684759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23907242160191306350246345 17930431620143479762684759)
      ·
        refine ⟨26895647430215219644027139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17930431620143479762684759 26895647430215219644027139)
        ·
          refine ⟨40343471145322829466040709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26895647430215219644027139 40343471145322829466040709)
          ·
            refine ⟨7564400839748030524882633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40343471145322829466040709 7564400839748030524882633)
            ·
              refine ⟨5673300629811022893661975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7564400839748030524882633 5673300629811022893661975)
              ·
                refine ⟨8509950944716534340492963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5673300629811022893661975 8509950944716534340492963)
                ·
                  refine ⟨12764926417074801510739445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8509950944716534340492963 12764926417074801510739445)
                  ·
                    refine ⟨1196711851600762641631823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12764926417074801510739445 1196711851600762641631823)
                    ·
                      rfl

theorem cell23_6991764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_6991764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991764 prefixEnd_6991764 := by exact prefixLift 6991764
  have htrace : WordTrace (prefixWord ++ tailWord_6991764) baseStart_6991764 baseEnd_6991764 := by
    simpa [prefixWord, tailWord_6991764, baseEnd_6991764] using wordTrace_append hprefix tailTrace_6991764
  have hstable : (prefixWord ++ tailWord_6991764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991764).length < 2 ^ (prefixWord ++ tailWord_6991764).sum := by decide
  have hdescent : baseEnd_6991764 < baseStart_6991764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991767 : List Nat := [1, 1, 3, 3, 1, 3, 4, 1, 1, 1, 4]
def baseStart_6991767 : Nat := 118140960795 + 6991767 * 2 ^ 59
def prefixEnd_6991767 : Nat := 4983230072969 + 3 ^ 40 * 6991767 * 2
def baseEnd_6991767 : Nat := 3590137095244251413157955

theorem tailTrace_6991767 : CollatzResearch.WordTrace tailWord_6991767 prefixEnd_6991767 3590137095244251413157955 := by
  unfold tailWord_6991767
  simp only [CollatzResearch.WordTrace]
  refine ⟨255010692461029732581653555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170007128307353155054435703 255010692461029732581653555)
  ·
    refine ⟨382516038691544598872480333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255010692461029732581653555 382516038691544598872480333)
    ·
      refine ⟨143443514509329224577180125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 382516038691544598872480333 143443514509329224577180125)
      ·
        refine ⟨53791317940998459216442547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143443514509329224577180125 53791317940998459216442547)
        ·
          refine ⟨80686976911497688824663821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53791317940998459216442547 80686976911497688824663821)
          ·
            refine ⟨30257616341811633309248933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80686976911497688824663821 30257616341811633309248933)
            ·
              refine ⟨5673303064089681245484175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30257616341811633309248933 5673303064089681245484175)
              ·
                refine ⟨8509954596134521868226263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5673303064089681245484175 8509954596134521868226263)
                ·
                  refine ⟨12764931894201782802339395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8509954596134521868226263 12764931894201782802339395)
                  ·
                    refine ⟨19147397841302674203509093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12764931894201782802339395 19147397841302674203509093)
                    ·
                      refine ⟨3590137095244251413157955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19147397841302674203509093 3590137095244251413157955)
                      ·
                        rfl

theorem cell23_6991767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_6991767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991767 prefixEnd_6991767 := by exact prefixLift 6991767
  have htrace : WordTrace (prefixWord ++ tailWord_6991767) baseStart_6991767 baseEnd_6991767 := by
    simpa [prefixWord, tailWord_6991767, baseEnd_6991767] using wordTrace_append hprefix tailTrace_6991767
  have hstable : (prefixWord ++ tailWord_6991767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991767).length < 2 ^ (prefixWord ++ tailWord_6991767).sum := by decide
  have hdescent : baseEnd_6991767 < baseStart_6991767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991773 : List Nat := [1, 4, 2, 1, 2, 3, 10]
def baseStart_6991773 : Nat := 118140960795 + 6991773 * 2 ^ 59
def prefixEnd_6991773 : Nat := 4983230072969 + 3 ^ 40 * 6991773 * 2
def baseEnd_6991773 : Nat := 44322718223804671477567

theorem tailTrace_6991773 : CollatzResearch.WordTrace tailWord_6991773 prefixEnd_6991773 44322718223804671477567 := by
  unfold tailWord_6991773
  simp only [CollatzResearch.WordTrace]
  refine ⟨255010911299007995606371973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170007274199338663737581315 255010911299007995606371973)
  ·
    refine ⟨47814545868563999176194745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255010911299007995606371973 47814545868563999176194745)
    ·
      refine ⟨35860909401422999382146059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47814545868563999176194745 35860909401422999382146059)
      ·
        refine ⟨53791364102134499073219089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35860909401422999382146059 53791364102134499073219089)
        ·
          refine ⟨40343523076600874304914317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53791364102134499073219089 40343523076600874304914317)
          ·
            refine ⟨15128821153725327864342869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40343523076600874304914317 15128821153725327864342869)
            ·
              refine ⟨44322718223804671477567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15128821153725327864342869 44322718223804671477567)
              ·
                rfl

theorem cell23_6991773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 10].length) (baseStart_6991773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991773 prefixEnd_6991773 := by exact prefixLift 6991773
  have htrace : WordTrace (prefixWord ++ tailWord_6991773) baseStart_6991773 baseEnd_6991773 := by
    simpa [prefixWord, tailWord_6991773, baseEnd_6991773] using wordTrace_append hprefix tailTrace_6991773
  have hstable : (prefixWord ++ tailWord_6991773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991773).length < 2 ^ (prefixWord ++ tailWord_6991773).sum := by decide
  have hdescent : baseEnd_6991773 < baseStart_6991773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991777 : List Nat := [1, 2, 3, 4, 2, 1, 1, 1, 4, 4]
def baseStart_6991777 : Nat := 118140960795 + 6991777 * 2 ^ 59
def prefixEnd_6991777 : Nat := 4983230072969 + 3 ^ 40 * 6991777 * 2
def baseEnd_6991777 : Nat := 1196714076683598791344303

theorem tailTrace_6991777 : CollatzResearch.WordTrace tailWord_6991777 prefixEnd_6991777 1196714076683598791344303 := by
  unfold tailWord_6991777
  simp only [CollatzResearch.WordTrace]
  refine ⟨255011057190993504289517585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170007371460662336193011723 255011057190993504289517585)
  ·
    refine ⟨191258292893245128217138189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255011057190993504289517585 191258292893245128217138189)
    ·
      refine ⟨71721859834966923081426821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191258292893245128217138189 71721859834966923081426821)
      ·
        refine ⟨13447848719056298077767529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71721859834966923081426821 13447848719056298077767529)
        ·
          refine ⟨10085886539292223558325647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13447848719056298077767529 10085886539292223558325647)
          ·
            refine ⟨15128829808938335337488471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10085886539292223558325647 15128829808938335337488471)
            ·
              refine ⟨22693244713407503006232707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15128829808938335337488471 22693244713407503006232707)
              ·
                refine ⟨34039867070111254509349061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22693244713407503006232707 34039867070111254509349061)
                ·
                  refine ⟨6382475075645860220502949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34039867070111254509349061 6382475075645860220502949)
                  ·
                    refine ⟨1196714076683598791344303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6382475075645860220502949 1196714076683598791344303)
                    ·
                      rfl

theorem cell23_6991777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_6991777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991777 prefixEnd_6991777 := by exact prefixLift 6991777
  have htrace : WordTrace (prefixWord ++ tailWord_6991777) baseStart_6991777 baseEnd_6991777 := by
    simpa [prefixWord, tailWord_6991777, baseEnd_6991777] using wordTrace_append hprefix tailTrace_6991777
  have hstable : (prefixWord ++ tailWord_6991777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991777).length < 2 ^ (prefixWord ++ tailWord_6991777).sum := by decide
  have hdescent : baseEnd_6991777 < baseStart_6991777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991797 : List Nat := [1, 3, 3, 2, 1, 4, 1, 1, 1, 2, 4]
def baseStart_6991797 : Nat := 118140960795 + 6991797 * 2 ^ 59
def prefixEnd_6991797 : Nat := 4983230072969 + 3 ^ 40 * 6991797 * 2
def baseEnd_6991797 : Nat := 3590152499663886295782817

theorem tailTrace_6991797 : CollatzResearch.WordTrace tailWord_6991797 prefixEnd_6991797 3590152499663886295782817 := by
  unfold tailWord_6991797
  simp only [CollatzResearch.WordTrace]
  refine ⟨255011786650921047705245645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170007857767280698470163763 255011786650921047705245645)
  ·
    refine ⟨95629419994095392889467117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255011786650921047705245645 95629419994095392889467117)
    ·
      refine ⟨35861032497785772333550169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95629419994095392889467117 35861032497785772333550169)
      ·
        refine ⟨26895774373339329250162627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35861032497785772333550169 26895774373339329250162627)
        ·
          refine ⟨40343661560008993875243941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26895774373339329250162627 40343661560008993875243941)
          ·
            refine ⟨7564436542501686351608239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40343661560008993875243941 7564436542501686351608239)
            ·
              refine ⟨11346654813752529527412359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7564436542501686351608239 11346654813752529527412359)
              ·
                refine ⟨17019982220628794291118539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11346654813752529527412359 17019982220628794291118539)
                ·
                  refine ⟨25529973330943191436677809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17019982220628794291118539 25529973330943191436677809)
                  ·
                    refine ⟨19147479998207393577508357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25529973330943191436677809 19147479998207393577508357)
                    ·
                      refine ⟨3590152499663886295782817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19147479998207393577508357 3590152499663886295782817)
                      ·
                        rfl

theorem cell23_6991797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_6991797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991797 prefixEnd_6991797 := by exact prefixLift 6991797
  have htrace : WordTrace (prefixWord ++ tailWord_6991797) baseStart_6991797 baseEnd_6991797 := by
    simpa [prefixWord, tailWord_6991797, baseEnd_6991797] using wordTrace_append hprefix tailTrace_6991797
  have hstable : (prefixWord ++ tailWord_6991797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991797).length < 2 ^ (prefixWord ++ tailWord_6991797).sum := by decide
  have hdescent : baseEnd_6991797 < baseStart_6991797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991885 : List Nat := [1, 7, 1, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_6991885 : Nat := 118140960795 + 6991885 * 2 ^ 59
def prefixEnd_6991885 : Nat := 4983230072969 + 3 ^ 40 * 6991885 * 2
def baseEnd_6991885 : Nat := 3590197685961481951482413

theorem tailTrace_6991885 : CollatzResearch.WordTrace tailWord_6991885 prefixEnd_6991885 3590197685961481951482413 := by
  unfold tailWord_6991885
  simp only [CollatzResearch.WordTrace]
  refine ⟨255014996274602238734449109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170009997516401492489632739 255014996274602238734449109)
  ·
    refine ⟨5976913975185989970338651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 255014996274602238734449109 5976913975185989970338651)
    ·
      refine ⟨8965370962778984955507977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5976913975185989970338651 8965370962778984955507977)
      ·
        refine ⟨6724028222084238716630983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8965370962778984955507977 6724028222084238716630983)
        ·
          refine ⟨10086042333126358074946475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6724028222084238716630983 10086042333126358074946475)
          ·
            refine ⟨15129063499689537112419713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10086042333126358074946475 15129063499689537112419713)
            ·
              refine ⟨11346797624767152834314785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15129063499689537112419713 11346797624767152834314785)
              ·
                refine ⟨8510098218575364625736089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11346797624767152834314785 8510098218575364625736089)
                ·
                  refine ⟨6382573663931523469302067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8510098218575364625736089 6382573663931523469302067)
                  ·
                    refine ⟨9573860495897285203953101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6382573663931523469302067 9573860495897285203953101)
                    ·
                      refine ⟨3590197685961481951482413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9573860495897285203953101 3590197685961481951482413)
                      ·
                        rfl

theorem cell23_6991885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_6991885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991885 prefixEnd_6991885 := by exact prefixLift 6991885
  have htrace : WordTrace (prefixWord ++ tailWord_6991885) baseStart_6991885 baseEnd_6991885 := by
    simpa [prefixWord, tailWord_6991885, baseEnd_6991885] using wordTrace_append hprefix tailTrace_6991885
  have hstable : (prefixWord ++ tailWord_6991885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991885).length < 2 ^ (prefixWord ++ tailWord_6991885).sum := by decide
  have hdescent : baseEnd_6991885 < baseStart_6991885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991957 : List Nat := [1, 3, 2, 2, 1, 3, 1, 3, 3, 4]
def baseStart_6991957 : Nat := 118140960795 + 6991957 * 2 ^ 59
def prefixEnd_6991957 : Nat := 4983230072969 + 3 ^ 40 * 6991957 * 2
def baseEnd_6991957 : Nat := 1196744885522868556594027

theorem tailTrace_6991957 : CollatzResearch.WordTrace tailWord_6991957 prefixEnd_6991957 1196744885522868556594027 := by
  unfold tailWord_6991957
  simp only [CollatzResearch.WordTrace]
  refine ⟨255017622330341395031070125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170011748220227596687380083 255017622330341395031070125)
  ·
    refine ⟨95631608373878023136651297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255017622330341395031070125 95631608373878023136651297)
    ·
      refine ⟨71723706280408517352488473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95631608373878023136651297 71723706280408517352488473)
      ·
        refine ⟨53792779710306388014366355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71723706280408517352488473 53792779710306388014366355)
        ·
          refine ⟨80689169565459582021549533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53792779710306388014366355 80689169565459582021549533)
          ·
            refine ⟨30258438587047343258081075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80689169565459582021549533 30258438587047343258081075)
            ·
              refine ⟨45387657880571014887121613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30258438587047343258081075 45387657880571014887121613)
              ·
                refine ⟨17020371705214130582670605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45387657880571014887121613 17020371705214130582670605)
                ·
                  refine ⟨6382639389455298968501477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17020371705214130582670605 6382639389455298968501477)
                  ·
                    refine ⟨1196744885522868556594027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6382639389455298968501477 1196744885522868556594027)
                    ·
                      rfl

theorem cell23_6991957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_6991957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991957 prefixEnd_6991957 := by exact prefixLift 6991957
  have htrace : WordTrace (prefixWord ++ tailWord_6991957) baseStart_6991957 baseEnd_6991957 := by
    simpa [prefixWord, tailWord_6991957, baseEnd_6991957] using wordTrace_append hprefix tailTrace_6991957
  have hstable : (prefixWord ++ tailWord_6991957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991957).length < 2 ^ (prefixWord ++ tailWord_6991957).sum := by decide
  have hdescent : baseEnd_6991957 < baseStart_6991957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991964 : List Nat := [2, 2, 4, 1, 1, 2, 2, 1, 2, 4, 2]
def baseStart_6991964 : Nat := 118140960795 + 6991964 * 2 ^ 59
def prefixEnd_6991964 : Nat := 4983230072969 + 3 ^ 40 * 6991964 * 2
def baseEnd_6991964 : Nat := 3590238250933187142394549

theorem tailTrace_6991964 : CollatzResearch.WordTrace tailWord_6991964 prefixEnd_6991964 3590238250933187142394549 := by
  unfold tailWord_6991964
  simp only [CollatzResearch.WordTrace]
  refine ⟨127508938820658017613287473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170011918427544023484383297 127508938820658017613287473)
  ·
    refine ⟨95631704115493513209965605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127508938820658017613287473 95631704115493513209965605)
    ·
      refine ⟨17930944521655033726868551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95631704115493513209965605 17930944521655033726868551)
      ·
        refine ⟨26896416782482550590302827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17930944521655033726868551 26896416782482550590302827)
        ·
          refine ⟨40344625173723825885454241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26896416782482550590302827 40344625173723825885454241)
          ·
            refine ⟨30258468880292869414090681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40344625173723825885454241 30258468880292869414090681)
            ·
              refine ⟨22693851660219652060568011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30258468880292869414090681 22693851660219652060568011)
              ·
                refine ⟨34040777490329478090852017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22693851660219652060568011 34040777490329478090852017)
                ·
                  refine ⟨25530583117747108568139013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34040777490329478090852017 25530583117747108568139013)
                  ·
                    refine ⟨4786984334577582856526065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25530583117747108568139013 4786984334577582856526065)
                    ·
                      refine ⟨3590238250933187142394549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4786984334577582856526065 3590238250933187142394549)
                      ·
                        rfl

theorem cell23_6991964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_6991964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991964 prefixEnd_6991964 := by exact prefixLift 6991964
  have htrace : WordTrace (prefixWord ++ tailWord_6991964) baseStart_6991964 baseEnd_6991964 := by
    simpa [prefixWord, tailWord_6991964, baseEnd_6991964] using wordTrace_append hprefix tailTrace_6991964
  have hstable : (prefixWord ++ tailWord_6991964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991964).length < 2 ^ (prefixWord ++ tailWord_6991964).sum := by decide
  have hdescent : baseEnd_6991964 < baseStart_6991964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991991 : List Nat := [1, 1, 3, 1, 1, 7, 1, 3, 1, 4]
def baseStart_6991991 : Nat := 118140960795 + 6991991 * 2 ^ 59
def prefixEnd_6991991 : Nat := 4983230072969 + 3 ^ 40 * 6991991 * 2
def baseEnd_6991991 : Nat := 1196750704970286178918975

theorem tailTrace_6991991 : CollatzResearch.WordTrace tailWord_6991991 prefixEnd_6991991 1196750704970286178918975 := by
  unfold tailWord_6991991
  simp only [CollatzResearch.WordTrace]
  refine ⟨255018862412218218837807827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170012574941478812558538551 255018862412218218837807827)
  ·
    refine ⟨382528293618327328256711741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255018862412218218837807827 382528293618327328256711741)
    ·
      refine ⟨143448110106872748096266903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 382528293618327328256711741 143448110106872748096266903)
      ·
        refine ⟨215172165160309122144400355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143448110106872748096266903 215172165160309122144400355)
        ·
          refine ⟨322758247740463683216600533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215172165160309122144400355 322758247740463683216600533)
          ·
            refine ⟨7564646431417117575389075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 322758247740463683216600533 7564646431417117575389075)
            ·
              refine ⟨11346969647125676363083613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7564646431417117575389075 11346969647125676363083613)
              ·
                refine ⟨4255113617672128636156355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11346969647125676363083613 4255113617672128636156355)
                ·
                  refine ⟨6382670426508192954234533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4255113617672128636156355 6382670426508192954234533)
                  ·
                    refine ⟨1196750704970286178918975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6382670426508192954234533 1196750704970286178918975)
                    ·
                      rfl

theorem cell23_6991991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 3, 1, 4].length) (baseStart_6991991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991991 prefixEnd_6991991 := by exact prefixLift 6991991
  have htrace : WordTrace (prefixWord ++ tailWord_6991991) baseStart_6991991 baseEnd_6991991 := by
    simpa [prefixWord, tailWord_6991991, baseEnd_6991991] using wordTrace_append hprefix tailTrace_6991991
  have hstable : (prefixWord ++ tailWord_6991991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991991).length < 2 ^ (prefixWord ++ tailWord_6991991).sum := by decide
  have hdescent : baseEnd_6991991 < baseStart_6991991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992000 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 5, 5]
def baseStart_6992000 : Nat := 118140960795 + 6992000 * 2 ^ 59
def prefixEnd_6992000 : Nat := 4983230072969 + 3 ^ 40 * 6992000 * 2
def baseEnd_6992000 : Nat := 1196752245412249667181461

theorem tailTrace_6992000 : CollatzResearch.WordTrace tailWord_6992000 prefixEnd_6992000 1196752245412249667181461 := by
  unfold tailWord_6992000
  simp only [CollatzResearch.WordTrace]
  refine ⟨127509595334592806687442727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170012793779457075583256969 127509595334592806687442727)
  ·
    refine ⟨191264393001889210031164091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127509595334592806687442727 191264393001889210031164091)
    ·
      refine ⟨286896589502833815046746137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191264393001889210031164091 286896589502833815046746137)
      ·
        refine ⟨215172442127125361285059603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286896589502833815046746137 215172442127125361285059603)
        ·
          refine ⟨322758663190688041927589405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215172442127125361285059603 322758663190688041927589405)
          ·
            refine ⟨121034498696508015722846027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 322758663190688041927589405 121034498696508015722846027)
            ·
              refine ⟨181551748044762023584269041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121034498696508015722846027 181551748044762023584269041)
              ·
                refine ⟨136163811033571517688201781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181551748044762023584269041 136163811033571517688201781)
                ·
                  refine ⟨12765357284397329783268917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136163811033571517688201781 12765357284397329783268917)
                  ·
                    refine ⟨1196752245412249667181461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12765357284397329783268917 1196752245412249667181461)
                    ·
                      rfl

theorem cell23_6992000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 5, 5].length) (baseStart_6992000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992000 prefixEnd_6992000 := by exact prefixLift 6992000
  have htrace : WordTrace (prefixWord ++ tailWord_6992000) baseStart_6992000 baseEnd_6992000 := by
    simpa [prefixWord, tailWord_6992000, baseEnd_6992000] using wordTrace_append hprefix tailTrace_6992000
  have hstable : (prefixWord ++ tailWord_6992000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992000).length < 2 ^ (prefixWord ++ tailWord_6992000).sum := by decide
  have hdescent : baseEnd_6992000 < baseStart_6992000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992008 : List Nat := [2, 1, 3, 4, 1, 2, 3, 2, 1, 4]
def baseStart_6992008 : Nat := 118140960795 + 6992008 * 2 ^ 59
def prefixEnd_6992008 : Nat := 4983230072969 + 3 ^ 40 * 6992008 * 2
def baseEnd_6992008 : Nat := 1196753614693994990081449

theorem tailTrace_6992008 : CollatzResearch.WordTrace tailWord_6992008 prefixEnd_6992008 1196753614693994990081449 := by
  unfold tailWord_6992008
  simp only [CollatzResearch.WordTrace]
  refine ⟨127509741226578315370588339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170012988302104420494117785 127509741226578315370588339)
  ·
    refine ⟨191264611839867473055882509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127509741226578315370588339 191264611839867473055882509)
    ·
      refine ⟨71724229439950302395955941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191264611839867473055882509 71724229439950302395955941)
      ·
        refine ⟨13448293019990681699241739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71724229439950302395955941 13448293019990681699241739)
        ·
          refine ⟨20172439529986022548862609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13448293019990681699241739 20172439529986022548862609)
          ·
            refine ⟨15129329647489516911646957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20172439529986022548862609 15129329647489516911646957)
            ·
              refine ⟨5673498617808568841867609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15129329647489516911646957 5673498617808568841867609)
              ·
                refine ⟨4255123963356426631400707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5673498617808568841867609 4255123963356426631400707)
                ·
                  refine ⟨6382685945034639947101061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4255123963356426631400707 6382685945034639947101061)
                  ·
                    refine ⟨1196753614693994990081449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6382685945034639947101061 1196753614693994990081449)
                    ·
                      rfl

theorem cell23_6992008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_6992008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992008 prefixEnd_6992008 := by exact prefixLift 6992008
  have htrace : WordTrace (prefixWord ++ tailWord_6992008) baseStart_6992008 baseEnd_6992008 := by
    simpa [prefixWord, tailWord_6992008, baseEnd_6992008] using wordTrace_append hprefix tailTrace_6992008
  have hstable : (prefixWord ++ tailWord_6992008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992008).length < 2 ^ (prefixWord ++ tailWord_6992008).sum := by decide
  have hdescent : baseEnd_6992008 < baseStart_6992008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992034 : List Nat := [3, 3, 1, 3, 1, 2, 1, 1, 3, 5]
def baseStart_6992034 : Nat := 118140960795 + 6992034 * 2 ^ 59
def prefixEnd_6992034 : Nat := 4983230072969 + 3 ^ 40 * 6992034 * 2
def baseEnd_6992034 : Nat := 1196758064859667289506409

theorem tailTrace_6992034 : CollatzResearch.WordTrace tailWord_6992034 prefixEnd_6992034 1196758064859667289506409 := by
  unfold tailWord_6992034
  simp only [CollatzResearch.WordTrace]
  refine ⟨63755107687765609295405789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170013620500708291454415437 63755107687765609295405789)
  ·
    refine ⟨23908165382912103485777171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63755107687765609295405789 23908165382912103485777171)
    ·
      refine ⟨35862248074368155228665757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23908165382912103485777171 35862248074368155228665757)
      ·
        refine ⟨13448343027888058210749659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35862248074368155228665757 13448343027888058210749659)
        ·
          refine ⟨20172514541832087316124489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13448343027888058210749659 20172514541832087316124489)
          ·
            refine ⟨15129385906374065487093367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20172514541832087316124489 15129385906374065487093367)
            ·
              refine ⟨22694078859561098230640051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15129385906374065487093367 22694078859561098230640051)
              ·
                refine ⟨34041118289341647345960077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22694078859561098230640051 34041118289341647345960077)
                ·
                  refine ⟨12765419358503117754735029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34041118289341647345960077 12765419358503117754735029)
                  ·
                    refine ⟨1196758064859667289506409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12765419358503117754735029 1196758064859667289506409)
                    ·
                      rfl

theorem cell23_6992034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_6992034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992034 prefixEnd_6992034 := by exact prefixLift 6992034
  have htrace : WordTrace (prefixWord ++ tailWord_6992034) baseStart_6992034 baseEnd_6992034 := by
    simpa [prefixWord, tailWord_6992034, baseEnd_6992034] using wordTrace_append hprefix tailTrace_6992034
  have hstable : (prefixWord ++ tailWord_6992034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992034).length < 2 ^ (prefixWord ++ tailWord_6992034).sum := by decide
  have hdescent : baseEnd_6992034 < baseStart_6992034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992037 : List Nat := [1, 3, 1, 2, 1, 3, 3, 1, 3, 1, 4]
def baseStart_6992037 : Nat := 118140960795 + 6992037 * 2 ^ 59
def prefixEnd_6992037 : Nat := 4983230072969 + 3 ^ 40 * 6992037 * 2
def baseEnd_6992037 : Nat := 3590275735020965356781713

theorem tailTrace_6992037 : CollatzResearch.WordTrace tailWord_6992037 prefixEnd_6992037 3590275735020965356781713 := by
  unfold tailWord_6992037
  simp only [CollatzResearch.WordTrace]
  refine ⟨255020540170051568693982365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170013693446701045795988243 255020540170051568693982365)
  ·
    refine ⟨95632702563769338260243387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255020540170051568693982365 95632702563769338260243387)
    ·
      refine ⟨143449053845654007390365081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95632702563769338260243387 143449053845654007390365081)
      ·
        refine ⟨107586790384240505542773811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143449053845654007390365081 107586790384240505542773811)
        ·
          refine ⟨161380185576360758314160717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107586790384240505542773811 161380185576360758314160717)
          ·
            refine ⟨60517569591135284367810269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161380185576360758314160717 60517569591135284367810269)
            ·
              refine ⟨22694088596675731637928851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60517569591135284367810269 22694088596675731637928851)
              ·
                refine ⟨34041132895013597456893277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22694088596675731637928851 34041132895013597456893277)
                ·
                  refine ⟨12765424835630099046334979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34041132895013597456893277 12765424835630099046334979)
                  ·
                    refine ⟨19148137253445148569502469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12765424835630099046334979 19148137253445148569502469)
                    ·
                      refine ⟨3590275735020965356781713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19148137253445148569502469 3590275735020965356781713)
                      ·
                        rfl

theorem cell23_6992037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_6992037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992037 prefixEnd_6992037 := by exact prefixLift 6992037
  have htrace : WordTrace (prefixWord ++ tailWord_6992037) baseStart_6992037 baseEnd_6992037 := by
    simpa [prefixWord, tailWord_6992037, baseEnd_6992037] using wordTrace_append hprefix tailTrace_6992037
  have hstable : (prefixWord ++ tailWord_6992037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992037).length < 2 ^ (prefixWord ++ tailWord_6992037).sum := by decide
  have hdescent : baseEnd_6992037 < baseStart_6992037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992060 : List Nat := [2, 2, 2, 3, 14]
def baseStart_6992060 : Nat := 118140960795 + 6992060 * 2 ^ 59
def prefixEnd_6992060 : Nat := 4983230072969 + 3 ^ 40 * 6992060 * 2
def baseEnd_6992060 : Nat := 4924948621503455098483

theorem tailTrace_6992060 : CollatzResearch.WordTrace tailWord_6992060 prefixEnd_6992060 4924948621503455098483 := by
  unfold tailWord_6992060
  simp only [CollatzResearch.WordTrace]
  refine ⟨127510689524484121811034817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170014252699312162414713089 127510689524484121811034817)
  ·
    refine ⟨95633017143363091358276113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127510689524484121811034817 95633017143363091358276113)
    ·
      refine ⟨71724762857522318518707085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95633017143363091358276113 71724762857522318518707085)
      ·
        refine ⟨26896786071570869444515157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71724762857522318518707085 26896786071570869444515157)
        ·
          refine ⟨4924948621503455098483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 26896786071570869444515157 4924948621503455098483)
          ·
            rfl

theorem cell23_6992060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 14].length) (baseStart_6992060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992060 prefixEnd_6992060 := by exact prefixLift 6992060
  have htrace : WordTrace (prefixWord ++ tailWord_6992060) baseStart_6992060 baseEnd_6992060 := by
    simpa [prefixWord, tailWord_6992060, baseEnd_6992060] using wordTrace_append hprefix tailTrace_6992060
  have hstable : (prefixWord ++ tailWord_6992060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992060).length < 2 ^ (prefixWord ++ tailWord_6992060).sum := by decide
  have hdescent : baseEnd_6992060 < baseStart_6992060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992064 : List Nat := [2, 1, 1, 2, 5, 1, 1, 4, 2, 4]
def baseStart_6992064 : Nat := 118140960795 + 6992064 * 2 ^ 59
def prefixEnd_6992064 : Nat := 4983230072969 + 3 ^ 40 * 6992064 * 2
def baseEnd_6992064 : Nat := 1196763199666212250381363

theorem tailTrace_6992064 : CollatzResearch.WordTrace tailWord_6992064 prefixEnd_6992064 1196763199666212250381363 := by
  unfold tailWord_6992064
  simp only [CollatzResearch.WordTrace]
  refine ⟨127510762470476876152607623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170014349960635834870143497 127510762470476876152607623)
  ·
    refine ⟨191266143705715314228911435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127510762470476876152607623 191266143705715314228911435)
    ·
      refine ⟨286899215558572971343367153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191266143705715314228911435 286899215558572971343367153)
      ·
        refine ⟨215174411668929728507525365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286899215558572971343367153 215174411668929728507525365)
        ·
          refine ⟨20172601093962162047580503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 215174411668929728507525365 20172601093962162047580503)
          ·
            refine ⟨30258901640943243071370755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20172601093962162047580503 30258901640943243071370755)
            ·
              refine ⟨45388352461414864607056133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30258901640943243071370755 45388352461414864607056133)
              ·
                refine ⟨8510316086515287113823025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45388352461414864607056133 8510316086515287113823025)
                ·
                  refine ⟨6382737064886465335367269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8510316086515287113823025 6382737064886465335367269)
                  ·
                    refine ⟨1196763199666212250381363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6382737064886465335367269 1196763199666212250381363)
                    ·
                      rfl

theorem cell23_6992064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 2, 4].length) (baseStart_6992064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992064 prefixEnd_6992064 := by exact prefixLift 6992064
  have htrace : WordTrace (prefixWord ++ tailWord_6992064) baseStart_6992064 baseEnd_6992064 := by
    simpa [prefixWord, tailWord_6992064, baseEnd_6992064] using wordTrace_append hprefix tailTrace_6992064
  have hstable : (prefixWord ++ tailWord_6992064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992064).length < 2 ^ (prefixWord ++ tailWord_6992064).sum := by decide
  have hdescent : baseEnd_6992064 < baseStart_6992064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992065 : List Nat := [1, 2, 6, 1, 2, 1, 1, 4, 1, 1, 3]
def baseStart_6992065 : Nat := 118140960795 + 6992065 * 2 ^ 59
def prefixEnd_6992065 : Nat := 4983230072969 + 3 ^ 40 * 6992065 * 2
def baseEnd_6992065 : Nat := 3590290112479291247231585

theorem tailTrace_6992065 : CollatzResearch.WordTrace tailWord_6992065 prefixEnd_6992065 3590290112479291247231585 := by
  unfold tailWord_6992065
  simp only [CollatzResearch.WordTrace]
  refine ⟨255021561413950129476001649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170014374275966752984001099 255021561413950129476001649)
  ·
    refine ⟨191266171060462597107001237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255021561413950129476001649 191266171060462597107001237)
    ·
      refine ⟨8965601768459184239390683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 191266171060462597107001237 8965601768459184239390683)
      ·
        refine ⟨13448402652688776359086025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8965601768459184239390683 13448402652688776359086025)
        ·
          refine ⟨10086301989516582269314519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13448402652688776359086025 10086301989516582269314519)
          ·
            refine ⟨15129452984274873403971779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10086301989516582269314519 15129452984274873403971779)
            ·
              refine ⟨22694179476412310105957669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15129452984274873403971779 22694179476412310105957669)
              ·
                refine ⟨4255158651827308144867063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22694179476412310105957669 4255158651827308144867063)
                ·
                  refine ⟨6382737977740962217300595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4255158651827308144867063 6382737977740962217300595)
                  ·
                    refine ⟨9574106966611443325950893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6382737977740962217300595 9574106966611443325950893)
                    ·
                      refine ⟨3590290112479291247231585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9574106966611443325950893 3590290112479291247231585)
                      ·
                        rfl

theorem cell23_6992065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_6992065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992065 prefixEnd_6992065 := by exact prefixLift 6992065
  have htrace : WordTrace (prefixWord ++ tailWord_6992065) baseStart_6992065 baseEnd_6992065 := by
    simpa [prefixWord, tailWord_6992065, baseEnd_6992065] using wordTrace_append hprefix tailTrace_6992065
  have hstable : (prefixWord ++ tailWord_6992065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992065).length < 2 ^ (prefixWord ++ tailWord_6992065).sum := by decide
  have hdescent : baseEnd_6992065 < baseStart_6992065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992092 : List Nat := [2, 2, 5, 2, 2, 1, 1, 1, 2, 3, 2]
def baseStart_6992092 : Nat := 118140960795 + 6992092 * 2 ^ 59
def prefixEnd_6992092 : Nat := 4983230072969 + 3 ^ 40 * 6992092 * 2
def baseEnd_6992092 : Nat := 3590303976456962641593961

theorem tailTrace_6992092 : CollatzResearch.WordTrace tailWord_6992092 prefixEnd_6992092 3590303976456962641593961 := by
  unfold tailWord_6992092
  simp only [CollatzResearch.WordTrace]
  refine ⟨127511273092426156543617265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170015030789901542058156353 127511273092426156543617265)
  ·
    refine ⟨95633454819319617407712949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127511273092426156543617265 95633454819319617407712949)
    ·
      refine ⟨8965636389311214131973089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95633454819319617407712949 8965636389311214131973089)
      ·
        refine ⟨6724227291983410598979817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8965636389311214131973089 6724227291983410598979817)
        ·
          refine ⟨5043170468987557949234863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6724227291983410598979817 5043170468987557949234863)
          ·
            refine ⟨7564755703481336923852295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5043170468987557949234863 7564755703481336923852295)
            ·
              refine ⟨11347133555222005385778443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7564755703481336923852295 11347133555222005385778443)
              ·
                refine ⟨17020700332833008078667665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11347133555222005385778443 17020700332833008078667665)
                ·
                  refine ⟨12765525249624756059000749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17020700332833008078667665 12765525249624756059000749)
                  ·
                    refine ⟨4787071968609283522125281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12765525249624756059000749 4787071968609283522125281)
                    ·
                      refine ⟨3590303976456962641593961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4787071968609283522125281 3590303976456962641593961)
                      ·
                        rfl

theorem cell23_6992092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_6992092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992092 prefixEnd_6992092 := by exact prefixLift 6992092
  have htrace : WordTrace (prefixWord ++ tailWord_6992092) baseStart_6992092 baseEnd_6992092 := by
    simpa [prefixWord, tailWord_6992092, baseEnd_6992092] using wordTrace_append hprefix tailTrace_6992092
  have hstable : (prefixWord ++ tailWord_6992092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992092).length < 2 ^ (prefixWord ++ tailWord_6992092).sum := by decide
  have hdescent : baseEnd_6992092 < baseStart_6992092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992104 : List Nat := [2, 1, 4, 1, 2, 2, 2, 2, 1, 3, 3]
def baseStart_6992104 : Nat := 118140960795 + 6992104 * 2 ^ 59
def prefixEnd_6992104 : Nat := 4983230072969 + 3 ^ 40 * 6992104 * 2
def baseEnd_6992104 : Nat := 3590310138224816594643905

theorem tailTrace_6992104 : CollatzResearch.WordTrace tailWord_6992104 prefixEnd_6992104 3590310138224816594643905 := by
  unfold tailWord_6992104
  simp only [CollatzResearch.WordTrace]
  refine ⟨127511491930404419568335683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170015322573872559424447577 127511491930404419568335683)
  ·
    refine ⟨191267237895606629352503525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127511491930404419568335683 191267237895606629352503525)
    ·
      refine ⟨35862607105426243003594411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191267237895606629352503525 35862607105426243003594411)
      ·
        refine ⟨53793910658139364505391617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35862607105426243003594411 53793910658139364505391617)
        ·
          refine ⟨40345432993604523379043713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53793910658139364505391617 40345432993604523379043713)
          ·
            refine ⟨30259074745203392534282785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40345432993604523379043713 30259074745203392534282785)
            ·
              refine ⟨22694306058902544400712089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30259074745203392534282785 22694306058902544400712089)
              ·
                refine ⟨17020729544176908300534067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22694306058902544400712089 17020729544176908300534067)
                ·
                  refine ⟨25531094316265362450801101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17020729544176908300534067 25531094316265362450801101)
                  ·
                    refine ⟨9574160368599510919050413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25531094316265362450801101 9574160368599510919050413)
                    ·
                      refine ⟨3590310138224816594643905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9574160368599510919050413 3590310138224816594643905)
                      ·
                        rfl

theorem cell23_6992104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_6992104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992104 prefixEnd_6992104 := by exact prefixLift 6992104
  have htrace : WordTrace (prefixWord ++ tailWord_6992104) baseStart_6992104 baseEnd_6992104 := by
    simpa [prefixWord, tailWord_6992104, baseEnd_6992104] using wordTrace_append hprefix tailTrace_6992104
  have hstable : (prefixWord ++ tailWord_6992104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992104).length < 2 ^ (prefixWord ++ tailWord_6992104).sum := by decide
  have hdescent : baseEnd_6992104 < baseStart_6992104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992137 : List Nat := [1, 2, 1, 1, 3, 4, 2, 1, 2, 6]
def baseStart_6992137 : Nat := 118140960795 + 6992137 * 2 ^ 59
def prefixEnd_6992137 : Nat := 4983230072969 + 3 ^ 40 * 6992137 * 2
def baseEnd_6992137 : Nat := 1196775694362138321843751

theorem tailTrace_6992137 : CollatzResearch.WordTrace tailWord_6992137 prefixEnd_6992137 1196775694362138321843751 := by
  unfold tailWord_6992137
  simp only [CollatzResearch.WordTrace]
  refine ⟨255024187469689285772622665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170016124979792857181748443 255024187469689285772622665)
  ·
    refine ⟨191268140602266964329466999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255024187469689285772622665 191268140602266964329466999)
    ·
      refine ⟨286902210903400446494200499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191268140602266964329466999 286902210903400446494200499)
      ·
        refine ⟨430353316355100669741300749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286902210903400446494200499 430353316355100669741300749)
        ·
          refine ⟨161382493633162751152987781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 430353316355100669741300749 161382493633162751152987781)
          ·
            refine ⟨30259217556218015841185209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161382493633162751152987781 30259217556218015841185209)
            ·
              refine ⟨22694413167163511880888907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30259217556218015841185209 22694413167163511880888907)
              ·
                refine ⟨34041619750745267821333361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22694413167163511880888907 34041619750745267821333361)
                ·
                  refine ⟨25531214813058950866000021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34041619750745267821333361 25531214813058950866000021)
                  ·
                    refine ⟨1196775694362138321843751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25531214813058950866000021 1196775694362138321843751)
                    ·
                      rfl

theorem cell23_6992137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 6].length) (baseStart_6992137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992137 prefixEnd_6992137 := by exact prefixLift 6992137
  have htrace : WordTrace (prefixWord ++ tailWord_6992137) baseStart_6992137 baseEnd_6992137 := by
    simpa [prefixWord, tailWord_6992137, baseEnd_6992137] using wordTrace_append hprefix tailTrace_6992137
  have hstable : (prefixWord ++ tailWord_6992137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992137).length < 2 ^ (prefixWord ++ tailWord_6992137).sum := by decide
  have hdescent : baseEnd_6992137 < baseStart_6992137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992147 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 2, 4, 3]
def baseStart_6992147 : Nat := 118140960795 + 6992147 * 2 ^ 59
def prefixEnd_6992147 : Nat := 4983230072969 + 3 ^ 40 * 6992147 * 2
def baseEnd_6992147 : Nat := 3590332217892959926406207

theorem tailTrace_6992147 : CollatzResearch.WordTrace tailWord_6992147 prefixEnd_6992147 3590332217892959926406207 := by
  unfold tailWord_6992147
  simp only [CollatzResearch.WordTrace]
  refine ⟨255024552199653057480486695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170016368133102038320324463 255024552199653057480486695)
  ·
    refine ⟨382536828299479586220730043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255024552199653057480486695 382536828299479586220730043)
    ·
      refine ⟨573805242449219379331095065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382536828299479586220730043 573805242449219379331095065)
      ·
        refine ⟨430353931836914534498321299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 573805242449219379331095065 430353931836914534498321299)
        ·
          refine ⟨645530897755371801747481949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430353931836914534498321299 645530897755371801747481949)
          ·
            refine ⟨242074086658264425655305731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 645530897755371801747481949 242074086658264425655305731)
            ·
              refine ⟨363111129987396638482958597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242074086658264425655305731 363111129987396638482958597)
              ·
                refine ⟨68083336872636869715554737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 363111129987396638482958597 68083336872636869715554737)
                ·
                  refine ⟨51062502654477652286666053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68083336872636869715554737 51062502654477652286666053)
                  ·
                    refine ⟨9574219247714559803749885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51062502654477652286666053 9574219247714559803749885)
                    ·
                      refine ⟨3590332217892959926406207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9574219247714559803749885 3590332217892959926406207)
                      ·
                        rfl

theorem cell23_6992147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 4, 3].length) (baseStart_6992147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992147 prefixEnd_6992147 := by exact prefixLift 6992147
  have htrace : WordTrace (prefixWord ++ tailWord_6992147) baseStart_6992147 baseEnd_6992147 := by
    simpa [prefixWord, tailWord_6992147, baseEnd_6992147] using wordTrace_append hprefix tailTrace_6992147
  have hstable : (prefixWord ++ tailWord_6992147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992147).length < 2 ^ (prefixWord ++ tailWord_6992147).sum := by decide
  have hdescent : baseEnd_6992147 < baseStart_6992147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992161 : List Nat := [1, 2, 3, 2, 1, 1, 3, 2, 4, 2, 2]
def baseStart_6992161 : Nat := 118140960795 + 6992161 * 2 ^ 59
def prefixEnd_6992161 : Nat := 4983230072969 + 3 ^ 40 * 6992161 * 2
def baseEnd_6992161 : Nat := 3590339406622122871631143

theorem tailTrace_6992161 : CollatzResearch.WordTrace tailWord_6992161 prefixEnd_6992161 3590339406622122871631143 := by
  unfold tailWord_6992161
  simp only [CollatzResearch.WordTrace]
  refine ⟨255025062821602337871496337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170016708547734891914330891 255025062821602337871496337)
  ·
    refine ⟨191268797116201753403622253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255025062821602337871496337 191268797116201753403622253)
    ·
      refine ⟨71725798918575657526358345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191268797116201753403622253 71725798918575657526358345)
      ·
        refine ⟨53794349188931743144768759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71725798918575657526358345 53794349188931743144768759)
        ·
          refine ⟨80691523783397614717153139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53794349188931743144768759 80691523783397614717153139)
          ·
            refine ⟨121037285675096422075729709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80691523783397614717153139 121037285675096422075729709)
            ·
              refine ⟨45388982128161158278398641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121037285675096422075729709 45388982128161158278398641)
              ·
                refine ⟨34041736596120868708798981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45388982128161158278398641 34041736596120868708798981)
                ·
                  refine ⟨6382825611772662882899809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34041736596120868708798981 6382825611772662882899809)
                  ·
                    refine ⟨4787119208829497162174857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6382825611772662882899809 4787119208829497162174857)
                    ·
                      refine ⟨3590339406622122871631143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4787119208829497162174857 3590339406622122871631143)
                      ·
                        rfl

theorem cell23_6992161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_6992161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992161 prefixEnd_6992161 := by exact prefixLift 6992161
  have htrace : WordTrace (prefixWord ++ tailWord_6992161) baseStart_6992161 baseEnd_6992161 := by
    simpa [prefixWord, tailWord_6992161, baseEnd_6992161] using wordTrace_append hprefix tailTrace_6992161
  have hstable : (prefixWord ++ tailWord_6992161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992161).length < 2 ^ (prefixWord ++ tailWord_6992161).sum := by decide
  have hdescent : baseEnd_6992161 < baseStart_6992161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992164 : List Nat := [2, 3, 1, 3, 1, 3, 1, 1, 2, 1, 5]
def baseStart_6992164 : Nat := 118140960795 + 6992164 * 2 ^ 59
def prefixEnd_6992164 : Nat := 4983230072969 + 3 ^ 40 * 6992164 * 2
def baseEnd_6992164 : Nat := 3590340947064086359893629

theorem tailTrace_6992164 : CollatzResearch.WordTrace tailWord_6992164 prefixEnd_6992164 3590340947064086359893629 := by
  unfold tailWord_6992164
  simp only [CollatzResearch.WordTrace]
  refine ⟨127512586120295734691927773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170016781493727646255903697 127512586120295734691927773)
  ·
    refine ⟨47817219795110900509472915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127512586120295734691927773 47817219795110900509472915)
    ·
      refine ⟨71725829692666350764209373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47817219795110900509472915 71725829692666350764209373)
      ·
        refine ⟨26897186134749881536578515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71725829692666350764209373 26897186134749881536578515)
        ·
          refine ⟨40345779202124822304867773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26897186134749881536578515 40345779202124822304867773)
          ·
            refine ⟨15129667200796808364325415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40345779202124822304867773 15129667200796808364325415)
            ·
              refine ⟨22694500801195212546488123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15129667200796808364325415 22694500801195212546488123)
              ·
                refine ⟨34041751201792818819732185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22694500801195212546488123 34041751201792818819732185)
                ·
                  refine ⟨25531313401344614114799139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34041751201792818819732185 25531313401344614114799139)
                  ·
                    refine ⟨38296970102016921172198709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25531313401344614114799139 38296970102016921172198709)
                    ·
                      refine ⟨3590340947064086359893629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38296970102016921172198709 3590340947064086359893629)
                      ·
                        rfl

theorem cell23_6992164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_6992164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992164 prefixEnd_6992164 := by exact prefixLift 6992164
  have htrace : WordTrace (prefixWord ++ tailWord_6992164) baseStart_6992164 baseEnd_6992164 := by
    simpa [prefixWord, tailWord_6992164, baseEnd_6992164] using wordTrace_append hprefix tailTrace_6992164
  have hstable : (prefixWord ++ tailWord_6992164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992164).length < 2 ^ (prefixWord ++ tailWord_6992164).sum := by decide
  have hdescent : baseEnd_6992164 < baseStart_6992164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992184 : List Nat := [2, 1, 2, 1, 3, 1, 2, 6, 5]
def baseStart_6992184 : Nat := 118140960795 + 6992184 * 2 ^ 59
def prefixEnd_6992184 : Nat := 4983230072969 + 3 ^ 40 * 6992184 * 2
def baseEnd_6992184 : Nat := 398927912964130697960393

theorem tailTrace_6992184 : CollatzResearch.WordTrace tailWord_6992184 prefixEnd_6992184 398927912964130697960393 := by
  unfold tailWord_6992184
  simp only [CollatzResearch.WordTrace]
  refine ⟨127512950850259506399791803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170017267800346008533055737 127512950850259506399791803)
  ·
    refine ⟨191269426275389259599687705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127512950850259506399791803 191269426275389259599687705)
    ·
      refine ⟨143452069706541944699765779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191269426275389259599687705 143452069706541944699765779)
      ·
        refine ⟨215178104559812917049648669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143452069706541944699765779 215178104559812917049648669)
        ·
          refine ⟨80691789209929843893618251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215178104559812917049648669 80691789209929843893618251)
          ·
            refine ⟨121037683814894765840427377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80691789209929843893618251 121037683814894765840427377)
            ·
              refine ⟨90778262861171074380320533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121037683814894765840427377 90778262861171074380320533)
              ·
                refine ⟨4255231071617394111577525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90778262861171074380320533 4255231071617394111577525)
                ·
                  refine ⟨398927912964130697960393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4255231071617394111577525 398927912964130697960393)
                  ·
                    rfl

theorem cell23_6992184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 6, 5].length) (baseStart_6992184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992184 prefixEnd_6992184 := by exact prefixLift 6992184
  have htrace : WordTrace (prefixWord ++ tailWord_6992184) baseStart_6992184 baseEnd_6992184 := by
    simpa [prefixWord, tailWord_6992184, baseEnd_6992184] using wordTrace_append hprefix tailTrace_6992184
  have hstable : (prefixWord ++ tailWord_6992184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992184).length < 2 ^ (prefixWord ++ tailWord_6992184).sum := by decide
  have hdescent : baseEnd_6992184 < baseStart_6992184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992247 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 6]
def baseStart_6992247 : Nat := 118140960795 + 6992247 * 2 ^ 59
def prefixEnd_6992247 : Nat := 4983230072969 + 3 ^ 40 * 6992247 * 2
def baseEnd_6992247 : Nat := 3590383565958409535155747

theorem tailTrace_6992247 : CollatzResearch.WordTrace tailWord_6992247 prefixEnd_6992247 3590383565958409535155747 := by
  unfold tailWord_6992247
  simp only [CollatzResearch.WordTrace]
  refine ⟨255028199499290774559126995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170018799666193849706084663 255028199499290774559126995)
  ·
    refine ⟨382542299248936161838690493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255028199499290774559126995 382542299248936161838690493)
    ·
      refine ⟨143453362218351060689508935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 382542299248936161838690493 143453362218351060689508935)
      ·
        refine ⟨215180043327526591034263403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143453362218351060689508935 215180043327526591034263403)
        ·
          refine ⟨322770064991289886551395105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215180043327526591034263403 322770064991289886551395105)
          ·
            refine ⟨242077548743467414913546329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322770064991289886551395105 242077548743467414913546329)
            ·
              refine ⟨181558161557600561185159747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242077548743467414913546329 181558161557600561185159747)
              ·
                refine ⟨272337242336400841777739621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181558161557600561185159747 272337242336400841777739621)
                ·
                  refine ⟨51063232938075157833326179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272337242336400841777739621 51063232938075157833326179)
                  ·
                    refine ⟨76594849407112736749989269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51063232938075157833326179 76594849407112736749989269)
                    ·
                      refine ⟨3590383565958409535155747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76594849407112736749989269 3590383565958409535155747)
                      ·
                        rfl

theorem cell23_6992247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_6992247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992247 prefixEnd_6992247 := by exact prefixLift 6992247
  have htrace : WordTrace (prefixWord ++ tailWord_6992247) baseStart_6992247 baseEnd_6992247 := by
    simpa [prefixWord, tailWord_6992247, baseEnd_6992247] using wordTrace_append hprefix tailTrace_6992247
  have hstable : (prefixWord ++ tailWord_6992247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992247).length < 2 ^ (prefixWord ++ tailWord_6992247).sum := by decide
  have hdescent : baseEnd_6992247 < baseStart_6992247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992251 : List Nat := [1, 1, 1, 1, 1, 8, 1, 1, 2, 4, 2]
def baseStart_6992251 : Nat := 118140960795 + 6992251 * 2 ^ 59
def prefixEnd_6992251 : Nat := 4983230072969 + 3 ^ 40 * 6992251 * 2
def baseEnd_6992251 : Nat := 3590385619881027519505729

theorem tailTrace_6992251 : CollatzResearch.WordTrace tailWord_6992251 prefixEnd_6992251 3590385619881027519505729 := by
  unfold tailWord_6992251
  simp only [CollatzResearch.WordTrace]
  refine ⟨255028345391276283242272607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170018896927517522161515071 255028345391276283242272607)
  ·
    refine ⟨382542518086914424863408911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255028345391276283242272607 382542518086914424863408911)
    ·
      refine ⟨573813777130371637295113367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382542518086914424863408911 573813777130371637295113367)
      ·
        refine ⟨860720665695557455942670051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573813777130371637295113367 860720665695557455942670051)
        ·
          refine ⟨1291080998543336183914005077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860720665695557455942670051 1291080998543336183914005077)
          ·
            refine ⟨15129855451679720905242247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1291080998543336183914005077 15129855451679720905242247)
            ·
              refine ⟨22694783177519581357863371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15129855451679720905242247 22694783177519581357863371)
              ·
                refine ⟨34042174766279372036795057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22694783177519581357863371 34042174766279372036795057)
                ·
                  refine ⟨25531631074709529027596293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34042174766279372036795057 25531631074709529027596293)
                  ·
                    refine ⟨4787180826508036692674305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25531631074709529027596293 4787180826508036692674305)
                    ·
                      refine ⟨3590385619881027519505729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4787180826508036692674305 3590385619881027519505729)
                      ·
                        rfl

theorem cell23_6992251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 4, 2].length) (baseStart_6992251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992251 prefixEnd_6992251 := by exact prefixLift 6992251
  have htrace : WordTrace (prefixWord ++ tailWord_6992251) baseStart_6992251 baseEnd_6992251 := by
    simpa [prefixWord, tailWord_6992251, baseEnd_6992251] using wordTrace_append hprefix tailTrace_6992251
  have hstable : (prefixWord ++ tailWord_6992251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992251).length < 2 ^ (prefixWord ++ tailWord_6992251).sum := by decide
  have hdescent : baseEnd_6992251 < baseStart_6992251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992291 : List Nat := [1, 1, 1, 4, 1, 6, 1, 2, 6]
def baseStart_6992291 : Nat := 118140960795 + 6992291 * 2 ^ 59
def prefixEnd_6992291 : Nat := 4983230072969 + 3 ^ 40 * 6992291 * 2
def baseEnd_6992291 : Nat := 398934017678578595889505

theorem tailTrace_6992291 : CollatzResearch.WordTrace tailWord_6992291 prefixEnd_6992291 398934017678578595889505 := by
  unfold tailWord_6992291
  simp only [CollatzResearch.WordTrace]
  refine ⟨255029804311131370073728727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170019869540754246715819151 255029804311131370073728727)
  ·
    refine ⟨382544706466697055110593091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255029804311131370073728727 382544706466697055110593091)
    ·
      refine ⟨573817059700045582665889637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382544706466697055110593091 573817059700045582665889637)
      ·
        refine ⟨107590698693758546749854307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 573817059700045582665889637 107590698693758546749854307)
        ·
          refine ⟨161386048040637820124781461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107590698693758546749854307 161386048040637820124781461)
          ·
            refine ⟨7564971001904897818349131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 161386048040637820124781461 7564971001904897818349131)
            ·
              refine ⟨11347456502857346727523697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7564971001904897818349131 11347456502857346727523697)
              ·
                refine ⟨8510592377143010045642773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11347456502857346727523697 8510592377143010045642773)
                ·
                  refine ⟨398934017678578595889505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8510592377143010045642773 398934017678578595889505)
                  ·
                    rfl

theorem cell23_6992291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 6].length) (baseStart_6992291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992291 prefixEnd_6992291 := by exact prefixLift 6992291
  have htrace : WordTrace (prefixWord ++ tailWord_6992291) baseStart_6992291 baseEnd_6992291 := by
    simpa [prefixWord, tailWord_6992291, baseEnd_6992291] using wordTrace_append hprefix tailTrace_6992291
  have hstable : (prefixWord ++ tailWord_6992291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992291).length < 2 ^ (prefixWord ++ tailWord_6992291).sum := by decide
  have hdescent : baseEnd_6992291 < baseStart_6992291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992311 : List Nat := [1, 1, 3, 1, 3, 3, 1, 2, 1, 5, 2]
def baseStart_6992311 : Nat := 118140960795 + 6992311 * 2 ^ 59
def prefixEnd_6992311 : Nat := 4983230072969 + 3 ^ 40 * 6992311 * 2
def baseEnd_6992311 : Nat := 3590416428720297284755453

theorem tailTrace_6992311 : CollatzResearch.WordTrace tailWord_6992311 prefixEnd_6992311 3590416428720297284755453 := by
  unfold tailWord_6992311
  simp only [CollatzResearch.WordTrace]
  refine ⟨255030533771058913489456787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170020355847372608992971191 255030533771058913489456787)
  ·
    refine ⟨382545800656588370234185181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255030533771058913489456787 382545800656588370234185181)
    ·
      refine ⟨143454675246220638837819443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 382545800656588370234185181 143454675246220638837819443)
      ·
        refine ⟨215182012869330958256729165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143454675246220638837819443 215182012869330958256729165)
        ·
          refine ⟨80693254825999109346273437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215182012869330958256729165 80693254825999109346273437)
          ·
            refine ⟨30259970559749666004852539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80693254825999109346273437 30259970559749666004852539)
            ·
              refine ⟨45389955839624499007278809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30259970559749666004852539 45389955839624499007278809)
              ·
                refine ⟨34042466879718374255459107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45389955839624499007278809 34042466879718374255459107)
                ·
                  refine ⟨51063700319577561383188661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34042466879718374255459107 51063700319577561383188661)
                  ·
                    refine ⟨4787221904960396379673937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51063700319577561383188661 4787221904960396379673937)
                    ·
                      refine ⟨3590416428720297284755453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4787221904960396379673937 3590416428720297284755453)
                      ·
                        rfl

theorem cell23_6992311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 5, 2].length) (baseStart_6992311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992311 prefixEnd_6992311 := by exact prefixLift 6992311
  have htrace : WordTrace (prefixWord ++ tailWord_6992311) baseStart_6992311 baseEnd_6992311 := by
    simpa [prefixWord, tailWord_6992311, baseEnd_6992311] using wordTrace_append hprefix tailTrace_6992311
  have hstable : (prefixWord ++ tailWord_6992311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992311).length < 2 ^ (prefixWord ++ tailWord_6992311).sum := by decide
  have hdescent : baseEnd_6992311 < baseStart_6992311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992318 : List Nat := [4, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3]
def baseStart_6992318 : Nat := 118140960795 + 6992318 * 2 ^ 59
def prefixEnd_6992318 : Nat := 4983230072969 + 3 ^ 40 * 6992318 * 2
def baseEnd_6992318 : Nat := 3590420023084878757367921

theorem tailTrace_6992318 : CollatzResearch.WordTrace tailWord_6992318 prefixEnd_6992318 3590420023084878757367921 := by
  unfold tailWord_6992318
  simp only [CollatzResearch.WordTrace]
  refine ⟨31878848635254194210620201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170020526054689035789974405 31878848635254194210620201)
  ·
    refine ⟨23909136476440645657965151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31878848635254194210620201 23909136476440645657965151)
    ·
      refine ⟨35863704714660968486947727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23909136476440645657965151 35863704714660968486947727)
      ·
        refine ⟨53795557071991452730421591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35863704714660968486947727 53795557071991452730421591)
        ·
          refine ⟨80693335607987179095632387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53795557071991452730421591 80693335607987179095632387)
          ·
            refine ⟨121040003411980768643448581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80693335607987179095632387 121040003411980768643448581)
            ·
              refine ⟨22695000639746394120646609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121040003411980768643448581 22695000639746394120646609)
              ·
                refine ⟨17021250479809795590484957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22695000639746394120646609 17021250479809795590484957)
                ·
                  refine ⟨6382968929928673346431859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17021250479809795590484957 6382968929928673346431859)
                  ·
                    refine ⟨9574453394893010019647789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6382968929928673346431859 9574453394893010019647789)
                    ·
                      refine ⟨3590420023084878757367921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9574453394893010019647789 3590420023084878757367921)
                      ·
                        rfl

theorem cell23_6992318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_6992318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992318 prefixEnd_6992318 := by exact prefixLift 6992318
  have htrace : WordTrace (prefixWord ++ tailWord_6992318) baseStart_6992318 baseEnd_6992318 := by
    simpa [prefixWord, tailWord_6992318, baseEnd_6992318] using wordTrace_append hprefix tailTrace_6992318
  have hstable : (prefixWord ++ tailWord_6992318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992318).length < 2 ^ (prefixWord ++ tailWord_6992318).sum := by decide
  have hdescent : baseEnd_6992318 < baseStart_6992318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992334 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 3, 6]
def baseStart_6992334 : Nat := 118140960795 + 6992334 * 2 ^ 59
def prefixEnd_6992334 : Nat := 4983230072969 + 3 ^ 40 * 6992334 * 2
def baseEnd_6992334 : Nat := 1196809412925116898255949

theorem tailTrace_6992334 : CollatzResearch.WordTrace tailWord_6992334 prefixEnd_6992334 1196809412925116898255949 := by
  unfold tailWord_6992334
  simp only [CollatzResearch.WordTrace]
  refine ⟨31878921581246948552193007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170020915099983725611696037 31878921581246948552193007)
  ·
    refine ⟨47818382371870422828289511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31878921581246948552193007 47818382371870422828289511)
    ·
      refine ⟨71727573557805634242434267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47818382371870422828289511 71727573557805634242434267)
      ·
        refine ⟨107591360336708451363651401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71727573557805634242434267 107591360336708451363651401)
        ·
          refine ⟨80693520252531338522738551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107591360336708451363651401 80693520252531338522738551)
          ·
            refine ⟨121040280378797007784107827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80693520252531338522738551 121040280378797007784107827)
            ·
              refine ⟨181560420568195511676161741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121040280378797007784107827 181560420568195511676161741)
              ·
                refine ⟨68085157713073316878560653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181560420568195511676161741 68085157713073316878560653)
                ·
                  refine ⟨25531934142402493829460245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68085157713073316878560653 25531934142402493829460245)
                  ·
                    refine ⟨1196809412925116898255949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25531934142402493829460245 1196809412925116898255949)
                    ·
                      rfl

theorem cell23_6992334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_6992334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992334 prefixEnd_6992334 := by exact prefixLift 6992334
  have htrace : WordTrace (prefixWord ++ tailWord_6992334) baseStart_6992334 baseEnd_6992334 := by
    simpa [prefixWord, tailWord_6992334, baseEnd_6992334] using wordTrace_append hprefix tailTrace_6992334
  have hstable : (prefixWord ++ tailWord_6992334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992334).length < 2 ^ (prefixWord ++ tailWord_6992334).sum := by decide
  have hdescent : baseEnd_6992334 < baseStart_6992334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992351 : List Nat := [1, 1, 2, 3, 3, 2, 2, 1, 4, 4]
def baseStart_6992351 : Nat := 118140960795 + 6992351 * 2 ^ 59
def prefixEnd_6992351 : Nat := 4983230072969 + 3 ^ 40 * 6992351 * 2
def baseEnd_6992351 : Nat := 1196812322648825709418423

theorem tailTrace_6992351 : CollatzResearch.WordTrace tailWord_6992351 prefixEnd_6992351 1196812322648825709418423 := by
  unfold tailWord_6992351
  simp only [CollatzResearch.WordTrace]
  refine ⟨255031992690914000320912907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170021328460609333547275271 255031992690914000320912907)
  ·
    refine ⟨382547989036371000481369361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255031992690914000320912907 382547989036371000481369361)
    ·
      refine ⟨286910991777278250361027021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382547989036371000481369361 286910991777278250361027021)
      ·
        refine ⟨107591621916479343885385133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286910991777278250361027021 107591621916479343885385133)
        ·
          refine ⟨40346858218679753957019425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107591621916479343885385133 40346858218679753957019425)
          ·
            refine ⟨30260143664009815467764569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40346858218679753957019425 30260143664009815467764569)
            ·
              refine ⟨22695107748007361600823427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30260143664009815467764569 22695107748007361600823427)
              ·
                refine ⟨34042661622011042401235141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22695107748007361600823427 34042661622011042401235141)
                ·
                  refine ⟨6382999054127070450231589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34042661622011042401235141 6382999054127070450231589)
                  ·
                    refine ⟨1196812322648825709418423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6382999054127070450231589 1196812322648825709418423)
                    ·
                      rfl

theorem cell23_6992351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 4, 4].length) (baseStart_6992351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992351 prefixEnd_6992351 := by exact prefixLift 6992351
  have htrace : WordTrace (prefixWord ++ tailWord_6992351) baseStart_6992351 baseEnd_6992351 := by
    simpa [prefixWord, tailWord_6992351, baseEnd_6992351] using wordTrace_append hprefix tailTrace_6992351
  have hstable : (prefixWord ++ tailWord_6992351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992351).length < 2 ^ (prefixWord ++ tailWord_6992351).sum := by decide
  have hdescent : baseEnd_6992351 < baseStart_6992351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992364 : List Nat := [2, 2, 1, 1, 2, 1, 6, 8]
def baseStart_6992364 : Nat := 118140960795 + 6992364 * 2 ^ 59
def prefixEnd_6992364 : Nat := 4983230072969 + 3 ^ 40 * 6992364 * 2
def baseEnd_6992364 : Nat := 132979394192406873236767

theorem tailTrace_6992364 : CollatzResearch.WordTrace tailWord_6992364 prefixEnd_6992364 132979394192406873236767 := by
  unfold tailWord_6992364
  simp only [CollatzResearch.WordTrace]
  refine ⟨127516233419933451770568073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170021644559911269027424097 127516233419933451770568073)
  ·
    refine ⟨95637175064950088827926055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127516233419933451770568073 95637175064950088827926055)
    ·
      refine ⟨143455762597425133241889083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95637175064950088827926055 143455762597425133241889083)
      ·
        refine ⟨215183643896137699862833625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143455762597425133241889083 215183643896137699862833625)
        ·
          refine ⟨161387732922103274897125219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215183643896137699862833625 161387732922103274897125219)
          ·
            refine ⟨242081599383154912345687829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161387732922103274897125219 242081599383154912345687829)
            ·
              refine ⟨11347574971085386516204117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 242081599383154912345687829 11347574971085386516204117)
              ·
                refine ⟨132979394192406873236767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11347574971085386516204117 132979394192406873236767)
                ·
                  rfl

theorem cell23_6992364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 8].length) (baseStart_6992364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992364 prefixEnd_6992364 := by exact prefixLift 6992364
  have htrace : WordTrace (prefixWord ++ tailWord_6992364) baseStart_6992364 baseEnd_6992364 := by
    simpa [prefixWord, tailWord_6992364, baseEnd_6992364] using wordTrace_append hprefix tailTrace_6992364
  have hstable : (prefixWord ++ tailWord_6992364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992364).length < 2 ^ (prefixWord ++ tailWord_6992364).sum := by decide
  have hdescent : baseEnd_6992364 < baseStart_6992364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992388 : List Nat := [2, 3, 2, 3, 1, 2, 1, 2, 1, 2, 4]
def baseStart_6992388 : Nat := 118140960795 + 6992388 * 2 ^ 59
def prefixEnd_6992388 : Nat := 4983230072969 + 3 ^ 40 * 6992388 * 2
def baseEnd_6992388 : Nat := 3590455966730693483492599

theorem tailTrace_6992388 : CollatzResearch.WordTrace tailWord_6992388 prefixEnd_6992388 3590455966730693483492599 := by
  unfold tailWord_6992388
  simp only [CollatzResearch.WordTrace]
  refine ⟨127516671095889977820004909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170022228127853303760006545 127516671095889977820004909)
  ·
    refine ⟨47818751660958741682501841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127516671095889977820004909 47818751660958741682501841)
    ·
      refine ⟨35864063745719056261876381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47818751660958741682501841 35864063745719056261876381)
      ·
        refine ⟨13449023904644646098203643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35864063745719056261876381 13449023904644646098203643)
        ·
          refine ⟨20173535856966969147305465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13449023904644646098203643 20173535856966969147305465)
          ·
            refine ⟨15130151892725226860479099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20173535856966969147305465 15130151892725226860479099)
            ·
              refine ⟨22695227839087840290718649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15130151892725226860479099 22695227839087840290718649)
              ·
                refine ⟨17021420879315880218038987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22695227839087840290718649 17021420879315880218038987)
                ·
                  refine ⟨25532131318973820327058481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17021420879315880218038987 25532131318973820327058481)
                  ·
                    refine ⟨19149098489230365245293861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25532131318973820327058481 19149098489230365245293861)
                    ·
                      refine ⟨3590455966730693483492599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19149098489230365245293861 3590455966730693483492599)
                      ·
                        rfl

theorem cell23_6992388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_6992388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992388 prefixEnd_6992388 := by exact prefixLift 6992388
  have htrace : WordTrace (prefixWord ++ tailWord_6992388) baseStart_6992388 baseEnd_6992388 := by
    simpa [prefixWord, tailWord_6992388, baseEnd_6992388] using wordTrace_append hprefix tailTrace_6992388
  have hstable : (prefixWord ++ tailWord_6992388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992388).length < 2 ^ (prefixWord ++ tailWord_6992388).sum := by decide
  have hdescent : baseEnd_6992388 < baseStart_6992388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992395 : List Nat := [1, 1, 1, 1, 7, 2, 3, 1, 1, 2, 3]
def baseStart_6992395 : Nat := 118140960795 + 6992395 * 2 ^ 59
def prefixEnd_6992395 : Nat := 4983230072969 + 3 ^ 40 * 6992395 * 2
def baseEnd_6992395 : Nat := 3590459561095274956105067

theorem tailTrace_6992395 : CollatzResearch.WordTrace tailWord_6992395 prefixEnd_6992395 3590459561095274956105067 := by
  unfold tailWord_6992395
  simp only [CollatzResearch.WordTrace]
  refine ⟨255033597502754595835514639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170022398335169730557009759 255033597502754595835514639)
  ·
    refine ⟨382550396254131893753271959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255033597502754595835514639 382550396254131893753271959)
    ·
      refine ⟨573825594381197840629907939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382550396254131893753271959 573825594381197840629907939)
      ·
        refine ⟨860738391571796760944861909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573825594381197840629907939 860738391571796760944861909)
        ·
          refine ⟨20173556052463986584645201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 860738391571796760944861909 20173556052463986584645201)
          ·
            refine ⟨15130167039347989938483901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20173556052463986584645201 15130167039347989938483901)
            ·
              refine ⟨5673812639755496226931463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15130167039347989938483901 5673812639755496226931463)
              ·
                refine ⟨8510718959633244340397195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5673812639755496226931463 8510718959633244340397195)
                ·
                  refine ⟨12766078439449866510595793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8510718959633244340397195 12766078439449866510595793)
                  ·
                    refine ⟨9574558829587399882946845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12766078439449866510595793 9574558829587399882946845)
                    ·
                      refine ⟨3590459561095274956105067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9574558829587399882946845 3590459561095274956105067)
                      ·
                        rfl

theorem cell23_6992395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 1, 2, 3].length) (baseStart_6992395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992395 prefixEnd_6992395 := by exact prefixLift 6992395
  have htrace : WordTrace (prefixWord ++ tailWord_6992395) baseStart_6992395 baseEnd_6992395 := by
    simpa [prefixWord, tailWord_6992395, baseEnd_6992395] using wordTrace_append hprefix tailTrace_6992395
  have hstable : (prefixWord ++ tailWord_6992395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992395).length < 2 ^ (prefixWord ++ tailWord_6992395).sum := by decide
  have hdescent : baseEnd_6992395 < baseStart_6992395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992446 : List Nat := [4, 2, 1, 4, 2, 1, 2, 1, 1, 2, 3]
def baseStart_6992446 : Nat := 118140960795 + 6992446 * 2 ^ 59
def prefixEnd_6992446 : Nat := 4983230072969 + 3 ^ 40 * 6992446 * 2
def baseEnd_6992446 : Nat := 3590485748608654256567333

theorem tailTrace_6992446 : CollatzResearch.WordTrace tailWord_6992446 prefixEnd_6992446 3590485748608654256567333 := by
  unfold tailWord_6992446
  simp only [CollatzResearch.WordTrace]
  refine ⟨31879432203196228943202649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170023638417046554363747461 31879432203196228943202649)
  ·
    refine ⟨23909574152397171707401987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31879432203196228943202649 23909574152397171707401987)
    ·
      refine ⟨35864361228595757561102981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23909574152397171707401987 35864361228595757561102981)
      ·
        refine ⟨6724567730361704542706809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35864361228595757561102981 6724567730361704542706809)
        ·
          refine ⟨5043425797771278407030107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6724567730361704542706809 5043425797771278407030107)
          ·
            refine ⟨7565138696656917610545161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5043425797771278407030107 7565138696656917610545161)
            ·
              refine ⟨5673854022492688207908871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7565138696656917610545161 5673854022492688207908871)
              ·
                refine ⟨8510781033739032311863307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5673854022492688207908871 8510781033739032311863307)
                ·
                  refine ⟨12766171550608548467794961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8510781033739032311863307 12766171550608548467794961)
                  ·
                    refine ⟨9574628662956411350846221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12766171550608548467794961 9574628662956411350846221)
                    ·
                      refine ⟨3590485748608654256567333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9574628662956411350846221 3590485748608654256567333)
                      ·
                        rfl

theorem cell23_6992446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_6992446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992446 prefixEnd_6992446 := by exact prefixLift 6992446
  have htrace : WordTrace (prefixWord ++ tailWord_6992446) baseStart_6992446 baseEnd_6992446 := by
    simpa [prefixWord, tailWord_6992446, baseEnd_6992446] using wordTrace_append hprefix tailTrace_6992446
  have hstable : (prefixWord ++ tailWord_6992446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992446).length < 2 ^ (prefixWord ++ tailWord_6992446).sum := by decide
  have hdescent : baseEnd_6992446 < baseStart_6992446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992448 : List Nat := [2, 1, 1, 2, 2, 2, 4, 2, 1, 4, 2]
def baseStart_6992448 : Nat := 118140960795 + 6992448 * 2 ^ 59
def prefixEnd_6992448 : Nat := 4983230072969 + 3 ^ 40 * 6992448 * 2
def baseEnd_6992448 : Nat := 3590486775569963248742323

theorem tailTrace_6992448 : CollatzResearch.WordTrace tailWord_6992448 prefixEnd_6992448 3590486775569963248742323 := by
  unfold tailWord_6992448
  simp only [CollatzResearch.WordTrace]
  refine ⟨127517765285781292943596999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170023687047708390591462665 127517765285781292943596999)
  ·
    refine ⟨191276647928671939415395499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127517765285781292943596999 191276647928671939415395499)
    ·
      refine ⟨286914971893007909123093249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191276647928671939415395499 286914971893007909123093249)
      ·
        refine ⟨215186228919755931842319937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286914971893007909123093249 215186228919755931842319937)
        ·
          refine ⟨161389671689816948881739953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215186228919755931842319937 161389671689816948881739953)
          ·
            refine ⟨121042253767362711661304965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161389671689816948881739953 121042253767362711661304965)
            ·
              refine ⟨22695422581380508436494681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121042253767362711661304965 22695422581380508436494681)
              ·
                refine ⟨17021566936035381327371011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22695422581380508436494681 17021566936035381327371011)
                ·
                  refine ⟨25532350404053071991056517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17021566936035381327371011 25532350404053071991056517)
                  ·
                    refine ⟨4787315700759950998323097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25532350404053071991056517 4787315700759950998323097)
                    ·
                      refine ⟨3590486775569963248742323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4787315700759950998323097 3590486775569963248742323)
                      ·
                        rfl

theorem cell23_6992448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 1, 4, 2].length) (baseStart_6992448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992448 prefixEnd_6992448 := by exact prefixLift 6992448
  have htrace : WordTrace (prefixWord ++ tailWord_6992448) baseStart_6992448 baseEnd_6992448 := by
    simpa [prefixWord, tailWord_6992448, baseEnd_6992448] using wordTrace_append hprefix tailTrace_6992448
  have hstable : (prefixWord ++ tailWord_6992448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992448).length < 2 ^ (prefixWord ++ tailWord_6992448).sum := by decide
  have hdescent : baseEnd_6992448 < baseStart_6992448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992464 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 9]
def baseStart_6992464 : Nat := 118140960795 + 6992464 * 2 ^ 59
def prefixEnd_6992464 : Nat := 4983230072969 + 3 ^ 40 * 6992464 * 2
def baseEnd_6992464 : Nat := 3590494991260435186142249

theorem tailTrace_6992464 : CollatzResearch.WordTrace tailWord_6992464 prefixEnd_6992464 3590494991260435186142249 := by
  unfold tailWord_6992464
  simp only [CollatzResearch.WordTrace]
  refine ⟨127518057069752310309888223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170024076093003080413184297 127518057069752310309888223)
  ·
    refine ⟨191277085604628465464832335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127518057069752310309888223 191277085604628465464832335)
    ·
      refine ⟨286915628406942698197248503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191277085604628465464832335 286915628406942698197248503)
      ·
        refine ⟨430373442610414047295872755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286915628406942698197248503 430373442610414047295872755)
        ·
          refine ⟨645560163915621070943809133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430373442610414047295872755 645560163915621070943809133)
          ·
            refine ⟨242085061468357901603928425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 645560163915621070943809133 242085061468357901603928425)
            ·
              refine ⟨181563796101268426202946319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242085061468357901603928425 181563796101268426202946319)
              ·
                refine ⟨272345694151902639304419479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181563796101268426202946319 272345694151902639304419479)
                ·
                  refine ⟨408518541227853958956629219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 272345694151902639304419479 408518541227853958956629219)
                  ·
                    refine ⟨612777811841780938434943829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 408518541227853958956629219 612777811841780938434943829)
                    ·
                      refine ⟨3590494991260435186142249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 612777811841780938434943829 3590494991260435186142249)
                      ·
                        rfl

theorem cell23_6992464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 9].length) (baseStart_6992464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992464 prefixEnd_6992464 := by exact prefixLift 6992464
  have htrace : WordTrace (prefixWord ++ tailWord_6992464) baseStart_6992464 baseEnd_6992464 := by
    simpa [prefixWord, tailWord_6992464, baseEnd_6992464] using wordTrace_append hprefix tailTrace_6992464
  have hstable : (prefixWord ++ tailWord_6992464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992464).length < 2 ^ (prefixWord ++ tailWord_6992464).sum := by decide
  have hdescent : baseEnd_6992464 < baseStart_6992464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992465 : List Nat := [1, 2, 2, 1, 3, 4, 1, 1, 4, 2, 2]
def baseStart_6992465 : Nat := 118140960795 + 6992465 * 2 ^ 59
def prefixEnd_6992465 : Nat := 4983230072969 + 3 ^ 40 * 6992465 * 2
def baseEnd_6992465 : Nat := 3590495504741089682229745

theorem tailTrace_6992465 : CollatzResearch.WordTrace tailWord_6992465 prefixEnd_6992465 3590495504741089682229745 := by
  unfold tailWord_6992465
  simp only [CollatzResearch.WordTrace]
  refine ⟨255036150612500997790562849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170024100408333998527041899 255036150612500997790562849)
  ·
    refine ⟨191277112959375748342922137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255036150612500997790562849 191277112959375748342922137)
    ·
      refine ⟨143457834719531811257191603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191277112959375748342922137 143457834719531811257191603)
      ·
        refine ⟨215186752079297716885787405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143457834719531811257191603 215186752079297716885787405)
        ·
          refine ⟨80695032029736643832170277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215186752079297716885787405 80695032029736643832170277)
          ·
            refine ⟨15130318505575620718531927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80695032029736643832170277 15130318505575620718531927)
            ·
              refine ⟨22695477758363431077797891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15130318505575620718531927 22695477758363431077797891)
              ·
                refine ⟨34043216637545146616696837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22695477758363431077797891 34043216637545146616696837)
                ·
                  refine ⟨6383103119539714990630657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34043216637545146616696837 6383103119539714990630657)
                  ·
                    refine ⟨4787327339654786242972993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6383103119539714990630657 4787327339654786242972993)
                    ·
                      refine ⟨3590495504741089682229745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4787327339654786242972993 3590495504741089682229745)
                      ·
                        rfl

theorem cell23_6992465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 4, 2, 2].length) (baseStart_6992465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992465 prefixEnd_6992465 := by exact prefixLift 6992465
  have htrace : WordTrace (prefixWord ++ tailWord_6992465) baseStart_6992465 baseEnd_6992465 := by
    simpa [prefixWord, tailWord_6992465, baseEnd_6992465] using wordTrace_append hprefix tailTrace_6992465
  have hstable : (prefixWord ++ tailWord_6992465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992465).length < 2 ^ (prefixWord ++ tailWord_6992465).sum := by decide
  have hdescent : baseEnd_6992465 < baseStart_6992465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992471 : List Nat := [1, 1, 3, 2, 2, 2, 4, 1, 7]
def baseStart_6992471 : Nat := 118140960795 + 6992471 * 2 ^ 59
def prefixEnd_6992471 : Nat := 4983230072969 + 3 ^ 40 * 6992471 * 2
def baseEnd_6992471 : Nat := 398944287291668517639413

theorem tailTrace_6992471 : CollatzResearch.WordTrace tailWord_6992471 prefixEnd_6992471 398944287291668517639413 := by
  unfold tailWord_6992471
  simp only [CollatzResearch.WordTrace]
  refine ⟨255036369450479260815281267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170024246300319507210187511 255036369450479260815281267)
  ·
    refine ⟨382554554175718891222921901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255036369450479260815281267 382554554175718891222921901)
    ·
      refine ⟨143457957815894584208595713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 382554554175718891222921901 143457957815894584208595713)
      ·
        refine ⟨107593468361920938156446785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143457957815894584208595713 107593468361920938156446785)
        ·
          refine ⟨80695101271440703617335089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107593468361920938156446785 80695101271440703617335089)
          ·
            refine ⟨60521325953580527713001317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80695101271440703617335089 60521325953580527713001317)
            ·
              refine ⟨11347748616296348946187747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60521325953580527713001317 11347748616296348946187747)
              ·
                refine ⟨17021622924444523419281621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11347748616296348946187747 17021622924444523419281621)
                ·
                  refine ⟨398944287291668517639413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17021622924444523419281621 398944287291668517639413)
                  ·
                    rfl

theorem cell23_6992471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 7].length) (baseStart_6992471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992471 prefixEnd_6992471 := by exact prefixLift 6992471
  have htrace : WordTrace (prefixWord ++ tailWord_6992471) baseStart_6992471 baseEnd_6992471 := by
    simpa [prefixWord, tailWord_6992471, baseEnd_6992471] using wordTrace_append hprefix tailTrace_6992471
  have hstable : (prefixWord ++ tailWord_6992471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992471).length < 2 ^ (prefixWord ++ tailWord_6992471).sum := by decide
  have hdescent : baseEnd_6992471 < baseStart_6992471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992505 : List Nat := [1, 2, 1, 3, 3, 4, 1, 3, 5]
def baseStart_6992505 : Nat := 118140960795 + 6992505 * 2 ^ 59
def prefixEnd_6992505 : Nat := 4983230072969 + 3 ^ 40 * 6992505 * 2
def baseEnd_6992505 : Nat := 398946227107474391747729

theorem tailTrace_6992505 : CollatzResearch.WordTrace tailWord_6992505 prefixEnd_6992505 398946227107474391747729 := by
  unfold tailWord_6992505
  simp only [CollatzResearch.WordTrace]
  refine ⟨255037609532356084622018969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170025073021570723081345979 255037609532356084622018969)
  ·
    refine ⟨191278207149267063466514227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255037609532356084622018969 191278207149267063466514227)
    ·
      refine ⟨286917310723900595199771341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191278207149267063466514227 286917310723900595199771341)
      ·
        refine ⟨107593991521462723199914253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286917310723900595199771341 107593991521462723199914253)
        ·
          refine ⟨40347746820548521199967845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107593991521462723199914253 40347746820548521199967845)
          ·
            refine ⟨7565202528852847724993971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40347746820548521199967845 7565202528852847724993971)
            ·
              refine ⟨11347803793279271587490957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7565202528852847724993971 11347803793279271587490957)
              ·
                refine ⟨4255426422479726845309109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11347803793279271587490957 4255426422479726845309109)
                ·
                  refine ⟨398946227107474391747729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4255426422479726845309109 398946227107474391747729)
                  ·
                    rfl

theorem cell23_6992505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 3, 5].length) (baseStart_6992505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992505 prefixEnd_6992505 := by exact prefixLift 6992505
  have htrace : WordTrace (prefixWord ++ tailWord_6992505) baseStart_6992505 baseEnd_6992505 := by
    simpa [prefixWord, tailWord_6992505, baseEnd_6992505] using wordTrace_append hprefix tailTrace_6992505
  have hstable : (prefixWord ++ tailWord_6992505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992505).length < 2 ^ (prefixWord ++ tailWord_6992505).sum := by decide
  have hdescent : baseEnd_6992505 < baseStart_6992505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992522 : List Nat := [3, 1, 2, 3, 3, 1, 3, 2, 5]
def baseStart_6992522 : Nat := 118140960795 + 6992522 * 2 ^ 59
def prefixEnd_6992522 : Nat := 4983230072969 + 3 ^ 40 * 6992522 * 2
def baseEnd_6992522 : Nat := 398947197015377328801887

theorem tailTrace_6992522 : CollatzResearch.WordTrace tailWord_6992522 prefixEnd_6992522 398947197015377328801887 := by
  unfold tailWord_6992522
  simp only [CollatzResearch.WordTrace]
  refine ⟨63759557393323624131346955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170025486382196331016925213 63759557393323624131346955)
  ·
    refine ⟨95639336089985436197020433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63759557393323624131346955 95639336089985436197020433)
    ·
      refine ⟨71729502067489077147765325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95639336089985436197020433 71729502067489077147765325)
      ·
        refine ⟨26898563275308403930411997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71729502067489077147765325 26898563275308403930411997)
        ·
          refine ⟨10086961228240651473904499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26898563275308403930411997 10086961228240651473904499)
          ·
            refine ⟨15130441842360977210856749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10086961228240651473904499 15130441842360977210856749)
            ·
              refine ⟨5673915690885366454071281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15130441842360977210856749 5673915690885366454071281)
              ·
                refine ⟨4255436768164024840553461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5673915690885366454071281 4255436768164024840553461)
                ·
                  refine ⟨398947197015377328801887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4255436768164024840553461 398947197015377328801887)
                  ·
                    rfl

theorem cell23_6992522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 2, 5].length) (baseStart_6992522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992522 prefixEnd_6992522 := by exact prefixLift 6992522
  have htrace : WordTrace (prefixWord ++ tailWord_6992522) baseStart_6992522 baseEnd_6992522 := by
    simpa [prefixWord, tailWord_6992522, baseEnd_6992522] using wordTrace_append hprefix tailTrace_6992522
  have hstable : (prefixWord ++ tailWord_6992522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992522).length < 2 ^ (prefixWord ++ tailWord_6992522).sum := by decide
  have hdescent : baseEnd_6992522 < baseStart_6992522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992548 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 5, 4]
def baseStart_6992548 : Nat := 118140960795 + 6992548 * 2 ^ 59
def prefixEnd_6992548 : Nat := 4983230072969 + 3 ^ 40 * 6992548 * 2
def baseEnd_6992548 : Nat := 1196846041211804285830621

theorem tailTrace_6992548 : CollatzResearch.WordTrace tailWord_6992548 prefixEnd_6992548 1196846041211804285830621 := by
  unfold tailWord_6992548
  simp only [CollatzResearch.WordTrace]
  refine ⟨127519588935600151482917149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170026118580800201977222865 127519588935600151482917149)
  ·
    refine ⟨47819845850850056806093931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127519588935600151482917149 47819845850850056806093931)
    ·
      refine ⟨71729768776275085209140897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47819845850850056806093931 71729768776275085209140897)
      ·
        refine ⟨53797326582206313906855673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71729768776275085209140897 53797326582206313906855673)
        ·
          refine ⟨40347994936654735430141755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53797326582206313906855673 40347994936654735430141755)
          ·
            refine ⟨60521992404982103145212633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40347994936654735430141755 60521992404982103145212633)
            ·
              refine ⟨45391494303736577358909475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60521992404982103145212633 45391494303736577358909475)
              ·
                refine ⟨68087241455604866038364213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45391494303736577358909475 68087241455604866038364213)
                ·
                  refine ⟨6383178886462956191096645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68087241455604866038364213 6383178886462956191096645)
                  ·
                    refine ⟨1196846041211804285830621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6383178886462956191096645 1196846041211804285830621)
                    ·
                      rfl

theorem cell23_6992548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_6992548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992548 prefixEnd_6992548 := by exact prefixLift 6992548
  have htrace : WordTrace (prefixWord ++ tailWord_6992548) baseStart_6992548 baseEnd_6992548 := by
    simpa [prefixWord, tailWord_6992548, baseEnd_6992548] using wordTrace_append hprefix tailTrace_6992548
  have hstable : (prefixWord ++ tailWord_6992548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992548).length < 2 ^ (prefixWord ++ tailWord_6992548).sum := by decide
  have hdescent : baseEnd_6992548 < baseStart_6992548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992589 : List Nat := [1, 6, 2, 1, 2, 1, 1, 1, 2, 4, 2]
def baseStart_6992589 : Nat := 118140960795 + 6992589 * 2 ^ 59
def prefixEnd_6992589 : Nat := 4983230072969 + 3 ^ 40 * 6992589 * 2
def baseEnd_6992589 : Nat := 3590559176342247197079175

theorem tailTrace_6992589 : CollatzResearch.WordTrace tailWord_6992589 prefixEnd_6992589 3590559176342247197079175 := by
  unfold tailWord_6992589
  simp only [CollatzResearch.WordTrace]
  refine ⟨255040673264051766968076821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170027115509367844645384547 255040673264051766968076821)
  ·
    refine ⟨11955031559252426576628601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 255040673264051766968076821 11955031559252426576628601)
    ·
      refine ⟨8966273669439319932471451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11955031559252426576628601 8966273669439319932471451)
      ·
        refine ⟨13449410504158979898707177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8966273669439319932471451 13449410504158979898707177)
        ·
          refine ⟨10087057878119234924030383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13449410504158979898707177 10087057878119234924030383)
          ·
            refine ⟨15130586817178852386045575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10087057878119234924030383 15130586817178852386045575)
            ·
              refine ⟨22695880225768278579068363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15130586817178852386045575 22695880225768278579068363)
              ·
                refine ⟨34043820338652417868602545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22695880225768278579068363 34043820338652417868602545)
                ·
                  refine ⟨25532865253989313401451909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34043820338652417868602545 25532865253989313401451909)
                  ·
                    refine ⟨4787412235122996262772233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25532865253989313401451909 4787412235122996262772233)
                    ·
                      refine ⟨3590559176342247197079175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4787412235122996262772233 3590559176342247197079175)
                      ·
                        rfl

theorem cell23_6992589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_6992589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992589 prefixEnd_6992589 := by exact prefixLift 6992589
  have htrace : WordTrace (prefixWord ++ tailWord_6992589) baseStart_6992589 baseEnd_6992589 := by
    simpa [prefixWord, tailWord_6992589, baseEnd_6992589] using wordTrace_append hprefix tailTrace_6992589
  have hstable : (prefixWord ++ tailWord_6992589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992589).length < 2 ^ (prefixWord ++ tailWord_6992589).sum := by decide
  have hdescent : baseEnd_6992589 < baseStart_6992589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992601 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 2, 1, 7]
def baseStart_6992601 : Nat := 118140960795 + 6992601 * 2 ^ 59
def prefixEnd_6992601 : Nat := 4983230072969 + 3 ^ 40 * 6992601 * 2
def baseEnd_6992601 : Nat := 3590565338110101150129119

theorem tailTrace_6992601 : CollatzResearch.WordTrace tailWord_6992601 prefixEnd_6992601 3590565338110101150129119 := by
  unfold tailWord_6992601
  simp only [CollatzResearch.WordTrace]
  refine ⟨255041110940008293017513657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170027407293338862011675771 255041110940008293017513657)
  ·
    refine ⟨191280833205006219763135243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255041110940008293017513657 191280833205006219763135243)
    ·
      refine ⟨286921249807509329644702865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191280833205006219763135243 286921249807509329644702865)
      ·
        refine ⟨215190937355631997233527149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286921249807509329644702865 215190937355631997233527149)
        ·
          refine ⟨80696601508361998962572681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215190937355631997233527149 80696601508361998962572681)
          ·
            refine ⟨60522451131271499221929511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80696601508361998962572681 60522451131271499221929511)
            ·
              refine ⟨90783676696907248832894267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60522451131271499221929511 90783676696907248832894267)
              ·
                refine ⟨136175515045360873249341401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90783676696907248832894267 136175515045360873249341401)
                ·
                  refine ⟨102131636284020654937006051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136175515045360873249341401 102131636284020654937006051)
                  ·
                    refine ⟨153197454426030982405509077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102131636284020654937006051 153197454426030982405509077)
                    ·
                      refine ⟨3590565338110101150129119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 153197454426030982405509077 3590565338110101150129119)
                      ·
                        rfl

theorem cell23_6992601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_6992601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992601 prefixEnd_6992601 := by exact prefixLift 6992601
  have htrace : WordTrace (prefixWord ++ tailWord_6992601) baseStart_6992601 baseEnd_6992601 := by
    simpa [prefixWord, tailWord_6992601, baseEnd_6992601] using wordTrace_append hprefix tailTrace_6992601
  have hstable : (prefixWord ++ tailWord_6992601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992601).length < 2 ^ (prefixWord ++ tailWord_6992601).sum := by decide
  have hdescent : baseEnd_6992601 < baseStart_6992601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992608 : List Nat := [2, 1, 1, 3, 1, 2, 1, 6, 1, 5]
def baseStart_6992608 : Nat := 118140960795 + 6992608 * 2 ^ 59
def prefixEnd_6992608 : Nat := 4983230072969 + 3 ^ 40 * 6992608 * 2
def baseEnd_6992608 : Nat := 1196856310824894207580529

theorem tailTrace_6992608 : CollatzResearch.WordTrace tailWord_6992608 prefixEnd_6992608 1196856310824894207580529 := by
  unfold tailWord_6992608
  simp only [CollatzResearch.WordTrace]
  refine ⟨127520683125491466606509239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170027577500655288808678985 127520683125491466606509239)
  ·
    refine ⟨191281024688237199909763859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127520683125491466606509239 191281024688237199909763859)
    ·
      refine ⟨286921537032355799864645789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191281024688237199909763859 286921537032355799864645789)
      ·
        refine ⟨107595576387133424949242171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286921537032355799864645789 107595576387133424949242171)
        ·
          refine ⟨161393364580700137423863257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107595576387133424949242171 161393364580700137423863257)
          ·
            refine ⟨121045023435525103067897443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161393364580700137423863257 121045023435525103067897443)
            ·
              refine ⟨181567535153287654601846165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121045023435525103067897443 181567535153287654601846165)
              ·
                refine ⟨8510978210310358809461539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 181567535153287654601846165 8510978210310358809461539)
                ·
                  refine ⟨12766467315465538214192309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8510978210310358809461539 12766467315465538214192309)
                  ·
                    refine ⟨1196856310824894207580529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12766467315465538214192309 1196856310824894207580529)
                    ·
                      rfl

theorem cell23_6992608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 1, 5].length) (baseStart_6992608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992608 prefixEnd_6992608 := by exact prefixLift 6992608
  have htrace : WordTrace (prefixWord ++ tailWord_6992608) baseStart_6992608 baseEnd_6992608 := by
    simpa [prefixWord, tailWord_6992608, baseEnd_6992608] using wordTrace_append hprefix tailTrace_6992608
  have hstable : (prefixWord ++ tailWord_6992608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992608).length < 2 ^ (prefixWord ++ tailWord_6992608).sum := by decide
  have hdescent : baseEnd_6992608 < baseStart_6992608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992648 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 3, 1, 5]
def baseStart_6992648 : Nat := 118140960795 + 6992648 * 2 ^ 59
def prefixEnd_6992648 : Nat := 4983230072969 + 3 ^ 40 * 6992648 * 2
def baseEnd_6992648 : Nat := 3590589471700862466241403

theorem tailTrace_6992648 : CollatzResearch.WordTrace tailWord_6992648 prefixEnd_6992648 3590589471700862466241403 := by
  unfold tailWord_6992648
  simp only [CollatzResearch.WordTrace]
  refine ⟨127521412585419010022237299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170028550113892013362983065 127521412585419010022237299)
  ·
    refine ⟨191282118878128515033355949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127521412585419010022237299 191282118878128515033355949)
    ·
      refine ⟨71730794579298193137508481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191282118878128515033355949 71730794579298193137508481)
      ·
        refine ⟨53798095934473644853131361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71730794579298193137508481 53798095934473644853131361)
        ·
          refine ⟨40348571950855233639848521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53798095934473644853131361 40348571950855233639848521)
          ·
            refine ⟨30261428963141425229886391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40348571950855233639848521 30261428963141425229886391)
            ·
              refine ⟨45392143444712137844829587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30261428963141425229886391 45392143444712137844829587)
              ·
                refine ⟨68088215167068206767244381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45392143444712137844829587 68088215167068206767244381)
                ·
                  refine ⟨25533080687650577537716643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68088215167068206767244381 25533080687650577537716643)
                  ·
                    refine ⟨38299621031475866306574965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25533080687650577537716643 38299621031475866306574965)
                    ·
                      refine ⟨3590589471700862466241403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38299621031475866306574965 3590589471700862466241403)
                      ·
                        rfl

theorem cell23_6992648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_6992648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992648 prefixEnd_6992648 := by exact prefixLift 6992648
  have htrace : WordTrace (prefixWord ++ tailWord_6992648) baseStart_6992648 baseEnd_6992648 := by
    simpa [prefixWord, tailWord_6992648, baseEnd_6992648] using wordTrace_append hprefix tailTrace_6992648
  have hstable : (prefixWord ++ tailWord_6992648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992648).length < 2 ^ (prefixWord ++ tailWord_6992648).sum := by decide
  have hdescent : baseEnd_6992648 < baseStart_6992648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992651 : List Nat := [1, 1, 1, 1, 5, 1, 1, 12]
def baseStart_6992651 : Nat := 118140960795 + 6992651 * 2 ^ 59
def prefixEnd_6992651 : Nat := 4983230072969 + 3 ^ 40 * 6992651 * 2
def baseEnd_6992651 : Nat := 132984852301586146463107

theorem tailTrace_6992651 : CollatzResearch.WordTrace tailWord_6992651 prefixEnd_6992651 132984852301586146463107 := by
  unfold tailWord_6992651
  simp only [CollatzResearch.WordTrace]
  refine ⟨255042934589827151556833807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170028623059884767704555871 255042934589827151556833807)
  ·
    refine ⟨382564401884740727335250711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255042934589827151556833807 382564401884740727335250711)
    ·
      refine ⟨573846602827111091002876067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382564401884740727335250711 573846602827111091002876067)
      ·
        refine ⟨860769904240666636504314101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573846602827111091002876067 860769904240666636504314101)
        ·
          refine ⟨80697178522562497172279447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 860769904240666636504314101 80697178522562497172279447)
          ·
            refine ⟨121045767783843745758419171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80697178522562497172279447 121045767783843745758419171)
            ·
              refine ⟨181568651675765618637628757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121045767783843745758419171 181568651675765618637628757)
              ·
                refine ⟨132984852301586146463107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 181568651675765618637628757 132984852301586146463107)
                ·
                  rfl

theorem cell23_6992651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 12].length) (baseStart_6992651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992651 prefixEnd_6992651 := by exact prefixLift 6992651
  have htrace : WordTrace (prefixWord ++ tailWord_6992651) baseStart_6992651 baseEnd_6992651 := by
    simpa [prefixWord, tailWord_6992651, baseEnd_6992651] using wordTrace_append hprefix tailTrace_6992651
  have hstable : (prefixWord ++ tailWord_6992651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992651).length < 2 ^ (prefixWord ++ tailWord_6992651).sum := by decide
  have hdescent : baseEnd_6992651 < baseStart_6992651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992668 : List Nat := [2, 2, 3, 1, 1, 4, 1, 9]
def baseStart_6992668 : Nat := 118140960795 + 6992668 * 2 ^ 59
def prefixEnd_6992668 : Nat := 4983230072969 + 3 ^ 40 * 6992668 * 2
def baseEnd_6992668 : Nat := 132985175604220458814493

theorem tailTrace_6992668 : CollatzResearch.WordTrace tailWord_6992668 prefixEnd_6992668 132985175604220458814493 := by
  unfold tailWord_6992668
  simp only [CollatzResearch.WordTrace]
  refine ⟨127521777315382781730101329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170029036420510375640135105 127521777315382781730101329)
  ·
    refine ⟨95641332986537086297575997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127521777315382781730101329 95641332986537086297575997)
    ·
      refine ⟨35865499869951407361590999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95641332986537086297575997 35865499869951407361590999)
      ·
        refine ⟨53798249804927111042386499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35865499869951407361590999 53798249804927111042386499)
        ·
          refine ⟨80697374707390666563579749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53798249804927111042386499 80697374707390666563579749)
          ·
            refine ⟨15130757757635749980671203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80697374707390666563579749 15130757757635749980671203)
            ·
              refine ⟨22696136636453624971006805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15130757757635749980671203 22696136636453624971006805)
              ·
                refine ⟨132985175604220458814493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22696136636453624971006805 132985175604220458814493)
                ·
                  rfl

theorem cell23_6992668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 9].length) (baseStart_6992668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992668 prefixEnd_6992668 := by exact prefixLift 6992668
  have htrace : WordTrace (prefixWord ++ tailWord_6992668) baseStart_6992668 baseEnd_6992668 := by
    simpa [prefixWord, tailWord_6992668, baseEnd_6992668] using wordTrace_append hprefix tailTrace_6992668
  have hstable : (prefixWord ++ tailWord_6992668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992668).length < 2 ^ (prefixWord ++ tailWord_6992668).sum := by decide
  have hdescent : baseEnd_6992668 < baseStart_6992668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992695 : List Nat := [1, 1, 3, 1, 2, 1, 3, 3, 4, 1, 3]
def baseStart_6992695 : Nat := 118140960795 + 6992695 * 2 ^ 59
def prefixEnd_6992695 : Nat := 4983230072969 + 3 ^ 40 * 6992695 * 2
def baseEnd_6992695 : Nat := 3590613605291623782353687

theorem tailTrace_6992695 : CollatzResearch.WordTrace tailWord_6992695 prefixEnd_6992695 3590613605291623782353687 := by
  unfold tailWord_6992695
  simp only [CollatzResearch.WordTrace]
  refine ⟨255044539401667747071435539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170029692934445164714290359 255044539401667747071435539)
  ·
    refine ⟨382566809102501620607153309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255044539401667747071435539 382566809102501620607153309)
    ·
      refine ⟨143462553413438107727682491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 382566809102501620607153309 143462553413438107727682491)
      ·
        refine ⟨215193830120157161591523737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143462553413438107727682491 215193830120157161591523737)
        ·
          refine ⟨161395372590117871193642803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215193830120157161591523737 161395372590117871193642803)
          ·
            refine ⟨242093058885176806790464205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161395372590117871193642803 242093058885176806790464205)
            ·
              refine ⟨90784897081941302546424077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242093058885176806790464205 90784897081941302546424077)
              ·
                refine ⟨34044336405727988454909029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90784897081941302546424077 34044336405727988454909029)
                ·
                  refine ⟨6383313076073997835295443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34044336405727988454909029 6383313076073997835295443)
                  ·
                    refine ⟨9574969614110996752943165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6383313076073997835295443 9574969614110996752943165)
                    ·
                      refine ⟨3590613605291623782353687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9574969614110996752943165 3590613605291623782353687)
                      ·
                        rfl

theorem cell23_6992695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 4, 1, 3].length) (baseStart_6992695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992695 prefixEnd_6992695 := by exact prefixLift 6992695
  have htrace : WordTrace (prefixWord ++ tailWord_6992695) baseStart_6992695 baseEnd_6992695 := by
    simpa [prefixWord, tailWord_6992695, baseEnd_6992695] using wordTrace_append hprefix tailTrace_6992695
  have hstable : (prefixWord ++ tailWord_6992695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992695).length < 2 ^ (prefixWord ++ tailWord_6992695).sum := by decide
  have hdescent : baseEnd_6992695 < baseStart_6992695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992696 : List Nat := [2, 1, 2, 1, 3, 2, 5, 2, 1, 2, 2]
def baseStart_6992696 : Nat := 118140960795 + 6992696 * 2 ^ 59
def prefixEnd_6992696 : Nat := 4983230072969 + 3 ^ 40 * 6992696 * 2
def baseEnd_6992696 : Nat := 3590614118772278278441183

theorem tailTrace_6992696 : CollatzResearch.WordTrace tailWord_6992696 prefixEnd_6992696 3590614118772278278441183 := by
  unfold tailWord_6992696
  simp only [CollatzResearch.WordTrace]
  refine ⟨127522287937332062121110971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170029717249776082828147961 127522287937332062121110971)
  ·
    refine ⟨191283431905998093181666457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127522287937332062121110971 191283431905998093181666457)
    ·
      refine ⟨143462573929498569886249843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191283431905998093181666457 143462573929498569886249843)
      ·
        refine ⟨215193860894247854829374765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143462573929498569886249843 215193860894247854829374765)
        ·
          refine ⟨80697697835342945561015537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215193860894247854829374765 80697697835342945561015537)
          ·
            refine ⟨60523273376507209170761653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80697697835342945561015537 60523273376507209170761653)
            ·
              refine ⟨5674056879047550859758905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60523273376507209170761653 5674056879047550859758905)
              ·
                refine ⟨4255542659285663144819179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5674056879047550859758905 4255542659285663144819179)
                ·
                  refine ⟨6383313988928494717228769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4255542659285663144819179 6383313988928494717228769)
                  ·
                    refine ⟨4787485491696371037921577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6383313988928494717228769 4787485491696371037921577)
                    ·
                      refine ⟨3590614118772278278441183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4787485491696371037921577 3590614118772278278441183)
                      ·
                        rfl

theorem cell23_6992696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 2, 1, 2, 2].length) (baseStart_6992696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992696 prefixEnd_6992696 := by exact prefixLift 6992696
  have htrace : WordTrace (prefixWord ++ tailWord_6992696) baseStart_6992696 baseEnd_6992696 := by
    simpa [prefixWord, tailWord_6992696, baseEnd_6992696] using wordTrace_append hprefix tailTrace_6992696
  have hstable : (prefixWord ++ tailWord_6992696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992696).length < 2 ^ (prefixWord ++ tailWord_6992696).sum := by decide
  have hdescent : baseEnd_6992696 < baseStart_6992696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992712 : List Nat := [2, 1, 3, 1, 1, 3, 3, 3, 2, 1, 3]
def baseStart_6992712 : Nat := 118140960795 + 6992712 * 2 ^ 59
def prefixEnd_6992712 : Nat := 4983230072969 + 3 ^ 40 * 6992712 * 2
def baseEnd_6992712 : Nat := 3590622334462750215841109

theorem tailTrace_6992712 : CollatzResearch.WordTrace tailWord_6992712 prefixEnd_6992712 3590622334462750215841109 := by
  unfold tailWord_6992712
  simp only [CollatzResearch.WordTrace]
  refine ⟨127522579721303079487402195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170030106295070772649869593 127522579721303079487402195)
  ·
    refine ⟨191283869581954619231103293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127522579721303079487402195 191283869581954619231103293)
    ·
      refine ⟨71731451093232982211663735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191283869581954619231103293 71731451093232982211663735)
      ·
        refine ⟨107597176639849473317495603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71731451093232982211663735 107597176639849473317495603)
        ·
          refine ⟨161395764959774209976243405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107597176639849473317495603 161395764959774209976243405)
          ·
            refine ⟨60523411859915328741091277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161395764959774209976243405 60523411859915328741091277)
            ·
              refine ⟨22696279447468248277909229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60523411859915328741091277 22696279447468248277909229)
              ·
                refine ⟨8511104792800593104215961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22696279447468248277909229 8511104792800593104215961)
                ·
                  refine ⟨6383328594600444828161971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8511104792800593104215961 6383328594600444828161971)
                  ·
                    refine ⟨9574992891900667242242957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6383328594600444828161971 9574992891900667242242957)
                    ·
                      refine ⟨3590622334462750215841109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9574992891900667242242957 3590622334462750215841109)
                      ·
                        rfl

theorem cell23_6992712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_6992712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992712 prefixEnd_6992712 := by exact prefixLift 6992712
  have htrace : WordTrace (prefixWord ++ tailWord_6992712) baseStart_6992712 baseEnd_6992712 := by
    simpa [prefixWord, tailWord_6992712, baseEnd_6992712] using wordTrace_append hprefix tailTrace_6992712
  have hstable : (prefixWord ++ tailWord_6992712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992712).length < 2 ^ (prefixWord ++ tailWord_6992712).sum := by decide
  have hdescent : baseEnd_6992712 < baseStart_6992712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992722 : List Nat := [3, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2]
def baseStart_6992722 : Nat := 118140960795 + 6992722 * 2 ^ 59
def prefixEnd_6992722 : Nat := 4983230072969 + 3 ^ 40 * 6992722 * 2
def baseEnd_6992722 : Nat := 3590627469269295176716063

theorem tailTrace_6992722 : CollatzResearch.WordTrace tailWord_6992722 prefixEnd_6992722 3590627469269295176716063 := by
  unfold tailWord_6992722
  simp only [CollatzResearch.WordTrace]
  refine ⟨63761381043142482670667105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170030349448379953788445613 63761381043142482670667105)
  ·
    refine ⟨47821035782356862003000329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63761381043142482670667105 47821035782356862003000329)
    ·
      refine ⟨35865776836767646502250247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47821035782356862003000329 35865776836767646502250247)
      ·
        refine ⟨53798665255151469753375371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35865776836767646502250247 53798665255151469753375371)
        ·
          refine ⟨80697997882727204630063057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53798665255151469753375371 80697997882727204630063057)
          ·
            refine ⟨60523498412045403472547293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80697997882727204630063057 60523498412045403472547293)
            ·
              refine ⟨22696311904517026302205235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60523498412045403472547293 22696311904517026302205235)
              ·
                refine ⟨34044467856775539453307853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22696311904517026302205235 34044467856775539453307853)
                ·
                  refine ⟨12766675446290827294990445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34044467856775539453307853 12766675446290827294990445)
                  ·
                    refine ⟨4787503292359060235621417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12766675446290827294990445 4787503292359060235621417)
                    ·
                      refine ⟨3590627469269295176716063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4787503292359060235621417 3590627469269295176716063)
                      ·
                        rfl

theorem cell23_6992722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_6992722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992722 prefixEnd_6992722 := by exact prefixLift 6992722
  have htrace : WordTrace (prefixWord ++ tailWord_6992722) baseStart_6992722 baseEnd_6992722 := by
    simpa [prefixWord, tailWord_6992722, baseEnd_6992722] using wordTrace_append hprefix tailTrace_6992722
  have hstable : (prefixWord ++ tailWord_6992722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992722).length < 2 ^ (prefixWord ++ tailWord_6992722).sum := by decide
  have hdescent : baseEnd_6992722 < baseStart_6992722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992752 : List Nat := [2, 1, 1, 1, 4, 1, 2, 3, 4, 2, 2]
def baseStart_6992752 : Nat := 118140960795 + 6992752 * 2 ^ 59
def prefixEnd_6992752 : Nat := 4983230072969 + 3 ^ 40 * 6992752 * 2
def baseEnd_6992752 : Nat := 3590642873688930059340925

theorem tailTrace_6992752 : CollatzResearch.WordTrace tailWord_6992752 prefixEnd_6992752 3590642873688930059340925 := by
  unfold tailWord_6992752
  simp only [CollatzResearch.WordTrace]
  refine ⟨127523309181230622903130255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170031078908307497204173673 127523309181230622903130255)
  ·
    refine ⟨191284963771845934354695383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127523309181230622903130255 191284963771845934354695383)
    ·
      refine ⟨286927445657768901532043075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191284963771845934354695383 286927445657768901532043075)
      ·
        refine ⟨430391168486653352298064613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286927445657768901532043075 430391168486653352298064613)
        ·
          refine ⟨80698344091247503555887115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 430391168486653352298064613 80698344091247503555887115)
          ·
            refine ⟨121047516136871255333830673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80698344091247503555887115 121047516136871255333830673)
            ·
              refine ⟨90785637102653441500373005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121047516136871255333830673 90785637102653441500373005)
              ·
                refine ⟨34044613913495040562639877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90785637102653441500373005 34044613913495040562639877)
                ·
                  refine ⟨6383365108780320105494977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34044613913495040562639877 6383365108780320105494977)
                  ·
                    refine ⟨4787523831585240079121233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6383365108780320105494977 4787523831585240079121233)
                    ·
                      refine ⟨3590642873688930059340925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4787523831585240079121233 3590642873688930059340925)
                      ·
                        rfl

theorem cell23_6992752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 4, 2, 2].length) (baseStart_6992752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992752 prefixEnd_6992752 := by exact prefixLift 6992752
  have htrace : WordTrace (prefixWord ++ tailWord_6992752) baseStart_6992752 baseEnd_6992752 := by
    simpa [prefixWord, tailWord_6992752, baseEnd_6992752] using wordTrace_append hprefix tailTrace_6992752
  have hstable : (prefixWord ++ tailWord_6992752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992752).length < 2 ^ (prefixWord ++ tailWord_6992752).sum := by decide
  have hdescent : baseEnd_6992752 < baseStart_6992752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992775 : List Nat := [1, 1, 4, 2, 3, 2, 1, 2, 7]
def baseStart_6992775 : Nat := 118140960795 + 6992775 * 2 ^ 59
def prefixEnd_6992775 : Nat := 4983230072969 + 3 ^ 40 * 6992775 * 2
def baseEnd_6992775 : Nat := 398961631527109274372591

theorem tailTrace_6992775 : CollatzResearch.WordTrace tailWord_6992775 prefixEnd_6992775 398961631527109274372591 := by
  unfold tailWord_6992775
  simp only [CollatzResearch.WordTrace]
  refine ⟨255047457241377920734347779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170031638160918613822898519 255047457241377920734347779)
  ·
    refine ⟨382571185862066881101521669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255047457241377920734347779 382571185862066881101521669)
    ·
      refine ⟨71732097349137540206535313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 382571185862066881101521669 71732097349137540206535313)
      ·
        refine ⟨53799073011853155154901485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71732097349137540206535313 53799073011853155154901485)
        ·
          refine ⟨20174652379444933183088057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53799073011853155154901485 20174652379444933183088057)
          ·
            refine ⟨15130989284583699887316043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20174652379444933183088057 15130989284583699887316043)
            ·
              refine ⟨22696483926875549830974065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15130989284583699887316043 22696483926875549830974065)
              ·
                refine ⟨17022362945156662373230549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22696483926875549830974065 17022362945156662373230549)
                ·
                  refine ⟨398961631527109274372591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17022362945156662373230549 398961631527109274372591)
                  ·
                    rfl

theorem cell23_6992775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 7].length) (baseStart_6992775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992775 prefixEnd_6992775 := by exact prefixLift 6992775
  have htrace : WordTrace (prefixWord ++ tailWord_6992775) baseStart_6992775 baseEnd_6992775 := by
    simpa [prefixWord, tailWord_6992775, baseEnd_6992775] using wordTrace_append hprefix tailTrace_6992775
  have hstable : (prefixWord ++ tailWord_6992775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992775).length < 2 ^ (prefixWord ++ tailWord_6992775).sum := by decide
  have hdescent : baseEnd_6992775 < baseStart_6992775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992790 : List Nat := [5, 3, 1, 1, 1, 1, 4, 1, 1, 3, 2]
def baseStart_6992790 : Nat := 118140960795 + 6992790 * 2 ^ 59
def prefixEnd_6992790 : Nat := 4983230072969 + 3 ^ 40 * 6992790 * 2
def baseEnd_6992790 : Nat := 3590662385953800910665751

theorem tailTrace_6992790 : CollatzResearch.WordTrace tailWord_6992790 prefixEnd_6992790 3590662385953800910665751 := by
  unfold tailWord_6992790
  simp only [CollatzResearch.WordTrace]
  refine ⟨15940500271020223643508989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170032002890882385530762549 15940500271020223643508989)
  ·
    refine ⟨5977687601632583866315871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15940500271020223643508989 5977687601632583866315871)
    ·
      refine ⟨8966531402448875799473807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5977687601632583866315871 8966531402448875799473807)
      ·
        refine ⟨13449797103673313699210711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8966531402448875799473807 13449797103673313699210711)
        ·
          refine ⟨20174695655509970548816067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13449797103673313699210711 20174695655509970548816067)
          ·
            refine ⟨30262043483264955823224101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20174695655509970548816067 30262043483264955823224101)
            ·
              refine ⟨5674133153112179216854519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30262043483264955823224101 5674133153112179216854519)
              ·
                refine ⟨8511199729668268825281779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5674133153112179216854519 8511199729668268825281779)
                ·
                  refine ⟨12766799594502403237922669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8511199729668268825281779 12766799594502403237922669)
                  ·
                    refine ⟨4787549847938401214221001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12766799594502403237922669 4787549847938401214221001)
                    ·
                      refine ⟨3590662385953800910665751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4787549847938401214221001 3590662385953800910665751)
                      ·
                        rfl

theorem cell23_6992790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_6992790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992790 prefixEnd_6992790 := by exact prefixLift 6992790
  have htrace : WordTrace (prefixWord ++ tailWord_6992790) baseStart_6992790 baseEnd_6992790 := by
    simpa [prefixWord, tailWord_6992790, baseEnd_6992790] using wordTrace_append hprefix tailTrace_6992790
  have hstable : (prefixWord ++ tailWord_6992790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992790).length < 2 ^ (prefixWord ++ tailWord_6992790).sum := by decide
  have hdescent : baseEnd_6992790 < baseStart_6992790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992802 : List Nat := [3, 3, 1, 2, 2, 1, 1, 2, 2, 3, 3]
def baseStart_6992802 : Nat := 118140960795 + 6992802 * 2 ^ 59
def prefixEnd_6992802 : Nat := 4983230072969 + 3 ^ 40 * 6992802 * 2
def baseEnd_6992802 : Nat := 3590668547721654863715695

theorem tailTrace_6992802 : CollatzResearch.WordTrace tailWord_6992802 prefixEnd_6992802 3590668547721654863715695 := by
  unfold tailWord_6992802
  simp only [CollatzResearch.WordTrace]
  refine ⟨63762110503070026086395165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170032294674853402897053773 63762110503070026086395165)
  ·
    refine ⟨23910791438651259782398187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63762110503070026086395165 23910791438651259782398187)
    ·
      refine ⟨35866187157976889673597281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23910791438651259782398187 35866187157976889673597281)
      ·
        refine ⟨26899640368482667255197961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35866187157976889673597281 26899640368482667255197961)
        ·
          refine ⟨20174730276362000441398471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26899640368482667255197961 20174730276362000441398471)
          ·
            refine ⟨30262095414543000662097707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20174730276362000441398471 30262095414543000662097707)
            ·
              refine ⟨45393143121814500993146561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30262095414543000662097707 45393143121814500993146561)
              ·
                refine ⟨34044857341360875744859921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45393143121814500993146561 34044857341360875744859921)
                ·
                  refine ⟨25533643006020656808644941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34044857341360875744859921 25533643006020656808644941)
                  ·
                    refine ⟨9575116127257746303241853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25533643006020656808644941 9575116127257746303241853)
                    ·
                      refine ⟨3590668547721654863715695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9575116127257746303241853 3590668547721654863715695)
                      ·
                        rfl

theorem cell23_6992802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_6992802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992802 prefixEnd_6992802 := by exact prefixLift 6992802
  have htrace : WordTrace (prefixWord ++ tailWord_6992802) baseStart_6992802 baseEnd_6992802 := by
    simpa [prefixWord, tailWord_6992802, baseEnd_6992802] using wordTrace_append hprefix tailTrace_6992802
  have hstable : (prefixWord ++ tailWord_6992802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992802).length < 2 ^ (prefixWord ++ tailWord_6992802).sum := by decide
  have hdescent : baseEnd_6992802 < baseStart_6992802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992820 : List Nat := [2, 5, 2, 1, 1, 2, 3, 1, 2, 2, 2]
def baseStart_6992820 : Nat := 118140960795 + 6992820 * 2 ^ 59
def prefixEnd_6992820 : Nat := 4983230072969 + 3 ^ 40 * 6992820 * 2
def baseEnd_6992820 : Nat := 3590677790373435793290613

theorem tailTrace_6992820 : CollatzResearch.WordTrace tailWord_6992820 prefixEnd_6992820 3590677790373435793290613 := by
  unfold tailWord_6992820
  simp only [CollatzResearch.WordTrace]
  refine ⟨127524549263107446709867957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170032732350809928946490609 127524549263107446709867957)
  ·
    refine ⟨11955426493416323129050121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127524549263107446709867957 11955426493416323129050121)
    ·
      refine ⟨8966569870062242346787591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11955426493416323129050121 8966569870062242346787591)
      ·
        refine ⟨13449854805093363520181387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8966569870062242346787591 13449854805093363520181387)
        ·
          refine ⟨20174782207640045280272081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13449854805093363520181387 20174782207640045280272081)
          ·
            refine ⟨15131086655730033960204061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20174782207640045280272081 15131086655730033960204061)
            ·
              refine ⟨5674157495898762735076523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15131086655730033960204061 5674157495898762735076523)
              ·
                refine ⟨8511236243848144102614785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5674157495898762735076523 8511236243848144102614785)
                ·
                  refine ⟨6383427182886108076961089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8511236243848144102614785 6383427182886108076961089)
                  ·
                    refine ⟨4787570387164581057720817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6383427182886108076961089 4787570387164581057720817)
                    ·
                      refine ⟨3590677790373435793290613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4787570387164581057720817 3590677790373435793290613)
                      ·
                        rfl

theorem cell23_6992820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_6992820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992820 prefixEnd_6992820 := by exact prefixLift 6992820
  have htrace : WordTrace (prefixWord ++ tailWord_6992820) baseStart_6992820 baseEnd_6992820 := by
    simpa [prefixWord, tailWord_6992820, baseEnd_6992820] using wordTrace_append hprefix tailTrace_6992820
  have hstable : (prefixWord ++ tailWord_6992820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992820).length < 2 ^ (prefixWord ++ tailWord_6992820).sum := by decide
  have hdescent : baseEnd_6992820 < baseStart_6992820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992825 : List Nat := [1, 2, 1, 4, 2, 2, 1, 2, 1, 3, 4]
def baseStart_6992825 : Nat := 118140960795 + 6992825 * 2 ^ 59
def prefixEnd_6992825 : Nat := 4983230072969 + 3 ^ 40 * 6992825 * 2
def baseEnd_6992825 : Nat := 3590680357776708273728089

theorem tailTrace_6992825 : CollatzResearch.WordTrace tailWord_6992825 prefixEnd_6992825 3590680357776708273728089 := by
  unfold tailWord_6992825
  simp only [CollatzResearch.WordTrace]
  refine ⟨255049280891196779273667929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170032853927464519515778619 255049280891196779273667929)
  ·
    refine ⟨191286960668397584455250947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255049280891196779273667929 191286960668397584455250947)
    ·
      refine ⟨286930441002596376682876421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191286960668397584455250947 286930441002596376682876421)
      ·
        refine ⟨53799457687986820628039329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286930441002596376682876421 53799457687986820628039329)
        ·
          refine ⟨40349593265990115471029497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53799457687986820628039329 40349593265990115471029497)
          ·
            refine ⟨30262194949492586603272123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40349593265990115471029497 30262194949492586603272123)
            ·
              refine ⟨45393292424238879904908185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30262194949492586603272123 45393292424238879904908185)
              ·
                refine ⟨34044969318179159928681139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45393292424238879904908185 34044969318179159928681139)
                ·
                  refine ⟨51067453977268739893021709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34044969318179159928681139 51067453977268739893021709)
                  ·
                    refine ⟨19150295241475777459883141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51067453977268739893021709 19150295241475777459883141)
                    ·
                      refine ⟨3590680357776708273728089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19150295241475777459883141 3590680357776708273728089)
                      ·
                        rfl

theorem cell23_6992825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_6992825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992825 prefixEnd_6992825 := by exact prefixLift 6992825
  have htrace : WordTrace (prefixWord ++ tailWord_6992825) baseStart_6992825 baseEnd_6992825 := by
    simpa [prefixWord, tailWord_6992825, baseEnd_6992825] using wordTrace_append hprefix tailTrace_6992825
  have hstable : (prefixWord ++ tailWord_6992825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992825).length < 2 ^ (prefixWord ++ tailWord_6992825).sum := by decide
  have hdescent : baseEnd_6992825 < baseStart_6992825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992865 : List Nat := [1, 2, 3, 1, 2, 1, 1, 6, 6]
def baseStart_6992865 : Nat := 118140960795 + 6992865 * 2 ^ 59
def prefixEnd_6992865 : Nat := 4983230072969 + 3 ^ 40 * 6992865 * 2
def baseEnd_6992865 : Nat := 398966766333654235247545

theorem tailTrace_6992865 : CollatzResearch.WordTrace tailWord_6992865 prefixEnd_6992865 398966766333654235247545 := by
  unfold tailWord_6992865
  simp only [CollatzResearch.WordTrace]
  refine ⟨255050739811051866105124049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170033826540701244070082699 255050739811051866105124049)
  ·
    refine ⟨191288054858288899578843037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255050739811051866105124049 191288054858288899578843037)
    ·
      refine ⟨71733020571858337342066139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191288054858288899578843037 71733020571858337342066139)
      ·
        refine ⟨107599530857787506013099209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71733020571858337342066139 107599530857787506013099209)
        ·
          refine ⟨80699648143340629509824407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107599530857787506013099209 80699648143340629509824407)
          ·
            refine ⟨121049472215010944264736611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80699648143340629509824407 121049472215010944264736611)
            ·
              refine ⟨181574208322516416397104917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121049472215010944264736611 181574208322516416397104917)
              ·
                refine ⟨8511291015117957018614293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 181574208322516416397104917 8511291015117957018614293)
                ·
                  refine ⟨398966766333654235247545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8511291015117957018614293 398966766333654235247545)
                  ·
                    rfl

theorem cell23_6992865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 6].length) (baseStart_6992865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992865 prefixEnd_6992865 := by exact prefixLift 6992865
  have htrace : WordTrace (prefixWord ++ tailWord_6992865) baseStart_6992865 baseEnd_6992865 := by
    simpa [prefixWord, tailWord_6992865, baseEnd_6992865] using wordTrace_append hprefix tailTrace_6992865
  have hstable : (prefixWord ++ tailWord_6992865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992865).length < 2 ^ (prefixWord ++ tailWord_6992865).sum := by decide
  have hdescent : baseEnd_6992865 < baseStart_6992865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992985 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 2, 7]
def baseStart_6992985 : Nat := 118140960795 + 6992985 * 2 ^ 59
def prefixEnd_6992985 : Nat := 4983230072969 + 3 ^ 40 * 6992985 * 2
def baseEnd_6992985 : Nat := 1196920838227142549242451

theorem tailTrace_6992985 : CollatzResearch.WordTrace tailWord_6992985 prefixEnd_6992985 1196920838227142549242451 := by
  unfold tailWord_6992985
  simp only [CollatzResearch.WordTrace]
  refine ⟨255055116570617126599492409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170036744380411417732994939 255055116570617126599492409)
  ·
    refine ⟨191291337427962844949619307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255055116570617126599492409 191291337427962844949619307)
    ·
      refine ⟨286937006141944267424428961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191291337427962844949619307 286937006141944267424428961)
      ·
        refine ⟨215202754606458200568321721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286937006141944267424428961 215202754606458200568321721)
        ·
          refine ⟨161402065954843650426241291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215202754606458200568321721 161402065954843650426241291)
          ·
            refine ⟨242103098932265475639361937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161402065954843650426241291 242103098932265475639361937)
            ·
              refine ⟨181577324199199106729521453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242103098932265475639361937 181577324199199106729521453)
              ·
                refine ⟨68091496574699665023570545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181577324199199106729521453 68091496574699665023570545)
                ·
                  refine ⟨51068622431024748767677909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68091496574699665023570545 51068622431024748767677909)
                  ·
                    refine ⟨1196920838227142549242451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51068622431024748767677909 1196920838227142549242451)
                    ·
                      rfl

theorem cell23_6992985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 7].length) (baseStart_6992985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992985 prefixEnd_6992985 := by exact prefixLift 6992985
  have htrace : WordTrace (prefixWord ++ tailWord_6992985) baseStart_6992985 baseEnd_6992985 := by
    simpa [prefixWord, tailWord_6992985, baseEnd_6992985] using wordTrace_append hprefix tailTrace_6992985
  have hstable : (prefixWord ++ tailWord_6992985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992985).length < 2 ^ (prefixWord ++ tailWord_6992985).sum := by decide
  have hdescent : baseEnd_6992985 < baseStart_6992985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6992999 : List Nat := [1, 1, 5, 1, 1, 3, 3, 1, 1, 3, 3]
def baseStart_6992999 : Nat := 118140960795 + 6992999 * 2 ^ 59
def prefixEnd_6992999 : Nat := 4983230072969 + 3 ^ 40 * 6992999 * 2
def baseEnd_6992999 : Nat := 3590769703410590592952289

theorem tailTrace_6992999 : CollatzResearch.WordTrace tailWord_6992999 prefixEnd_6992999 3590769703410590592952289 := by
  unfold tailWord_6992999
  simp only [CollatzResearch.WordTrace]
  refine ⟨255055627192566406990502051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170037084795044271327001367 255055627192566406990502051)
  ·
    refine ⟨382583440788849610485753077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255055627192566406990502051 382583440788849610485753077)
    ·
      refine ⟨35867197573954650983039351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 382583440788849610485753077 35867197573954650983039351)
      ·
        refine ⟨53800796360931976474559027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35867197573954650983039351 53800796360931976474559027)
        ·
          refine ⟨80701194541397964711838541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53800796360931976474559027 80701194541397964711838541)
          ·
            refine ⟨30262947953024236766939453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80701194541397964711838541 30262947953024236766939453)
            ·
              refine ⟨11348605482384088787602295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30262947953024236766939453 11348605482384088787602295)
              ·
                refine ⟨17022908223576133181403443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11348605482384088787602295 17022908223576133181403443)
                ·
                  refine ⟨25534362335364199772105165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17022908223576133181403443 25534362335364199772105165)
                  ·
                    refine ⟨9575385875761574914539437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25534362335364199772105165 9575385875761574914539437)
                    ·
                      refine ⟨3590769703410590592952289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9575385875761574914539437 3590769703410590592952289)
                      ·
                        rfl

theorem cell23_6992999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_6992999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6992999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6992999 prefixEnd_6992999 := by exact prefixLift 6992999
  have htrace : WordTrace (prefixWord ++ tailWord_6992999) baseStart_6992999 baseEnd_6992999 := by
    simpa [prefixWord, tailWord_6992999, baseEnd_6992999] using wordTrace_append hprefix tailTrace_6992999
  have hstable : (prefixWord ++ tailWord_6992999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6992999).length < 2 ^ (prefixWord ++ tailWord_6992999).sum := by decide
  have hdescent : baseEnd_6992999 < baseStart_6992999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6992999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993017 : List Nat := [1, 2, 1, 3, 6, 1, 1, 3, 1, 2, 2]
def baseStart_6993017 : Nat := 118140960795 + 6993017 * 2 ^ 59
def prefixEnd_6993017 : Nat := 4983230072969 + 3 ^ 40 * 6993017 * 2
def baseEnd_6993017 : Nat := 3590778946062371522527207

theorem tailTrace_6993017 : CollatzResearch.WordTrace tailWord_6993017 prefixEnd_6993017 3590778946062371522527207 := by
  unfold tailWord_6993017
  simp only [CollatzResearch.WordTrace]
  refine ⟨255056283706501196064657305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170037522471000797376438203 255056283706501196064657305)
  ·
    refine ⟨191292212779875897048492979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255056283706501196064657305 191292212779875897048492979)
    ·
      refine ⟨286938319169813845572739469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191292212779875897048492979 286938319169813845572739469)
      ·
        refine ⟨107601869688680192089777301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286938319169813845572739469 107601869688680192089777301)
        ·
          refine ⟨5043837641656884004208311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 107601869688680192089777301 5043837641656884004208311)
          ·
            refine ⟨7565756462485326006312467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5043837641656884004208311 7565756462485326006312467)
            ·
              refine ⟨11348634693727989009468701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7565756462485326006312467 11348634693727989009468701)
              ·
                refine ⟨4255738010147995878550763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11348634693727989009468701 4255738010147995878550763)
                ·
                  refine ⟨6383607015221993817826145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4255738010147995878550763 6383607015221993817826145)
                  ·
                    refine ⟨4787705261416495363369609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6383607015221993817826145 4787705261416495363369609)
                    ·
                      refine ⟨3590778946062371522527207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4787705261416495363369609 3590778946062371522527207)
                      ·
                        rfl

theorem cell23_6993017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 3, 1, 2, 2].length) (baseStart_6993017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993017 prefixEnd_6993017 := by exact prefixLift 6993017
  have htrace : WordTrace (prefixWord ++ tailWord_6993017) baseStart_6993017 baseEnd_6993017 := by
    simpa [prefixWord, tailWord_6993017, baseEnd_6993017] using wordTrace_append hprefix tailTrace_6993017
  have hstable : (prefixWord ++ tailWord_6993017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993017).length < 2 ^ (prefixWord ++ tailWord_6993017).sum := by decide
  have hdescent : baseEnd_6993017 < baseStart_6993017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993050 : List Nat := [3, 1, 1, 5, 1, 3, 2, 1, 2, 1, 3]
def baseStart_6993050 : Nat := 118140960795 + 6993050 * 2 ^ 59
def prefixEnd_6993050 : Nat := 4983230072969 + 3 ^ 40 * 6993050 * 2
def baseEnd_6993050 : Nat := 3590795890923969893414555

theorem tailTrace_6993050 : CollatzResearch.WordTrace tailWord_6993050 prefixEnd_6993050 3590795890923969893414555 := by
  unfold tailWord_6993050
  simp only [CollatzResearch.WordTrace]
  refine ⟨63764371828845410675152151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170038324876921095133739069 63764371828845410675152151)
  ·
    refine ⟨95646557743268116012728227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63764371828845410675152151 95646557743268116012728227)
    ·
      refine ⟨143469836614902174019092341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95646557743268116012728227 143469836614902174019092341)
      ·
        refine ⟨13450297182647078814289907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143469836614902174019092341 13450297182647078814289907)
        ·
          refine ⟨20175445773970618221434861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13450297182647078814289907 20175445773970618221434861)
          ·
            refine ⟨7565792165238981833038073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20175445773970618221434861 7565792165238981833038073)
            ·
              refine ⟨5674344123929236374778555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7565792165238981833038073 5674344123929236374778555)
              ·
                refine ⟨8511516185893854562167833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5674344123929236374778555 8511516185893854562167833)
                ·
                  refine ⟨6383637139420390921625875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8511516185893854562167833 6383637139420390921625875)
                  ·
                    refine ⟨9575455709130586382438813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6383637139420390921625875 9575455709130586382438813)
                    ·
                      refine ⟨3590795890923969893414555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9575455709130586382438813 3590795890923969893414555)
                      ·
                        rfl

theorem cell23_6993050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_6993050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993050 prefixEnd_6993050 := by exact prefixLift 6993050
  have htrace : WordTrace (prefixWord ++ tailWord_6993050) baseStart_6993050 baseEnd_6993050 := by
    simpa [prefixWord, tailWord_6993050, baseEnd_6993050] using wordTrace_append hprefix tailTrace_6993050
  have hstable : (prefixWord ++ tailWord_6993050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993050).length < 2 ^ (prefixWord ++ tailWord_6993050).sum := by decide
  have hdescent : baseEnd_6993050 < baseStart_6993050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993072 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 3]
def baseStart_6993072 : Nat := 118140960795 + 6993072 * 2 ^ 59
def prefixEnd_6993072 : Nat := 4983230072969 + 3 ^ 40 * 6993072 * 2
def baseEnd_6993072 : Nat := 3590807187498368807339453

theorem tailTrace_6993072 : CollatzResearch.WordTrace tailWord_6993072 prefixEnd_6993072 3590807187498368807339453 := by
  unfold tailWord_6993072
  simp only [CollatzResearch.WordTrace]
  refine ⟨127529144860650970228954735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170038859814201293638606313 127529144860650970228954735)
  ·
    refine ⟨191293717290976455343432103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127529144860650970228954735 191293717290976455343432103)
    ·
      refine ⟨286940575936464683015148155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191293717290976455343432103 286940575936464683015148155)
      ·
        refine ⟨430410863904697024522722233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286940575936464683015148155 430410863904697024522722233)
        ·
          refine ⟨322808147928522768392041675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 430410863904697024522722233 322808147928522768392041675)
          ·
            refine ⟨484212221892784152588062513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322808147928522768392041675 484212221892784152588062513)
            ·
              refine ⟨363159166419588114441046885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 484212221892784152588062513 363159166419588114441046885)
              ·
                refine ⟨68092343703672771457696291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 363159166419588114441046885 68092343703672771457696291)
                ·
                  refine ⟨102138515555509157186544437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68092343703672771457696291 102138515555509157186544437)
                  ·
                    refine ⟨9575485833328983486238541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102138515555509157186544437 9575485833328983486238541)
                    ·
                      refine ⟨3590807187498368807339453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9575485833328983486238541 3590807187498368807339453)
                      ·
                        rfl

theorem cell23_6993072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 3].length) (baseStart_6993072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993072 prefixEnd_6993072 := by exact prefixLift 6993072
  have htrace : WordTrace (prefixWord ++ tailWord_6993072) baseStart_6993072 baseEnd_6993072 := by
    simpa [prefixWord, tailWord_6993072, baseEnd_6993072] using wordTrace_append hprefix tailTrace_6993072
  have hstable : (prefixWord ++ tailWord_6993072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993072).length < 2 ^ (prefixWord ++ tailWord_6993072).sum := by decide
  have hdescent : baseEnd_6993072 < baseStart_6993072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993079 : List Nat := [1, 1, 3, 1, 4, 1, 2, 5, 5]
def baseStart_6993079 : Nat := 118140960795 + 6993079 * 2 ^ 59
def prefixEnd_6993079 : Nat := 4983230072969 + 3 ^ 40 * 6993079 * 2
def baseEnd_6993079 : Nat := 398978975762550031105769

theorem tailTrace_6993079 : CollatzResearch.WordTrace tailWord_6993079 prefixEnd_6993079 398978975762550031105769 := by
  unfold tailWord_6993079
  simp only [CollatzResearch.WordTrace]
  refine ⟨255058545032276580653414291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170039030021517720435609527 255058545032276580653414291)
  ·
    refine ⟨382587817548414870980121437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255058545032276580653414291 382587817548414870980121437)
    ·
      refine ⟨143470431580655576617545539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 382587817548414870980121437 143470431580655576617545539)
      ·
        refine ⟨215205647370983364926318309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143470431580655576617545539 215205647370983364926318309)
        ·
          refine ⟨40351058882059380923684683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215205647370983364926318309 40351058882059380923684683)
          ·
            refine ⟨60526588323089071385527025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40351058882059380923684683 60526588323089071385527025)
            ·
              refine ⟨45394941242316803539145269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60526588323089071385527025 45394941242316803539145269)
              ·
                refine ⟨4255775741467200331794869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45394941242316803539145269 4255775741467200331794869)
                ·
                  refine ⟨398978975762550031105769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4255775741467200331794869 398978975762550031105769)
                  ·
                    rfl

theorem cell23_6993079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 5, 5].length) (baseStart_6993079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993079 prefixEnd_6993079 := by exact prefixLift 6993079
  have htrace : WordTrace (prefixWord ++ tailWord_6993079) baseStart_6993079 baseEnd_6993079 := by
    simpa [prefixWord, tailWord_6993079, baseEnd_6993079] using wordTrace_append hprefix tailTrace_6993079
  have hstable : (prefixWord ++ tailWord_6993079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993079).length < 2 ^ (prefixWord ++ tailWord_6993079).sum := by decide
  have hdescent : baseEnd_6993079 < baseStart_6993079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993096 : List Nat := [2, 1, 3, 1, 2, 1, 6, 2, 5]
def baseStart_6993096 : Nat := 118140960795 + 6993096 * 2 ^ 59
def prefixEnd_6993096 : Nat := 4983230072969 + 3 ^ 40 * 6993096 * 2
def baseEnd_6993096 : Nat := 398979945670452968159927

theorem tailTrace_6993096 : CollatzResearch.WordTrace tailWord_6993096 prefixEnd_6993096 398979945670452968159927 := by
  unfold tailWord_6993096
  simp only [CollatzResearch.WordTrace]
  refine ⟨127529582536607496278391571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170039443382143328371188761 127529582536607496278391571)
  ·
    refine ⟨191294373804911244417587357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127529582536607496278391571 191294373804911244417587357)
    ·
      refine ⟨71735390176841716656595259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191294373804911244417587357 71735390176841716656595259)
      ·
        refine ⟨107603085265262574984892889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71735390176841716656595259 107603085265262574984892889)
        ·
          refine ⟨80702313948946931238669667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107603085265262574984892889 80702313948946931238669667)
          ·
            refine ⟨121053470923420396858004501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80702313948946931238669667 121053470923420396858004501)
            ·
              refine ⟨5674381449535331102718961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121053470923420396858004501 5674381449535331102718961)
              ·
                refine ⟨4255786087151498327039221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5674381449535331102718961 4255786087151498327039221)
                ·
                  refine ⟨398979945670452968159927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4255786087151498327039221 398979945670452968159927)
                  ·
                    rfl

theorem cell23_6993096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 2, 5].length) (baseStart_6993096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993096 prefixEnd_6993096 := by exact prefixLift 6993096
  have htrace : WordTrace (prefixWord ++ tailWord_6993096) baseStart_6993096 baseEnd_6993096 := by
    simpa [prefixWord, tailWord_6993096, baseEnd_6993096] using wordTrace_append hprefix tailTrace_6993096
  have hstable : (prefixWord ++ tailWord_6993096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993096).length < 2 ^ (prefixWord ++ tailWord_6993096).sum := by decide
  have hdescent : baseEnd_6993096 < baseStart_6993096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993129 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 6, 4, 2]
def baseStart_6993129 : Nat := 118140960795 + 6993129 * 2 ^ 59
def prefixEnd_6993129 : Nat := 4983230072969 + 3 ^ 40 * 6993129 * 2
def baseEnd_6993129 : Nat := 3590836455895675084326691

theorem tailTrace_6993129 : CollatzResearch.WordTrace tailWord_6993129 prefixEnd_6993129 3590836455895675084326691 := by
  unfold tailWord_6993129
  simp only [CollatzResearch.WordTrace]
  refine ⟨255060368682095439192734441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170040245788063626128489627 255060368682095439192734441)
  ·
    refine ⟨191295276511571579394550831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255060368682095439192734441 191295276511571579394550831)
    ·
      refine ⟨286942914767357369091826247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191295276511571579394550831 286942914767357369091826247)
      ·
        refine ⟨430414372151036053637739371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286942914767357369091826247 430414372151036053637739371)
        ·
          refine ⟨645621558226554080456609057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430414372151036053637739371 645621558226554080456609057)
          ·
            refine ⟨484216168669915560342456793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 645621558226554080456609057 484216168669915560342456793)
            ·
              refine ⟨363162126502436670256842595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 484216168669915560342456793 363162126502436670256842595)
              ·
                refine ⟨544743189753655005385263893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363162126502436670256842595 544743189753655005385263893)
                ·
                  refine ⟨25534837019702578377434245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 544743189753655005385263893 25534837019702578377434245)
                  ·
                    refine ⟨4787781941194233445768921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25534837019702578377434245 4787781941194233445768921)
                    ·
                      refine ⟨3590836455895675084326691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4787781941194233445768921 3590836455895675084326691)
                      ·
                        rfl

theorem cell23_6993129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 4, 2].length) (baseStart_6993129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993129 prefixEnd_6993129 := by exact prefixLift 6993129
  have htrace : WordTrace (prefixWord ++ tailWord_6993129) baseStart_6993129 baseEnd_6993129 := by
    simpa [prefixWord, tailWord_6993129, baseEnd_6993129] using wordTrace_append hprefix tailTrace_6993129
  have hstable : (prefixWord ++ tailWord_6993129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993129).length < 2 ^ (prefixWord ++ tailWord_6993129).sum := by decide
  have hdescent : baseEnd_6993129 < baseStart_6993129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993156 : List Nat := [2, 3, 2, 2, 2, 1, 1, 3, 3, 4]
def baseStart_6993156 : Nat := 118140960795 + 6993156 * 2 ^ 59
def prefixEnd_6993156 : Nat := 4983230072969 + 3 ^ 40 * 6993156 * 2
def baseEnd_6993156 : Nat := 1196950106624448826229689

theorem tailTrace_6993156 : CollatzResearch.WordTrace tailWord_6993156 prefixEnd_6993156 1196950106624448826229689 := by
  unfold tailWord_6993156
  simp only [CollatzResearch.WordTrace]
  refine ⟨127530676726498811401983661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170040902301998415202644881 127530676726498811401983661)
  ·
    refine ⟨47824003772437054275743873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127530676726498811401983661 47824003772437054275743873)
    ·
      refine ⟨35868002829327790706807905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47824003772437054275743873 35868002829327790706807905)
      ·
        refine ⟨26901002121995843030105929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35868002829327790706807905 26901002121995843030105929)
        ·
          refine ⟨20175751591496882272579447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26901002121995843030105929 20175751591496882272579447)
          ·
            refine ⟨30263627387245323408869171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20175751591496882272579447 30263627387245323408869171)
            ·
              refine ⟨45395441080867985113303757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30263627387245323408869171 45395441080867985113303757)
              ·
                refine ⟨17023290405325494417488909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45395441080867985113303757 17023290405325494417488909)
                ·
                  refine ⟨6383733901997060406558341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17023290405325494417488909 6383733901997060406558341)
                  ·
                    refine ⟨1196950106624448826229689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6383733901997060406558341 1196950106624448826229689)
                    ·
                      rfl

theorem cell23_6993156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_6993156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993156 prefixEnd_6993156 := by exact prefixLift 6993156
  have htrace : WordTrace (prefixWord ++ tailWord_6993156) baseStart_6993156 baseEnd_6993156 := by
    simpa [prefixWord, tailWord_6993156, baseEnd_6993156] using wordTrace_append hprefix tailTrace_6993156
  have hstable : (prefixWord ++ tailWord_6993156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993156).length < 2 ^ (prefixWord ++ tailWord_6993156).sum := by decide
  have hdescent : baseEnd_6993156 < baseStart_6993156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993219 : List Nat := [1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 4]
def baseStart_6993219 : Nat := 118140960795 + 6993219 * 2 ^ 59
def prefixEnd_6993219 : Nat := 4983230072969 + 3 ^ 40 * 6993219 * 2
def baseEnd_6993219 : Nat := 3590882669154579732201277

theorem tailTrace_6993219 : CollatzResearch.WordTrace tailWord_6993219 prefixEnd_6993219 3590882669154579732201277 := by
  unfold tailWord_6993219
  simp only [CollatzResearch.WordTrace]
  refine ⟨255063651251769384563510711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170042434167846256375673807 255063651251769384563510711)
  ·
    refine ⟨382595476877654076845266067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255063651251769384563510711 382595476877654076845266067)
    ·
      refine ⟨573893215316481115267899101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382595476877654076845266067 573893215316481115267899101)
      ·
        refine ⟨215209955743680418225462163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 573893215316481115267899101 215209955743680418225462163)
        ·
          refine ⟨322814933615520627338193245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215209955743680418225462163 322814933615520627338193245)
          ·
            refine ⟨121055600105820235251822467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 322814933615520627338193245 121055600105820235251822467)
            ·
              refine ⟨181583400158730352877733701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121055600105820235251822467 181583400158730352877733701)
              ·
                refine ⟨34046887529761941164575069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181583400158730352877733701 34046887529761941164575069)
                ·
                  refine ⟨12767582823660727936715651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34046887529761941164575069 12767582823660727936715651)
                  ·
                    refine ⟨19151374235491091905073477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12767582823660727936715651 19151374235491091905073477)
                    ·
                      refine ⟨3590882669154579732201277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19151374235491091905073477 3590882669154579732201277)
                      ·
                        rfl

theorem cell23_6993219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_6993219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993219 prefixEnd_6993219 := by exact prefixLift 6993219
  have htrace : WordTrace (prefixWord ++ tailWord_6993219) baseStart_6993219 baseEnd_6993219 := by
    simpa [prefixWord, tailWord_6993219, baseEnd_6993219] using wordTrace_append hprefix tailTrace_6993219
  have hstable : (prefixWord ++ tailWord_6993219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993219).length < 2 ^ (prefixWord ++ tailWord_6993219).sum := by decide
  have hdescent : baseEnd_6993219 < baseStart_6993219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993220 : List Nat := [2, 3, 4, 1, 1, 3, 2, 1, 6]
def baseStart_6993220 : Nat := 118140960795 + 6993220 * 2 ^ 59
def prefixEnd_6993220 : Nat := 4983230072969 + 3 ^ 40 * 6993220 * 2
def baseEnd_6993220 : Nat := 398987020292803803143197

theorem tailTrace_6993220 : CollatzResearch.WordTrace tailWord_6993220 prefixEnd_6993220 398987020292803803143197 := by
  unfold tailWord_6993220
  simp only [CollatzResearch.WordTrace]
  refine ⟨127531843862382880867148557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170042458483177174489531409 127531843862382880867148557)
  ·
    refine ⟨47824441448393580325180709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127531843862382880867148557 47824441448393580325180709)
    ·
      refine ⟨8967082771573796310971383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47824441448393580325180709 8967082771573796310971383)
      ·
        refine ⟨13450624157360694466457075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8967082771573796310971383 13450624157360694466457075)
        ·
          refine ⟨20175936236041041699685613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13450624157360694466457075 20175936236041041699685613)
          ·
            refine ⟨7565976088515390637382105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20175936236041041699685613 7565976088515390637382105)
            ·
              refine ⟨5674482066386542978036579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7565976088515390637382105 5674482066386542978036579)
              ·
                refine ⟨8511723099579814467054869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5674482066386542978036579 8511723099579814467054869)
                ·
                  refine ⟨398987020292803803143197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8511723099579814467054869 398987020292803803143197)
                  ·
                    rfl

theorem cell23_6993220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 6].length) (baseStart_6993220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993220 prefixEnd_6993220 := by exact prefixLift 6993220
  have htrace : WordTrace (prefixWord ++ tailWord_6993220) baseStart_6993220 baseEnd_6993220 := by
    simpa [prefixWord, tailWord_6993220, baseEnd_6993220] using wordTrace_append hprefix tailTrace_6993220
  have hstable : (prefixWord ++ tailWord_6993220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993220).length < 2 ^ (prefixWord ++ tailWord_6993220).sum := by decide
  have hdescent : baseEnd_6993220 < baseStart_6993220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993236 : List Nat := [2, 4, 1, 1, 2, 1, 3, 1, 3, 1, 4]
def baseStart_6993236 : Nat := 118140960795 + 6993236 * 2 ^ 59
def prefixEnd_6993236 : Nat := 4983230072969 + 3 ^ 40 * 6993236 * 2
def baseEnd_6993236 : Nat := 3590891398325706165688699

theorem tailTrace_6993236 : CollatzResearch.WordTrace tailWord_6993236 prefixEnd_6993236 3590891398325706165688699 := by
  unfold tailWord_6993236
  simp only [CollatzResearch.WordTrace]
  refine ⟨127532135646353898233439781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170042847528471864311253041 127532135646353898233439781)
  ·
    refine ⟨23912275433691355918769959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127532135646353898233439781 23912275433691355918769959)
    ·
      refine ⟨35868413150537033878154939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23912275433691355918769959 35868413150537033878154939)
      ·
        refine ⟨53802619725805550817232409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35868413150537033878154939 53802619725805550817232409)
        ·
          refine ⟨40351964794354163112924307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53802619725805550817232409 40351964794354163112924307)
          ·
            refine ⟨60527947191531244669386461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40351964794354163112924307 60527947191531244669386461)
            ·
              refine ⟨22697980196824216751019923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60527947191531244669386461 22697980196824216751019923)
              ·
                refine ⟨34046970295236325126529885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22697980196824216751019923 34046970295236325126529885)
                ·
                  refine ⟨12767613860713621922448707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34046970295236325126529885 12767613860713621922448707)
                  ·
                    refine ⟨19151420791070432883673061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12767613860713621922448707 19151420791070432883673061)
                    ·
                      refine ⟨3590891398325706165688699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19151420791070432883673061 3590891398325706165688699)
                      ·
                        rfl

theorem cell23_6993236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_6993236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993236 prefixEnd_6993236 := by exact prefixLift 6993236
  have htrace : WordTrace (prefixWord ++ tailWord_6993236) baseStart_6993236 baseEnd_6993236 := by
    simpa [prefixWord, tailWord_6993236, baseEnd_6993236] using wordTrace_append hprefix tailTrace_6993236
  have hstable : (prefixWord ++ tailWord_6993236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993236).length < 2 ^ (prefixWord ++ tailWord_6993236).sum := by decide
  have hdescent : baseEnd_6993236 < baseStart_6993236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993253 : List Nat := [1, 3, 1, 3, 1, 2, 5, 1, 1, 1, 4]
def baseStart_6993253 : Nat := 118140960795 + 6993253 * 2 ^ 59
def prefixEnd_6993253 : Nat := 4983230072969 + 3 ^ 40 * 6993253 * 2
def baseEnd_6993253 : Nat := 3590900127496832599176121

theorem tailTrace_6993253 : CollatzResearch.WordTrace tailWord_6993253 prefixEnd_6993253 3590900127496832599176121 := by
  unfold tailWord_6993253
  simp only [CollatzResearch.WordTrace]
  refine ⟨255064891333646208370248413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170043260889097472246832275 255064891333646208370248413)
  ·
    refine ⟨95649334250117328138843155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255064891333646208370248413 95649334250117328138843155)
    ·
      refine ⟨143474001375175992208264733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95649334250117328138843155 143474001375175992208264733)
      ·
        refine ⟨53802750515690997078099275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143474001375175992208264733 53802750515690997078099275)
        ·
          refine ⟨80704125773536495617148913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53802750515690997078099275 80704125773536495617148913)
          ·
            refine ⟨60528094330152371712861685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80704125773536495617148913 60528094330152371712861685)
            ·
              refine ⟨5674508843451784848080783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60528094330152371712861685 5674508843451784848080783)
              ·
                refine ⟨8511763265177677272121175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5674508843451784848080783 8511763265177677272121175)
                ·
                  refine ⟨12767644897766515908181763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8511763265177677272121175 12767644897766515908181763)
                  ·
                    refine ⟨19151467346649773862272645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12767644897766515908181763 19151467346649773862272645)
                    ·
                      refine ⟨3590900127496832599176121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19151467346649773862272645 3590900127496832599176121)
                      ·
                        rfl

theorem cell23_6993253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_6993253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993253 prefixEnd_6993253 := by exact prefixLift 6993253
  have htrace : WordTrace (prefixWord ++ tailWord_6993253) baseStart_6993253 baseEnd_6993253 := by
    simpa [prefixWord, tailWord_6993253, baseEnd_6993253] using wordTrace_append hprefix tailTrace_6993253
  have hstable : (prefixWord ++ tailWord_6993253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993253).length < 2 ^ (prefixWord ++ tailWord_6993253).sum := by decide
  have hdescent : baseEnd_6993253 < baseStart_6993253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993304 : List Nat := [2, 1, 2, 5, 2, 1, 2, 3, 1, 2, 2]
def baseStart_6993304 : Nat := 118140960795 + 6993304 * 2 ^ 59
def prefixEnd_6993304 : Nat := 4983230072969 + 3 ^ 40 * 6993304 * 2
def baseEnd_6993304 : Nat := 3590926315010211899638387

theorem tailTrace_6993304 : CollatzResearch.WordTrace tailWord_6993304 prefixEnd_6993304 3590926315010211899638387 := by
  unfold tailWord_6993304
  simp only [CollatzResearch.WordTrace]
  refine ⟨127533375728230722040177483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170044500970974296053569977 127533375728230722040177483)
  ·
    refine ⟨191300063592346083060266225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127533375728230722040177483 191300063592346083060266225)
    ·
      refine ⟨143475047694259562295199669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191300063592346083060266225 143475047694259562295199669)
      ·
        refine ⟨13450785721336833965174969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143475047694259562295199669 13450785721336833965174969)
        ·
          refine ⟨10088089291002625473881227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13450785721336833965174969 10088089291002625473881227)
          ·
            refine ⟨15132133936503938210821841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10088089291002625473881227 15132133936503938210821841)
            ·
              refine ⟨11349100452377953658116381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15132133936503938210821841 11349100452377953658116381)
              ·
                refine ⟨4255912669641732621793643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11349100452377953658116381 4255912669641732621793643)
                ·
                  refine ⟨6383869004462598932690465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4255912669641732621793643 6383869004462598932690465)
                  ·
                    refine ⟨4787901753346949199517849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6383869004462598932690465 4787901753346949199517849)
                    ·
                      refine ⟨3590926315010211899638387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4787901753346949199517849 3590926315010211899638387)
                      ·
                        rfl

theorem cell23_6993304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_6993304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993304 prefixEnd_6993304 := by exact prefixLift 6993304
  have htrace : WordTrace (prefixWord ++ tailWord_6993304) baseStart_6993304 baseEnd_6993304 := by
    simpa [prefixWord, tailWord_6993304, baseEnd_6993304] using wordTrace_append hprefix tailTrace_6993304
  have hstable : (prefixWord ++ tailWord_6993304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993304).length < 2 ^ (prefixWord ++ tailWord_6993304).sum := by decide
  have hdescent : baseEnd_6993304 < baseStart_6993304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993337 : List Nat := [1, 2, 1, 4, 4, 1, 3, 1, 2, 1, 3]
def baseStart_6993337 : Nat := 118140960795 + 6993337 * 2 ^ 59
def prefixEnd_6993337 : Nat := 4983230072969 + 3 ^ 40 * 6993337 * 2
def baseEnd_6993337 : Nat := 3590943259871810270525735

theorem tailTrace_6993337 : CollatzResearch.WordTrace tailWord_6993337 prefixEnd_6993337 3590943259871810270525735 := by
  unfold tailWord_6993337
  simp only [CollatzResearch.WordTrace]
  refine ⟨255067955065341890716306265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170045303376894593810870843 255067955065341890716306265)
  ·
    refine ⟨191300966299006418037229699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255067955065341890716306265 191300966299006418037229699)
    ·
      refine ⟨286951449448509627055844549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191300966299006418037229699 286951449448509627055844549)
      ·
        refine ⟨53803396771595555072970853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286951449448509627055844549 53803396771595555072970853)
        ·
          refine ⟨10088136894674166576182035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53803396771595555072970853 10088136894674166576182035)
          ·
            refine ⟨15132205342011249864273053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10088136894674166576182035 15132205342011249864273053)
            ·
              refine ⟨5674577003254218699102395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15132205342011249864273053 5674577003254218699102395)
              ·
                refine ⟨8511865504881328048653593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5674577003254218699102395 8511865504881328048653593)
                ·
                  refine ⟨6383899128660996036490195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8511865504881328048653593 6383899128660996036490195)
                  ·
                    refine ⟨9575848692991494054735293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6383899128660996036490195 9575848692991494054735293)
                    ·
                      refine ⟨3590943259871810270525735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9575848692991494054735293 3590943259871810270525735)
                      ·
                        rfl

theorem cell23_6993337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_6993337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993337 prefixEnd_6993337 := by exact prefixLift 6993337
  have htrace : WordTrace (prefixWord ++ tailWord_6993337) baseStart_6993337 baseEnd_6993337 := by
    simpa [prefixWord, tailWord_6993337, baseEnd_6993337] using wordTrace_append hprefix tailTrace_6993337
  have hstable : (prefixWord ++ tailWord_6993337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993337).length < 2 ^ (prefixWord ++ tailWord_6993337).sum := by decide
  have hdescent : baseEnd_6993337 < baseStart_6993337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993376 : List Nat := [2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 3]
def baseStart_6993376 : Nat := 118140960795 + 6993376 * 2 ^ 59
def prefixEnd_6993376 : Nat := 4983230072969 + 3 ^ 40 * 6993376 * 2
def baseEnd_6993376 : Nat := 3590963285617335617938055

theorem tailTrace_6993376 : CollatzResearch.WordTrace tailWord_6993376 prefixEnd_6993376 3590963285617335617938055 := by
  unfold tailWord_6993376
  simp only [CollatzResearch.WordTrace]
  refine ⟨127534688756100300188487991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170046251674800400251317321 127534688756100300188487991)
  ·
    refine ⟨191302033134150450282731987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127534688756100300188487991 191302033134150450282731987)
    ·
      refine ⟨286953049701225675424097981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191302033134150450282731987 286953049701225675424097981)
      ·
        refine ⟨107607393637959628284036743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286953049701225675424097981 107607393637959628284036743)
        ·
          refine ⟨161411090456939442426055115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107607393637959628284036743 161411090456939442426055115)
          ·
            refine ⟨242116635685409163639082673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161411090456939442426055115 242116635685409163639082673)
            ·
              refine ⟨181587476764056872729312005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242116635685409163639082673 181587476764056872729312005)
              ·
                refine ⟨34047651893260663636746001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181587476764056872729312005 34047651893260663636746001)
                ·
                  refine ⟨25535738919945497727559501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34047651893260663636746001 25535738919945497727559501)
                  ·
                    refine ⟨9575902094979561647834813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25535738919945497727559501 9575902094979561647834813)
                    ·
                      refine ⟨3590963285617335617938055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9575902094979561647834813 3590963285617335617938055)
                      ·
                        rfl

theorem cell23_6993376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_6993376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993376 prefixEnd_6993376 := by exact prefixLift 6993376
  have htrace : WordTrace (prefixWord ++ tailWord_6993376) baseStart_6993376 baseEnd_6993376 := by
    simpa [prefixWord, tailWord_6993376, baseEnd_6993376] using wordTrace_append hprefix tailTrace_6993376
  have hstable : (prefixWord ++ tailWord_6993376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993376).length < 2 ^ (prefixWord ++ tailWord_6993376).sum := by decide
  have hdescent : baseEnd_6993376 < baseStart_6993376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993383 : List Nat := [1, 1, 5, 2, 1, 4, 1, 1, 7]
def baseStart_6993383 : Nat := 118140960795 + 6993383 * 2 ^ 59
def prefixEnd_6993383 : Nat := 4983230072969 + 3 ^ 40 * 6993383 * 2
def baseEnd_6993383 : Nat := 398996319997990787838947

theorem tailTrace_6993383 : CollatzResearch.WordTrace tailWord_6993383 prefixEnd_6993383 398996319997990787838947 := by
  unfold tailWord_6993383
  simp only [CollatzResearch.WordTrace]
  refine ⟨255069632823175240572480803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170046421882116827048320535 255069632823175240572480803)
  ·
    refine ⟨382604449234762860858721205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255069632823175240572480803 382604449234762860858721205)
    ·
      refine ⟨35869167115759018205505113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 382604449234762860858721205 35869167115759018205505113)
      ·
        refine ⟨26901875336819263654128835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35869167115759018205505113 26901875336819263654128835)
        ·
          refine ⟨40352813005228895481193253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26901875336819263654128835 40352813005228895481193253)
          ·
            refine ⟨7566152438480417902723735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40352813005228895481193253 7566152438480417902723735)
            ·
              refine ⟨11349228657720626854085603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7566152438480417902723735 11349228657720626854085603)
              ·
                refine ⟨17023842986580940281128405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11349228657720626854085603 17023842986580940281128405)
                ·
                  refine ⟨398996319997990787838947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17023842986580940281128405 398996319997990787838947)
                  ·
                    rfl

theorem cell23_6993383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 7].length) (baseStart_6993383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993383 prefixEnd_6993383 := by exact prefixLift 6993383
  have htrace : WordTrace (prefixWord ++ tailWord_6993383) baseStart_6993383 baseEnd_6993383 := by
    simpa [prefixWord, tailWord_6993383, baseEnd_6993383] using wordTrace_append hprefix tailTrace_6993383
  have hstable : (prefixWord ++ tailWord_6993383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993383).length < 2 ^ (prefixWord ++ tailWord_6993383).sum := by decide
  have hdescent : baseEnd_6993383 < baseStart_6993383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993394 : List Nat := [3, 2, 1, 4, 1, 1, 4, 1, 2, 2, 2]
def baseStart_6993394 : Nat := 118140960795 + 6993394 * 2 ^ 59
def prefixEnd_6993394 : Nat := 4983230072969 + 3 ^ 40 * 6993394 * 2
def baseEnd_6993394 : Nat := 3590972528269116547512973

theorem tailTrace_6993394 : CollatzResearch.WordTrace tailWord_6993394 prefixEnd_6993394 3590972528269116547512973 := by
  unfold tailWord_6993394
  simp only [CollatzResearch.WordTrace]
  refine ⟨63767508506533847362782809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170046689350756926300754157 63767508506533847362782809)
  ·
    refine ⟨47825631379900385522087107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63767508506533847362782809 47825631379900385522087107)
    ·
      refine ⟨71738447069850578283130661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47825631379900385522087107 71738447069850578283130661)
      ·
        refine ⟨13450958825596983428086999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71738447069850578283130661 13450958825596983428086999)
        ·
          refine ⟨20176438238395475142130499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13450958825596983428086999 20176438238395475142130499)
          ·
            refine ⟨30264657357593212713195749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20176438238395475142130499 30264657357593212713195749)
            ·
              refine ⟨5674623254548727383724203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30264657357593212713195749 5674623254548727383724203)
              ·
                refine ⟨8511934881823091075586305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5674623254548727383724203 8511934881823091075586305)
                ·
                  refine ⟨6383951161367318306689729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8511934881823091075586305 6383951161367318306689729)
                  ·
                    refine ⟨4787963371025488730017297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6383951161367318306689729 4787963371025488730017297)
                    ·
                      refine ⟨3590972528269116547512973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4787963371025488730017297 3590972528269116547512973)
                      ·
                        rfl

theorem cell23_6993394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_6993394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993394 prefixEnd_6993394 := by exact prefixLift 6993394
  have htrace : WordTrace (prefixWord ++ tailWord_6993394) baseStart_6993394 baseEnd_6993394 := by
    simpa [prefixWord, tailWord_6993394, baseEnd_6993394] using wordTrace_append hprefix tailTrace_6993394
  have hstable : (prefixWord ++ tailWord_6993394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993394).length < 2 ^ (prefixWord ++ tailWord_6993394).sum := by decide
  have hdescent : baseEnd_6993394 < baseStart_6993394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993416 : List Nat := [2, 1, 3, 2, 1, 1, 2, 3, 1, 3, 4]
def baseStart_6993416 : Nat := 118140960795 + 6993416 * 2 ^ 59
def prefixEnd_6993416 : Nat := 4983230072969 + 3 ^ 40 * 6993416 * 2
def baseEnd_6993416 : Nat := 3590983824843515461437871

theorem tailTrace_6993416 : CollatzResearch.WordTrace tailWord_6993416 prefixEnd_6993416 3590983824843515461437871 := by
  unfold tailWord_6993416
  simp only [CollatzResearch.WordTrace]
  refine ⟨127535418216027843604216051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170047224288037124805621401 127535418216027843604216051)
  ·
    refine ⟨191303127324041765406324077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127535418216027843604216051 191303127324041765406324077)
    ·
      refine ⟨71738672746515662027371529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191303127324041765406324077 71738672746515662027371529)
      ·
        refine ⟨53804004559886746520528647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71738672746515662027371529 53804004559886746520528647)
        ·
          refine ⟨80706006839830119780792971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53804004559886746520528647 80706006839830119780792971)
          ·
            refine ⟨121059010259745179671189457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80706006839830119780792971 121059010259745179671189457)
            ·
              refine ⟨90794257694808884753392093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121059010259745179671189457 90794257694808884753392093)
              ·
                refine ⟨34047846635553331782522035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90794257694808884753392093 34047846635553331782522035)
                ·
                  refine ⟨51071769953329997673783053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34047846635553331782522035 51071769953329997673783053)
                  ·
                    refine ⟨19151913732498749127668645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51071769953329997673783053 19151913732498749127668645)
                    ·
                      refine ⟨3590983824843515461437871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19151913732498749127668645 3590983824843515461437871)
                      ·
                        rfl

theorem cell23_6993416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_6993416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993416 prefixEnd_6993416 := by exact prefixLift 6993416
  have htrace : WordTrace (prefixWord ++ tailWord_6993416) baseStart_6993416 baseEnd_6993416 := by
    simpa [prefixWord, tailWord_6993416, baseEnd_6993416] using wordTrace_append hprefix tailTrace_6993416
  have hstable : (prefixWord ++ tailWord_6993416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993416).length < 2 ^ (prefixWord ++ tailWord_6993416).sum := by decide
  have hdescent : baseEnd_6993416 < baseStart_6993416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993436 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 2, 3, 5]
def baseStart_6993436 : Nat := 118140960795 + 6993436 * 2 ^ 59
def prefixEnd_6993436 : Nat := 4983230072969 + 3 ^ 40 * 6993436 * 2
def baseEnd_6993436 : Nat := 3590994094456605383187779

theorem tailTrace_6993436 : CollatzResearch.WordTrace tailWord_6993436 prefixEnd_6993436 3590994094456605383187779 := by
  unfold tailWord_6993436
  simp only [CollatzResearch.WordTrace]
  refine ⟨127535782945991615312080081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170047710594655487082773441 127535782945991615312080081)
  ·
    refine ⟨95651837209493711484060061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127535782945991615312080081 95651837209493711484060061)
    ·
      refine ⟨35869438953560141806522523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95651837209493711484060061 35869438953560141806522523)
      ·
        refine ⟨53804158430340212709783785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35869438953560141806522523 53804158430340212709783785)
        ·
          refine ⟨40353118822755159532337839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53804158430340212709783785 40353118822755159532337839)
          ·
            refine ⟨60529678234132739298506759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40353118822755159532337839 60529678234132739298506759)
            ·
              refine ⟨90794517351199108947760139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60529678234132739298506759 90794517351199108947760139)
              ·
                refine ⟨136191776026798663421640209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90794517351199108947760139 136191776026798663421640209)
                ·
                  refine ⟨102143832020098997566230157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136191776026798663421640209 102143832020098997566230157)
                  ·
                    refine ⟨38303937007537124087336309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102143832020098997566230157 38303937007537124087336309)
                    ·
                      refine ⟨3590994094456605383187779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38303937007537124087336309 3590994094456605383187779)
                      ·
                        rfl

theorem cell23_6993436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_6993436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993436 prefixEnd_6993436 := by exact prefixLift 6993436
  have htrace : WordTrace (prefixWord ++ tailWord_6993436) baseStart_6993436 baseEnd_6993436 := by
    simpa [prefixWord, tailWord_6993436, baseEnd_6993436] using wordTrace_append hprefix tailTrace_6993436
  have hstable : (prefixWord ++ tailWord_6993436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993436).length < 2 ^ (prefixWord ++ tailWord_6993436).sum := by decide
  have hdescent : baseEnd_6993436 < baseStart_6993436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993450 : List Nat := [3, 1, 4, 1, 1, 1, 3, 1, 2, 4, 2]
def baseStart_6993450 : Nat := 118140960795 + 6993450 * 2 ^ 59
def prefixEnd_6993450 : Nat := 4983230072969 + 3 ^ 40 * 6993450 * 2
def baseEnd_6993450 : Nat := 3591001283185768328412715

theorem tailTrace_6993450 : CollatzResearch.WordTrace tailWord_6993450 prefixEnd_6993450 3591001283185768328412715 := by
  unfold tailWord_6993450
  simp only [CollatzResearch.WordTrace]
  refine ⟨63768019128483127753792451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170048051009288340676779869 63768019128483127753792451)
  ·
    refine ⟨95652028692724691630688677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63768019128483127753792451 95652028692724691630688677)
    ·
      refine ⟨17934755379885879680754127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95652028692724691630688677 17934755379885879680754127)
      ·
        refine ⟨26902133069828819521131191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17934755379885879680754127 26902133069828819521131191)
        ·
          refine ⟨40353199604743229281696787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26902133069828819521131191 40353199604743229281696787)
          ·
            refine ⟨60529799407114843922545181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40353199604743229281696787 60529799407114843922545181)
            ·
              refine ⟨22698674777668066470954443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60529799407114843922545181 22698674777668066470954443)
              ·
                refine ⟨34048012166502099706431665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22698674777668066470954443 34048012166502099706431665)
                ·
                  refine ⟨25536009124876574779823749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34048012166502099706431665 25536009124876574779823749)
                  ·
                    refine ⟨4788001710914357771216953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25536009124876574779823749 4788001710914357771216953)
                    ·
                      refine ⟨3591001283185768328412715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4788001710914357771216953 3591001283185768328412715)
                      ·
                        rfl

theorem cell23_6993450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_6993450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993450 prefixEnd_6993450 := by exact prefixLift 6993450
  have htrace : WordTrace (prefixWord ++ tailWord_6993450) baseStart_6993450 baseEnd_6993450 := by
    simpa [prefixWord, tailWord_6993450, baseEnd_6993450] using wordTrace_append hprefix tailTrace_6993450
  have hstable : (prefixWord ++ tailWord_6993450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993450).length < 2 ^ (prefixWord ++ tailWord_6993450).sum := by decide
  have hdescent : baseEnd_6993450 < baseStart_6993450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993483 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 7, 1, 3]
def baseStart_6993483 : Nat := 118140960795 + 6993483 * 2 ^ 59
def prefixEnd_6993483 : Nat := 4983230072969 + 3 ^ 40 * 6993483 * 2
def baseEnd_6993483 : Nat := 3591018228047366699300063

theorem tailTrace_6993483 : CollatzResearch.WordTrace tailWord_6993483 prefixEnd_6993483 3591018228047366699300063 := by
  unfold tailWord_6993483
  simp only [CollatzResearch.WordTrace]
  refine ⟨255073280122812957651121103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170048853415208638434080735 255073280122812957651121103)
  ·
    refine ⟨382609920184219436476681655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255073280122812957651121103 382609920184219436476681655)
    ·
      refine ⟨573914880276329154715022483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382609920184219436476681655 573914880276329154715022483)
      ·
        refine ⟨860872320414493732072533725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573914880276329154715022483 860872320414493732072533725)
        ·
          refine ⟨322827120155435149527200147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 860872320414493732072533725 322827120155435149527200147)
          ·
            refine ⟨484240680233152724290800221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322827120155435149527200147 484240680233152724290800221)
            ·
              refine ⟨181590255087432271609050083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 484240680233152724290800221 181590255087432271609050083)
              ·
                refine ⟨272385382631148407413575125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181590255087432271609050083 272385382631148407413575125)
                ·
                  refine ⟨6384032405417540798755667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 272385382631148407413575125 6384032405417540798755667)
                  ·
                    refine ⟨9576048608126311198133501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6384032405417540798755667 9576048608126311198133501)
                    ·
                      refine ⟨3591018228047366699300063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9576048608126311198133501 3591018228047366699300063)
                      ·
                        rfl

theorem cell23_6993483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 7, 1, 3].length) (baseStart_6993483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993483 prefixEnd_6993483 := by exact prefixLift 6993483
  have htrace : WordTrace (prefixWord ++ tailWord_6993483) baseStart_6993483 baseEnd_6993483 := by
    simpa [prefixWord, tailWord_6993483, baseEnd_6993483] using wordTrace_append hprefix tailTrace_6993483
  have hstable : (prefixWord ++ tailWord_6993483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993483).length < 2 ^ (prefixWord ++ tailWord_6993483).sum := by decide
  have hdescent : baseEnd_6993483 < baseStart_6993483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993490 : List Nat := [3, 2, 2, 1, 2, 4, 1, 2, 6]
def baseStart_6993490 : Nat := 118140960795 + 6993490 * 2 ^ 59
def prefixEnd_6993490 : Nat := 4983230072969 + 3 ^ 40 * 6993490 * 2
def baseEnd_6993490 : Nat := 399002424712438685768059

theorem tailTrace_6993490 : CollatzResearch.WordTrace tailWord_6993490 prefixEnd_6993490 399002424712438685768059 := by
  unfold tailWord_6993490
  simp only [CollatzResearch.WordTrace]
  refine ⟨63768383858446899461656481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170049023622525065231083949 63768383858446899461656481)
  ·
    refine ⟨47826287893835174596242361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63768383858446899461656481 47826287893835174596242361)
    ·
      refine ⟨35869715920376380947181771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47826287893835174596242361 35869715920376380947181771)
      ·
        refine ⟨53804573880564571420772657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35869715920376380947181771 53804573880564571420772657)
        ·
          refine ⟨40353430410423428565579493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53804573880564571420772657 40353430410423428565579493)
          ·
            refine ⟨7566268201954392856046155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40353430410423428565579493 7566268201954392856046155)
            ·
              refine ⟨11349402302931589284069233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7566268201954392856046155 11349402302931589284069233)
              ·
                refine ⟨8512051727198691963051925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11349402302931589284069233 8512051727198691963051925)
                ·
                  refine ⟨399002424712438685768059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8512051727198691963051925 399002424712438685768059)
                  ·
                    rfl

theorem cell23_6993490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 6].length) (baseStart_6993490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993490 prefixEnd_6993490 := by exact prefixLift 6993490
  have htrace : WordTrace (prefixWord ++ tailWord_6993490) baseStart_6993490 baseEnd_6993490 := by
    simpa [prefixWord, tailWord_6993490, baseEnd_6993490] using wordTrace_append hprefix tailTrace_6993490
  have hstable : (prefixWord ++ tailWord_6993490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993490).length < 2 ^ (prefixWord ++ tailWord_6993490).sum := by decide
  have hdescent : baseEnd_6993490 < baseStart_6993490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993520 : List Nat := [2, 1, 1, 1, 6, 2, 2, 2, 1, 5]
def baseStart_6993520 : Nat := 118140960795 + 6993520 * 2 ^ 59
def prefixEnd_6993520 : Nat := 4983230072969 + 3 ^ 40 * 6993520 * 2
def baseEnd_6993520 : Nat := 1197012408943861018179131

theorem tailTrace_6993520 : CollatzResearch.WordTrace tailWord_6993520 prefixEnd_6993520 1197012408943861018179131 := by
  unfold tailWord_6993520
  simp only [CollatzResearch.WordTrace]
  refine ⟨127537314811839456485109007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170049753082452608646812009 127537314811839456485109007)
  ·
    refine ⟨191305972217759184727663511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127537314811839456485109007 191305972217759184727663511)
    ·
      refine ⟨286958958326638777091495267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191305972217759184727663511 286958958326638777091495267)
      ·
        refine ⟨430438437489958165637242901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286958958326638777091495267 430438437489958165637242901)
        ·
          refine ⟨20176801757341789014245761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 430438437489958165637242901 20176801757341789014245761)
          ·
            refine ⟨15132601318006341760684321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20176801757341789014245761 15132601318006341760684321)
            ·
              refine ⟨11349450988504756320513241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15132601318006341760684321 11349450988504756320513241)
              ·
                refine ⟨8512088241378567240384931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11349450988504756320513241 8512088241378567240384931)
                ·
                  refine ⟨12768132362067850860577397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8512088241378567240384931 12768132362067850860577397)
                  ·
                    refine ⟨1197012408943861018179131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12768132362067850860577397 1197012408943861018179131)
                    ·
                      rfl

theorem cell23_6993520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 1, 5].length) (baseStart_6993520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993520 prefixEnd_6993520 := by exact prefixLift 6993520
  have htrace : WordTrace (prefixWord ++ tailWord_6993520) baseStart_6993520 baseEnd_6993520 := by
    simpa [prefixWord, tailWord_6993520, baseEnd_6993520] using wordTrace_append hprefix tailTrace_6993520
  have hstable : (prefixWord ++ tailWord_6993520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993520).length < 2 ^ (prefixWord ++ tailWord_6993520).sum := by decide
  have hdescent : baseEnd_6993520 < baseStart_6993520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993543 : List Nat := [1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 5]
def baseStart_6993543 : Nat := 118140960795 + 6993543 * 2 ^ 59
def prefixEnd_6993543 : Nat := 4983230072969 + 3 ^ 40 * 6993543 * 2
def baseEnd_6993543 : Nat := 3591049036886636464549787

theorem tailTrace_6993543 : CollatzResearch.WordTrace tailWord_6993543 prefixEnd_6993543 3591049036886636464549787 := by
  unfold tailWord_6993543
  simp only [CollatzResearch.WordTrace]
  refine ⟨255075468502595587898305283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170050312335063725265536855 255075468502595587898305283)
  ·
    refine ⟨382613202753893381847457925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255075468502595587898305283 382613202753893381847457925)
    ·
      refine ⟨71739975516355009096398361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 382613202753893381847457925 71739975516355009096398361)
      ·
        refine ⟨53804981637266256822298771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71739975516355009096398361 53804981637266256822298771)
        ·
          refine ⟨80707472455899385233448157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53804981637266256822298771 80707472455899385233448157)
          ·
            refine ⟨30265302170962269462543059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80707472455899385233448157 30265302170962269462543059)
            ·
              refine ⟨45397953256443404193814589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30265302170962269462543059 45397953256443404193814589)
              ·
                refine ⟨17024232471166276572680471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45397953256443404193814589 17024232471166276572680471)
                ·
                  refine ⟨25536348706749414859020707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17024232471166276572680471 25536348706749414859020707)
                  ·
                    refine ⟨38304523060124122288531061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25536348706749414859020707 38304523060124122288531061)
                    ·
                      refine ⟨3591049036886636464549787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38304523060124122288531061 3591049036886636464549787)
                      ·
                        rfl

theorem cell23_6993543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_6993543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993543 prefixEnd_6993543 := by exact prefixLift 6993543
  have htrace : WordTrace (prefixWord ++ tailWord_6993543) baseStart_6993543 baseEnd_6993543 := by
    simpa [prefixWord, tailWord_6993543, baseEnd_6993543] using wordTrace_append hprefix tailTrace_6993543
  have hstable : (prefixWord ++ tailWord_6993543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993543).length < 2 ^ (prefixWord ++ tailWord_6993543).sum := by decide
  have hdescent : baseEnd_6993543 < baseStart_6993543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993544 : List Nat := [2, 1, 3, 5, 1, 1, 1, 2, 2, 3, 2]
def baseStart_6993544 : Nat := 118140960795 + 6993544 * 2 ^ 59
def prefixEnd_6993544 : Nat := 4983230072969 + 3 ^ 40 * 6993544 * 2
def baseEnd_6993544 : Nat := 3591049550367290960637283

theorem tailTrace_6993544 : CollatzResearch.WordTrace tailWord_6993544 prefixEnd_6993544 3591049550367290960637283 := by
  unfold tailWord_6993544
  simp only [CollatzResearch.WordTrace]
  refine ⟨127537752487795982534545843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170050336650394643379394457 127537752487795982534545843)
  ·
    refine ⟨191306628731693973801818765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127537752487795982534545843 191306628731693973801818765)
    ·
      refine ⟨71739985774385240175682037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191306628731693973801818765 71739985774385240175682037)
      ·
        refine ⟨6725623666348616266470191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71739985774385240175682037 6725623666348616266470191)
        ·
          refine ⟨10088435499522924399705287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6725623666348616266470191 10088435499522924399705287)
          ·
            refine ⟨15132653249284386599557931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10088435499522924399705287 15132653249284386599557931)
            ·
              refine ⟨22698979873926579899336897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15132653249284386599557931 22698979873926579899336897)
              ·
                refine ⟨17024234905444934924502673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22698979873926579899336897 17024234905444934924502673)
                ·
                  refine ⟨12768176179083701193377005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17024234905444934924502673 12768176179083701193377005)
                  ·
                    refine ⟨4788066067156387947516377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12768176179083701193377005 4788066067156387947516377)
                    ·
                      refine ⟨3591049550367290960637283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4788066067156387947516377 3591049550367290960637283)
                      ·
                        rfl

theorem cell23_6993544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_6993544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993544 prefixEnd_6993544 := by exact prefixLift 6993544
  have htrace : WordTrace (prefixWord ++ tailWord_6993544) baseStart_6993544 baseEnd_6993544 := by
    simpa [prefixWord, tailWord_6993544, baseEnd_6993544] using wordTrace_append hprefix tailTrace_6993544
  have hstable : (prefixWord ++ tailWord_6993544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993544).length < 2 ^ (prefixWord ++ tailWord_6993544).sum := by decide
  have hdescent : baseEnd_6993544 < baseStart_6993544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993550 : List Nat := [4, 1, 1, 3, 1, 2, 2, 1, 4, 4]
def baseStart_6993550 : Nat := 118140960795 + 6993550 * 2 ^ 59
def prefixEnd_6993550 : Nat := 4983230072969 + 3 ^ 40 * 6993550 * 2
def baseEnd_6993550 : Nat := 1197017543750405979054085

theorem tailTrace_6993550 : CollatzResearch.WordTrace tailWord_6993550 prefixEnd_6993550 1197017543750405979054085 := by
  unfold tailWord_6993550
  simp only [CollatzResearch.WordTrace]
  refine ⟨31884465476696278511726263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170050482542380152062540069 31884465476696278511726263)
  ·
    refine ⟨47826698215044417767589395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31884465476696278511726263 47826698215044417767589395)
    ·
      refine ⟨71740047322566626651384093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47826698215044417767589395 71740047322566626651384093)
      ·
        refine ⟨26902517745962484994269035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71740047322566626651384093 26902517745962484994269035)
        ·
          refine ⟨40353776618943727491403553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26902517745962484994269035 40353776618943727491403553)
          ·
            refine ⟨30265332464207795618552665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40353776618943727491403553 30265332464207795618552665)
            ·
              refine ⟨22698999348155846713914499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30265332464207795618552665 22698999348155846713914499)
              ·
                refine ⟨34048499022233770070871749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22698999348155846713914499 34048499022233770070871749)
                ·
                  refine ⟨6384093566668831888288453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34048499022233770070871749 6384093566668831888288453)
                  ·
                    refine ⟨1197017543750405979054085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6384093566668831888288453 1197017543750405979054085)
                    ·
                      rfl

theorem cell23_6993550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_6993550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993550 prefixEnd_6993550 := by exact prefixLift 6993550
  have htrace : WordTrace (prefixWord ++ tailWord_6993550) baseStart_6993550 baseEnd_6993550 := by
    simpa [prefixWord, tailWord_6993550, baseEnd_6993550] using wordTrace_append hprefix tailTrace_6993550
  have hstable : (prefixWord ++ tailWord_6993550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993550).length < 2 ^ (prefixWord ++ tailWord_6993550).sum := by decide
  have hdescent : baseEnd_6993550 < baseStart_6993550 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993602 : List Nat := [3, 5, 1, 2, 1, 2, 2, 2, 1, 1, 3]
def baseStart_6993602 : Nat := 118140960795 + 6993602 * 2 ^ 59
def prefixEnd_6993602 : Nat := 4983230072969 + 3 ^ 40 * 6993602 * 2
def baseEnd_6993602 : Nat := 3591079332245251733712017

theorem tailTrace_6993602 : CollatzResearch.WordTrace tailWord_6993602 prefixEnd_6993602 3591079332245251733712017 := by
  unfold tailWord_6993602
  simp only [CollatzResearch.WordTrace]
  refine ⟨63769405102345460243675765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170051746939587893983135373 63769405102345460243675765)
  ·
    refine ⟨5978381728344886897844603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63769405102345460243675765 5978381728344886897844603)
    ·
      refine ⟨8967572592517330346766905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5978381728344886897844603 8967572592517330346766905)
      ·
        refine ⟨6725679444387997760075179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8967572592517330346766905 6725679444387997760075179)
        ·
          refine ⟨10088519166581996640112769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6725679444387997760075179 10088519166581996640112769)
          ·
            refine ⟨7566389374936497480084577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10088519166581996640112769 7566389374936497480084577)
            ·
              refine ⟨5674792031202373110063433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7566389374936497480084577 5674792031202373110063433)
              ·
                refine ⟨4256094023401779832547575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5674792031202373110063433 4256094023401779832547575)
                ·
                  refine ⟨6384141035102669748821363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4256094023401779832547575 6384141035102669748821363)
                  ·
                    refine ⟨9576211552654004623232045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6384141035102669748821363 9576211552654004623232045)
                    ·
                      refine ⟨3591079332245251733712017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9576211552654004623232045 3591079332245251733712017)
                      ·
                        rfl

theorem cell23_6993602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_6993602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993602 prefixEnd_6993602 := by exact prefixLift 6993602
  have htrace : WordTrace (prefixWord ++ tailWord_6993602) baseStart_6993602 baseEnd_6993602 := by
    simpa [prefixWord, tailWord_6993602, baseEnd_6993602] using wordTrace_append hprefix tailTrace_6993602
  have hstable : (prefixWord ++ tailWord_6993602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993602).length < 2 ^ (prefixWord ++ tailWord_6993602).sum := by decide
  have hdescent : baseEnd_6993602 < baseStart_6993602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993607 : List Nat := [1, 1, 4, 1, 1, 1, 6, 2, 2, 1, 3]
def baseStart_6993607 : Nat := 118140960795 + 6993607 * 2 ^ 59
def prefixEnd_6993607 : Nat := 4983230072969 + 3 ^ 40 * 6993607 * 2
def baseEnd_6993607 : Nat := 3591081899648524214149493

theorem tailTrace_6993607 : CollatzResearch.WordTrace tailWord_6993607 prefixEnd_6993607 3591081899648524214149493 := by
  unfold tailWord_6993607
  simp only [CollatzResearch.WordTrace]
  refine ⟨255077802774363726828635075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170051868516242484552423383 255077802774363726828635075)
  ·
    refine ⟨382616704161545590242952613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255077802774363726828635075 382616704161545590242952613)
    ·
      refine ⟨71740632030289798170553615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 382616704161545590242952613 71740632030289798170553615)
      ·
        refine ⟨107610948045434697255830423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71740632030289798170553615 107610948045434697255830423)
        ·
          refine ⟨161416422068152045883745635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107610948045434697255830423 161416422068152045883745635)
          ·
            refine ⟨242124633102228068825618453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161416422068152045883745635 242124633102228068825618453)
            ·
              refine ⟨11349592176666940726200865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 242124633102228068825618453 11349592176666940726200865)
              ·
                refine ⟨8512194132500205544650649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11349592176666940726200865 8512194132500205544650649)
                ·
                  refine ⟨6384145599375154158487987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8512194132500205544650649 6384145599375154158487987)
                  ·
                    refine ⟨9576218399062731237731981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6384145599375154158487987 9576218399062731237731981)
                    ·
                      refine ⟨3591081899648524214149493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9576218399062731237731981 3591081899648524214149493)
                      ·
                        rfl

theorem cell23_6993607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_6993607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993607 prefixEnd_6993607 := by exact prefixLift 6993607
  have htrace : WordTrace (prefixWord ++ tailWord_6993607) baseStart_6993607 baseEnd_6993607 := by
    simpa [prefixWord, tailWord_6993607, baseEnd_6993607] using wordTrace_append hprefix tailTrace_6993607
  have hstable : (prefixWord ++ tailWord_6993607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993607).length < 2 ^ (prefixWord ++ tailWord_6993607).sum := by decide
  have hdescent : baseEnd_6993607 < baseStart_6993607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993623 : List Nat := [1, 1, 3, 2, 1, 3, 3, 1, 2, 6]
def baseStart_6993623 : Nat := 118140960795 + 6993623 * 2 ^ 59
def prefixEnd_6993623 : Nat := 4983230072969 + 3 ^ 40 * 6993623 * 2
def baseEnd_6993623 : Nat := 1197030038446332050516473

theorem tailTrace_6993623 : CollatzResearch.WordTrace tailWord_6993623 prefixEnd_6993623 1197030038446332050516473 := by
  unfold tailWord_6993623
  simp only [CollatzResearch.WordTrace]
  refine ⟨255078386342305761561217523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170052257561537174374145015 255078386342305761561217523)
  ·
    refine ⟨382617579513458642341826285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255078386342305761561217523 382617579513458642341826285)
    ·
      refine ⟨143481592317546990878184857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 382617579513458642341826285 143481592317546990878184857)
      ·
        refine ⟨107611194238160243158638643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143481592317546990878184857 107611194238160243158638643)
        ·
          refine ⟨161416791357240364737957965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107611194238160243158638643 161416791357240364737957965)
          ·
            refine ⟨60531296758965136776734237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161416791357240364737957965 60531296758965136776734237)
            ·
              refine ⟨22699236284611926291275339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60531296758965136776734237 22699236284611926291275339)
              ·
                refine ⟨34048854426917889436913009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22699236284611926291275339 34048854426917889436913009)
                ·
                  refine ⟨25536640820188417077684757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34048854426917889436913009 25536640820188417077684757)
                  ·
                    refine ⟨1197030038446332050516473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25536640820188417077684757 1197030038446332050516473)
                    ·
                      rfl

theorem cell23_6993623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 6].length) (baseStart_6993623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993623 prefixEnd_6993623 := by exact prefixLift 6993623
  have htrace : WordTrace (prefixWord ++ tailWord_6993623) baseStart_6993623 baseEnd_6993623 := by
    simpa [prefixWord, tailWord_6993623, baseEnd_6993623] using wordTrace_append hprefix tailTrace_6993623
  have hstable : (prefixWord ++ tailWord_6993623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993623).length < 2 ^ (prefixWord ++ tailWord_6993623).sum := by decide
  have hdescent : baseEnd_6993623 < baseStart_6993623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993647 : List Nat := [1, 1, 2, 1, 5, 1, 2, 2, 4, 2, 2]
def baseStart_6993647 : Nat := 118140960795 + 6993647 * 2 ^ 59
def prefixEnd_6993647 : Nat := 4983230072969 + 3 ^ 40 * 6993647 * 2
def baseEnd_6993647 : Nat := 3591102438874704057649309

theorem tailTrace_6993647 : CollatzResearch.WordTrace tailWord_6993647 prefixEnd_6993647 3591102438874704057649309 := by
  unfold tailWord_6993647
  simp only [CollatzResearch.WordTrace]
  refine ⟨255079261694218813660091195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170052841129479209106727463 255079261694218813660091195)
  ·
    refine ⟨382618892541328220490136793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255079261694218813660091195 382618892541328220490136793)
    ·
      refine ⟨286964169405996165367602595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382618892541328220490136793 286964169405996165367602595)
      ·
        refine ⟨430446254108994248051403893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286964169405996165367602595 430446254108994248051403893)
        ·
          refine ⟨40354336322718210754819115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 430446254108994248051403893 40354336322718210754819115)
          ·
            refine ⟨60531504484077316132228673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40354336322718210754819115 60531504484077316132228673)
            ·
              refine ⟨45398628363057987099171505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60531504484077316132228673 45398628363057987099171505)
              ·
                refine ⟨34048971272293490324378629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45398628363057987099171505 34048971272293490324378629)
                ·
                  refine ⟨6384182113555029435820993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34048971272293490324378629 6384182113555029435820993)
                  ·
                    refine ⟨4788136585166272076865745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6384182113555029435820993 4788136585166272076865745)
                    ·
                      refine ⟨3591102438874704057649309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4788136585166272076865745 3591102438874704057649309)
                      ·
                        rfl

theorem cell23_6993647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 4, 2, 2].length) (baseStart_6993647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993647 prefixEnd_6993647 := by exact prefixLift 6993647
  have htrace : WordTrace (prefixWord ++ tailWord_6993647) baseStart_6993647 baseEnd_6993647 := by
    simpa [prefixWord, tailWord_6993647, baseEnd_6993647] using wordTrace_append hprefix tailTrace_6993647
  have hstable : (prefixWord ++ tailWord_6993647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993647).length < 2 ^ (prefixWord ++ tailWord_6993647).sum := by decide
  have hdescent : baseEnd_6993647 < baseStart_6993647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993683 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 6, 5]
def baseStart_6993683 : Nat := 118140960795 + 6993683 * 2 ^ 59
def prefixEnd_6993683 : Nat := 4983230072969 + 3 ^ 40 * 6993683 * 2
def baseEnd_6993683 : Nat := 1197040308059421972266381

theorem tailTrace_6993683 : CollatzResearch.WordTrace tailWord_6993683 prefixEnd_6993683 1197040308059421972266381 := by
  unfold tailWord_6993683
  simp only [CollatzResearch.WordTrace]
  refine ⟨255080574722088391808401703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170053716481392261205601135 255080574722088391808401703)
  ·
    refine ⟨382620862083132587712602555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255080574722088391808401703 382620862083132587712602555)
    ·
      refine ⟨573931293124698881568903833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382620862083132587712602555 573931293124698881568903833)
      ·
        refine ⟨430448469843524161176677875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 573931293124698881568903833 430448469843524161176677875)
        ·
          refine ⟨645672704765286241765016813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430448469843524161176677875 645672704765286241765016813)
          ·
            refine ⟨242127264286982340661881305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 645672704765286241765016813 242127264286982340661881305)
            ·
              refine ⟨181595448215236755496410979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242127264286982340661881305 181595448215236755496410979)
              ·
                refine ⟨272393172322855133244616469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181595448215236755496410979 272393172322855133244616469)
                ·
                  refine ⟨12768429952633834370841397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 272393172322855133244616469 12768429952633834370841397)
                  ·
                    refine ⟨1197040308059421972266381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12768429952633834370841397 1197040308059421972266381)
                    ·
                      rfl

theorem cell23_6993683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 5].length) (baseStart_6993683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993683 prefixEnd_6993683 := by exact prefixLift 6993683
  have htrace : WordTrace (prefixWord ++ tailWord_6993683) baseStart_6993683 baseEnd_6993683 := by
    simpa [prefixWord, tailWord_6993683, baseEnd_6993683] using wordTrace_append hprefix tailTrace_6993683
  have hstable : (prefixWord ++ tailWord_6993683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993683).length < 2 ^ (prefixWord ++ tailWord_6993683).sum := by decide
  have hdescent : baseEnd_6993683 < baseStart_6993683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993700 : List Nat := [2, 3, 1, 3, 2, 1, 2, 1, 1, 7]
def baseStart_6993700 : Nat := 118140960795 + 6993700 * 2 ^ 59
def prefixEnd_6993700 : Nat := 4983230072969 + 3 ^ 40 * 6993700 * 2
def baseEnd_6993700 : Nat := 1197043217783130783428855

theorem tailTrace_6993700 : CollatzResearch.WordTrace tailWord_6993700 prefixEnd_6993700 1197043217783130783428855 := by
  unfold tailWord_6993700
  simp only [CollatzResearch.WordTrace]
  refine ⟨127540597381513401855885277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170054129842017869141180369 127540597381513401855885277)
  ·
    refine ⟨47827724018067525695956979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127540597381513401855885277 47827724018067525695956979)
    ·
      refine ⟨71741586027101288543935469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47827724018067525695956979 71741586027101288543935469)
      ·
        refine ⟨26903094760162983203975801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71741586027101288543935469 26903094760162983203975801)
        ·
          refine ⟨20177321070122237402981851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26903094760162983203975801 20177321070122237402981851)
          ·
            refine ⟨30265981605183356104472777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20177321070122237402981851 30265981605183356104472777)
            ·
              refine ⟨22699486203887517078354583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30265981605183356104472777 22699486203887517078354583)
              ·
                refine ⟨34049229305831275617531875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22699486203887517078354583 34049229305831275617531875)
                ·
                  refine ⟨51073843958746913426297813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34049229305831275617531875 51073843958746913426297813)
                  ·
                    refine ⟨1197043217783130783428855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51073843958746913426297813 1197043217783130783428855)
                    ·
                      rfl

theorem cell23_6993700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_6993700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993700 prefixEnd_6993700 := by exact prefixLift 6993700
  have htrace : WordTrace (prefixWord ++ tailWord_6993700) baseStart_6993700 baseEnd_6993700 := by
    simpa [prefixWord, tailWord_6993700, baseEnd_6993700] using wordTrace_append hprefix tailTrace_6993700
  have hstable : (prefixWord ++ tailWord_6993700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993700).length < 2 ^ (prefixWord ++ tailWord_6993700).sum := by decide
  have hdescent : baseEnd_6993700 < baseStart_6993700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993704 : List Nat := [2, 1, 5, 1, 1, 4, 1, 3, 5]
def baseStart_6993704 : Nat := 118140960795 + 6993704 * 2 ^ 59
def prefixEnd_6993704 : Nat := 4983230072969 + 3 ^ 40 * 6993704 * 2
def baseEnd_6993704 : Nat := 399014634141334481626283

theorem tailTrace_6993704 : CollatzResearch.WordTrace tailWord_6993704 prefixEnd_6993704 399014634141334481626283 := by
  unfold tailWord_6993704
  simp only [CollatzResearch.WordTrace]
  refine ⟨127540670327506156197458083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170054227103341541596610777 127540670327506156197458083)
  ·
    refine ⟨191311005491259234296187125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127540670327506156197458083 191311005491259234296187125)
    ·
      refine ⟨17935406764805553215267543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 191311005491259234296187125 17935406764805553215267543)
      ·
        refine ⟨26903110147208329822901315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17935406764805553215267543 26903110147208329822901315)
        ·
          refine ⟨40354665220812494734351973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26903110147208329822901315 40354665220812494734351973)
          ·
            refine ⟨7566499728902342762690995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40354665220812494734351973 7566499728902342762690995)
            ·
              refine ⟨11349749593353514144036493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7566499728902342762690995 11349749593353514144036493)
              ·
                refine ⟨4256156097507567804013685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11349749593353514144036493 4256156097507567804013685)
                ·
                  refine ⟨399014634141334481626283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4256156097507567804013685 399014634141334481626283)
                  ·
                    rfl

theorem cell23_6993704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 3, 5].length) (baseStart_6993704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993704 prefixEnd_6993704 := by exact prefixLift 6993704
  have htrace : WordTrace (prefixWord ++ tailWord_6993704) baseStart_6993704 baseEnd_6993704 := by
    simpa [prefixWord, tailWord_6993704, baseEnd_6993704] using wordTrace_append hprefix tailTrace_6993704
  have hstable : (prefixWord ++ tailWord_6993704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993704).length < 2 ^ (prefixWord ++ tailWord_6993704).sum := by decide
  have hdescent : baseEnd_6993704 < baseStart_6993704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993717 : List Nat := [1, 3, 3, 1, 4, 1, 1, 2, 2, 5]
def baseStart_6993717 : Nat := 118140960795 + 6993717 * 2 ^ 59
def prefixEnd_6993717 : Nat := 4983230072969 + 3 ^ 40 * 6993717 * 2
def baseEnd_6993717 : Nat := 1197046127506839594591329

theorem tailTrace_6993717 : CollatzResearch.WordTrace tailWord_6993717 prefixEnd_6993717 1197046127506839594591329 := by
  unfold tailWord_6993717
  simp only [CollatzResearch.WordTrace]
  refine ⟨255081814803965215615139405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170054543202643477076759603 255081814803965215615139405)
  ·
    refine ⟨95655680551486955855677277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255081814803965215615139405 95655680551486955855677277)
    ·
      refine ⟨35870880206807608445878979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95655680551486955855677277 35870880206807608445878979)
      ·
        refine ⟨53806320310211412668818469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35870880206807608445878979 53806320310211412668818469)
        ·
          refine ⟨10088685058164639875403463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53806320310211412668818469 10088685058164639875403463)
          ·
            refine ⟨15133027587246959813105195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10088685058164639875403463 15133027587246959813105195)
            ·
              refine ⟨22699541380870439719657793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15133027587246959813105195 22699541380870439719657793)
              ·
                refine ⟨17024656035652829789743345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22699541380870439719657793 17024656035652829789743345)
                ·
                  refine ⟨12768492026739622342307509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17024656035652829789743345 12768492026739622342307509)
                  ·
                    refine ⟨1197046127506839594591329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12768492026739622342307509 1197046127506839594591329)
                    ·
                      rfl

theorem cell23_6993717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_6993717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993717 prefixEnd_6993717 := by exact prefixLift 6993717
  have htrace : WordTrace (prefixWord ++ tailWord_6993717) baseStart_6993717 baseEnd_6993717 := by
    simpa [prefixWord, tailWord_6993717, baseEnd_6993717] using wordTrace_append hprefix tailTrace_6993717
  have hstable : (prefixWord ++ tailWord_6993717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993717).length < 2 ^ (prefixWord ++ tailWord_6993717).sum := by decide
  have hdescent : baseEnd_6993717 < baseStart_6993717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993720 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 4, 1, 4]
def baseStart_6993720 : Nat := 118140960795 + 6993720 * 2 ^ 59
def prefixEnd_6993720 : Nat := 4983230072969 + 3 ^ 40 * 6993720 * 2
def baseEnd_6993720 : Nat := 3591139922962482272036473

theorem tailTrace_6993720 : CollatzResearch.WordTrace tailWord_6993720 prefixEnd_6993720 3591139922962482272036473 := by
  unfold tailWord_6993720
  simp only [CollatzResearch.WordTrace]
  refine ⟨127540962111477173563749307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170054616148636231418332409 127540962111477173563749307)
  ·
    refine ⟨191311443167215760345623961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127540962111477173563749307 191311443167215760345623961)
    ·
      refine ⟨143483582375411820259217971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191311443167215760345623961 143483582375411820259217971)
      ·
        refine ⟨215225373563117730388826957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143483582375411820259217971 215225373563117730388826957)
        ·
          refine ⟨80709515086169148895810109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215225373563117730388826957 80709515086169148895810109)
          ·
            refine ⟨30266068157313430835928791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80709515086169148895810109 30266068157313430835928791)
            ·
              refine ⟨45399102235970146253893187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30266068157313430835928791 45399102235970146253893187)
              ·
                refine ⟨68098653353955219380839781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45399102235970146253893187 68098653353955219380839781)
                ·
                  refine ⟨12768497503866603633907459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68098653353955219380839781 12768497503866603633907459)
                  ·
                    refine ⟨19152746255799905450861189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12768497503866603633907459 19152746255799905450861189)
                    ·
                      refine ⟨3591139922962482272036473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19152746255799905450861189 3591139922962482272036473)
                      ·
                        rfl

theorem cell23_6993720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_6993720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993720 prefixEnd_6993720 := by exact prefixLift 6993720
  have htrace : WordTrace (prefixWord ++ tailWord_6993720) baseStart_6993720 baseEnd_6993720 := by
    simpa [prefixWord, tailWord_6993720, baseEnd_6993720] using wordTrace_append hprefix tailTrace_6993720
  have hstable : (prefixWord ++ tailWord_6993720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993720).length < 2 ^ (prefixWord ++ tailWord_6993720).sum := by decide
  have hdescent : baseEnd_6993720 < baseStart_6993720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993721 : List Nat := [1, 2, 1, 7, 1, 1, 3, 2, 5]
def baseStart_6993721 : Nat := 118140960795 + 6993721 * 2 ^ 59
def prefixEnd_6993721 : Nat := 4983230072969 + 3 ^ 40 * 6993721 * 2
def baseEnd_6993721 : Nat := 399015604049237418680441

theorem tailTrace_6993721 : CollatzResearch.WordTrace tailWord_6993721 prefixEnd_6993721 399015604049237418680441 := by
  unfold tailWord_6993721
  simp only [CollatzResearch.WordTrace]
  refine ⟨255081960695950724298285017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170054640463967149532190011 255081960695950724298285017)
  ·
    refine ⟨191311470521963043223713763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255081960695950724298285017 191311470521963043223713763)
    ·
      refine ⟨286967205782944564835570645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191311470521963043223713763 286967205782944564835570645)
      ·
        refine ⟨6725793885537763238333687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 286967205782944564835570645 6725793885537763238333687)
        ·
          refine ⟨10088690828306644857500531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6725793885537763238333687 10088690828306644857500531)
          ·
            refine ⟨15133036242459967286250797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10088690828306644857500531 15133036242459967286250797)
            ·
              refine ⟨5674888590922487732344049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15133036242459967286250797 5674888590922487732344049)
              ·
                refine ⟨4256166443191865799258037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5674888590922487732344049 4256166443191865799258037)
                ·
                  refine ⟨399015604049237418680441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4256166443191865799258037 399015604049237418680441)
                  ·
                    rfl

theorem cell23_6993721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 2, 5].length) (baseStart_6993721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993721 prefixEnd_6993721 := by exact prefixLift 6993721
  have htrace : WordTrace (prefixWord ++ tailWord_6993721) baseStart_6993721 baseEnd_6993721 := by
    simpa [prefixWord, tailWord_6993721, baseEnd_6993721] using wordTrace_append hprefix tailTrace_6993721
  have hstable : (prefixWord ++ tailWord_6993721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993721).length < 2 ^ (prefixWord ++ tailWord_6993721).sum := by decide
  have hdescent : baseEnd_6993721 < baseStart_6993721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993774 : List Nat := [4, 1, 2, 3, 1, 1, 2, 2, 2, 2, 3]
def baseStart_6993774 : Nat := 118140960795 + 6993774 * 2 ^ 59
def prefixEnd_6993774 : Nat := 4983230072969 + 3 ^ 40 * 6993774 * 2
def baseEnd_6993774 : Nat := 3591167650917825060761225

theorem tailTrace_6993774 : CollatzResearch.WordTrace tailWord_6993774 prefixEnd_6993774 3591167650917825060761225 := by
  unfold tailWord_6993774
  simp only [CollatzResearch.WordTrace]
  refine ⟨31885486720594839293745547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170055929176505809566642917 31885486720594839293745547)
  ·
    refine ⟨47828230080892258940618321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31885486720594839293745547 47828230080892258940618321)
    ·
      refine ⟨35871172560669194205463741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47828230080892258940618321 35871172560669194205463741)
      ·
        refine ⟨13451689710250947827048903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35871172560669194205463741 13451689710250947827048903)
        ·
          refine ⟨20177534565376421740573355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13451689710250947827048903 20177534565376421740573355)
          ·
            refine ⟨30266301848064632610860033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20177534565376421740573355 30266301848064632610860033)
            ·
              refine ⟨22699726386048474458145025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30266301848064632610860033 22699726386048474458145025)
              ·
                refine ⟨17024794789536355843608769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22699726386048474458145025 17024794789536355843608769)
                ·
                  refine ⟨12768596092152266882706577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17024794789536355843608769 12768596092152266882706577)
                  ·
                    refine ⟨9576447069114200162029933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12768596092152266882706577 9576447069114200162029933)
                    ·
                      refine ⟨3591167650917825060761225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9576447069114200162029933 3591167650917825060761225)
                      ·
                        rfl

theorem cell23_6993774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_6993774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993774 prefixEnd_6993774 := by exact prefixLift 6993774
  have htrace : WordTrace (prefixWord ++ tailWord_6993774) baseStart_6993774 baseEnd_6993774 := by
    simpa [prefixWord, tailWord_6993774, baseEnd_6993774] using wordTrace_append hprefix tailTrace_6993774
  have hstable : (prefixWord ++ tailWord_6993774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993774).length < 2 ^ (prefixWord ++ tailWord_6993774).sum := by decide
  have hdescent : baseEnd_6993774 < baseStart_6993774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993787 : List Nat := [1, 1, 1, 1, 1, 5, 1, 5, 3, 1, 3]
def baseStart_6993787 : Nat := 118140960795 + 6993787 * 2 ^ 59
def prefixEnd_6993787 : Nat := 4983230072969 + 3 ^ 40 * 6993787 * 2
def baseEnd_6993787 : Nat := 3591174326166333509898665

theorem tailTrace_6993787 : CollatzResearch.WordTrace tailWord_6993787 prefixEnd_6993787 3591174326166333509898665 := by
  unfold tailWord_6993787
  simp only [CollatzResearch.WordTrace]
  refine ⟨255084367913711617570187615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170056245275807745046791743 255084367913711617570187615)
  ·
    refine ⟨382626551870567426355281423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255084367913711617570187615 382626551870567426355281423)
    ·
      refine ⟨573939827805851139532922135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382626551870567426355281423 573939827805851139532922135)
      ·
        refine ⟨860909741708776709299383203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573939827805851139532922135 860909741708776709299383203)
        ·
          refine ⟨1291364612563165063949074805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860909741708776709299383203 1291364612563165063949074805)
          ·
            refine ⟨121065432427796724745225763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1291364612563165063949074805 121065432427796724745225763)
            ·
              refine ⟨181598148641695087117838645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121065432427796724745225763 181598148641695087117838645)
              ·
                refine ⟨17024826435158914417297373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181598148641695087117838645 17024826435158914417297373)
                ·
                  refine ⟨6384309913184592906486515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17024826435158914417297373 6384309913184592906486515)
                  ·
                    refine ⟨9576464869776889359729773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6384309913184592906486515 9576464869776889359729773)
                    ·
                      refine ⟨3591174326166333509898665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9576464869776889359729773 3591174326166333509898665)
                      ·
                        rfl

theorem cell23_6993787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 3, 1, 3].length) (baseStart_6993787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993787 prefixEnd_6993787 := by exact prefixLift 6993787
  have htrace : WordTrace (prefixWord ++ tailWord_6993787) baseStart_6993787 baseEnd_6993787 := by
    simpa [prefixWord, tailWord_6993787, baseEnd_6993787] using wordTrace_append hprefix tailTrace_6993787
  have hstable : (prefixWord ++ tailWord_6993787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993787).length < 2 ^ (prefixWord ++ tailWord_6993787).sum := by decide
  have hdescent : baseEnd_6993787 < baseStart_6993787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993797 : List Nat := [1, 3, 1, 1, 3, 2, 2, 2, 1, 5, 2]
def baseStart_6993797 : Nat := 118140960795 + 6993797 * 2 ^ 59
def prefixEnd_6993797 : Nat := 4983230072969 + 3 ^ 40 * 6993797 * 2
def baseEnd_6993797 : Nat := 3591179460972878470773619

theorem tailTrace_6993797 : CollatzResearch.WordTrace tailWord_6993797 prefixEnd_6993797 3591179460972878470773619 := by
  unfold tailWord_6993797
  simp only [CollatzResearch.WordTrace]
  refine ⟨255084732643675389278051645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170056488429116926185367763 255084732643675389278051645)
  ·
    refine ⟨95656774741378270979269367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255084732643675389278051645 95656774741378270979269367)
    ·
      refine ⟨143485162112067406468904051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95656774741378270979269367 143485162112067406468904051)
      ·
        refine ⟨215227743168101109703356077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143485162112067406468904051 215227743168101109703356077)
        ·
          refine ⟨80710403688037916138758529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215227743168101109703356077 80710403688037916138758529)
          ·
            refine ⟨60532802766028437104068897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80710403688037916138758529 60532802766028437104068897)
            ·
              refine ⟨45399602074521327828051673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60532802766028437104068897 45399602074521327828051673)
              ·
                refine ⟨34049701555890995871038755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45399602074521327828051673 34049701555890995871038755)
                ·
                  refine ⟨51074552333836493806558133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34049701555890995871038755 51074552333836493806558133)
                  ·
                    refine ⟨4788239281297171294364825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51074552333836493806558133 4788239281297171294364825)
                    ·
                      refine ⟨3591179460972878470773619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4788239281297171294364825 3591179460972878470773619)
                      ·
                        rfl

theorem cell23_6993797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 5, 2].length) (baseStart_6993797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993797 prefixEnd_6993797 := by exact prefixLift 6993797
  have htrace : WordTrace (prefixWord ++ tailWord_6993797) baseStart_6993797 baseEnd_6993797 := by
    simpa [prefixWord, tailWord_6993797, baseEnd_6993797] using wordTrace_append hprefix tailTrace_6993797
  have hstable : (prefixWord ++ tailWord_6993797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993797).length < 2 ^ (prefixWord ++ tailWord_6993797).sum := by decide
  have hdescent : baseEnd_6993797 < baseStart_6993797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993821 : List Nat := [1, 4, 2, 1, 2, 2, 1, 5, 1, 1, 3]
def baseStart_6993821 : Nat := 118140960795 + 6993821 * 2 ^ 59
def prefixEnd_6993821 : Nat := 4983230072969 + 3 ^ 40 * 6993821 * 2
def baseEnd_6993821 : Nat := 3591191784508586376873509

theorem tailTrace_6993821 : CollatzResearch.WordTrace tailWord_6993821 prefixEnd_6993821 3591191784508586376873509 := by
  unfold tailWord_6993821
  simp only [CollatzResearch.WordTrace]
  refine ⟨255085607995588441376925317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170057071997058960917950211 255085607995588441376925317)
  ·
    refine ⟨47828551499172832758173497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255085607995588441376925317 47828551499172832758173497)
    ·
      refine ⟨35871413624379624568630123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47828551499172832758173497 35871413624379624568630123)
      ·
        refine ⟨53807120436569436852945185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35871413624379624568630123 53807120436569436852945185)
        ·
          refine ⟨40355340327427077639708889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53807120436569436852945185 40355340327427077639708889)
          ·
            refine ⟨30266505245570308229781667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40355340327427077639708889 30266505245570308229781667)
            ·
              refine ⟨45399757868355462344672501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30266505245570308229781667 45399757868355462344672501)
              ·
                refine ⟨4256227300158324594813047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45399757868355462344672501 4256227300158324594813047)
                ·
                  refine ⟨6384340950237486892219571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4256227300158324594813047 6384340950237486892219571)
                  ·
                    refine ⟨9576511425356230338329357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6384340950237486892219571 9576511425356230338329357)
                    ·
                      refine ⟨3591191784508586376873509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9576511425356230338329357 3591191784508586376873509)
                      ·
                        rfl

theorem cell23_6993821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_6993821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993821 prefixEnd_6993821 := by exact prefixLift 6993821
  have htrace : WordTrace (prefixWord ++ tailWord_6993821) baseStart_6993821 baseEnd_6993821 := by
    simpa [prefixWord, tailWord_6993821, baseEnd_6993821] using wordTrace_append hprefix tailTrace_6993821
  have hstable : (prefixWord ++ tailWord_6993821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993821).length < 2 ^ (prefixWord ++ tailWord_6993821).sum := by decide
  have hdescent : baseEnd_6993821 < baseStart_6993821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993854 : List Nat := [4, 2, 1, 1, 1, 5, 1, 1, 1, 6]
def baseStart_6993854 : Nat := 118140960795 + 6993854 * 2 ^ 59
def prefixEnd_6993854 : Nat := 4983230072969 + 3 ^ 40 * 6993854 * 2
def baseEnd_6993854 : Nat := 1197069576456728249253619

theorem tailTrace_6993854 : CollatzResearch.WordTrace tailWord_6993854 prefixEnd_6993854 1197069576456728249253619 := by
  unfold tailWord_6993854
  simp only [CollatzResearch.WordTrace]
  refine ⟨31885851450558611001609577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170057874402979258675251077 31885851450558611001609577)
  ·
    refine ⟨23914388587918958251207183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31885851450558611001609577 23914388587918958251207183)
    ·
      refine ⟨35871582881878437376810775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23914388587918958251207183 35871582881878437376810775)
      ·
        refine ⟨53807374322817656065216163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35871582881878437376810775 53807374322817656065216163)
        ·
          refine ⟨80711061484226484097824245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53807374322817656065216163 80711061484226484097824245)
          ·
            refine ⟨7566662014146232884171023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80711061484226484097824245 7566662014146232884171023)
            ·
              refine ⟨11349993021219349326256535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7566662014146232884171023 11349993021219349326256535)
              ·
                refine ⟨17024989531829023989384803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11349993021219349326256535 17024989531829023989384803)
                ·
                  refine ⟨25537484297743535984077205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17024989531829023989384803 25537484297743535984077205)
                  ·
                    refine ⟨1197069576456728249253619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25537484297743535984077205 1197069576456728249253619)
                    ·
                      rfl

theorem cell23_6993854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_6993854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993854 prefixEnd_6993854 := by exact prefixLift 6993854
  have htrace : WordTrace (prefixWord ++ tailWord_6993854) baseStart_6993854 baseEnd_6993854 := by
    simpa [prefixWord, tailWord_6993854, baseEnd_6993854] using wordTrace_append hprefix tailTrace_6993854
  have hstable : (prefixWord ++ tailWord_6993854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993854).length < 2 ^ (prefixWord ++ tailWord_6993854).sum := by decide
  have hdescent : baseEnd_6993854 < baseStart_6993854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993864 : List Nat := [2, 1, 3, 1, 4, 1, 1, 4, 1, 2, 3]
def baseStart_6993864 : Nat := 118140960795 + 6993864 * 2 ^ 59
def prefixEnd_6993864 : Nat := 4983230072969 + 3 ^ 40 * 6993864 * 2
def baseEnd_6993864 : Nat := 3591213864176729708635811

theorem tailTrace_6993864 : CollatzResearch.WordTrace tailWord_6993864 prefixEnd_6993864 3591213864176729708635811 := by
  unfold tailWord_6993864
  simp only [CollatzResearch.WordTrace]
  refine ⟨127543588167216329860370323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170058117556288439813827097 127543588167216329860370323)
  ·
    refine ⟨191315382250824494790555485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127543588167216329860370323 191315382250824494790555485)
    ·
      refine ⟨71743268344059185546458307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191315382250824494790555485 71743268344059185546458307)
      ·
        refine ⟨107614902516088778319687461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71743268344059185546458307 107614902516088778319687461)
        ·
          refine ⟨20177794221766645934941399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107614902516088778319687461 20177794221766645934941399)
          ·
            refine ⟨30266691332649968902412099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20177794221766645934941399 30266691332649968902412099)
            ·
              refine ⟨45400036998974953353618149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30266691332649968902412099 45400036998974953353618149)
              ·
                refine ⟨8512506937307803753803403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45400036998974953353618149 8512506937307803753803403)
                ·
                  refine ⟨12768760405961705630705105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8512506937307803753803403 12768760405961705630705105)
                  ·
                    refine ⟨9576570304471279223028829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12768760405961705630705105 9576570304471279223028829)
                    ·
                      refine ⟨3591213864176729708635811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9576570304471279223028829 3591213864176729708635811)
                      ·
                        rfl

theorem cell23_6993864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_6993864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993864 prefixEnd_6993864 := by exact prefixLift 6993864
  have htrace : WordTrace (prefixWord ++ tailWord_6993864) baseStart_6993864 baseEnd_6993864 := by
    simpa [prefixWord, tailWord_6993864, baseEnd_6993864] using wordTrace_append hprefix tailTrace_6993864
  have hstable : (prefixWord ++ tailWord_6993864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993864).length < 2 ^ (prefixWord ++ tailWord_6993864).sum := by decide
  have hdescent : baseEnd_6993864 < baseStart_6993864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993895 : List Nat := [1, 1, 5, 2, 4, 1, 1, 1, 3, 2, 2]
def baseStart_6993895 : Nat := 118140960795 + 6993895 * 2 ^ 59
def prefixEnd_6993895 : Nat := 4983230072969 + 3 ^ 40 * 6993895 * 2
def baseEnd_6993895 : Nat := 3591229782077019087348169

theorem tailTrace_6993895 : CollatzResearch.WordTrace tailWord_6993895 prefixEnd_6993895 3591229782077019087348169 := by
  unfold tailWord_6993895
  simp only [CollatzResearch.WordTrace]
  refine ⟨255088306997320352015119139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170058871331546901343412759 255088306997320352015119139)
  ·
    refine ⟨382632460495980528022678709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255088306997320352015119139 382632460495980528022678709)
    ·
      refine ⟨35871793171498174502126129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 382632460495980528022678709 35871793171498174502126129)
      ·
        refine ⟨26903844878623630876594597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35871793171498174502126129 26903844878623630876594597)
        ·
          refine ⟨5044470914741930789361487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26903844878623630876594597 5044470914741930789361487)
          ·
            refine ⟨7566706372112896184042231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5044470914741930789361487 7566706372112896184042231)
            ·
              refine ⟨11350059558169344276063347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7566706372112896184042231 11350059558169344276063347)
              ·
                refine ⟨17025089337254016414095021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11350059558169344276063347 17025089337254016414095021)
                ·
                  refine ⟨6384408501470256155285633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17025089337254016414095021 6384408501470256155285633)
                  ·
                    refine ⟨4788306376102692116464225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6384408501470256155285633 4788306376102692116464225)
                    ·
                      refine ⟨3591229782077019087348169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4788306376102692116464225 3591229782077019087348169)
                      ·
                        rfl

theorem cell23_6993895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_6993895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993895 prefixEnd_6993895 := by exact prefixLift 6993895
  have htrace : WordTrace (prefixWord ++ tailWord_6993895) baseStart_6993895 baseEnd_6993895 := by
    simpa [prefixWord, tailWord_6993895, baseEnd_6993895] using wordTrace_append hprefix tailTrace_6993895
  have hstable : (prefixWord ++ tailWord_6993895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993895).length < 2 ^ (prefixWord ++ tailWord_6993895).sum := by decide
  have hdescent : baseEnd_6993895 < baseStart_6993895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993974 : List Nat := [5, 1, 2, 1, 1, 1, 3, 2, 7]
def baseStart_6993974 : Nat := 118140960795 + 6993974 * 2 ^ 59
def prefixEnd_6993974 : Nat := 4983230072969 + 3 ^ 40 * 6993974 * 2
def baseEnd_6993974 : Nat := 399030038560969364251145

theorem tailTrace_6993974 : CollatzResearch.WordTrace tailWord_6993974 prefixEnd_6993974 399030038560969364251145 := by
  unfold tailWord_6993974
  simp only [CollatzResearch.WordTrace]
  refine ⟨15943199272752134281702811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170060792242689432338163317 15943199272752134281702811)
  ·
    refine ⟨23914798909128201422554217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15943199272752134281702811 23914798909128201422554217)
    ·
      refine ⟨17936099181846151066915663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23914798909128201422554217 17936099181846151066915663)
      ·
        refine ⟨26904148772769226600373495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17936099181846151066915663 26904148772769226600373495)
        ·
          refine ⟨40356223159153839900560243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26904148772769226600373495 40356223159153839900560243)
          ·
            refine ⟨60534334738730759850840365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40356223159153839900560243 60534334738730759850840365)
            ·
              refine ⟨22700375527024034944065137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60534334738730759850840365 22700375527024034944065137)
              ·
                refine ⟨17025281645268026208048853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22700375527024034944065137 17025281645268026208048853)
                ·
                  refine ⟨399030038560969364251145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17025281645268026208048853 399030038560969364251145)
                  ·
                    rfl

theorem cell23_6993974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_6993974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993974 prefixEnd_6993974 := by exact prefixLift 6993974
  have htrace : WordTrace (prefixWord ++ tailWord_6993974) baseStart_6993974 baseEnd_6993974 := by
    simpa [prefixWord, tailWord_6993974, baseEnd_6993974] using wordTrace_append hprefix tailTrace_6993974
  have hstable : (prefixWord ++ tailWord_6993974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993974).length < 2 ^ (prefixWord ++ tailWord_6993974).sum := by decide
  have hdescent : baseEnd_6993974 < baseStart_6993974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6993987 : List Nat := [1, 1, 1, 3, 1, 2, 2, 5, 2, 5]
def baseStart_6993987 : Nat := 118140960795 + 6993987 * 2 ^ 59
def prefixEnd_6993987 : Nat := 4983230072969 + 3 ^ 40 * 6993987 * 2
def baseEnd_6993987 : Nat := 1197092340765744242465915

theorem tailTrace_6993987 : CollatzResearch.WordTrace tailWord_6993987 prefixEnd_6993987 1197092340765744242465915 := by
  unfold tailWord_6993987
  simp only [CollatzResearch.WordTrace]
  refine ⟨255091662512987051727468215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170061108341991367818312143 255091662512987051727468215)
  ·
    refine ⟨382637493769480577591202323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255091662512987051727468215 382637493769480577591202323)
    ·
      refine ⟨573956240654220866386803485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382637493769480577591202323 573956240654220866386803485)
      ·
        refine ⟨215233590245332824895051307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 573956240654220866386803485 215233590245332824895051307)
        ·
          refine ⟨322850385367999237342576961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215233590245332824895051307 322850385367999237342576961)
          ·
            refine ⟨242137789025999428006932721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322850385367999237342576961 242137789025999428006932721)
            ·
              refine ⟨181603341769499571005199541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242137789025999428006932721 181603341769499571005199541)
              ·
                refine ⟨17025313290890584781737457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181603341769499571005199541 17025313290890584781737457)
                ·
                  refine ⟨12768984968167938586303093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17025313290890584781737457 12768984968167938586303093)
                  ·
                    refine ⟨1197092340765744242465915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12768984968167938586303093 1197092340765744242465915)
                    ·
                      rfl

theorem cell23_6993987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 5].length) (baseStart_6993987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6993987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6993987 prefixEnd_6993987 := by exact prefixLift 6993987
  have htrace : WordTrace (prefixWord ++ tailWord_6993987) baseStart_6993987 baseEnd_6993987 := by
    simpa [prefixWord, tailWord_6993987, baseEnd_6993987] using wordTrace_append hprefix tailTrace_6993987
  have hstable : (prefixWord ++ tailWord_6993987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6993987).length < 2 ^ (prefixWord ++ tailWord_6993987).sum := by decide
  have hdescent : baseEnd_6993987 < baseStart_6993987 := by decide
  rcases family_descends (prefixWord ++ tailWord_6993987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994002 : List Nat := [3, 2, 2, 1, 5, 1, 1, 2, 2, 2, 2]
def baseStart_6994002 : Nat := 118140960795 + 6994002 * 2 ^ 59
def prefixEnd_6994002 : Nat := 4983230072969 + 3 ^ 40 * 6994002 * 2
def baseEnd_6994002 : Nat := 3591284724507050168710177

theorem tailTrace_6994002 : CollatzResearch.WordTrace tailWord_6994002 prefixEnd_6994002 3591284724507050168710177 := by
  unfold tailWord_6994002
  simp only [CollatzResearch.WordTrace]
  refine ⟨63773052401983177322316065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170061473071955139526176173 63773052401983177322316065)
  ·
    refine ⟨47829789301487382991737049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63773052401983177322316065 47829789301487382991737049)
    ·
      refine ⟨35872341976115537243802787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47829789301487382991737049 35872341976115537243802787)
      ·
        refine ⟨53808512964173305865704181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35872341976115537243802787 53808512964173305865704181)
        ·
          refine ⟨5044548090391247424909767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53808512964173305865704181 5044548090391247424909767)
          ·
            refine ⟨7566822135586871137364651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5044548090391247424909767 7566822135586871137364651)
            ·
              refine ⟨11350233203380306706046977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7566822135586871137364651 11350233203380306706046977)
              ·
                refine ⟨8512674902535230029535233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11350233203380306706046977 8512674902535230029535233)
                ·
                  refine ⟨6384506176901422522151425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8512674902535230029535233 6384506176901422522151425)
                  ·
                    refine ⟨4788379632676066891613569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6384506176901422522151425 4788379632676066891613569)
                    ·
                      refine ⟨3591284724507050168710177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4788379632676066891613569 3591284724507050168710177)
                      ·
                        rfl

theorem cell23_6994002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_6994002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994002 prefixEnd_6994002 := by exact prefixLift 6994002
  have htrace : WordTrace (prefixWord ++ tailWord_6994002) baseStart_6994002 baseEnd_6994002 := by
    simpa [prefixWord, tailWord_6994002, baseEnd_6994002] using wordTrace_append hprefix tailTrace_6994002
  have hstable : (prefixWord ++ tailWord_6994002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994002).length < 2 ^ (prefixWord ++ tailWord_6994002).sum := by decide
  have hdescent : baseEnd_6994002 < baseStart_6994002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994044 : List Nat := [2, 2, 2, 1, 1, 4, 2, 1, 1, 4, 3]
def baseStart_6994044 : Nat := 118140960795 + 6994044 * 2 ^ 59
def prefixEnd_6994044 : Nat := 4983230072969 + 3 ^ 40 * 6994044 * 2
def baseEnd_6994044 : Nat := 3591306290694539004384983

theorem tailTrace_6994044 : CollatzResearch.WordTrace tailWord_6994044 prefixEnd_6994044 3591306290694539004384983 := by
  unfold tailWord_6994044
  simp only [CollatzResearch.WordTrace]
  refine ⟨127546870736890275231146593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170062494315853700308195457 127546870736890275231146593)
  ·
    refine ⟨95660153052667706423359945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127546870736890275231146593 95660153052667706423359945)
    ·
      refine ⟨71745114789500779817519959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95660153052667706423359945 71745114789500779817519959)
      ·
        refine ⟨107617672184251169726279939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71745114789500779817519959 107617672184251169726279939)
        ·
          refine ⟨161426508276376754589419909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107617672184251169726279939 161426508276376754589419909)
          ·
            refine ⟨30267470301820641485516233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161426508276376754589419909 30267470301820641485516233)
            ·
              refine ⟨22700602726365481114137175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30267470301820641485516233 22700602726365481114137175)
              ·
                refine ⟨34050904089548221671205763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22700602726365481114137175 34050904089548221671205763)
                ·
                  refine ⟨51076356134322332506808645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34050904089548221671205763 51076356134322332506808645)
                  ·
                    refine ⟨9576816775185437345026621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51076356134322332506808645 9576816775185437345026621)
                    ·
                      refine ⟨3591306290694539004384983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9576816775185437345026621 3591306290694539004384983)
                      ·
                        rfl

theorem cell23_6994044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_6994044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994044 prefixEnd_6994044 := by exact prefixLift 6994044
  have htrace : WordTrace (prefixWord ++ tailWord_6994044) baseStart_6994044 baseEnd_6994044 := by
    simpa [prefixWord, tailWord_6994044, baseEnd_6994044] using wordTrace_append hprefix tailTrace_6994044
  have hstable : (prefixWord ++ tailWord_6994044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994044).length < 2 ^ (prefixWord ++ tailWord_6994044).sum := by decide
  have hdescent : baseEnd_6994044 < baseStart_6994044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994070 : List Nat := [5, 3, 2, 1, 2, 1, 2, 1, 2, 2, 2]
def baseStart_6994070 : Nat := 118140960795 + 6994070 * 2 ^ 59
def prefixEnd_6994070 : Nat := 4983230072969 + 3 ^ 40 * 6994070 * 2
def baseEnd_6994070 : Nat := 3591319641191555902659865

theorem tailTrace_6994070 : CollatzResearch.WordTrace tailWord_6994070 prefixEnd_6994070 3591319641191555902659865 := by
  unfold tailWord_6994070
  simp only [CollatzResearch.WordTrace]
  refine ⟨15943418110730397306421229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170063126514457571268493109 15943418110730397306421229)
  ·
    refine ⟨5978781791523898989907961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15943418110730397306421229 5978781791523898989907961)
    ·
      refine ⟨4484086343642924242430971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5978781791523898989907961 4484086343642924242430971)
      ·
        refine ⟨6726129515464386363646457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4484086343642924242430971 6726129515464386363646457)
        ·
          refine ⟨5044597136598289772734843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6726129515464386363646457 5044597136598289772734843)
          ·
            refine ⟨7566895704897434659102265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5044597136598289772734843 7566895704897434659102265)
            ·
              refine ⟨5675171778673075994326699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7566895704897434659102265 5675171778673075994326699)
              ·
                refine ⟨8512757668009613991490049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5675171778673075994326699 8512757668009613991490049)
                ·
                  refine ⟨6384568251007210493617537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8512757668009613991490049 6384568251007210493617537)
                  ·
                    refine ⟨4788426188255407870213153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6384568251007210493617537 4788426188255407870213153)
                    ·
                      refine ⟨3591319641191555902659865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4788426188255407870213153 3591319641191555902659865)
                      ·
                        rfl

theorem cell23_6994070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_6994070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994070 prefixEnd_6994070 := by exact prefixLift 6994070
  have htrace : WordTrace (prefixWord ++ tailWord_6994070) baseStart_6994070 baseEnd_6994070 := by
    simpa [prefixWord, tailWord_6994070, baseEnd_6994070] using wordTrace_append hprefix tailTrace_6994070
  have hstable : (prefixWord ++ tailWord_6994070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994070).length < 2 ^ (prefixWord ++ tailWord_6994070).sum := by decide
  have hdescent : baseEnd_6994070 < baseStart_6994070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994081 : List Nat := [1, 2, 3, 3, 1, 2, 4, 1, 6]
def baseStart_6994081 : Nat := 118140960795 + 6994081 * 2 ^ 59
def prefixEnd_6994081 : Nat := 4983230072969 + 3 ^ 40 * 6994081 * 2
def baseEnd_6994081 : Nat := 399036143275417262180257

theorem tailTrace_6994081 : CollatzResearch.WordTrace tailWord_6994081 prefixEnd_6994081 399036143275417262180257 := by
  unfold tailWord_6994081
  simp only [CollatzResearch.WordTrace]
  refine ⟨255095090974646505781390097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170063393983097670520926731 255095090974646505781390097)
  ·
    refine ⟨191321318230984879336042573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255095090974646505781390097 191321318230984879336042573)
    ·
      refine ⟨71745494336619329751015965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191321318230984879336042573 71745494336619329751015965)
      ·
        refine ⟨26904560376232248656630987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71745494336619329751015965 26904560376232248656630987)
        ·
          refine ⟨40356840564348372984946481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26904560376232248656630987 40356840564348372984946481)
          ·
            refine ⟨30267630423261279738709861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40356840564348372984946481 30267630423261279738709861)
            ·
              refine ⟨5675180704361489951008099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30267630423261279738709861 5675180704361489951008099)
              ·
                refine ⟨8512771056542234926512149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5675180704361489951008099 8512771056542234926512149)
                ·
                  refine ⟨399036143275417262180257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8512771056542234926512149 399036143275417262180257)
                  ·
                    rfl

theorem cell23_6994081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 6].length) (baseStart_6994081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994081 prefixEnd_6994081 := by exact prefixLift 6994081
  have htrace : WordTrace (prefixWord ++ tailWord_6994081) baseStart_6994081 baseEnd_6994081 := by
    simpa [prefixWord, tailWord_6994081, baseEnd_6994081] using wordTrace_append hprefix tailTrace_6994081
  have hstable : (prefixWord ++ tailWord_6994081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994081).length < 2 ^ (prefixWord ++ tailWord_6994081).sum := by decide
  have hdescent : baseEnd_6994081 < baseStart_6994081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994141 : List Nat := [1, 4, 3, 2, 1, 1, 1, 3, 1, 6]
def baseStart_6994141 : Nat := 118140960795 + 6994141 * 2 ^ 59
def prefixEnd_6994141 : Nat := 4983230072969 + 3 ^ 40 * 6994141 * 2
def baseEnd_6994141 : Nat := 1197118699439341708290679

theorem tailTrace_6994141 : CollatzResearch.WordTrace tailWord_6994141 prefixEnd_6994141 1197118699439341708290679 := by
  unfold tailWord_6994141
  simp only [CollatzResearch.WordTrace]
  refine ⟨255097279354429136028574277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170064852902952757352382851 255097279354429136028574277)
  ·
    refine ⟨47830739878955463005357677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255097279354429136028574277 47830739878955463005357677)
    ·
      refine ⟨17936527454608298627009129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47830739878955463005357677 17936527454608298627009129)
      ·
        refine ⟨13452395590956223970256847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17936527454608298627009129 13452395590956223970256847)
        ·
          refine ⟨20178593386434335955385271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13452395590956223970256847 20178593386434335955385271)
          ·
            refine ⟨30267890079651503933077907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20178593386434335955385271 30267890079651503933077907)
            ·
              refine ⟨45401835119477255899616861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30267890079651503933077907 45401835119477255899616861)
              ·
                refine ⟨17025688169803970962356323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45401835119477255899616861 17025688169803970962356323)
                ·
                  refine ⟨25538532254705956443534485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17025688169803970962356323 25538532254705956443534485)
                  ·
                    refine ⟨1197118699439341708290679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25538532254705956443534485 1197118699439341708290679)
                    ·
                      rfl

theorem cell23_6994141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_6994141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994141 prefixEnd_6994141 := by exact prefixLift 6994141
  have htrace : WordTrace (prefixWord ++ tailWord_6994141) baseStart_6994141 baseEnd_6994141 := by
    simpa [prefixWord, tailWord_6994141, baseEnd_6994141] using wordTrace_append hprefix tailTrace_6994141
  have hstable : (prefixWord ++ tailWord_6994141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994141).length < 2 ^ (prefixWord ++ tailWord_6994141).sum := by decide
  have hdescent : baseEnd_6994141 < baseStart_6994141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994191 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 5, 3, 2]
def baseStart_6994191 : Nat := 118140960795 + 6994191 * 2 ^ 59
def prefixEnd_6994191 : Nat := 4983230072969 + 3 ^ 40 * 6994191 * 2
def baseEnd_6994191 : Nat := 3591381772350749929246807

theorem tailTrace_6994191 : CollatzResearch.WordTrace tailWord_6994191 prefixEnd_6994191 3591381772350749929246807 := by
  unfold tailWord_6994191
  simp only [CollatzResearch.WordTrace]
  refine ⟨255099103004247994567894427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170066068669498663045262951 255099103004247994567894427)
  ·
    refine ⟨382648654506371991851841641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255099103004247994567894427 382648654506371991851841641)
    ·
      refine ⟨286986490879778993888881231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382648654506371991851841641 286986490879778993888881231)
      ·
        refine ⟨430479736319668490833321847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286986490879778993888881231 430479736319668490833321847)
        ·
          refine ⟨645719604479502736249982771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430479736319668490833321847 645719604479502736249982771)
          ·
            refine ⟨968579406719254104374974157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645719604479502736249982771 968579406719254104374974157)
            ·
              refine ⟨363217277519720289140615309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 968579406719254104374974157 363217277519720289140615309)
              ·
                refine ⟨136206479069895108427730741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 363217277519720289140615309 136206479069895108427730741)
                ·
                  refine ⟨12769357412802666415099757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136206479069895108427730741 12769357412802666415099757)
                  ·
                    refine ⟨4788509029800999905662409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12769357412802666415099757 4788509029800999905662409)
                    ·
                      refine ⟨3591381772350749929246807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4788509029800999905662409 3591381772350749929246807)
                      ·
                        rfl

theorem cell23_6994191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 3, 2].length) (baseStart_6994191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994191 prefixEnd_6994191 := by exact prefixLift 6994191
  have htrace : WordTrace (prefixWord ++ tailWord_6994191) baseStart_6994191 baseEnd_6994191 := by
    simpa [prefixWord, tailWord_6994191, baseEnd_6994191] using wordTrace_append hprefix tailTrace_6994191
  have hstable : (prefixWord ++ tailWord_6994191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994191).length < 2 ^ (prefixWord ++ tailWord_6994191).sum := by decide
  have hdescent : baseEnd_6994191 < baseStart_6994191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994205 : List Nat := [1, 4, 2, 3, 3, 1, 2, 7]
def baseStart_6994205 : Nat := 118140960795 + 6994205 * 2 ^ 59
def prefixEnd_6994205 : Nat := 4983230072969 + 3 ^ 40 * 6994205 * 2
def baseEnd_6994205 : Nat := 133014405965922699054509

theorem tailTrace_6994205 : CollatzResearch.WordTrace tailWord_6994205 prefixEnd_6994205 133014405965922699054509 := by
  unfold tailWord_6994205
  simp only [CollatzResearch.WordTrace]
  refine ⟨255099613626197274958904069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170066409084131516639269379 255099613626197274958904069)
  ·
    refine ⟨47831177554911989054794513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255099613626197274958904069 47831177554911989054794513)
    ·
      refine ⟨35873383166183991791095885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47831177554911989054794513 35873383166183991791095885)
      ·
        refine ⟨13452518687318996921660957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35873383166183991791095885 13452518687318996921660957)
        ·
          refine ⟨5044694507744623845622859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13452518687318996921660957 5044694507744623845622859)
          ·
            refine ⟨7567041761616935768434289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5044694507744623845622859 7567041761616935768434289)
            ·
              refine ⟨5675281321212701826325717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7567041761616935768434289 5675281321212701826325717)
              ·
                refine ⟨133014405965922699054509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5675281321212701826325717 133014405965922699054509)
                ·
                  rfl

theorem cell23_6994205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 7].length) (baseStart_6994205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994205 prefixEnd_6994205 := by exact prefixLift 6994205
  have htrace : WordTrace (prefixWord ++ tailWord_6994205) baseStart_6994205 baseEnd_6994205 := by
    simpa [prefixWord, tailWord_6994205, baseEnd_6994205] using wordTrace_append hprefix tailTrace_6994205
  have hstable : (prefixWord ++ tailWord_6994205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994205).length < 2 ^ (prefixWord ++ tailWord_6994205).sum := by decide
  have hdescent : baseEnd_6994205 < baseStart_6994205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994216 : List Nat := [2, 1, 5, 1, 4, 1, 1, 3, 1, 2, 2]
def baseStart_6994216 : Nat := 118140960795 + 6994216 * 2 ^ 59
def prefixEnd_6994216 : Nat := 4983230072969 + 3 ^ 40 * 6994216 * 2
def baseEnd_6994216 : Nat := 3591394609367112331434193

theorem tailTrace_6994216 : CollatzResearch.WordTrace tailWord_6994216 prefixEnd_6994216 3591394609367112331434193 := by
  unfold tailWord_6994216
  simp only [CollatzResearch.WordTrace]
  refine ⟨127550007414578711918777251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170066676552771615891703001 127550007414578711918777251)
  ·
    refine ⟨191325011121868067878165877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127550007414578711918777251 191325011121868067878165877)
    ·
      refine ⟨17936719792675131363578051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 191325011121868067878165877 17936719792675131363578051)
      ·
        refine ⟨26905079689012697045367077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17936719792675131363578051 26905079689012697045367077)
        ·
          refine ⟨5044702441689880696006327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26905079689012697045367077 5044702441689880696006327)
          ·
            refine ⟨7567053662534821044009491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5044702441689880696006327 7567053662534821044009491)
            ·
              refine ⟨11350580493802231566014237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7567053662534821044009491 11350580493802231566014237)
              ·
                refine ⟨4256467685175836837255339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11350580493802231566014237 4256467685175836837255339)
                ·
                  refine ⟨6384701527763755255883009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4256467685175836837255339 6384701527763755255883009)
                  ·
                    refine ⟨4788526145822816441912257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6384701527763755255883009 4788526145822816441912257)
                    ·
                      refine ⟨3591394609367112331434193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4788526145822816441912257 3591394609367112331434193)
                      ·
                        rfl

theorem cell23_6994216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_6994216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994216 prefixEnd_6994216 := by exact prefixLift 6994216
  have htrace : WordTrace (prefixWord ++ tailWord_6994216) baseStart_6994216 baseEnd_6994216 := by
    simpa [prefixWord, tailWord_6994216, baseEnd_6994216] using wordTrace_append hprefix tailTrace_6994216
  have hstable : (prefixWord ++ tailWord_6994216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994216).length < 2 ^ (prefixWord ++ tailWord_6994216).sum := by decide
  have hdescent : baseEnd_6994216 < baseStart_6994216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994301 : List Nat := [1, 4, 1, 1, 2, 3, 2, 1, 1, 2, 5]
def baseStart_6994301 : Nat := 118140960795 + 6994301 * 2 ^ 59
def prefixEnd_6994301 : Nat := 4983230072969 + 3 ^ 40 * 6994301 * 2
def baseEnd_6994301 : Nat := 3591438255222744498871301

theorem tailTrace_6994301 : CollatzResearch.WordTrace tailWord_6994301 prefixEnd_6994301 3591438255222744498871301 := by
  unfold tailWord_6994301
  simp only [CollatzResearch.WordTrace]
  refine ⟨255103115033849483354398757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170068743355899655569599171 255103115033849483354398757)
  ·
    refine ⟨47831834068846778128949767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255103115033849483354398757 47831834068846778128949767)
    ·
      refine ⟨71747751103270167193424651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47831834068846778128949767 71747751103270167193424651)
      ·
        refine ⟨107621626654905250790136977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71747751103270167193424651 107621626654905250790136977)
        ·
          refine ⟨80716219991178938092602733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107621626654905250790136977 80716219991178938092602733)
          ·
            refine ⟨30268582496692101784726025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80716219991178938092602733 30268582496692101784726025)
            ·
              refine ⟨22701436872519076338544519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30268582496692101784726025 22701436872519076338544519)
              ·
                refine ⟨34052155308778614507816779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22701436872519076338544519 34052155308778614507816779)
                ·
                  refine ⟨51078232963167921761725169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34052155308778614507816779 51078232963167921761725169)
                  ·
                    refine ⟨38308674722375941321293877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51078232963167921761725169 38308674722375941321293877)
                    ·
                      refine ⟨3591438255222744498871301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38308674722375941321293877 3591438255222744498871301)
                      ·
                        rfl

theorem cell23_6994301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_6994301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994301 prefixEnd_6994301 := by exact prefixLift 6994301
  have htrace : WordTrace (prefixWord ++ tailWord_6994301) baseStart_6994301 baseEnd_6994301 := by
    simpa [prefixWord, tailWord_6994301, baseEnd_6994301] using wordTrace_append hprefix tailTrace_6994301
  have hstable : (prefixWord ++ tailWord_6994301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994301).length < 2 ^ (prefixWord ++ tailWord_6994301).sum := by decide
  have hdescent : baseEnd_6994301 < baseStart_6994301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994304 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 4, 8]
def baseStart_6994304 : Nat := 118140960795 + 6994304 * 2 ^ 59
def prefixEnd_6994304 : Nat := 4983230072969 + 3 ^ 40 * 6994304 * 2
def baseEnd_6994304 : Nat := 1197146598554902662377929

theorem tailTrace_6994304 : CollatzResearch.WordTrace tailWord_6994304 prefixEnd_6994304 1197146598554902662377929 := by
  unfold tailWord_6994304
  simp only [CollatzResearch.WordTrace]
  refine ⟨127551612226419307433378983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170068816301892409911171977 127551612226419307433378983)
  ·
    refine ⟨191327418339628961150068475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127551612226419307433378983 191327418339628961150068475)
    ·
      refine ⟨286991127509443441725102713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191327418339628961150068475 286991127509443441725102713)
      ·
        refine ⟨215243345632082581293827035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286991127509443441725102713 215243345632082581293827035)
        ·
          refine ⟨322865018448123871940740553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215243345632082581293827035 322865018448123871940740553)
          ·
            refine ⟨242148763836092903955555415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322865018448123871940740553 242148763836092903955555415)
            ·
              refine ⟨363223145754139355933333123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242148763836092903955555415 363223145754139355933333123)
              ·
                refine ⟨544834718631209033899999685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363223145754139355933333123 544834718631209033899999685)
                ·
                  refine ⟨102156509743351693856249941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 544834718631209033899999685 102156509743351693856249941)
                  ·
                    refine ⟨1197146598554902662377929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102156509743351693856249941 1197146598554902662377929)
                    ·
                      rfl

theorem cell23_6994304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 4, 8].length) (baseStart_6994304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994304 prefixEnd_6994304 := by exact prefixLift 6994304
  have htrace : WordTrace (prefixWord ++ tailWord_6994304) baseStart_6994304 baseEnd_6994304 := by
    simpa [prefixWord, tailWord_6994304, baseEnd_6994304] using wordTrace_append hprefix tailTrace_6994304
  have hstable : (prefixWord ++ tailWord_6994304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994304).length < 2 ^ (prefixWord ++ tailWord_6994304).sum := by decide
  have hdescent : baseEnd_6994304 < baseStart_6994304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994311 : List Nat := [1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 4]
def baseStart_6994311 : Nat := 118140960795 + 6994311 * 2 ^ 59
def prefixEnd_6994311 : Nat := 4983230072969 + 3 ^ 40 * 6994311 * 2
def baseEnd_6994311 : Nat := 3591443390029289459746255

theorem tailTrace_6994311 : CollatzResearch.WordTrace tailWord_6994311 prefixEnd_6994311 3591443390029289459746255 := by
  unfold tailWord_6994311
  simp only [CollatzResearch.WordTrace]
  refine ⟨255103479763813255062262787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170068986509208836708175191 255103479763813255062262787)
  ·
    refine ⟨382655219645719882593394181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255103479763813255062262787 382655219645719882593394181)
    ·
      refine ⟨71747853683572477986261409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 382655219645719882593394181 71747853683572477986261409)
      ·
        refine ⟨53810890262679358489696057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71747853683572477986261409 53810890262679358489696057)
        ·
          refine ⟨40358167697009518867272043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53810890262679358489696057 40358167697009518867272043)
          ·
            refine ⟨60537251545514278300908065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40358167697009518867272043 60537251545514278300908065)
            ·
              refine ⟨45402938659135708725681049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60537251545514278300908065 45402938659135708725681049)
              ·
                refine ⟨34052203994351781544260787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45402938659135708725681049 34052203994351781544260787)
                ·
                  refine ⟨51078305991527672316391181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34052203994351781544260787 51078305991527672316391181)
                  ·
                    refine ⟨19154364746822877118646693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51078305991527672316391181 19154364746822877118646693)
                    ·
                      refine ⟨3591443390029289459746255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19154364746822877118646693 3591443390029289459746255)
                      ·
                        rfl

theorem cell23_6994311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_6994311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994311 prefixEnd_6994311 := by exact prefixLift 6994311
  have htrace : WordTrace (prefixWord ++ tailWord_6994311) baseStart_6994311 baseEnd_6994311 := by
    simpa [prefixWord, tailWord_6994311, baseEnd_6994311] using wordTrace_append hprefix tailTrace_6994311
  have hstable : (prefixWord ++ tailWord_6994311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994311).length < 2 ^ (prefixWord ++ tailWord_6994311).sum := by decide
  have hdescent : baseEnd_6994311 < baseStart_6994311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994328 : List Nat := [2, 1, 2, 5, 1, 2, 1, 1, 1, 3, 4]
def baseStart_6994328 : Nat := 118140960795 + 6994328 * 2 ^ 59
def prefixEnd_6994328 : Nat := 4983230072969 + 3 ^ 40 * 6994328 * 2
def baseEnd_6994328 : Nat := 3591452119200415893233677

theorem tailTrace_6994328 : CollatzResearch.WordTrace tailWord_6994328 prefixEnd_6994328 3591452119200415893233677 := by
  unfold tailWord_6994328
  simp only [CollatzResearch.WordTrace]
  refine ⟨127552049902375833482815819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170069399869834444643754425 127552049902375833482815819)
  ·
    refine ⟨191328074853563750224223729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127552049902375833482815819 191328074853563750224223729)
    ·
      refine ⟨143496056140172812668167797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191328074853563750224223729 143496056140172812668167797)
      ·
        refine ⟨13452755263141201187640731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143496056140172812668167797 13452755263141201187640731)
        ·
          refine ⟨20179132894711801781461097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13452755263141201187640731 20179132894711801781461097)
          ·
            refine ⟨15134349671033851336095823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20179132894711801781461097 15134349671033851336095823)
            ·
              refine ⟨22701524506550777004143735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15134349671033851336095823 22701524506550777004143735)
              ·
                refine ⟨34052286759826165506215603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22701524506550777004143735 34052286759826165506215603)
                ·
                  refine ⟨51078430139739248259323405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34052286759826165506215603 51078430139739248259323405)
                  ·
                    refine ⟨19154411302402218097246277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51078430139739248259323405 19154411302402218097246277)
                    ·
                      refine ⟨3591452119200415893233677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19154411302402218097246277 3591452119200415893233677)
                      ·
                        rfl

theorem cell23_6994328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_6994328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994328 prefixEnd_6994328 := by exact prefixLift 6994328
  have htrace : WordTrace (prefixWord ++ tailWord_6994328) baseStart_6994328 baseEnd_6994328 := by
    simpa [prefixWord, tailWord_6994328, baseEnd_6994328] using wordTrace_append hprefix tailTrace_6994328
  have hstable : (prefixWord ++ tailWord_6994328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994328).length < 2 ^ (prefixWord ++ tailWord_6994328).sum := by decide
  have hdescent : baseEnd_6994328 < baseStart_6994328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994338 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 5, 4]
def baseStart_6994338 : Nat := 118140960795 + 6994338 * 2 ^ 59
def prefixEnd_6994338 : Nat := 4983230072969 + 3 ^ 40 * 6994338 * 2
def baseEnd_6994338 : Nat := 1197152418002320284702877

theorem tailTrace_6994338 : CollatzResearch.WordTrace tailWord_6994338 prefixEnd_6994338 1197152418002320284702877 := by
  unfold tailWord_6994338
  simp only [CollatzResearch.WordTrace]
  refine ⟨63776116133678859668373917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170069643023143625782330445 63776116133678859668373917)
  ·
    refine ⟨23916043550129572375640219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63776116133678859668373917 23916043550129572375640219)
    ·
      refine ⟨35874065325194358563460329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23916043550129572375640219 35874065325194358563460329)
      ·
        refine ⟨26905548993895768922595247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35874065325194358563460329 26905548993895768922595247)
        ·
          refine ⟨40358323490843653383892871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26905548993895768922595247 40358323490843653383892871)
          ·
            refine ⟨60537485236265480075839307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40358323490843653383892871 60537485236265480075839307)
            ·
              refine ⟨90806227854398220113758961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60537485236265480075839307 90806227854398220113758961)
              ·
                refine ⟨68104670890798665085319221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90806227854398220113758961 68104670890798665085319221)
                ·
                  refine ⟨6384812896012374851748677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68104670890798665085319221 6384812896012374851748677)
                  ·
                    refine ⟨1197152418002320284702877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6384812896012374851748677 1197152418002320284702877)
                    ·
                      rfl

theorem cell23_6994338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_6994338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994338 prefixEnd_6994338 := by exact prefixLift 6994338
  have htrace : WordTrace (prefixWord ++ tailWord_6994338) baseStart_6994338 baseEnd_6994338 := by
    simpa [prefixWord, tailWord_6994338, baseEnd_6994338] using wordTrace_append hprefix tailTrace_6994338
  have hstable : (prefixWord ++ tailWord_6994338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994338).length < 2 ^ (prefixWord ++ tailWord_6994338).sum := by decide
  have hdescent : baseEnd_6994338 < baseStart_6994338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994431 : List Nat := [1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 6]
def baseStart_6994431 : Nat := 118140960795 + 6994431 * 2 ^ 59
def prefixEnd_6994431 : Nat := 4983230072969 + 3 ^ 40 * 6994431 * 2
def baseEnd_6994431 : Nat := 3591505007707828990245703

theorem tailTrace_6994431 : CollatzResearch.WordTrace tailWord_6994431 prefixEnd_6994431 3591505007707828990245703 := by
  unfold tailWord_6994431
  simp only [CollatzResearch.WordTrace]
  refine ⟨255107856523378515556631147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170071904348919010371087431 255107856523378515556631147)
  ·
    refine ⟨382661784785067773334946721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255107856523378515556631147 382661784785067773334946721)
    ·
      refine ⟨286996338588800830001210041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382661784785067773334946721 286996338588800830001210041)
      ·
        refine ⟨215247253941600622500907531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286996338588800830001210041 215247253941600622500907531)
        ·
          refine ⟨322870880912400933751361297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215247253941600622500907531 322870880912400933751361297)
          ·
            refine ⟨242153160684300700313520973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322870880912400933751361297 242153160684300700313520973)
            ·
              refine ⟨90807435256612762617570365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242153160684300700313520973 90807435256612762617570365)
              ·
                refine ⟨34052788221229785981588887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90807435256612762617570365 34052788221229785981588887)
                ·
                  refine ⟨51079182331844678972383331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34052788221229785981588887 51079182331844678972383331)
                  ·
                    refine ⟨76618773497767018458574997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51079182331844678972383331 76618773497767018458574997)
                    ·
                      refine ⟨3591505007707828990245703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76618773497767018458574997 3591505007707828990245703)
                      ·
                        rfl

theorem cell23_6994431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_6994431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994431 prefixEnd_6994431 := by exact prefixLift 6994431
  have htrace : WordTrace (prefixWord ++ tailWord_6994431) baseStart_6994431 baseEnd_6994431 := by
    simpa [prefixWord, tailWord_6994431, baseEnd_6994431] using wordTrace_append hprefix tailTrace_6994431
  have hstable : (prefixWord ++ tailWord_6994431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994431).length < 2 ^ (prefixWord ++ tailWord_6994431).sum := by decide
  have hdescent : baseEnd_6994431 < baseStart_6994431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994435 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 5, 2, 2]
def baseStart_6994435 : Nat := 118140960795 + 6994435 * 2 ^ 59
def prefixEnd_6994435 : Nat := 4983230072969 + 3 ^ 40 * 6994435 * 2
def baseEnd_6994435 : Nat := 3591507061630446974595685

theorem tailTrace_6994435 : CollatzResearch.WordTrace tailWord_6994435 prefixEnd_6994435 3591507061630446974595685 := by
  unfold tailWord_6994435
  simp only [CollatzResearch.WordTrace]
  refine ⟨255108002415364024239776759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170072001610242682826517839 255108002415364024239776759)
  ·
    refine ⟨382662003623046036359665139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255108002415364024239776759 382662003623046036359665139)
    ·
      refine ⟨573993005434569054539497709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382662003623046036359665139 573993005434569054539497709)
      ·
        refine ⟨215247377037963395452311641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 573993005434569054539497709 215247377037963395452311641)
        ·
          refine ⟨161435532778472546589233731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215247377037963395452311641 161435532778472546589233731)
          ·
            refine ⟨242153299167708819883850597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161435532778472546589233731 242153299167708819883850597)
            ·
              refine ⟨45403743593945403728221987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 242153299167708819883850597 45403743593945403728221987)
              ·
                refine ⟨68105615390918105592332981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45403743593945403728221987 68105615390918105592332981)
                ·
                  refine ⟨6384901442898572399281217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68105615390918105592332981 6384901442898572399281217)
                  ·
                    refine ⟨4788676082173929299460913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6384901442898572399281217 4788676082173929299460913)
                    ·
                      refine ⟨3591507061630446974595685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4788676082173929299460913 3591507061630446974595685)
                      ·
                        rfl

theorem cell23_6994435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 5, 2, 2].length) (baseStart_6994435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994435 prefixEnd_6994435 := by exact prefixLift 6994435
  have htrace : WordTrace (prefixWord ++ tailWord_6994435) baseStart_6994435 baseEnd_6994435 := by
    simpa [prefixWord, tailWord_6994435, baseEnd_6994435] using wordTrace_append hprefix tailTrace_6994435
  have hstable : (prefixWord ++ tailWord_6994435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994435).length < 2 ^ (prefixWord ++ tailWord_6994435).sum := by decide
  have hdescent : baseEnd_6994435 < baseStart_6994435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994485 : List Nat := [1, 3, 3, 1, 1, 2, 4, 1, 1, 3, 3]
def baseStart_6994485 : Nat := 118140960795 + 6994485 * 2 ^ 59
def prefixEnd_6994485 : Nat := 4983230072969 + 3 ^ 40 * 6994485 * 2
def baseEnd_6994485 : Nat := 3591532735663171778970455

theorem tailTrace_6994485 : CollatzResearch.WordTrace tailWord_6994485 prefixEnd_6994485 3591532735663171778970455 := by
  unfold tailWord_6994485
  simp only [CollatzResearch.WordTrace]
  refine ⟨255109826065182882779096909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170073217376788588519397939 255109826065182882779096909)
  ·
    refine ⟨95666184774443581042161341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255109826065182882779096909 95666184774443581042161341)
    ·
      refine ⟨35874819290416342890810503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95666184774443581042161341 35874819290416342890810503)
      ·
        refine ⟨53812228935624514336215755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35874819290416342890810503 53812228935624514336215755)
        ·
          refine ⟨80718343403436771504323633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53812228935624514336215755 80718343403436771504323633)
          ·
            refine ⟨60538757552577578628242725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80718343403436771504323633 60538757552577578628242725)
            ·
              refine ⟨11351017041108295992795511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60538757552577578628242725 11351017041108295992795511)
              ·
                refine ⟨17026525561662443989193267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11351017041108295992795511 17026525561662443989193267)
                ·
                  refine ⟨25539788342493665983789901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17026525561662443989193267 25539788342493665983789901)
                  ·
                    refine ⟨9577420628435124743921213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25539788342493665983789901 9577420628435124743921213)
                    ·
                      refine ⟨3591532735663171778970455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9577420628435124743921213 3591532735663171778970455)
                      ·
                        rfl

theorem cell23_6994485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_6994485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994485 prefixEnd_6994485 := by exact prefixLift 6994485
  have htrace : WordTrace (prefixWord ++ tailWord_6994485) baseStart_6994485 baseEnd_6994485 := by
    simpa [prefixWord, tailWord_6994485, baseEnd_6994485] using wordTrace_append hprefix tailTrace_6994485
  have hstable : (prefixWord ++ tailWord_6994485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994485).length < 2 ^ (prefixWord ++ tailWord_6994485).sum := by decide
  have hdescent : baseEnd_6994485 < baseStart_6994485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994495 : List Nat := [1, 1, 2, 2, 3, 2, 1, 3, 3, 3, 2]
def baseStart_6994495 : Nat := 118140960795 + 6994495 * 2 ^ 59
def prefixEnd_6994495 : Nat := 4983230072969 + 3 ^ 40 * 6994495 * 2
def baseEnd_6994495 : Nat := 3591537870469716739845409

theorem tailTrace_6994495 : CollatzResearch.WordTrace tailWord_6994495 prefixEnd_6994495 3591537870469716739845409 := by
  unfold tailWord_6994495
  simp only [CollatzResearch.WordTrace]
  refine ⟨255110190795146654486960939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170073460530097769657973959 255110190795146654486960939)
  ·
    refine ⟨382665286192719981730441409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255110190795146654486960939 382665286192719981730441409)
    ·
      refine ⟨286998964644539986297831057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382665286192719981730441409 286998964644539986297831057)
      ·
        refine ⟨215249223483404989723373293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286998964644539986297831057 215249223483404989723373293)
        ·
          refine ⟨80718458806276871146264985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215249223483404989723373293 80718458806276871146264985)
          ·
            refine ⟨60538844104707653359698739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80718458806276871146264985 60538844104707653359698739)
            ·
              refine ⟨90808266157061480039548109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60538844104707653359698739 90808266157061480039548109)
              ·
                refine ⟨34053099808898055014830541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90808266157061480039548109 34053099808898055014830541)
                ·
                  refine ⟨12769912428336770630561453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34053099808898055014830541 12769912428336770630561453)
                  ·
                    refine ⟨4788717160626288986460545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12769912428336770630561453 4788717160626288986460545)
                    ·
                      refine ⟨3591537870469716739845409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4788717160626288986460545 3591537870469716739845409)
                      ·
                        rfl

theorem cell23_6994495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 3, 2].length) (baseStart_6994495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994495 prefixEnd_6994495 := by exact prefixLift 6994495
  have htrace : WordTrace (prefixWord ++ tailWord_6994495) baseStart_6994495 baseEnd_6994495 := by
    simpa [prefixWord, tailWord_6994495, baseEnd_6994495] using wordTrace_append hprefix tailTrace_6994495
  have hstable : (prefixWord ++ tailWord_6994495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994495).length < 2 ^ (prefixWord ++ tailWord_6994495).sum := by decide
  have hdescent : baseEnd_6994495 < baseStart_6994495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994528 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 3]
def baseStart_6994528 : Nat := 118140960795 + 6994528 * 2 ^ 59
def prefixEnd_6994528 : Nat := 4983230072969 + 3 ^ 40 * 6994528 * 2
def baseEnd_6994528 : Nat := 3591554815331315110732757

theorem tailTrace_6994528 : CollatzResearch.WordTrace tailWord_6994528 prefixEnd_6994528 3591554815331315110732757 := by
  unfold tailWord_6994528
  simp only [CollatzResearch.WordTrace]
  refine ⟨127555697202013550561456119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170074262936018067415274825 127555697202013550561456119)
  ·
    refine ⟨191333545803020325842184179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127555697202013550561456119 191333545803020325842184179)
    ·
      refine ⟨287000318704530488763276269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191333545803020325842184179 287000318704530488763276269)
      ·
        refine ⟨107625119514198933286228601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287000318704530488763276269 107625119514198933286228601)
        ·
          refine ⟨80718839635649199964671451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107625119514198933286228601 80718839635649199964671451)
          ·
            refine ⟨121078259453473799947007177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80718839635649199964671451 121078259453473799947007177)
            ·
              refine ⟨90808694590105349960255383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121078259453473799947007177 90808694590105349960255383)
              ·
                refine ⟨136213041885158024940383075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90808694590105349960255383 136213041885158024940383075)
                ·
                  refine ⟨204319562827737037410574613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136213041885158024940383075 204319562827737037410574613)
                  ·
                    refine ⟨9577479507550173628620685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 204319562827737037410574613 9577479507550173628620685)
                    ·
                      refine ⟨3591554815331315110732757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9577479507550173628620685 3591554815331315110732757)
                      ·
                        rfl

theorem cell23_6994528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_6994528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994528 prefixEnd_6994528 := by exact prefixLift 6994528
  have htrace : WordTrace (prefixWord ++ tailWord_6994528) baseStart_6994528 baseEnd_6994528 := by
    simpa [prefixWord, tailWord_6994528, baseEnd_6994528] using wordTrace_append hprefix tailTrace_6994528
  have hstable : (prefixWord ++ tailWord_6994528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994528).length < 2 ^ (prefixWord ++ tailWord_6994528).sum := by decide
  have hdescent : baseEnd_6994528 < baseStart_6994528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994536 : List Nat := [2, 1, 4, 3, 2, 1, 3, 1, 2, 1, 3]
def baseStart_6994536 : Nat := 118140960795 + 6994536 * 2 ^ 59
def prefixEnd_6994536 : Nat := 4983230072969 + 3 ^ 40 * 6994536 * 2
def baseEnd_6994536 : Nat := 3591558923176551079432721

theorem tailTrace_6994536 : CollatzResearch.WordTrace tailWord_6994536 prefixEnd_6994536 3591558923176551079432721 := by
  unfold tailWord_6994536
  simp only [CollatzResearch.WordTrace]
  refine ⟨127555843093999059244601731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170074457458665412326135641 127555843093999059244601731)
  ·
    refine ⟨191333764640998588866902597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127555843093999059244601731 191333764640998588866902597)
    ·
      refine ⟨35875080870187235412544237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191333764640998588866902597 35875080870187235412544237)
      ·
        refine ⟨13453155326320213279704089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35875080870187235412544237 13453155326320213279704089)
        ·
          refine ⟨10089866494740159959778067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13453155326320213279704089 10089866494740159959778067)
          ·
            refine ⟨15134799742110239939667101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10089866494740159959778067 15134799742110239939667101)
            ·
              refine ⟨5675549903291339977375163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15134799742110239939667101 5675549903291339977375163)
              ·
                refine ⟨8513324854937009966062745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5675549903291339977375163 8513324854937009966062745)
                ·
                  refine ⟨6384993641202757474547059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8513324854937009966062745 6384993641202757474547059)
                  ·
                    refine ⟨9577490461804136211820589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6384993641202757474547059 9577490461804136211820589)
                    ·
                      refine ⟨3591558923176551079432721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9577490461804136211820589 3591558923176551079432721)
                      ·
                        rfl

theorem cell23_6994536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_6994536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994536 prefixEnd_6994536 := by exact prefixLift 6994536
  have htrace : WordTrace (prefixWord ++ tailWord_6994536) baseStart_6994536 baseEnd_6994536 := by
    simpa [prefixWord, tailWord_6994536, baseEnd_6994536] using wordTrace_append hprefix tailTrace_6994536
  have hstable : (prefixWord ++ tailWord_6994536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994536).length < 2 ^ (prefixWord ++ tailWord_6994536).sum := by decide
  have hdescent : baseEnd_6994536 < baseStart_6994536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994585 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 2, 5, 2]
def baseStart_6994585 : Nat := 118140960795 + 6994585 * 2 ^ 59
def prefixEnd_6994585 : Nat := 4983230072969 + 3 ^ 40 * 6994585 * 2
def baseEnd_6994585 : Nat := 3591584083728621387719995

theorem tailTrace_6994585 : CollatzResearch.WordTrace tailWord_6994585 prefixEnd_6994585 3591584083728621387719995 := by
  unfold tailWord_6994585
  simp only [CollatzResearch.WordTrace]
  refine ⟨255113473364820599857737209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170075648909880399905158139 255113473364820599857737209)
  ·
    refine ⟨191335105023615449893302907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255113473364820599857737209 191335105023615449893302907)
    ·
      refine ⟨287002657535423174839954361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191335105023615449893302907 287002657535423174839954361)
      ·
        refine ⟨215251993151567381129965771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287002657535423174839954361 215251993151567381129965771)
        ·
          refine ⟨322877989727351071694948657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215251993151567381129965771 322877989727351071694948657)
          ·
            refine ⟨242158492295513303771211493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322877989727351071694948657 242158492295513303771211493)
            ·
              refine ⟨45404717305408744457102155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 242158492295513303771211493 45404717305408744457102155)
              ·
                refine ⟨68107075958113116685653233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45404717305408744457102155 68107075958113116685653233)
                ·
                  refine ⟨51080306968584837514239925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68107075958113116685653233 51080306968584837514239925)
                  ·
                    refine ⟨4788778778304828516959993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51080306968584837514239925 4788778778304828516959993)
                    ·
                      refine ⟨3591584083728621387719995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4788778778304828516959993 3591584083728621387719995)
                      ·
                        rfl

theorem cell23_6994585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 5, 2].length) (baseStart_6994585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994585 prefixEnd_6994585 := by exact prefixLift 6994585
  have htrace : WordTrace (prefixWord ++ tailWord_6994585) baseStart_6994585 baseEnd_6994585 := by
    simpa [prefixWord, tailWord_6994585, baseEnd_6994585] using wordTrace_append hprefix tailTrace_6994585
  have hstable : (prefixWord ++ tailWord_6994585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994585).length < 2 ^ (prefixWord ++ tailWord_6994585).sum := by decide
  have hdescent : baseEnd_6994585 < baseStart_6994585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994593 : List Nat := [1, 2, 3, 3, 3, 2, 2, 1, 2, 2, 2]
def baseStart_6994593 : Nat := 118140960795 + 6994593 * 2 ^ 59
def prefixEnd_6994593 : Nat := 4983230072969 + 3 ^ 40 * 6994593 * 2
def baseEnd_6994593 : Nat := 3591588191573857356419959

theorem tailTrace_6994593 : CollatzResearch.WordTrace tailWord_6994593 prefixEnd_6994593 3591588191573857356419959 := by
  unfold tailWord_6994593
  simp only [CollatzResearch.WordTrace]
  refine ⟨255113765148791617224028433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170075843432527744816018955 255113765148791617224028433)
  ·
    refine ⟨191335323861593712918021325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255113765148791617224028433 191335323861593712918021325)
    ·
      refine ⟨71750746448097642344257997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191335323861593712918021325 71750746448097642344257997)
      ·
        refine ⟨26906529918036615879096749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71750746448097642344257997 26906529918036615879096749)
        ·
          refine ⟨10089948719263730954661281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26906529918036615879096749 10089948719263730954661281)
          ·
            refine ⟨7567461539447798215995961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10089948719263730954661281 7567461539447798215995961)
            ·
              refine ⟨5675596154585848661996971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7567461539447798215995961 5675596154585848661996971)
              ·
                refine ⟨8513394231878772992995457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5675596154585848661996971 8513394231878772992995457)
                ·
                  refine ⟨6385045673909079744746593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8513394231878772992995457 6385045673909079744746593)
                  ·
                    refine ⟨4788784255431809808559945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6385045673909079744746593 4788784255431809808559945)
                    ·
                      refine ⟨3591588191573857356419959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4788784255431809808559945 3591588191573857356419959)
                      ·
                        rfl

theorem cell23_6994593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_6994593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994593 prefixEnd_6994593 := by exact prefixLift 6994593
  have htrace : WordTrace (prefixWord ++ tailWord_6994593) baseStart_6994593 baseEnd_6994593 := by
    simpa [prefixWord, tailWord_6994593, baseEnd_6994593] using wordTrace_append hprefix tailTrace_6994593
  have hstable : (prefixWord ++ tailWord_6994593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994593).length < 2 ^ (prefixWord ++ tailWord_6994593).sum := by decide
  have hdescent : baseEnd_6994593 < baseStart_6994593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994655 : List Nat := [1, 1, 2, 3, 2, 3, 2, 3, 6]
def baseStart_6994655 : Nat := 118140960795 + 6994655 * 2 ^ 59
def prefixEnd_6994655 : Nat := 4983230072969 + 3 ^ 40 * 6994655 * 2
def baseEnd_6994655 : Nat := 399068891930492901538297

theorem tailTrace_6994655 : CollatzResearch.WordTrace tailWord_6994655 prefixEnd_6994655 399068891930492901538297 := by
  unfold tailWord_6994655
  simp only [CollatzResearch.WordTrace]
  refine ⟨255116026474567001812785419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170077350983044667875190279 255116026474567001812785419)
  ·
    refine ⟨382674039711850502719178129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255116026474567001812785419 382674039711850502719178129)
    ·
      refine ⟨287005529783887877039383597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382674039711850502719178129 287005529783887877039383597)
      ·
        refine ⟨107627073668957953889768849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287005529783887877039383597 107627073668957953889768849)
        ·
          refine ⟨80720305251718465417326637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107627073668957953889768849 80720305251718465417326637)
          ·
            refine ⟨30270114469394424531497489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80720305251718465417326637 30270114469394424531497489)
            ·
              refine ⟨22702585852045818398623117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30270114469394424531497489 22702585852045818398623117)
              ·
                refine ⟨8513469694517181899483669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22702585852045818398623117 8513469694517181899483669)
                ·
                  refine ⟨399068891930492901538297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8513469694517181899483669 399068891930492901538297)
                  ·
                    rfl

theorem cell23_6994655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 6].length) (baseStart_6994655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994655 prefixEnd_6994655 := by exact prefixLift 6994655
  have htrace : WordTrace (prefixWord ++ tailWord_6994655) baseStart_6994655 baseEnd_6994655 := by
    simpa [prefixWord, tailWord_6994655, baseEnd_6994655] using wordTrace_append hprefix tailTrace_6994655
  have hstable : (prefixWord ++ tailWord_6994655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994655).length < 2 ^ (prefixWord ++ tailWord_6994655).sum := by decide
  have hdescent : baseEnd_6994655 < baseStart_6994655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994705 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 4]
def baseStart_6994705 : Nat := 118140960795 + 6994705 * 2 ^ 59
def prefixEnd_6994705 : Nat := 4983230072969 + 3 ^ 40 * 6994705 * 2
def baseEnd_6994705 : Nat := 3591645701407160918219443

theorem tailTrace_6994705 : CollatzResearch.WordTrace tailWord_6994705 prefixEnd_6994705 3591645701407160918219443 := by
  unfold tailWord_6994705
  simp only [CollatzResearch.WordTrace]
  refine ⟨255117850124385860352105569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170078566749590573568070379 255117850124385860352105569)
  ·
    refine ⟨191338387593289395264079177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255117850124385860352105569 191338387593289395264079177)
    ·
      refine ⟨143503790694967046448059383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191338387593289395264079177 143503790694967046448059383)
      ·
        refine ⟨215255686042450569672089075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143503790694967046448059383 215255686042450569672089075)
        ·
          refine ⟨322883529063675854508133613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215255686042450569672089075 322883529063675854508133613)
          ·
            refine ⟨121081323398878445440550105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 322883529063675854508133613 121081323398878445440550105)
            ·
              refine ⟨90810992549158834080412579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121081323398878445440550105 90810992549158834080412579)
              ·
                refine ⟨136216488823738251120618869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90810992549158834080412579 136216488823738251120618869)
                ·
                  refine ⟨12770295827225461042558019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136216488823738251120618869 12770295827225461042558019)
                  ·
                    refine ⟨19155443740838191563837029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12770295827225461042558019 19155443740838191563837029)
                    ·
                      refine ⟨3591645701407160918219443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19155443740838191563837029 3591645701407160918219443)
                      ·
                        rfl

theorem cell23_6994705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_6994705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994705 prefixEnd_6994705 := by exact prefixLift 6994705
  have htrace : WordTrace (prefixWord ++ tailWord_6994705) baseStart_6994705 baseEnd_6994705 := by
    simpa [prefixWord, tailWord_6994705, baseEnd_6994705] using wordTrace_append hprefix tailTrace_6994705
  have hstable : (prefixWord ++ tailWord_6994705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994705).length < 2 ^ (prefixWord ++ tailWord_6994705).sum := by decide
  have hdescent : baseEnd_6994705 < baseStart_6994705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994706 : List Nat := [3, 2, 4, 1, 2, 1, 3, 1, 6]
def baseStart_6994706 : Nat := 118140960795 + 6994706 * 2 ^ 59
def prefixEnd_6994706 : Nat := 4983230072969 + 3 ^ 40 * 6994706 * 2
def baseEnd_6994706 : Nat := 399071801654201712700771

theorem tailTrace_6994706 : CollatzResearch.WordTrace tailWord_6994706 prefixEnd_6994706 399071801654201712700771 := by
  unfold tailWord_6994706
  simp only [CollatzResearch.WordTrace]
  refine ⟨63779471649345559380722993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170078591064921491681927981 63779471649345559380722993)
  ·
    refine ⟨47834603737009169535542245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63779471649345559380722993 47834603737009169535542245)
    ·
      refine ⟨8968988200689219287914171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47834603737009169535542245 8968988200689219287914171)
      ·
        refine ⟨13453482301033828931871257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8968988200689219287914171 13453482301033828931871257)
        ·
          refine ⟨10090111725775371698903443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13453482301033828931871257 10090111725775371698903443)
          ·
            refine ⟨15135167588663057548355165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10090111725775371698903443 15135167588663057548355165)
            ·
              refine ⟨5675687845748646580633187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15135167588663057548355165 5675687845748646580633187)
              ·
                refine ⟨8513531768622969870949781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5675687845748646580633187 8513531768622969870949781)
                ·
                  refine ⟨399071801654201712700771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8513531768622969870949781 399071801654201712700771)
                  ·
                    rfl

theorem cell23_6994706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 6].length) (baseStart_6994706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994706 prefixEnd_6994706 := by exact prefixLift 6994706
  have htrace : WordTrace (prefixWord ++ tailWord_6994706) baseStart_6994706 baseEnd_6994706 := by
    simpa [prefixWord, tailWord_6994706, baseEnd_6994706] using wordTrace_append hprefix tailTrace_6994706
  have hstable : (prefixWord ++ tailWord_6994706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994706).length < 2 ^ (prefixWord ++ tailWord_6994706).sum := by decide
  have hdescent : baseEnd_6994706 < baseStart_6994706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994715 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 8, 4]
def baseStart_6994715 : Nat := 118140960795 + 6994715 * 2 ^ 59
def prefixEnd_6994715 : Nat := 4983230072969 + 3 ^ 40 * 6994715 * 2
def baseEnd_6994715 : Nat := 1197216945404568626364799

theorem tailTrace_6994715 : CollatzResearch.WordTrace tailWord_6994715 prefixEnd_6994715 1197216945404568626364799 := by
  unfold tailWord_6994715
  simp only [CollatzResearch.WordTrace]
  refine ⟨255118214854349632059969599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170078809902899754706646399 255118214854349632059969599)
  ·
    refine ⟨382677322281524448089954399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255118214854349632059969599 382677322281524448089954399)
    ·
      refine ⟨574015983422286672134931599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382677322281524448089954399 574015983422286672134931599)
      ·
        refine ⟨861023975133430008202397399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574015983422286672134931599 861023975133430008202397399)
        ·
          refine ⟨1291535962700145012303596099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 861023975133430008202397399 1291535962700145012303596099)
          ·
            refine ⟨1937303944050217518455394149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1291535962700145012303596099 1937303944050217518455394149)
            ·
              refine ⟨363244489509415784710386403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1937303944050217518455394149 363244489509415784710386403)
              ·
                refine ⟨544866734264123677065579605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363244489509415784710386403 544866734264123677065579605)
                ·
                  refine ⟨6385157042157699340612261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 544866734264123677065579605 6385157042157699340612261)
                  ·
                    refine ⟨1197216945404568626364799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6385157042157699340612261 1197216945404568626364799)
                    ·
                      rfl

theorem cell23_6994715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 8, 4].length) (baseStart_6994715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994715 prefixEnd_6994715 := by exact prefixLift 6994715
  have htrace : WordTrace (prefixWord ++ tailWord_6994715) baseStart_6994715 baseEnd_6994715 := by
    simpa [prefixWord, tailWord_6994715, baseEnd_6994715] using wordTrace_append hprefix tailTrace_6994715
  have hstable : (prefixWord ++ tailWord_6994715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994715).length < 2 ^ (prefixWord ++ tailWord_6994715).sum := by decide
  have hdescent : baseEnd_6994715 < baseStart_6994715 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994725 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 3, 1, 5]
def baseStart_6994725 : Nat := 118140960795 + 6994725 * 2 ^ 59
def prefixEnd_6994725 : Nat := 4983230072969 + 3 ^ 40 * 6994725 * 2
def baseEnd_6994725 : Nat := 3591655971020250839969351

theorem tailTrace_6994725 : CollatzResearch.WordTrace tailWord_6994725 prefixEnd_6994725 3591655971020250839969351 := by
  unfold tailWord_6994725
  simp only [CollatzResearch.WordTrace]
  refine ⟨255118579584313403767833629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170079053056208935845222419 255118579584313403767833629)
  ·
    refine ⟨95669467344117526412937611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255118579584313403767833629 95669467344117526412937611)
    ·
      refine ⟨143504201016176289619406417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95669467344117526412937611 143504201016176289619406417)
      ·
        refine ⟨107628150762132217214554813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143504201016176289619406417 107628150762132217214554813)
        ·
          refine ⟨40360556535799581455458055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107628150762132217214554813 40360556535799581455458055)
          ·
            refine ⟨60540834803699372183187083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40360556535799581455458055 60540834803699372183187083)
            ·
              refine ⟨90811252205549058274780625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60540834803699372183187083 90811252205549058274780625)
              ·
                refine ⟨68108439154161793706085469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90811252205549058274780625 68108439154161793706085469)
                ·
                  refine ⟨25540664682810672639782051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68108439154161793706085469 25540664682810672639782051)
                  ·
                    refine ⟨38310997024216008959673077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25540664682810672639782051 38310997024216008959673077)
                    ·
                      refine ⟨3591655971020250839969351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38310997024216008959673077 3591655971020250839969351)
                      ·
                        rfl

theorem cell23_6994725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_6994725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994725 prefixEnd_6994725 := by exact prefixLift 6994725
  have htrace : WordTrace (prefixWord ++ tailWord_6994725) baseStart_6994725 baseEnd_6994725 := by
    simpa [prefixWord, tailWord_6994725, baseEnd_6994725] using wordTrace_append hprefix tailTrace_6994725
  have hstable : (prefixWord ++ tailWord_6994725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994725).length < 2 ^ (prefixWord ++ tailWord_6994725).sum := by decide
  have hdescent : baseEnd_6994725 < baseStart_6994725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994750 : List Nat := [4, 2, 1, 2, 3, 1, 3, 2, 1, 1, 3]
def baseStart_6994750 : Nat := 118140960795 + 6994750 * 2 ^ 59
def prefixEnd_6994750 : Nat := 4983230072969 + 3 ^ 40 * 6994750 * 2
def baseEnd_6994750 : Nat := 3591668808036613242156737

theorem tailTrace_6994750 : CollatzResearch.WordTrace tailWord_6994750 prefixEnd_6994750 3591668808036613242156737 := by
  unfold tailWord_6994750
  simp only [CollatzResearch.WordTrace]
  refine ⟨31889936426152854129686713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170079660939481888691662469 31889936426152854129686713)
  ·
    refine ⟨23917452319614640597265035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31889936426152854129686713 23917452319614640597265035)
    ·
      refine ⟨35876178479421960895897553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23917452319614640597265035 35876178479421960895897553)
      ·
        refine ⟨26907133859566470671923165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35876178479421960895897553 26907133859566470671923165)
        ·
          refine ⟨10090175197337426501971187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26907133859566470671923165 10090175197337426501971187)
          ·
            refine ⟨15135262796006139752956781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10090175197337426501971187 15135262796006139752956781)
            ·
              refine ⟨5675723548502302407358793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15135262796006139752956781 5675723548502302407358793)
              ·
                refine ⟨4256792661376726805519095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5675723548502302407358793 4256792661376726805519095)
                ·
                  refine ⟨6385188992065090208278643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4256792661376726805519095 6385188992065090208278643)
                  ·
                    refine ⟨9577783488097635312417965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6385188992065090208278643 9577783488097635312417965)
                    ·
                      refine ⟨3591668808036613242156737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9577783488097635312417965 3591668808036613242156737)
                      ·
                        rfl

theorem cell23_6994750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_6994750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994750 prefixEnd_6994750 := by exact prefixLift 6994750
  have htrace : WordTrace (prefixWord ++ tailWord_6994750) baseStart_6994750 baseEnd_6994750 := by
    simpa [prefixWord, tailWord_6994750, baseEnd_6994750] using wordTrace_append hprefix tailTrace_6994750
  have hstable : (prefixWord ++ tailWord_6994750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994750).length < 2 ^ (prefixWord ++ tailWord_6994750).sum := by decide
  have hdescent : baseEnd_6994750 < baseStart_6994750 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994785 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 2, 2, 5]
def baseStart_6994785 : Nat := 118140960795 + 6994785 * 2 ^ 59
def prefixEnd_6994785 : Nat := 4983230072969 + 3 ^ 40 * 6994785 * 2
def baseEnd_6994785 : Nat := 3591686779859520605219075

theorem tailTrace_6994785 : CollatzResearch.WordTrace tailWord_6994785 prefixEnd_6994785 3591686779859520605219075 := by
  unfold tailWord_6994785
  simp only [CollatzResearch.WordTrace]
  refine ⟨255120767964096034015017809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170080511976064022676678539 255120767964096034015017809)
  ·
    refine ⟨191340575973072025511263357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255120767964096034015017809 191340575973072025511263357)
    ·
      refine ⟨71752715989902009566723759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191340575973072025511263357 71752715989902009566723759)
      ·
        refine ⟨107629073984853014350085639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71752715989902009566723759 107629073984853014350085639)
        ·
          refine ⟨161443610977279521525128459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107629073984853014350085639 161443610977279521525128459)
          ·
            refine ⟨242165416465919282287692689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161443610977279521525128459 242165416465919282287692689)
            ·
              refine ⟨181624062349439461715769517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242165416465919282287692689 181624062349439461715769517)
              ·
                refine ⟨68109023381039798143413569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181624062349439461715769517 68109023381039798143413569)
                ·
                  refine ⟨51081767535779848607560177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68109023381039798143413569 51081767535779848607560177)
                  ·
                    refine ⟨38311325651834886455670133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51081767535779848607560177 38311325651834886455670133)
                    ·
                      refine ⟨3591686779859520605219075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38311325651834886455670133 3591686779859520605219075)
                      ·
                        rfl

theorem cell23_6994785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_6994785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994785 prefixEnd_6994785 := by exact prefixLift 6994785
  have htrace : WordTrace (prefixWord ++ tailWord_6994785) baseStart_6994785 baseEnd_6994785 := by
    simpa [prefixWord, tailWord_6994785, baseEnd_6994785] using wordTrace_append hprefix tailTrace_6994785
  have hstable : (prefixWord ++ tailWord_6994785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994785).length < 2 ^ (prefixWord ++ tailWord_6994785).sum := by decide
  have hdescent : baseEnd_6994785 < baseStart_6994785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994799 : List Nat := [1, 1, 2, 1, 3, 1, 1, 7, 1, 3, 2]
def baseStart_6994799 : Nat := 118140960795 + 6994799 * 2 ^ 59
def prefixEnd_6994799 : Nat := 4983230072969 + 3 ^ 40 * 6994799 * 2
def baseEnd_6994799 : Nat := 3591693968588683550444011

theorem tailTrace_6994799 : CollatzResearch.WordTrace tailWord_6994799 prefixEnd_6994799 3591693968588683550444011 := by
  unfold tailWord_6994799
  simp only [CollatzResearch.WordTrace]
  refine ⟨255121278586045314406027451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170080852390696876270684967 255121278586045314406027451)
  ·
    refine ⟨382681917879067971609041177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255121278586045314406027451 382681917879067971609041177)
    ·
      refine ⟨287011438409300978706780883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382681917879067971609041177 287011438409300978706780883)
      ·
        refine ⟨430517157613951468060171325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287011438409300978706780883 430517157613951468060171325)
        ·
          refine ⟨161443934105231800522564247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 430517157613951468060171325 161443934105231800522564247)
          ·
            refine ⟨242165901157847700783846371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161443934105231800522564247 242165901157847700783846371)
            ·
              refine ⟨363248851736771551175769557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242165901157847700783846371 363248851736771551175769557)
              ·
                refine ⟨8513644962580583230682099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 363248851736771551175769557 8513644962580583230682099)
                ·
                  refine ⟨12770467443870874846023149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8513644962580583230682099 12770467443870874846023149)
                  ·
                    refine ⟨4788925291451578067258681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12770467443870874846023149 4788925291451578067258681)
                    ·
                      refine ⟨3591693968588683550444011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4788925291451578067258681 3591693968588683550444011)
                      ·
                        rfl

theorem cell23_6994799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 3, 2].length) (baseStart_6994799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994799 prefixEnd_6994799 := by exact prefixLift 6994799
  have htrace : WordTrace (prefixWord ++ tailWord_6994799) baseStart_6994799 baseEnd_6994799 := by
    simpa [prefixWord, tailWord_6994799, baseEnd_6994799] using wordTrace_append hprefix tailTrace_6994799
  have hstable : (prefixWord ++ tailWord_6994799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994799).length < 2 ^ (prefixWord ++ tailWord_6994799).sum := by decide
  have hdescent : baseEnd_6994799 < baseStart_6994799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994815 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 5]
def baseStart_6994815 : Nat := 118140960795 + 6994815 * 2 ^ 59
def prefixEnd_6994815 : Nat := 4983230072969 + 3 ^ 40 * 6994815 * 2
def baseEnd_6994815 : Nat := 3591702184279155487843937

theorem tailTrace_6994815 : CollatzResearch.WordTrace tailWord_6994815 prefixEnd_6994815 3591702184279155487843937 := by
  unfold tailWord_6994815
  simp only [CollatzResearch.WordTrace]
  refine ⟨255121862153987349138609899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170081241435991566092406599 255121862153987349138609899)
  ·
    refine ⟨382682793230981023707914849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255121862153987349138609899 382682793230981023707914849)
    ·
      refine ⟨287012094923235767780936137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382682793230981023707914849 287012094923235767780936137)
      ·
        refine ⟨215259071192426825835702103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287012094923235767780936137 215259071192426825835702103)
        ·
          refine ⟨322888606788640238753553155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215259071192426825835702103 322888606788640238753553155)
          ·
            refine ⟨484332910182960358130329733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322888606788640238753553155 484332910182960358130329733)
            ·
              refine ⟨90812420659305067149436825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 484332910182960358130329733 90812420659305067149436825)
              ·
                refine ⟨68109315494478800362077619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90812420659305067149436825 68109315494478800362077619)
                ·
                  refine ⟨102163973241718200543116429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68109315494478800362077619 102163973241718200543116429)
                  ·
                    refine ⟨38311489965644325203668661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102163973241718200543116429 38311489965644325203668661)
                    ·
                      refine ⟨3591702184279155487843937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38311489965644325203668661 3591702184279155487843937)
                      ·
                        rfl

theorem cell23_6994815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_6994815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994815 prefixEnd_6994815 := by exact prefixLift 6994815
  have htrace : WordTrace (prefixWord ++ tailWord_6994815) baseStart_6994815 baseEnd_6994815 := by
    simpa [prefixWord, tailWord_6994815, baseEnd_6994815] using wordTrace_append hprefix tailTrace_6994815
  have hstable : (prefixWord ++ tailWord_6994815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994815).length < 2 ^ (prefixWord ++ tailWord_6994815).sum := by decide
  have hdescent : baseEnd_6994815 < baseStart_6994815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994850 : List Nat := [3, 3, 1, 2, 2, 3, 2, 1, 1, 3, 2]
def baseStart_6994850 : Nat := 118140960795 + 6994850 * 2 ^ 59
def prefixEnd_6994850 : Nat := 4983230072969 + 3 ^ 40 * 6994850 * 2
def baseEnd_6994850 : Nat := 3591720156102062850906277

theorem tailTrace_6994850 : CollatzResearch.WordTrace tailWord_6994850 prefixEnd_6994850 3591720156102062850906277 := by
  unfold tailWord_6994850
  simp only [CollatzResearch.WordTrace]
  refine ⟨63780784677215137529033501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170082092472573700077422669 63780784677215137529033501)
  ·
    refine ⟨23917794253955676573387563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63780784677215137529033501 23917794253955676573387563)
    ·
      refine ⟨35876691380933514860081345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23917794253955676573387563 35876691380933514860081345)
      ·
        refine ⟨26907518535700136145061009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35876691380933514860081345 26907518535700136145061009)
        ·
          refine ⟨20180638901775102108795757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26907518535700136145061009 20180638901775102108795757)
          ·
            refine ⟨7567739588165663290798409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20180638901775102108795757 7567739588165663290798409)
            ·
              refine ⟨5675804691124247468098807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7567739588165663290798409 5675804691124247468098807)
              ·
                refine ⟨8513707036686371202148211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5675804691124247468098807 8513707036686371202148211)
                ·
                  refine ⟨12770560555029556803222317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8513707036686371202148211 12770560555029556803222317)
                  ·
                    refine ⟨4788960208136083801208369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12770560555029556803222317 4788960208136083801208369)
                    ·
                      refine ⟨3591720156102062850906277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4788960208136083801208369 3591720156102062850906277)
                      ·
                        rfl

theorem cell23_6994850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_6994850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994850 prefixEnd_6994850 := by exact prefixLift 6994850
  have htrace : WordTrace (prefixWord ++ tailWord_6994850) baseStart_6994850 baseEnd_6994850 := by
    simpa [prefixWord, tailWord_6994850, baseEnd_6994850] using wordTrace_append hprefix tailTrace_6994850
  have hstable : (prefixWord ++ tailWord_6994850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994850).length < 2 ^ (prefixWord ++ tailWord_6994850).sum := by decide
  have hdescent : baseEnd_6994850 < baseStart_6994850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994869 : List Nat := [1, 3, 3, 2, 1, 1, 1, 6, 5]
def baseStart_6994869 : Nat := 118140960795 + 6994869 * 2 ^ 59
def prefixEnd_6994869 : Nat := 4983230072969 + 3 ^ 40 * 6994869 * 2
def baseEnd_6994869 : Nat := 399081101359388697396521

theorem tailTrace_6994869 : CollatzResearch.WordTrace tailWord_6994869 prefixEnd_6994869 399081101359388697396521 := by
  unfold tailWord_6994869
  simp only [CollatzResearch.WordTrace]
  refine ⟨255123831695791716361075661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170082554463861144240717107 255123831695791716361075661)
  ·
    refine ⟨95671436885921893635403373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255123831695791716361075661 95671436885921893635403373)
    ·
      refine ⟨35876788832220710113276265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95671436885921893635403373 35876788832220710113276265)
      ·
        refine ⟨26907591624165532584957199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35876788832220710113276265 26907591624165532584957199)
        ·
          refine ⟨40361387436248298877435799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26907591624165532584957199 40361387436248298877435799)
          ·
            refine ⟨60542081154372448316153699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40361387436248298877435799 60542081154372448316153699)
            ·
              refine ⟨90813121731558672474230549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60542081154372448316153699 90813121731558672474230549)
              ·
                refine ⟨4256865081166812772229557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90813121731558672474230549 4256865081166812772229557)
                ·
                  refine ⟨399081101359388697396521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4256865081166812772229557 399081101359388697396521)
                  ·
                    rfl

theorem cell23_6994869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 6, 5].length) (baseStart_6994869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994869 prefixEnd_6994869 := by exact prefixLift 6994869
  have htrace : WordTrace (prefixWord ++ tailWord_6994869) baseStart_6994869 baseEnd_6994869 := by
    simpa [prefixWord, tailWord_6994869, baseEnd_6994869] using wordTrace_append hprefix tailTrace_6994869
  have hstable : (prefixWord ++ tailWord_6994869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994869).length < 2 ^ (prefixWord ++ tailWord_6994869).sum := by decide
  have hdescent : baseEnd_6994869 < baseStart_6994869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994919 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 4]
def baseStart_6994919 : Nat := 118140960795 + 6994919 * 2 ^ 59
def prefixEnd_6994919 : Nat := 4983230072969 + 3 ^ 40 * 6994919 * 2
def baseEnd_6994919 : Nat := 3591755586267223080943459

theorem tailTrace_6994919 : CollatzResearch.WordTrace tailWord_6994919 prefixEnd_6994919 3591755586267223080943459 := by
  unfold tailWord_6994919
  simp only [CollatzResearch.WordTrace]
  refine ⟨255125655345610574900395811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170083770230407049933597207 255125655345610574900395811)
  ·
    refine ⟨382688483018415862350593717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255125655345610574900395811 382688483018415862350593717)
    ·
      refine ⟨35877045282976487095368161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 382688483018415862350593717 35877045282976487095368161)
      ·
        refine ⟨26907783962232365321526121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35877045282976487095368161 26907783962232365321526121)
        ·
          refine ⟨20180837971674273991144591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26907783962232365321526121 20180837971674273991144591)
          ·
            refine ⟨30271256957511410986716887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20180837971674273991144591 30271256957511410986716887)
            ·
              refine ⟨45406885436267116480075331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30271256957511410986716887 45406885436267116480075331)
              ·
                refine ⟨68110328154400674720112997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45406885436267116480075331 68110328154400674720112997)
                ·
                  refine ⟨12770686528950126510021187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68110328154400674720112997 12770686528950126510021187)
                  ·
                    refine ⟨19156029793425189765031781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12770686528950126510021187 19156029793425189765031781)
                    ·
                      refine ⟨3591755586267223080943459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19156029793425189765031781 3591755586267223080943459)
                      ·
                        rfl

theorem cell23_6994919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_6994919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994919 prefixEnd_6994919 := by exact prefixLift 6994919
  have htrace : WordTrace (prefixWord ++ tailWord_6994919) baseStart_6994919 baseEnd_6994919 := by
    simpa [prefixWord, tailWord_6994919, baseEnd_6994919] using wordTrace_append hprefix tailTrace_6994919
  have hstable : (prefixWord ++ tailWord_6994919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994919).length < 2 ^ (prefixWord ++ tailWord_6994919).sum := by decide
  have hdescent : baseEnd_6994919 < baseStart_6994919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994956 : List Nat := [2, 2, 1, 2, 3, 3, 2, 1, 2, 2, 3]
def baseStart_6994956 : Nat := 118140960795 + 6994956 * 2 ^ 59
def prefixEnd_6994956 : Nat := 4983230072969 + 3 ^ 40 * 6994956 * 2
def baseEnd_6994956 : Nat := 3591774585051439436180789

theorem tailTrace_6994956 : CollatzResearch.WordTrace tailWord_6994956 prefixEnd_6994956 3591774585051439436180789 := by
  unfold tailWord_6994956
  simp only [CollatzResearch.WordTrace]
  refine ⟨127563502423238265109746361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170084669897651020146328481 127563502423238265109746361)
  ·
    refine ⟨95672626817428698832309771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127563502423238265109746361 95672626817428698832309771)
    ·
      refine ⟨143508940226143048248464657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95672626817428698832309771 143508940226143048248464657)
      ·
        refine ⟨107631705169607286186348493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143508940226143048248464657 107631705169607286186348493)
        ·
          refine ⟨40361889438602732319880685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107631705169607286186348493 40361889438602732319880685)
          ·
            refine ⟨15135708539476024619955257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40361889438602732319880685 15135708539476024619955257)
            ·
              refine ⟨11351781404607018464966443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15135708539476024619955257 11351781404607018464966443)
              ·
                refine ⟨17027672106910527697449665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11351781404607018464966443 17027672106910527697449665)
                ·
                  refine ⟨12770754080182895773087249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17027672106910527697449665 12770754080182895773087249)
                  ·
                    refine ⟨9578065560137171829815437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12770754080182895773087249 9578065560137171829815437)
                    ·
                      refine ⟨3591774585051439436180789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9578065560137171829815437 3591774585051439436180789)
                      ·
                        rfl

theorem cell23_6994956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_6994956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994956 prefixEnd_6994956 := by exact prefixLift 6994956
  have htrace : WordTrace (prefixWord ++ tailWord_6994956) baseStart_6994956 baseEnd_6994956 := by
    simpa [prefixWord, tailWord_6994956, baseEnd_6994956] using wordTrace_append hprefix tailTrace_6994956
  have hstable : (prefixWord ++ tailWord_6994956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994956).length < 2 ^ (prefixWord ++ tailWord_6994956).sum := by decide
  have hdescent : baseEnd_6994956 < baseStart_6994956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6994980 : List Nat := [2, 3, 1, 4, 1, 1, 4, 2, 1, 4]
def baseStart_6994980 : Nat := 118140960795 + 6994980 * 2 ^ 59
def prefixEnd_6994980 : Nat := 4983230072969 + 3 ^ 40 * 6994980 * 2
def baseEnd_6994980 : Nat := 1197262302862382447426893

theorem tailTrace_6994980 : CollatzResearch.WordTrace tailWord_6994980 prefixEnd_6994980 1197262302862382447426893 := by
  unfold tailWord_6994980
  simp only [CollatzResearch.WordTrace]
  refine ⟨127563940099194791159183197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170085253465593054878910929 127563940099194791159183197)
  ·
    refine ⟨47836477537198046684693699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127563940099194791159183197 47836477537198046684693699)
    ·
      refine ⟨71754716305797070027040549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47836477537198046684693699 71754716305797070027040549)
      ·
        refine ⟨13454009307336950630070103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71754716305797070027040549 13454009307336950630070103)
        ·
          refine ⟨20181013961005425945105155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13454009307336950630070103 20181013961005425945105155)
          ·
            refine ⟨30271520941508138917657733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20181013961005425945105155 30271520941508138917657733)
            ·
              refine ⟨5675910176532776047060825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30271520941508138917657733 5675910176532776047060825)
              ·
                refine ⟨4256932632399582035295619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5675910176532776047060825 4256932632399582035295619)
                ·
                  refine ⟨6385398948599373052943429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4256932632399582035295619 6385398948599373052943429)
                  ·
                    refine ⟨1197262302862382447426893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6385398948599373052943429 1197262302862382447426893)
                    ·
                      rfl

theorem cell23_6994980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_6994980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6994980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6994980 prefixEnd_6994980 := by exact prefixLift 6994980
  have htrace : WordTrace (prefixWord ++ tailWord_6994980) baseStart_6994980 baseEnd_6994980 := by
    simpa [prefixWord, tailWord_6994980, baseEnd_6994980] using wordTrace_append hprefix tailTrace_6994980
  have hstable : (prefixWord ++ tailWord_6994980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6994980).length < 2 ^ (prefixWord ++ tailWord_6994980).sum := by decide
  have hdescent : baseEnd_6994980 < baseStart_6994980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6994980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995006 : List Nat := [4, 2, 1, 3, 1, 1, 2, 1, 3, 5]
def baseStart_6995006 : Nat := 118140960795 + 6995006 * 2 ^ 59
def prefixEnd_6995006 : Nat := 4983230072969 + 3 ^ 40 * 6995006 * 2
def baseEnd_6995006 : Nat := 1197266753028054746851853

theorem tailTrace_6995006 : CollatzResearch.WordTrace tailWord_6995006 prefixEnd_6995006 1197266753028054746851853 := by
  unfold tailWord_6995006
  simp only [CollatzResearch.WordTrace]
  refine ⟨31891103562036923594851609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170085885664196925839208581 31891103562036923594851609)
  ·
    refine ⟨23918327671527692696138707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31891103562036923594851609 23918327671527692696138707)
    ·
      refine ⟨35877491507291539044208061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23918327671527692696138707 35877491507291539044208061)
      ·
        refine ⟨13454059315234327141578023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35877491507291539044208061 13454059315234327141578023)
        ·
          refine ⟨20181088972851490712367035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13454059315234327141578023 20181088972851490712367035)
          ·
            refine ⟨30271633459277236068550553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20181088972851490712367035 30271633459277236068550553)
            ·
              refine ⟨22703725094457927051412915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30271633459277236068550553 22703725094457927051412915)
              ·
                refine ⟨34055587641686890577119373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22703725094457927051412915 34055587641686890577119373)
                ·
                  refine ⟨12770845365632583966419765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34055587641686890577119373 12770845365632583966419765)
                  ·
                    refine ⟨1197266753028054746851853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12770845365632583966419765 1197266753028054746851853)
                    ·
                      rfl

theorem cell23_6995006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_6995006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995006 prefixEnd_6995006 := by exact prefixLift 6995006
  have htrace : WordTrace (prefixWord ++ tailWord_6995006) baseStart_6995006 baseEnd_6995006 := by
    simpa [prefixWord, tailWord_6995006, baseEnd_6995006] using wordTrace_append hprefix tailTrace_6995006
  have hstable : (prefixWord ++ tailWord_6995006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995006).length < 2 ^ (prefixWord ++ tailWord_6995006).sum := by decide
  have hdescent : baseEnd_6995006 < baseStart_6995006 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995029 : List Nat := [1, 3, 2, 2, 1, 2, 2, 3, 1, 1, 5]
def baseStart_6995029 : Nat := 118140960795 + 6995029 * 2 ^ 59
def prefixEnd_6995029 : Nat := 4983230072969 + 3 ^ 40 * 6995029 * 2
def baseEnd_6995029 : Nat := 3591812069139217650567953

theorem tailTrace_6995029 : CollatzResearch.WordTrace tailWord_6995029 prefixEnd_6995029 3591812069139217650567953 := by
  unfold tailWord_6995029
  simp only [CollatzResearch.WordTrace]
  refine ⟨255129667375212063686900141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170086444916808042457933427 255129667375212063686900141)
  ·
    refine ⟨95673625265704523882587553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255129667375212063686900141 95673625265704523882587553)
    ·
      refine ⟨71755218949278392911940665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95673625265704523882587553 71755218949278392911940665)
      ·
        refine ⟨53816414211958794683955499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71755218949278392911940665 53816414211958794683955499)
        ·
          refine ⟨80724621317938192025933249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53816414211958794683955499 80724621317938192025933249)
          ·
            refine ⟨60543465988453644019449937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80724621317938192025933249 60543465988453644019449937)
            ·
              refine ⟨45407599491340233014587453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60543465988453644019449937 45407599491340233014587453)
              ·
                refine ⟨17027849809252587380470295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45407599491340233014587453 17027849809252587380470295)
                ·
                  refine ⟨25541774713878881070705443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17027849809252587380470295 25541774713878881070705443)
                  ·
                    refine ⟨38312662070818321606058165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25541774713878881070705443 38312662070818321606058165)
                    ·
                      refine ⟨3591812069139217650567953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38312662070818321606058165 3591812069139217650567953)
                      ·
                        rfl

theorem cell23_6995029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_6995029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995029 prefixEnd_6995029 := by exact prefixLift 6995029
  have htrace : WordTrace (prefixWord ++ tailWord_6995029) baseStart_6995029 baseEnd_6995029 := by
    simpa [prefixWord, tailWord_6995029, baseEnd_6995029] using wordTrace_append hprefix tailTrace_6995029
  have hstable : (prefixWord ++ tailWord_6995029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995029).length < 2 ^ (prefixWord ++ tailWord_6995029).sum := by decide
  have hdescent : baseEnd_6995029 < baseStart_6995029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995032 : List Nat := [2, 1, 2, 2, 1, 3, 12]
def baseStart_6995032 : Nat := 118140960795 + 6995032 * 2 ^ 59
def prefixEnd_6995032 : Nat := 4983230072969 + 3 ^ 40 * 6995032 * 2
def baseEnd_6995032 : Nat := 44343377896063964676919

theorem tailTrace_6995032 : CollatzResearch.WordTrace tailWord_6995032 prefixEnd_6995032 44343377896063964676919 := by
  unfold tailWord_6995032
  simp only [CollatzResearch.WordTrace]
  refine ⟨127564888397100597599629675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170086517862800796799506233 127564888397100597599629675)
  ·
    refine ⟨191347332595650896399444513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127564888397100597599629675 191347332595650896399444513)
    ·
      refine ⟨143510499446738172299583385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191347332595650896399444513 143510499446738172299583385)
      ·
        refine ⟨107632874585053629224687539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143510499446738172299583385 107632874585053629224687539)
        ·
          refine ⟨161449311877580443837031309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107632874585053629224687539 161449311877580443837031309)
          ·
            refine ⟨60543491954092666438886741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161449311877580443837031309 60543491954092666438886741)
            ·
              refine ⟨44343377896063964676919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 60543491954092666438886741 44343377896063964676919)
              ·
                rfl

theorem cell23_6995032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 12].length) (baseStart_6995032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995032 prefixEnd_6995032 := by exact prefixLift 6995032
  have htrace : WordTrace (prefixWord ++ tailWord_6995032) baseStart_6995032 baseEnd_6995032 := by
    simpa [prefixWord, tailWord_6995032, baseEnd_6995032] using wordTrace_append hprefix tailTrace_6995032
  have hstable : (prefixWord ++ tailWord_6995032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995032).length < 2 ^ (prefixWord ++ tailWord_6995032).sum := by decide
  have hdescent : baseEnd_6995032 < baseStart_6995032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995036 : List Nat := [2, 2, 4, 1, 1, 1, 3, 1, 4, 4]
def baseStart_6995036 : Nat := 118140960795 + 6995036 * 2 ^ 59
def prefixEnd_6995036 : Nat := 4983230072969 + 3 ^ 40 * 6995036 * 2
def baseEnd_6995036 : Nat := 1197271887834599707726807

theorem tailTrace_6995036 : CollatzResearch.WordTrace tailWord_6995036 prefixEnd_6995036 1197271887834599707726807 := by
  unfold tailWord_6995036
  simp only [CollatzResearch.WordTrace]
  refine ⟨127564961343093351941202481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170086615124124469254936641 127564961343093351941202481)
  ·
    refine ⟨95673721007320013955901861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127564961343093351941202481 95673721007320013955901861)
    ·
      refine ⟨17938822688872502616731599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95673721007320013955901861 17938822688872502616731599)
      ·
        refine ⟨26908234033308753925097399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17938822688872502616731599 26908234033308753925097399)
        ·
          refine ⟨40362351049963130887646099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26908234033308753925097399 40362351049963130887646099)
          ·
            refine ⟨60543526574944696331469149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40362351049963130887646099 60543526574944696331469149)
            ·
              refine ⟨22703822465604261124300931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60543526574944696331469149 22703822465604261124300931)
              ·
                refine ⟨34055733698406391686451397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22703822465604261124300931 34055733698406391686451397)
                ·
                  refine ⟨6385450068451198441209637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34055733698406391686451397 6385450068451198441209637)
                  ·
                    refine ⟨1197271887834599707726807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6385450068451198441209637 1197271887834599707726807)
                    ·
                      rfl

theorem cell23_6995036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_6995036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995036 prefixEnd_6995036 := by exact prefixLift 6995036
  have htrace : WordTrace (prefixWord ++ tailWord_6995036) baseStart_6995036 baseEnd_6995036 := by
    simpa [prefixWord, tailWord_6995036, baseEnd_6995036] using wordTrace_append hprefix tailTrace_6995036
  have hstable : (prefixWord ++ tailWord_6995036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995036).length < 2 ^ (prefixWord ++ tailWord_6995036).sum := by decide
  have hdescent : baseEnd_6995036 < baseStart_6995036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995119 : List Nat := [1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 5]
def baseStart_6995119 : Nat := 118140960795 + 6995119 * 2 ^ 59
def prefixEnd_6995119 : Nat := 4983230072969 + 3 ^ 40 * 6995119 * 2
def baseEnd_6995119 : Nat := 3591858282398122298442539

theorem tailTrace_6995119 : CollatzResearch.WordTrace tailWord_6995119 prefixEnd_6995119 3591858282398122298442539 := by
  unfold tailWord_6995119
  simp only [CollatzResearch.WordTrace]
  refine ⟨255132949944886009057676411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170088633296590672705117607 255132949944886009057676411)
  ·
    refine ⟨382699424917329013586514617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255132949944886009057676411 382699424917329013586514617)
    ·
      refine ⟨287024568687996760189885963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382699424917329013586514617 287024568687996760189885963)
      ·
        refine ⟨430536853031995140284828945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287024568687996760189885963 430536853031995140284828945)
        ·
          refine ⟨322902639773996355213621709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 430536853031995140284828945 322902639773996355213621709)
          ·
            refine ⟨121088489915248633205108141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 322902639773996355213621709 121088489915248633205108141)
            ·
              refine ⟨45408183718218237451915553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121088489915248633205108141 45408183718218237451915553)
              ·
                refine ⟨34056137788663678088936665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45408183718218237451915553 34056137788663678088936665)
                ·
                  refine ⟨25542103341497758566702499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34056137788663678088936665 25542103341497758566702499)
                  ·
                    refine ⟨38313155012246637850053749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25542103341497758566702499 38313155012246637850053749)
                    ·
                      refine ⟨3591858282398122298442539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38313155012246637850053749 3591858282398122298442539)
                      ·
                        rfl

theorem cell23_6995119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 5].length) (baseStart_6995119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995119 prefixEnd_6995119 := by exact prefixLift 6995119
  have htrace : WordTrace (prefixWord ++ tailWord_6995119) baseStart_6995119 baseEnd_6995119 := by
    simpa [prefixWord, tailWord_6995119, baseEnd_6995119] using wordTrace_append hprefix tailTrace_6995119
  have hstable : (prefixWord ++ tailWord_6995119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995119).length < 2 ^ (prefixWord ++ tailWord_6995119).sum := by decide
  have hdescent : baseEnd_6995119 < baseStart_6995119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995133 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 6, 2, 2]
def baseStart_6995133 : Nat := 118140960795 + 6995133 * 2 ^ 59
def prefixEnd_6995133 : Nat := 4983230072969 + 3 ^ 40 * 6995133 * 2
def baseEnd_6995133 : Nat := 3591865471127285243667475

theorem tailTrace_6995133 : CollatzResearch.WordTrace tailWord_6995133 prefixEnd_6995133 3591865471127285243667475 := by
  unfold tailWord_6995133
  simp only [CollatzResearch.WordTrace]
  refine ⟨255133460566835289448686053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170088973711223526299124035 255133460566835289448686053)
  ·
    refine ⟨47837523856281616771628635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255133460566835289448686053 47837523856281616771628635)
    ·
      refine ⟨71756285784422425157442953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47837523856281616771628635 71756285784422425157442953)
      ·
        refine ⟨53817214338316818868082215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71756285784422425157442953 53817214338316818868082215)
        ·
          refine ⟨80725821507475228302123323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53817214338316818868082215 80725821507475228302123323)
          ·
            refine ⟨121088732261212842453184985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80725821507475228302123323 121088732261212842453184985)
            ·
              refine ⟨90816549195909631839888739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121088732261212842453184985 90816549195909631839888739)
              ·
                refine ⟨136224823793864447759833109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90816549195909631839888739 136224823793864447759833109)
                ·
                  refine ⟨6385538615337395988742177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 136224823793864447759833109 6385538615337395988742177)
                  ·
                    refine ⟨4789153961503046991556633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6385538615337395988742177 4789153961503046991556633)
                    ·
                      refine ⟨3591865471127285243667475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4789153961503046991556633 3591865471127285243667475)
                      ·
                        rfl

theorem cell23_6995133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_6995133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995133 prefixEnd_6995133 := by exact prefixLift 6995133
  have htrace : WordTrace (prefixWord ++ tailWord_6995133) baseStart_6995133 baseEnd_6995133 := by
    simpa [prefixWord, tailWord_6995133, baseEnd_6995133] using wordTrace_append hprefix tailTrace_6995133
  have hstable : (prefixWord ++ tailWord_6995133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995133).length < 2 ^ (prefixWord ++ tailWord_6995133).sum := by decide
  have hdescent : baseEnd_6995133 < baseStart_6995133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995188 : List Nat := [2, 6, 1, 2, 1, 2, 2, 1, 1, 3, 2]
def baseStart_6995188 : Nat := 118140960795 + 6995188 * 2 ^ 59
def prefixEnd_6995188 : Nat := 4983230072969 + 3 ^ 40 * 6995188 * 2
def baseEnd_6995188 : Nat := 3591893712563282528479723

theorem tailTrace_6995188 : CollatzResearch.WordTrace tailWord_6995188 prefixEnd_6995188 3591893712563282528479723 := by
  unfold tailWord_6995188
  simp only [CollatzResearch.WordTrace]
  refine ⟨127567733290818016920969109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170090311054424022561292145 127567733290818016920969109)
  ·
    refine ⟨5979737498007094543170427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 127567733290818016920969109 5979737498007094543170427)
    ·
      refine ⟨8969606247010641814755641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5979737498007094543170427 8969606247010641814755641)
      ·
        refine ⟨6727204685257981361066731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8969606247010641814755641 6727204685257981361066731)
        ·
          refine ⟨10090807027886972041600097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6727204685257981361066731 10090807027886972041600097)
          ·
            refine ⟨7568105270915229031200073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10090807027886972041600097 7568105270915229031200073)
            ·
              refine ⟨5676078953186421773400055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7568105270915229031200073 5676078953186421773400055)
              ·
                refine ⟨8514118429779632660100083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5676078953186421773400055 8514118429779632660100083)
                ·
                  refine ⟨12771177644669448990150125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8514118429779632660100083 12771177644669448990150125)
                  ·
                    refine ⟨4789191616751043371306297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12771177644669448990150125 4789191616751043371306297)
                    ·
                      refine ⟨3591893712563282528479723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4789191616751043371306297 3591893712563282528479723)
                      ·
                        rfl

theorem cell23_6995188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_6995188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995188 prefixEnd_6995188 := by exact prefixLift 6995188
  have htrace : WordTrace (prefixWord ++ tailWord_6995188) baseStart_6995188 baseEnd_6995188 := by
    simpa [prefixWord, tailWord_6995188, baseEnd_6995188] using wordTrace_append hprefix tailTrace_6995188
  have hstable : (prefixWord ++ tailWord_6995188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995188).length < 2 ^ (prefixWord ++ tailWord_6995188).sum := by decide
  have hdescent : baseEnd_6995188 < baseStart_6995188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995223 : List Nat := [1, 1, 3, 4, 1, 1, 1, 3, 2, 4, 2]
def baseStart_6995223 : Nat := 118140960795 + 6995223 * 2 ^ 59
def prefixEnd_6995223 : Nat := 4983230072969 + 3 ^ 40 * 6995223 * 2
def baseEnd_6995223 : Nat := 3591911684386189891542061

theorem tailTrace_6995223 : CollatzResearch.WordTrace tailWord_6995223 prefixEnd_6995223 3591911684386189891542061 := by
  unfold tailWord_6995223
  simp only [CollatzResearch.WordTrace]
  refine ⟨255136743136509234819462323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170091162091006156546308215 255136743136509234819462323)
  ·
    refine ⟨382705114704763852229193485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255136743136509234819462323 382705114704763852229193485)
    ·
      refine ⟨143514418014286444585947557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 382705114704763852229193485 143514418014286444585947557)
      ·
        refine ⟨26908953377678708359865167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143514418014286444585947557 26908953377678708359865167)
        ·
          refine ⟨40363430066518062539797751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26908953377678708359865167 40363430066518062539797751)
          ·
            refine ⟨60545145099777093809696627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40363430066518062539797751 60545145099777093809696627)
            ·
              refine ⟨90817717649665640714544941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60545145099777093809696627 90817717649665640714544941)
              ·
                refine ⟨34056644118624615267954353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90817717649665640714544941 34056644118624615267954353)
                ·
                  refine ⟨25542483088968461450965765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34056644118624615267954353 25542483088968461450965765)
                  ·
                    refine ⟨4789215579181586522056081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25542483088968461450965765 4789215579181586522056081)
                    ·
                      refine ⟨3591911684386189891542061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4789215579181586522056081 3591911684386189891542061)
                      ·
                        rfl

theorem cell23_6995223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_6995223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995223 prefixEnd_6995223 := by exact prefixLift 6995223
  have htrace : WordTrace (prefixWord ++ tailWord_6995223) baseStart_6995223 baseEnd_6995223 := by
    simpa [prefixWord, tailWord_6995223, baseEnd_6995223] using wordTrace_append hprefix tailTrace_6995223
  have hstable : (prefixWord ++ tailWord_6995223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995223).length < 2 ^ (prefixWord ++ tailWord_6995223).sum := by decide
  have hdescent : baseEnd_6995223 < baseStart_6995223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995236 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 2, 4, 4]
def baseStart_6995236 : Nat := 118140960795 + 6995236 * 2 ^ 59
def prefixEnd_6995236 : Nat := 4983230072969 + 3 ^ 40 * 6995236 * 2
def baseEnd_6995236 : Nat := 3591918359634698340679501

theorem tailTrace_6995236 : CollatzResearch.WordTrace tailWord_6995236 prefixEnd_6995236 3591918359634698340679501 := by
  unfold tailWord_6995236
  simp only [CollatzResearch.WordTrace]
  refine ⟨127568608642731069019842781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170091478190308092026457041 127568608642731069019842781)
  ·
    refine ⟨47838228241024150882441043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127568608642731069019842781 47838228241024150882441043)
    ·
      refine ⟨71757342361536226323661565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47838228241024150882441043 71757342361536226323661565)
      ·
        refine ⟨26909003385576084871373087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71757342361536226323661565 26909003385576084871373087)
        ·
          refine ⟨40363505078364127307059631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26909003385576084871373087 40363505078364127307059631)
          ·
            refine ⟨60545257617546190960589447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40363505078364127307059631 60545257617546190960589447)
            ·
              refine ⟨90817886426319286440884171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60545257617546190960589447 90817886426319286440884171)
              ·
                refine ⟨136226829639478929661326257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90817886426319286440884171 136226829639478929661326257)
                ·
                  refine ⟨102170122229609197245994693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136226829639478929661326257 102170122229609197245994693)
                  ·
                    refine ⟨19156897918051724483624005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102170122229609197245994693 19156897918051724483624005)
                    ·
                      refine ⟨3591918359634698340679501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19156897918051724483624005 3591918359634698340679501)
                      ·
                        rfl

theorem cell23_6995236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_6995236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995236 prefixEnd_6995236 := by exact prefixLift 6995236
  have htrace : WordTrace (prefixWord ++ tailWord_6995236) baseStart_6995236 baseEnd_6995236 := by
    simpa [prefixWord, tailWord_6995236, baseEnd_6995236] using wordTrace_append hprefix tailTrace_6995236
  have hstable : (prefixWord ++ tailWord_6995236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995236).length < 2 ^ (prefixWord ++ tailWord_6995236).sum := by decide
  have hdescent : baseEnd_6995236 < baseStart_6995236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995259 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 3, 11]
def baseStart_6995259 : Nat := 118140960795 + 6995259 * 2 ^ 59
def prefixEnd_6995259 : Nat := 4983230072969 + 3 ^ 40 * 6995259 * 2
def baseEnd_6995259 : Nat := 1197310056563250583563965

theorem tailTrace_6995259 : CollatzResearch.WordTrace tailWord_6995259 prefixEnd_6995259 1197310056563250583563965 := by
  unfold tailWord_6995259
  simp only [CollatzResearch.WordTrace]
  refine ⟨255138056164378812967772831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170092037442919208645181887 255138056164378812967772831)
  ·
    refine ⟨382707084246568219451659247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255138056164378812967772831 382707084246568219451659247)
    ·
      refine ⟨574060626369852329177488871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382707084246568219451659247 574060626369852329177488871)
      ·
        refine ⟨861090939554778493766233307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574060626369852329177488871 861090939554778493766233307)
        ·
          refine ⟨1291636409332167740649349961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 861090939554778493766233307 1291636409332167740649349961)
          ·
            refine ⟨968727306999125805487012471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1291636409332167740649349961 968727306999125805487012471)
            ·
              refine ⟨1453090960498688708230518707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 968727306999125805487012471 1453090960498688708230518707)
              ·
                refine ⟨2179636440748033062345778061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1453090960498688708230518707 2179636440748033062345778061)
                ·
                  refine ⟨817363665280512398379666773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2179636440748033062345778061 817363665280512398379666773)
                  ·
                    refine ⟨1197310056563250583563965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 817363665280512398379666773 1197310056563250583563965)
                    ·
                      rfl

theorem cell23_6995259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 11].length) (baseStart_6995259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995259 prefixEnd_6995259 := by exact prefixLift 6995259
  have htrace : WordTrace (prefixWord ++ tailWord_6995259) baseStart_6995259 baseEnd_6995259 := by
    simpa [prefixWord, tailWord_6995259, baseEnd_6995259] using wordTrace_append hprefix tailTrace_6995259
  have hstable : (prefixWord ++ tailWord_6995259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995259).length < 2 ^ (prefixWord ++ tailWord_6995259).sum := by decide
  have hdescent : baseEnd_6995259 < baseStart_6995259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995283 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 4, 3, 2]
def baseStart_6995283 : Nat := 118140960795 + 6995283 * 2 ^ 59
def prefixEnd_6995283 : Nat := 4983230072969 + 3 ^ 40 * 6995283 * 2
def baseEnd_6995283 : Nat := 3591942493225459656791785

theorem tailTrace_6995283 : CollatzResearch.WordTrace tailWord_6995283 prefixEnd_6995283 3591942493225459656791785 := by
  unfold tailWord_6995283
  simp only [CollatzResearch.WordTrace]
  refine ⟨255138931516291865066646503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170092621010861243377764335 255138931516291865066646503)
  ·
    refine ⟨382708397274437797599969755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255138931516291865066646503 382708397274437797599969755)
    ·
      refine ⟨574062595911656696399954633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382708397274437797599969755 574062595911656696399954633)
      ·
        refine ⟨430546946933742522299965975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 574062595911656696399954633 430546946933742522299965975)
        ·
          refine ⟨645820420400613783449948963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430546946933742522299965975 645820420400613783449948963)
          ·
            refine ⟨968730630600920675174923445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645820420400613783449948963 968730630600920675174923445)
            ·
              refine ⟨90818496618836313297649073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 968730630600920675174923445 90818496618836313297649073)
              ·
                refine ⟨68113872464127234973236805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90818496618836313297649073 68113872464127234973236805)
                ·
                  refine ⟨12771351087023856557481901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68113872464127234973236805 12771351087023856557481901)
                  ·
                    refine ⟨4789256657633946209055713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12771351087023856557481901 4789256657633946209055713)
                    ·
                      refine ⟨3591942493225459656791785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4789256657633946209055713 3591942493225459656791785)
                      ·
                        rfl

theorem cell23_6995283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 3, 2].length) (baseStart_6995283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995283 prefixEnd_6995283 := by exact prefixLift 6995283
  have htrace : WordTrace (prefixWord ++ tailWord_6995283) baseStart_6995283 baseEnd_6995283 := by
    simpa [prefixWord, tailWord_6995283, baseEnd_6995283] using wordTrace_append hprefix tailTrace_6995283
  have hstable : (prefixWord ++ tailWord_6995283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995283).length < 2 ^ (prefixWord ++ tailWord_6995283).sum := by decide
  have hdescent : baseEnd_6995283 < baseStart_6995283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995300 : List Nat := [2, 3, 1, 1, 3, 2, 1, 3, 2, 3, 2]
def baseStart_6995300 : Nat := 118140960795 + 6995300 * 2 ^ 59
def prefixEnd_6995300 : Nat := 4983230072969 + 3 ^ 40 * 6995300 * 2
def baseEnd_6995300 : Nat := 3591951222396586090279207

theorem tailTrace_6995300 : CollatzResearch.WordTrace tailWord_6995300 prefixEnd_6995300 3591951222396586090279207 := by
  unfold tailWord_6995300
  simp only [CollatzResearch.WordTrace]
  refine ⟨127569775778615138485007677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170093034371486851313343569 127569775778615138485007677)
  ·
    refine ⟨47838665916980676931877879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127569775778615138485007677 47838665916980676931877879)
    ·
      refine ⟨71757998875471015397816819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47838665916980676931877879 71757998875471015397816819)
      ·
        refine ⟨107636998313206523096725229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71757998875471015397816819 107636998313206523096725229)
        ·
          refine ⟨40363874367452446161271961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107636998313206523096725229 40363874367452446161271961)
          ·
            refine ⟨30272905775589334620953971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40363874367452446161271961 30272905775589334620953971)
            ·
              refine ⟨45409358663384001931430957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30272905775589334620953971 45409358663384001931430957)
              ·
                refine ⟨17028509498769000724286609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45409358663384001931430957 17028509498769000724286609)
                ·
                  refine ⟨12771382124076750543214957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17028509498769000724286609 12771382124076750543214957)
                  ·
                    refine ⟨4789268296528781453705609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12771382124076750543214957 4789268296528781453705609)
                    ·
                      refine ⟨3591951222396586090279207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4789268296528781453705609 3591951222396586090279207)
                      ·
                        rfl

theorem cell23_6995300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 2, 3, 2].length) (baseStart_6995300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995300 prefixEnd_6995300 := by exact prefixLift 6995300
  have htrace : WordTrace (prefixWord ++ tailWord_6995300) baseStart_6995300 baseEnd_6995300 := by
    simpa [prefixWord, tailWord_6995300, baseEnd_6995300] using wordTrace_append hprefix tailTrace_6995300
  have hstable : (prefixWord ++ tailWord_6995300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995300).length < 2 ^ (prefixWord ++ tailWord_6995300).sum := by decide
  have hdescent : baseEnd_6995300 < baseStart_6995300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995313 : List Nat := [1, 2, 2, 2, 1, 2, 2, 5, 1, 1, 4]
def baseStart_6995313 : Nat := 118140960795 + 6995313 * 2 ^ 59
def prefixEnd_6995313 : Nat := 4983230072969 + 3 ^ 40 * 6995313 * 2
def baseEnd_6995313 : Nat := 3591957897645094539416647

theorem tailTrace_6995313 : CollatzResearch.WordTrace tailWord_6995313 prefixEnd_6995313 3591957897645094539416647 := by
  unfold tailWord_6995313
  simp only [CollatzResearch.WordTrace]
  refine ⟨255140025706183180190238593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170093350470788786793492395 255140025706183180190238593)
  ·
    refine ⟨191355019279637385142678945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255140025706183180190238593 191355019279637385142678945)
    ·
      refine ⟨143516264459728038857009209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191355019279637385142678945 143516264459728038857009209)
      ·
        refine ⟨107637198344796029142756907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143516264459728038857009209 107637198344796029142756907)
        ·
          refine ⟨161455797517194043714135361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107637198344796029142756907 161455797517194043714135361)
          ·
            refine ⟨121091848137895532785601521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161455797517194043714135361 121091848137895532785601521)
            ·
              refine ⟨90818886103421649589201141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121091848137895532785601521 90818886103421649589201141)
              ·
                refine ⟨8514270572195779648987607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90818886103421649589201141 8514270572195779648987607)
                ·
                  refine ⟨12771405858293669473481411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8514270572195779648987607 12771405858293669473481411)
                  ·
                    refine ⟨19157108787440504210222117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12771405858293669473481411 19157108787440504210222117)
                    ·
                      refine ⟨3591957897645094539416647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19157108787440504210222117 3591957897645094539416647)
                      ·
                        rfl

theorem cell23_6995313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_6995313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995313 prefixEnd_6995313 := by exact prefixLift 6995313
  have htrace : WordTrace (prefixWord ++ tailWord_6995313) baseStart_6995313 baseEnd_6995313 := by
    simpa [prefixWord, tailWord_6995313, baseEnd_6995313] using wordTrace_append hprefix tailTrace_6995313
  have hstable : (prefixWord ++ tailWord_6995313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995313).length < 2 ^ (prefixWord ++ tailWord_6995313).sum := by decide
  have hdescent : baseEnd_6995313 < baseStart_6995313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995333 : List Nat := [1, 3, 1, 1, 3, 1, 3, 2, 3, 2, 3]
def baseStart_6995333 : Nat := 118140960795 + 6995333 * 2 ^ 59
def prefixEnd_6995333 : Nat := 4983230072969 + 3 ^ 40 * 6995333 * 2
def baseEnd_6995333 : Nat := 3591968167258184461166555

theorem tailTrace_6995333 : CollatzResearch.WordTrace tailWord_6995333 prefixEnd_6995333 3591968167258184461166555 := by
  unfold tailWord_6995333
  simp only [CollatzResearch.WordTrace]
  refine ⟨255140755166110723605966653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170093836777407149070644435 255140755166110723605966653)
  ·
    refine ⟨95677783187291521352237495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255140755166110723605966653 95677783187291521352237495)
    ·
      refine ⟨143516674780937282028356243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95677783187291521352237495 143516674780937282028356243)
      ·
        refine ⟨215275012171405923042534365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143516674780937282028356243 215275012171405923042534365)
        ·
          refine ⟨80728129564277221140950387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215275012171405923042534365 80728129564277221140950387)
          ·
            refine ⟨121092194346415831711425581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80728129564277221140950387 121092194346415831711425581)
            ·
              refine ⟨45409572879905936891784593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121092194346415831711425581 45409572879905936891784593)
              ·
                refine ⟨34057179659929452668838445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45409572879905936891784593 34057179659929452668838445)
                ·
                  refine ⟨12771442372473544750814417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34057179659929452668838445 12771442372473544750814417)
                  ·
                    refine ⟨9578581779355158563110813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12771442372473544750814417 9578581779355158563110813)
                    ·
                      refine ⟨3591968167258184461166555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9578581779355158563110813 3591968167258184461166555)
                      ·
                        rfl

theorem cell23_6995333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 2, 3].length) (baseStart_6995333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995333 prefixEnd_6995333 := by exact prefixLift 6995333
  have htrace : WordTrace (prefixWord ++ tailWord_6995333) baseStart_6995333 baseEnd_6995333 := by
    simpa [prefixWord, tailWord_6995333, baseEnd_6995333] using wordTrace_append hprefix tailTrace_6995333
  have hstable : (prefixWord ++ tailWord_6995333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995333).length < 2 ^ (prefixWord ++ tailWord_6995333).sum := by decide
  have hdescent : baseEnd_6995333 < baseStart_6995333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995353 : List Nat := [1, 2, 1, 2, 1, 6, 3, 7]
def baseStart_6995353 : Nat := 118140960795 + 6995353 * 2 ^ 59
def prefixEnd_6995353 : Nat := 4983230072969 + 3 ^ 40 * 6995353 * 2
def baseEnd_6995353 : Nat := 133036238402639791959869

theorem tailTrace_6995353 : CollatzResearch.WordTrace tailWord_6995353 prefixEnd_6995353 133036238402639791959869 := by
  unfold tailWord_6995353
  simp only [CollatzResearch.WordTrace]
  refine ⟨255141484626038267021694713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170094323084025511347796475 255141484626038267021694713)
  ·
    refine ⟨191356113469528700266271035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255141484626038267021694713 191356113469528700266271035)
    ·
      refine ⟨287034170204293050399406553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191356113469528700266271035 287034170204293050399406553)
      ·
        refine ⟨215275627653219787799554915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287034170204293050399406553 215275627653219787799554915)
        ·
          refine ⟨322913441479829681699332373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215275627653219787799554915 322913441479829681699332373)
          ·
            refine ⟨15136567569367016329656205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 322913441479829681699332373 15136567569367016329656205)
            ·
              refine ⟨5676212838512631123621077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15136567569367016329656205 5676212838512631123621077)
              ·
                refine ⟨133036238402639791959869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5676212838512631123621077 133036238402639791959869)
                ·
                  rfl

theorem cell23_6995353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 7].length) (baseStart_6995353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995353 prefixEnd_6995353 := by exact prefixLift 6995353
  have htrace : WordTrace (prefixWord ++ tailWord_6995353) baseStart_6995353 baseEnd_6995353 := by
    simpa [prefixWord, tailWord_6995353, baseEnd_6995353] using wordTrace_append hprefix tailTrace_6995353
  have hstable : (prefixWord ++ tailWord_6995353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995353).length < 2 ^ (prefixWord ++ tailWord_6995353).sum := by decide
  have hdescent : baseEnd_6995353 < baseStart_6995353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995363 : List Nat := [1, 1, 1, 4, 1, 3, 1, 4, 1, 3, 3]
def baseStart_6995363 : Nat := 118140960795 + 6995363 * 2 ^ 59
def prefixEnd_6995363 : Nat := 4983230072969 + 3 ^ 40 * 6995363 * 2
def baseEnd_6995363 : Nat := 3591983571677819343791417

theorem tailTrace_6995363 : CollatzResearch.WordTrace tailWord_6995363 prefixEnd_6995363 3591983571677819343791417 := by
  unfold tailWord_6995363
  simp only [CollatzResearch.WordTrace]
  refine ⟨255141849356002038729558743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170094566237334692486372495 255141849356002038729558743)
  ·
    refine ⟨382712774034003058094338115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255141849356002038729558743 382712774034003058094338115)
    ·
      refine ⟨574069161051004587141507173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382712774034003058094338115 574069161051004587141507173)
      ·
        refine ⟨107637967697063360089032595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 574069161051004587141507173 107637967697063360089032595)
        ·
          refine ⟨161456951545595040133548893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107637967697063360089032595 161456951545595040133548893)
          ·
            refine ⟨60546356829598140050080835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161456951545595040133548893 60546356829598140050080835)
            ·
              refine ⟨90819535244397210075121253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60546356829598140050080835 90819535244397210075121253)
              ·
                refine ⟨17028662858324476889085235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90819535244397210075121253 17028662858324476889085235)
                ·
                  refine ⟨25542994287486715333627853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17028662858324476889085235 25542994287486715333627853)
                  ·
                    refine ⟨9578622857807518250110445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25542994287486715333627853 9578622857807518250110445)
                    ·
                      refine ⟨3591983571677819343791417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9578622857807518250110445 3591983571677819343791417)
                      ·
                        rfl

theorem cell23_6995363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_6995363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995363 prefixEnd_6995363 := by exact prefixLift 6995363
  have htrace : WordTrace (prefixWord ++ tailWord_6995363) baseStart_6995363 baseEnd_6995363 := by
    simpa [prefixWord, tailWord_6995363, baseEnd_6995363] using wordTrace_append hprefix tailTrace_6995363
  have hstable : (prefixWord ++ tailWord_6995363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995363).length < 2 ^ (prefixWord ++ tailWord_6995363).sum := by decide
  have hdescent : baseEnd_6995363 < baseStart_6995363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995376 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 5]
def baseStart_6995376 : Nat := 118140960795 + 6995376 * 2 ^ 59
def prefixEnd_6995376 : Nat := 4983230072969 + 3 ^ 40 * 6995376 * 2
def baseEnd_6995376 : Nat := 3591990246926327792928857

theorem tailTrace_6995376 : CollatzResearch.WordTrace tailWord_6995376 prefixEnd_6995376 3591990246926327792928857 := by
  unfold tailWord_6995376
  simp only [CollatzResearch.WordTrace]
  refine ⟨127571161752477470974890991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170094882336636627966521321 127571161752477470974890991)
  ·
    refine ⟨191356742628716206462336487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127571161752477470974890991 191356742628716206462336487)
    ·
      refine ⟨287035113943074309693504731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191356742628716206462336487 287035113943074309693504731)
      ·
        refine ⟨430552670914611464540257097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287035113943074309693504731 430552670914611464540257097)
        ·
          refine ⟨322914503185958598405192823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 430552670914611464540257097 322914503185958598405192823)
          ·
            refine ⟨484371754778937897607789235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322914503185958598405192823 484371754778937897607789235)
            ·
              refine ⟨726557632168406846411683853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484371754778937897607789235 726557632168406846411683853)
              ·
                refine ⟨272459112063152567404381445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 726557632168406846411683853 272459112063152567404381445)
                ·
                  refine ⟨51086083511841106388321521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272459112063152567404381445 51086083511841106388321521)
                  ·
                    refine ⟨38314562633880829791241141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51086083511841106388321521 38314562633880829791241141)
                    ·
                      refine ⟨3591990246926327792928857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38314562633880829791241141 3591990246926327792928857)
                      ·
                        rfl

theorem cell23_6995376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 5].length) (baseStart_6995376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995376 prefixEnd_6995376 := by exact prefixLift 6995376
  have htrace : WordTrace (prefixWord ++ tailWord_6995376) baseStart_6995376 baseEnd_6995376 := by
    simpa [prefixWord, tailWord_6995376, baseEnd_6995376] using wordTrace_append hprefix tailTrace_6995376
  have hstable : (prefixWord ++ tailWord_6995376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995376).length < 2 ^ (prefixWord ++ tailWord_6995376).sum := by decide
  have hdescent : baseEnd_6995376 < baseStart_6995376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995423 : List Nat := [1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 5]
def baseStart_6995423 : Nat := 118140960795 + 6995423 * 2 ^ 59
def prefixEnd_6995423 : Nat := 4983230072969 + 3 ^ 40 * 6995423 * 2
def baseEnd_6995423 : Nat := 3592014380517089109041141

theorem tailTrace_6995423 : CollatzResearch.WordTrace tailWord_6995423 prefixEnd_6995423 3592014380517089109041141 := by
  unfold tailWord_6995423
  simp only [CollatzResearch.WordTrace]
  refine ⟨255144037735784668976742923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170096025157189779317828615 255144037735784668976742923)
  ·
    refine ⟨382716056603677003465114385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255144037735784668976742923 382716056603677003465114385)
    ·
      refine ⟨287037042452757752598835789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382716056603677003465114385 287037042452757752598835789)
      ·
        refine ⟨107638890919784157224563421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287037042452757752598835789 107638890919784157224563421)
        ·
          refine ⟨40364584094919058959211283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107638890919784157224563421 40364584094919058959211283)
          ·
            refine ⟨60546876142378588438816925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40364584094919058959211283 60546876142378588438816925)
            ·
              refine ⟨22705078553391970664556347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60546876142378588438816925 22705078553391970664556347)
              ·
                refine ⟨34057617830087955996834521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22705078553391970664556347 34057617830087955996834521)
                ·
                  refine ⟨25543213372565966997625891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34057617830087955996834521 25543213372565966997625891)
                  ·
                    refine ⟨38314820058848950496438837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25543213372565966997625891 38314820058848950496438837)
                    ·
                      refine ⟨3592014380517089109041141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38314820058848950496438837 3592014380517089109041141)
                      ·
                        rfl

theorem cell23_6995423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_6995423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995423 prefixEnd_6995423 := by exact prefixLift 6995423
  have htrace : WordTrace (prefixWord ++ tailWord_6995423) baseStart_6995423 baseEnd_6995423 := by
    simpa [prefixWord, tailWord_6995423, baseEnd_6995423] using wordTrace_append hprefix tailTrace_6995423
  have hstable : (prefixWord ++ tailWord_6995423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995423).length < 2 ^ (prefixWord ++ tailWord_6995423).sum := by decide
  have hdescent : baseEnd_6995423 < baseStart_6995423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995490 : List Nat := [3, 3, 1, 1, 1, 1, 4, 2, 2, 5]
def baseStart_6995490 : Nat := 118140960795 + 6995490 * 2 ^ 59
def prefixEnd_6995490 : Nat := 4983230072969 + 3 ^ 40 * 6995490 * 2
def baseEnd_6995490 : Nat := 1197349594573646782301111

theorem tailTrace_6995490 : CollatzResearch.WordTrace tailWord_6995490 prefixEnd_6995490 1197349594573646782301111 := by
  unfold tailWord_6995490
  simp only [CollatzResearch.WordTrace]
  refine ⟨63786620356635484854857981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170097654284361292946287949 63786620356635484854857981)
  ·
    refine ⟨23919982633738306820571743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63786620356635484854857981 23919982633738306820571743)
    ·
      refine ⟨35879973950607460230857615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23919982633738306820571743 35879973950607460230857615)
      ·
        refine ⟨53819960925911190346286423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35879973950607460230857615 53819960925911190346286423)
        ·
          refine ⟨80729941388866785519429635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53819960925911190346286423 80729941388866785519429635)
          ·
            refine ⟨121094912083300178279144453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80729941388866785519429635 121094912083300178279144453)
            ·
              refine ⟨22705296015618783427339585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121094912083300178279144453 22705296015618783427339585)
              ·
                refine ⟨17028972011714087570504689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22705296015618783427339585 17028972011714087570504689)
                ·
                  refine ⟨12771729008785565677878517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17028972011714087570504689 12771729008785565677878517)
                  ·
                    refine ⟨1197349594573646782301111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12771729008785565677878517 1197349594573646782301111)
                    ·
                      rfl

theorem cell23_6995490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_6995490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995490 prefixEnd_6995490 := by exact prefixLift 6995490
  have htrace : WordTrace (prefixWord ++ tailWord_6995490) baseStart_6995490 baseEnd_6995490 := by
    simpa [prefixWord, tailWord_6995490, baseEnd_6995490] using wordTrace_append hprefix tailTrace_6995490
  have hstable : (prefixWord ++ tailWord_6995490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995490).length < 2 ^ (prefixWord ++ tailWord_6995490).sum := by decide
  have hdescent : baseEnd_6995490 < baseStart_6995490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995493 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 3, 3, 4]
def baseStart_6995493 : Nat := 118140960795 + 6995493 * 2 ^ 59
def prefixEnd_6995493 : Nat := 4983230072969 + 3 ^ 40 * 6995493 * 2
def baseEnd_6995493 : Nat := 3592050324162903835165819

theorem tailTrace_6995493 : CollatzResearch.WordTrace tailWord_6995493 prefixEnd_6995493 3592050324162903835165819 := by
  unfold tailWord_6995493
  simp only [CollatzResearch.WordTrace]
  refine ⟨255146590845531070931791133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170097727230354047287860755 255146590845531070931791133)
  ·
    refine ⟨95679971567074151599421675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255146590845531070931791133 95679971567074151599421675)
    ·
      refine ⟨143519957350611227399132513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95679971567074151599421675 143519957350611227399132513)
      ·
        refine ⟨107639968012958420549349385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143519957350611227399132513 107639968012958420549349385)
        ·
          refine ⟨80729976009718815412012039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107639968012958420549349385 80729976009718815412012039)
          ·
            refine ⟨121094964014578223118018059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80729976009718815412012039 121094964014578223118018059)
            ·
              refine ⟨181642446021867334677027089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121094964014578223118018059 181642446021867334677027089)
              ·
                refine ⟨136231834516400501007770317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181642446021867334677027089 136231834516400501007770317)
                ·
                  refine ⟨51086937943650187877913869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136231834516400501007770317 51086937943650187877913869)
                  ·
                    refine ⟨19157601728868820454217701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51086937943650187877913869 19157601728868820454217701)
                    ·
                      refine ⟨3592050324162903835165819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19157601728868820454217701 3592050324162903835165819)
                      ·
                        rfl

theorem cell23_6995493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_6995493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995493 prefixEnd_6995493 := by exact prefixLift 6995493
  have htrace : WordTrace (prefixWord ++ tailWord_6995493) baseStart_6995493 baseEnd_6995493 := by
    simpa [prefixWord, tailWord_6995493, baseEnd_6995493] using wordTrace_append hprefix tailTrace_6995493
  have hstable : (prefixWord ++ tailWord_6995493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995493).length < 2 ^ (prefixWord ++ tailWord_6995493).sum := by decide
  have hdescent : baseEnd_6995493 < baseStart_6995493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995530 : List Nat := [3, 1, 2, 1, 1, 3, 3, 1, 1, 4, 3]
def baseStart_6995530 : Nat := 118140960795 + 6995530 * 2 ^ 59
def prefixEnd_6995530 : Nat := 4983230072969 + 3 ^ 40 * 6995530 * 2
def baseEnd_6995530 : Nat := 3592069322947120190403149

theorem tailTrace_6995530 : CollatzResearch.WordTrace tailWord_6995530 prefixEnd_6995530 3592069322947120190403149 := by
  unfold tailWord_6995530
  simp only [CollatzResearch.WordTrace]
  refine ⟨63786985086599256562722011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170098626897598017500592029 63786985086599256562722011)
  ·
    refine ⟨95680477629898884844083017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63786985086599256562722011 95680477629898884844083017)
    ·
      refine ⟨71760358222424163633062263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95680477629898884844083017 71760358222424163633062263)
      ·
        refine ⟨107640537333636245449593395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71760358222424163633062263 107640537333636245449593395)
        ·
          refine ⟨161460806000454368174390093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107640537333636245449593395 161460806000454368174390093)
          ·
            refine ⟨60547802250170388065396285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161460806000454368174390093 60547802250170388065396285)
            ·
              refine ⟨22705425843813895524523607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60547802250170388065396285 22705425843813895524523607)
              ·
                refine ⟨34058138765720843286785411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22705425843813895524523607 34058138765720843286785411)
                ·
                  refine ⟨51087208148581264930178117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34058138765720843286785411 51087208148581264930178117)
                  ·
                    refine ⟨9578851527858987174408397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51087208148581264930178117 9578851527858987174408397)
                    ·
                      refine ⟨3592069322947120190403149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9578851527858987174408397 3592069322947120190403149)
                      ·
                        rfl

theorem cell23_6995530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_6995530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995530 prefixEnd_6995530 := by exact prefixLift 6995530
  have htrace : WordTrace (prefixWord ++ tailWord_6995530) baseStart_6995530 baseEnd_6995530 := by
    simpa [prefixWord, tailWord_6995530, baseEnd_6995530] using wordTrace_append hprefix tailTrace_6995530
  have hstable : (prefixWord ++ tailWord_6995530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995530).length < 2 ^ (prefixWord ++ tailWord_6995530).sum := by decide
  have hdescent : baseEnd_6995530 < baseStart_6995530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995553 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 1, 1, 8]
def baseStart_6995553 : Nat := 118140960795 + 6995553 * 2 ^ 59
def prefixEnd_6995553 : Nat := 4983230072969 + 3 ^ 40 * 6995553 * 2
def baseEnd_6995553 : Nat := 3592081133002173600415543

theorem tailTrace_6995553 : CollatzResearch.WordTrace tailWord_6995553 prefixEnd_6995553 3592081133002173600415543 := by
  unfold tailWord_6995553
  simp only [CollatzResearch.WordTrace]
  refine ⟨255148779225313701178975313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170099186150209134119316875 255148779225313701178975313)
  ·
    refine ⟨191361584418985275884231485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255148779225313701178975313 191361584418985275884231485)
    ·
      refine ⟨71760594157119478456586807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191361584418985275884231485 71760594157119478456586807)
      ·
        refine ⟨107640891235679217684880211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71760594157119478456586807 107640891235679217684880211)
        ·
          refine ⟨161461336853518826527320317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107640891235679217684880211 161461336853518826527320317)
          ·
            refine ⟨60548001320069559947745119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161461336853518826527320317 60548001320069559947745119)
            ·
              refine ⟨90822001980104339921617679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60548001320069559947745119 90822001980104339921617679)
              ·
                refine ⟨136233002970156509882426519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90822001980104339921617679 136233002970156509882426519)
                ·
                  refine ⟨204349504455234764823639779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136233002970156509882426519 204349504455234764823639779)
                  ·
                    refine ⟨306524256682852147235459669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 204349504455234764823639779 306524256682852147235459669)
                    ·
                      refine ⟨3592081133002173600415543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 306524256682852147235459669 3592081133002173600415543)
                      ·
                        rfl

theorem cell23_6995553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_6995553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995553 prefixEnd_6995553 := by exact prefixLift 6995553
  have htrace : WordTrace (prefixWord ++ tailWord_6995553) baseStart_6995553 baseEnd_6995553 := by
    simpa [prefixWord, tailWord_6995553, baseEnd_6995553] using wordTrace_append hprefix tailTrace_6995553
  have hstable : (prefixWord ++ tailWord_6995553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995553).length < 2 ^ (prefixWord ++ tailWord_6995553).sum := by decide
  have hdescent : baseEnd_6995553 < baseStart_6995553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995577 : List Nat := [1, 2, 1, 3, 3, 1, 1, 4, 3, 1, 3]
def baseStart_6995577 : Nat := 118140960795 + 6995577 * 2 ^ 59
def prefixEnd_6995577 : Nat := 4983230072969 + 3 ^ 40 * 6995577 * 2
def baseEnd_6995577 : Nat := 3592093456537881506515433

theorem tailTrace_6995577 : CollatzResearch.WordTrace tailWord_6995577 prefixEnd_6995577 3592093456537881506515433 := by
  unfold tailWord_6995577
  simp only [CollatzResearch.WordTrace]
  refine ⟨255149654577226753277848985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170099769718151168851899323 255149654577226753277848985)
  ·
    refine ⟨191362240932920064958386739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255149654577226753277848985 191362240932920064958386739)
    ·
      refine ⟨287043361399380097437580109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191362240932920064958386739 287043361399380097437580109)
      ·
        refine ⟨107641260524767536539092541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287043361399380097437580109 107641260524767536539092541)
        ·
          refine ⟨40365472696787826202159703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107641260524767536539092541 40365472696787826202159703)
          ·
            refine ⟨60548209045181739303239555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40365472696787826202159703 60548209045181739303239555)
            ·
              refine ⟨90822313567772608954859333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60548209045181739303239555 90822313567772608954859333)
              ·
                refine ⟨17029183793957364179036125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90822313567772608954859333 17029183793957364179036125)
                ·
                  refine ⟨6385943922734011567138547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17029183793957364179036125 6385943922734011567138547)
                  ·
                    refine ⟨9578915884101017350707821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6385943922734011567138547 9578915884101017350707821)
                    ·
                      refine ⟨3592093456537881506515433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9578915884101017350707821 3592093456537881506515433)
                      ·
                        rfl

theorem cell23_6995577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_6995577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995577 prefixEnd_6995577 := by exact prefixLift 6995577
  have htrace : WordTrace (prefixWord ++ tailWord_6995577) baseStart_6995577 baseEnd_6995577 := by
    simpa [prefixWord, tailWord_6995577, baseEnd_6995577] using wordTrace_append hprefix tailTrace_6995577
  have hstable : (prefixWord ++ tailWord_6995577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995577).length < 2 ^ (prefixWord ++ tailWord_6995577).sum := by decide
  have hdescent : baseEnd_6995577 < baseStart_6995577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995587 : List Nat := [1, 1, 1, 3, 3, 1, 1, 5, 2, 3, 2]
def baseStart_6995587 : Nat := 118140960795 + 6995587 * 2 ^ 59
def prefixEnd_6995587 : Nat := 4983230072969 + 3 ^ 40 * 6995587 * 2
def baseEnd_6995587 : Nat := 3592098591344426467390387

theorem tailTrace_6995587 : CollatzResearch.WordTrace tailWord_6995587 prefixEnd_6995587 3592098591344426467390387 := by
  unfold tailWord_6995587
  simp only [CollatzResearch.WordTrace]
  refine ⟨255150019307190524985713015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170100012871460349990475343 255150019307190524985713015)
  ·
    refine ⟨382725028960785787478569523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255150019307190524985713015 382725028960785787478569523)
    ·
      refine ⟨574087543441178681217854285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382725028960785787478569523 574087543441178681217854285)
      ·
        refine ⟨215282828790442005456695357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 574087543441178681217854285 215282828790442005456695357)
        ·
          refine ⟨80731060796415752046260759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215282828790442005456695357 80731060796415752046260759)
          ·
            refine ⟨121096591194623628069391139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80731060796415752046260759 121096591194623628069391139)
            ·
              refine ⟨181644886791935442104086709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121096591194623628069391139 181644886791935442104086709)
              ·
                refine ⟨17029208136743947697258129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181644886791935442104086709 17029208136743947697258129)
                ·
                  refine ⟨12771906102557960772943597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17029208136743947697258129 12771906102557960772943597)
                  ·
                    refine ⟨4789464788459235289853849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12771906102557960772943597 4789464788459235289853849)
                    ·
                      refine ⟨3592098591344426467390387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4789464788459235289853849 3592098591344426467390387)
                      ·
                        rfl

theorem cell23_6995587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 3, 2].length) (baseStart_6995587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995587 prefixEnd_6995587 := by exact prefixLift 6995587
  have htrace : WordTrace (prefixWord ++ tailWord_6995587) baseStart_6995587 baseEnd_6995587 := by
    simpa [prefixWord, tailWord_6995587, baseEnd_6995587] using wordTrace_append hprefix tailTrace_6995587
  have hstable : (prefixWord ++ tailWord_6995587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995587).length < 2 ^ (prefixWord ++ tailWord_6995587).sum := by decide
  have hdescent : baseEnd_6995587 < baseStart_6995587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995588 : List Nat := [2, 3, 2, 1, 5, 1, 1, 3, 1, 4]
def baseStart_6995588 : Nat := 118140960795 + 6995588 * 2 ^ 59
def prefixEnd_6995588 : Nat := 4983230072969 + 3 ^ 40 * 6995588 * 2
def baseEnd_6995588 : Nat := 1197366368275026987825961

theorem tailTrace_6995588 : CollatzResearch.WordTrace tailWord_6995588 prefixEnd_6995588 1197366368275026987825961 := by
  unfold tailWord_6995588
  simp only [CollatzResearch.WordTrace]
  refine ⟨127575027890093451078249709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170100037186791268104332945 127575027890093451078249709)
  ·
    refine ⟨47840635458785044154343641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127575027890093451078249709 47840635458785044154343641)
    ·
      refine ⟨35880476594088783115757731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47840635458785044154343641 35880476594088783115757731)
      ·
        refine ⟨53820714891133174673636597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35880476594088783115757731 53820714891133174673636597)
        ·
          refine ⟨5045692021043735125653431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53820714891133174673636597 5045692021043735125653431)
          ·
            refine ⟨7568538031565602688480147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5045692021043735125653431 7568538031565602688480147)
            ·
              refine ⟨11352807047348404032720221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7568538031565602688480147 11352807047348404032720221)
              ·
                refine ⟨4257302642755651512270083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11352807047348404032720221 4257302642755651512270083)
                ·
                  refine ⟨6385953964133477268405125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4257302642755651512270083 6385953964133477268405125)
                  ·
                    refine ⟨1197366368275026987825961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6385953964133477268405125 1197366368275026987825961)
                    ·
                      rfl

theorem cell23_6995588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_6995588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995588 prefixEnd_6995588 := by exact prefixLift 6995588
  have htrace : WordTrace (prefixWord ++ tailWord_6995588) baseStart_6995588 baseEnd_6995588 := by
    simpa [prefixWord, tailWord_6995588, baseEnd_6995588] using wordTrace_append hprefix tailTrace_6995588
  have hstable : (prefixWord ++ tailWord_6995588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995588).length < 2 ^ (prefixWord ++ tailWord_6995588).sum := by decide
  have hdescent : baseEnd_6995588 < baseStart_6995588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995618 : List Nat := [3, 3, 1, 4, 2, 1, 2, 1, 6]
def baseStart_6995618 : Nat := 118140960795 + 6995618 * 2 ^ 59
def prefixEnd_6995618 : Nat := 4983230072969 + 3 ^ 40 * 6995618 * 2
def baseEnd_6995618 : Nat := 399123834360523982900305

theorem tailTrace_6995618 : CollatzResearch.WordTrace tailWord_6995618 prefixEnd_6995618 399123834360523982900305 := by
  unfold tailWord_6995618
  simp only [CollatzResearch.WordTrace]
  refine ⟨63787787492519554320022877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170100766646718811520061005 63787787492519554320022877)
  ·
    refine ⟨23920420309694832870008579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63787787492519554320022877 23920420309694832870008579)
    ·
      refine ⟨35880630464542249305012869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23920420309694832870008579 35880630464542249305012869)
      ·
        refine ⟨6727618212101671744689913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35880630464542249305012869 6727618212101671744689913)
        ·
          refine ⟨5045713659076253808517435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6727618212101671744689913 5045713659076253808517435)
          ·
            refine ⟨7568570488614380712776153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5045713659076253808517435 7568570488614380712776153)
            ·
              refine ⟨5676427866460785534582115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7568570488614380712776153 5676427866460785534582115)
              ·
                refine ⟨8514641799691178301873173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5676427866460785534582115 8514641799691178301873173)
                ·
                  refine ⟨399123834360523982900305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8514641799691178301873173 399123834360523982900305)
                  ·
                    rfl

theorem cell23_6995618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_6995618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995618 prefixEnd_6995618 := by exact prefixLift 6995618
  have htrace : WordTrace (prefixWord ++ tailWord_6995618) baseStart_6995618 baseEnd_6995618 := by
    simpa [prefixWord, tailWord_6995618, baseEnd_6995618] using wordTrace_append hprefix tailTrace_6995618
  have hstable : (prefixWord ++ tailWord_6995618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995618).length < 2 ^ (prefixWord ++ tailWord_6995618).sum := by decide
  have hdescent : baseEnd_6995618 < baseStart_6995618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995634 : List Nat := [3, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2]
def baseStart_6995634 : Nat := 118140960795 + 6995634 * 2 ^ 59
def prefixEnd_6995634 : Nat := 4983230072969 + 3 ^ 40 * 6995634 * 2
def baseEnd_6995634 : Nat := 3592122724935187783502671

theorem tailTrace_6995634 : CollatzResearch.WordTrace tailWord_6995634 prefixEnd_6995634 3592122724935187783502671 := by
  unfold tailWord_6995634
  simp only [CollatzResearch.WordTrace]
  refine ⟨63787933384505063003168489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170101155692013501341782637 63787933384505063003168489)
  ·
    refine ⟨47840950038378797252376367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63787933384505063003168489 47840950038378797252376367)
    ·
      refine ⟨71761425057568195878564551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47840950038378797252376367 71761425057568195878564551)
      ·
        refine ⟨107642137586352293817846827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71761425057568195878564551 107642137586352293817846827)
        ·
          refine ⟨161463206379528440726770241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107642137586352293817846827 161463206379528440726770241)
          ·
            refine ⟨121097404784646330545077681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161463206379528440726770241 121097404784646330545077681)
            ·
              refine ⟨90823053588484747908808261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121097404784646330545077681 90823053588484747908808261)
              ·
                refine ⟨17029322547840890232901549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90823053588484747908808261 17029322547840890232901549)
                ·
                  refine ⟨6385995955440333837338081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17029322547840890232901549 6385995955440333837338081)
                  ·
                    refine ⟨4789496966580250378003561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6385995955440333837338081 4789496966580250378003561)
                    ·
                      refine ⟨3592122724935187783502671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4789496966580250378003561 3592122724935187783502671)
                      ·
                        rfl

theorem cell23_6995634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2].length) (baseStart_6995634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995634 prefixEnd_6995634 := by exact prefixLift 6995634
  have htrace : WordTrace (prefixWord ++ tailWord_6995634) baseStart_6995634 baseEnd_6995634 := by
    simpa [prefixWord, tailWord_6995634, baseEnd_6995634] using wordTrace_append hprefix tailTrace_6995634
  have hstable : (prefixWord ++ tailWord_6995634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995634).length < 2 ^ (prefixWord ++ tailWord_6995634).sum := by decide
  have hdescent : baseEnd_6995634 < baseStart_6995634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995638 : List Nat := [5, 1, 3, 1, 1, 2, 2, 1, 2, 3, 2]
def baseStart_6995638 : Nat := 118140960795 + 6995638 * 2 ^ 59
def prefixEnd_6995638 : Nat := 4983230072969 + 3 ^ 40 * 6995638 * 2
def baseEnd_6995638 : Nat := 3592124778857805767852653

theorem tailTrace_6995638 : CollatzResearch.WordTrace tailWord_6995638 prefixEnd_6995638 3592124778857805767852653 := by
  unfold tailWord_6995638
  simp only [CollatzResearch.WordTrace]
  refine ⟨15946992464375360043488723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170101252953337173797213045 15946992464375360043488723)
  ·
    refine ⟨23920488696563040065233085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15946992464375360043488723 23920488696563040065233085)
    ·
      refine ⟨8970183261211140024462407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23920488696563040065233085 8970183261211140024462407)
      ·
        refine ⟨13455274891816710036693611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8970183261211140024462407 13455274891816710036693611)
        ·
          refine ⟨20182912337725065055040417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13455274891816710036693611 20182912337725065055040417)
          ·
            refine ⟨15137184253293798791280313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20182912337725065055040417 15137184253293798791280313)
            ·
              refine ⟨11352888189970349093460235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15137184253293798791280313 11352888189970349093460235)
              ·
                refine ⟨17029332284955523640190353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11352888189970349093460235 17029332284955523640190353)
                ·
                  refine ⟨12771999213716642730142765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17029332284955523640190353 12771999213716642730142765)
                  ·
                    refine ⟨4789499705143741023803537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12771999213716642730142765 4789499705143741023803537)
                    ·
                      refine ⟨3592124778857805767852653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4789499705143741023803537 3592124778857805767852653)
                      ·
                        rfl

theorem cell23_6995638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_6995638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995638 prefixEnd_6995638 := by exact prefixLift 6995638
  have htrace : WordTrace (prefixWord ++ tailWord_6995638) baseStart_6995638 baseEnd_6995638 := by
    simpa [prefixWord, tailWord_6995638, baseEnd_6995638] using wordTrace_append hprefix tailTrace_6995638
  have hstable : (prefixWord ++ tailWord_6995638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995638).length < 2 ^ (prefixWord ++ tailWord_6995638).sum := by decide
  have hdescent : baseEnd_6995638 < baseStart_6995638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995661 : List Nat := [1, 6, 2, 1, 1, 1, 1, 4, 2, 4]
def baseStart_6995661 : Nat := 118140960795 + 6995661 * 2 ^ 59
def prefixEnd_6995661 : Nat := 4983230072969 + 3 ^ 40 * 6995661 * 2
def baseEnd_6995661 : Nat := 1197378862970953059288349

theorem tailTrace_6995661 : CollatzResearch.WordTrace tailWord_6995661 prefixEnd_6995661 1197378862970953059288349 := by
  unfold tailWord_6995661
  simp only [CollatzResearch.WordTrace]
  refine ⟨255152718308922435623906837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170101812205948290415937891 255152718308922435623906837)
  ·
    refine ⟨11960283670730739169870633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 255152718308922435623906837 11960283670730739169870633)
    ·
      refine ⟨8970212753048054377402975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11960283670730739169870633 8970212753048054377402975)
      ·
        refine ⟨13455319129572081566104463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8970212753048054377402975 13455319129572081566104463)
        ·
          refine ⟨20182978694358122349156695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13455319129572081566104463 20182978694358122349156695)
          ·
            refine ⟨30274468041537183523735043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20182978694358122349156695 30274468041537183523735043)
            ·
              refine ⟨45411702062305775285602565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30274468041537183523735043 45411702062305775285602565)
              ·
                refine ⟨8514694136682332866050481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45411702062305775285602565 8514694136682332866050481)
                ·
                  refine ⟨6386020602511749649537861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8514694136682332866050481 6386020602511749649537861)
                  ·
                    refine ⟨1197378862970953059288349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6386020602511749649537861 1197378862970953059288349)
                    ·
                      rfl

theorem cell23_6995661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_6995661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995661 prefixEnd_6995661 := by exact prefixLift 6995661
  have htrace : WordTrace (prefixWord ++ tailWord_6995661) baseStart_6995661 baseEnd_6995661 := by
    simpa [prefixWord, tailWord_6995661, baseEnd_6995661] using wordTrace_append hprefix tailTrace_6995661
  have hstable : (prefixWord ++ tailWord_6995661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995661).length < 2 ^ (prefixWord ++ tailWord_6995661).sum := by decide
  have hdescent : baseEnd_6995661 < baseStart_6995661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995684 : List Nat := [2, 3, 1, 1, 1, 3, 1, 5, 2, 1, 3]
def baseStart_6995684 : Nat := 118140960795 + 6995684 * 2 ^ 59
def prefixEnd_6995684 : Nat := 4983230072969 + 3 ^ 40 * 6995684 * 2
def baseEnd_6995684 : Nat := 3592148398967912587877441

theorem tailTrace_6995684 : CollatzResearch.WordTrace tailWord_6995684 prefixEnd_6995684 3592148398967912587877441 := by
  unfold tailWord_6995684
  simp only [CollatzResearch.WordTrace]
  refine ⟨127576778593919555275997053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170102371458559407034662737 127576778593919555275997053)
  ·
    refine ⟨47841291972719833228498895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127576778593919555275997053 47841291972719833228498895)
    ·
      refine ⟨71761937959079749842748343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47841291972719833228498895 71761937959079749842748343)
      ·
        refine ⟨107642906938619624764122515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71761937959079749842748343 107642906938619624764122515)
        ·
          refine ⟨161464360407929437146183773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107642906938619624764122515 161464360407929437146183773)
          ·
            refine ⟨60549135152973538929818915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161464360407929437146183773 60549135152973538929818915)
            ·
              refine ⟨90823702729460308394728373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60549135152973538929818915 90823702729460308394728373)
              ·
                refine ⟨8514722130886903912005785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90823702729460308394728373 8514722130886903912005785)
                ·
                  refine ⟨6386041598165177934004339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8514722130886903912005785 6386041598165177934004339)
                  ·
                    refine ⟨9579062397247766901006509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6386041598165177934004339 9579062397247766901006509)
                    ·
                      refine ⟨3592148398967912587877441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9579062397247766901006509 3592148398967912587877441)
                      ·
                        rfl

theorem cell23_6995684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_6995684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995684 prefixEnd_6995684 := by exact prefixLift 6995684
  have htrace : WordTrace (prefixWord ++ tailWord_6995684) baseStart_6995684 baseEnd_6995684 := by
    simpa [prefixWord, tailWord_6995684, baseEnd_6995684] using wordTrace_append hprefix tailTrace_6995684
  have hstable : (prefixWord ++ tailWord_6995684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995684).length < 2 ^ (prefixWord ++ tailWord_6995684).sum := by decide
  have hdescent : baseEnd_6995684 < baseStart_6995684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995694 : List Nat := [4, 1, 2, 1, 1, 2, 1, 3, 3, 3, 2]
def baseStart_6995694 : Nat := 118140960795 + 6995694 * 2 ^ 59
def prefixEnd_6995694 : Nat := 4983230072969 + 3 ^ 40 * 6995694 * 2
def baseEnd_6995694 : Nat := 3592153533774457548752395

theorem tailTrace_6995694 : CollatzResearch.WordTrace tailWord_6995694 prefixEnd_6995694 3592153533774457548752395 := by
  unfold tailWord_6995694
  simp only [CollatzResearch.WordTrace]
  refine ⟨31894240239725360282482267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170102614611868588173238757 31894240239725360282482267)
  ·
    refine ⟨47841360359588040423723401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31894240239725360282482267 47841360359588040423723401)
    ·
      refine ⟨35881020269691030317792551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47841360359588040423723401 35881020269691030317792551)
      ·
        refine ⟨53821530404536545476688827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35881020269691030317792551 53821530404536545476688827)
        ·
          refine ⟨80732295606804818215033241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53821530404536545476688827 80732295606804818215033241)
          ·
            refine ⟨60549221705103613661274931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80732295606804818215033241 60549221705103613661274931)
            ·
              refine ⟨90823832557655420491912397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60549221705103613661274931 90823832557655420491912397)
              ·
                refine ⟨34058937209120782684467149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90823832557655420491912397 34058937209120782684467149)
                ·
                  refine ⟨12772101453420293506675181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34058937209120782684467149 12772101453420293506675181)
                  ·
                    refine ⟨4789538045032610065003193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12772101453420293506675181 4789538045032610065003193)
                    ·
                      refine ⟨3592153533774457548752395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4789538045032610065003193 3592153533774457548752395)
                      ·
                        rfl

theorem cell23_6995694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_6995694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995694 prefixEnd_6995694 := by exact prefixLift 6995694
  have htrace : WordTrace (prefixWord ++ tailWord_6995694) baseStart_6995694 baseEnd_6995694 := by
    simpa [prefixWord, tailWord_6995694, baseEnd_6995694] using wordTrace_append hprefix tailTrace_6995694
  have hstable : (prefixWord ++ tailWord_6995694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995694).length < 2 ^ (prefixWord ++ tailWord_6995694).sum := by decide
  have hdescent : baseEnd_6995694 < baseStart_6995694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995707 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 3, 4, 2]
def baseStart_6995707 : Nat := 118140960795 + 6995707 * 2 ^ 59
def prefixEnd_6995707 : Nat := 4983230072969 + 3 ^ 40 * 6995707 * 2
def baseEnd_6995707 : Nat := 3592160209022965997889835

theorem tailTrace_6995707 : CollatzResearch.WordTrace tailWord_6995707 prefixEnd_6995707 3592160209022965997889835 := by
  unfold tailWord_6995707
  simp only [CollatzResearch.WordTrace]
  refine ⟨255154396066755785480081375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170102930711170523653387583 255154396066755785480081375)
  ·
    refine ⟨382731594100133678220122063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255154396066755785480081375 382731594100133678220122063)
    ·
      refine ⟨574097391150200517330183095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382731594100133678220122063 574097391150200517330183095)
      ·
        refine ⟨861146086725300775995274643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574097391150200517330183095 861146086725300775995274643)
        ·
          refine ⟨1291719130087951163992911965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 861146086725300775995274643 1291719130087951163992911965)
          ·
            refine ⟨484394673782981686497341987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1291719130087951163992911965 484394673782981686497341987)
            ·
              refine ⟨726592010674472529746012981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484394673782981686497341987 726592010674472529746012981)
              ·
                refine ⟨68118001000731799663688717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 726592010674472529746012981 68118001000731799663688717)
                ·
                  refine ⟨25544250375274424873883269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68118001000731799663688717 25544250375274424873883269)
                  ·
                    refine ⟨4789546945363954663853113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25544250375274424873883269 4789546945363954663853113)
                    ·
                      refine ⟨3592160209022965997889835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4789546945363954663853113 3592160209022965997889835)
                      ·
                        rfl

theorem cell23_6995707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 4, 2].length) (baseStart_6995707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995707 prefixEnd_6995707 := by exact prefixLift 6995707
  have htrace : WordTrace (prefixWord ++ tailWord_6995707) baseStart_6995707 baseEnd_6995707 := by
    simpa [prefixWord, tailWord_6995707, baseEnd_6995707] using wordTrace_append hprefix tailTrace_6995707
  have hstable : (prefixWord ++ tailWord_6995707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995707).length < 2 ^ (prefixWord ++ tailWord_6995707).sum := by decide
  have hdescent : baseEnd_6995707 < baseStart_6995707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995711 : List Nat := [1, 1, 2, 2, 1, 3, 6, 1, 1, 3, 2]
def baseStart_6995711 : Nat := 118140960795 + 6995711 * 2 ^ 59
def prefixEnd_6995711 : Nat := 4983230072969 + 3 ^ 40 * 6995711 * 2
def baseEnd_6995711 : Nat := 3592162262945583982239817

theorem tailTrace_6995711 : CollatzResearch.WordTrace tailWord_6995711 prefixEnd_6995711 3592162262945583982239817 := by
  unfold tailWord_6995711
  simp only [CollatzResearch.WordTrace]
  refine ⟨255154541958741294163226987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170103027972494196108817991 255154541958741294163226987)
  ·
    refine ⟨382731812938111941244840481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255154541958741294163226987 382731812938111941244840481)
    ·
      refine ⟨287048859703583955933630361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382731812938111941244840481 287048859703583955933630361)
      ·
        refine ⟨215286644777687966950222771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287048859703583955933630361 215286644777687966950222771)
        ·
          refine ⟨322929967166531950425334157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215286644777687966950222771 322929967166531950425334157)
          ·
            refine ⟨121098737687449481409500309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 322929967166531950425334157 121098737687449481409500309)
            ·
              refine ⟨5676503329099194441070327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121098737687449481409500309 5676503329099194441070327)
              ·
                refine ⟨8514754993648791661605491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5676503329099194441070327 8514754993648791661605491)
                ·
                  refine ⟨12772132490473187492408237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8514754993648791661605491 12772132490473187492408237)
                  ·
                    refine ⟨4789549683927445309653089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12772132490473187492408237 4789549683927445309653089)
                    ·
                      refine ⟨3592162262945583982239817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4789549683927445309653089 3592162262945583982239817)
                      ·
                        rfl

theorem cell23_6995711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 1, 3, 2].length) (baseStart_6995711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995711 prefixEnd_6995711 := by exact prefixLift 6995711
  have htrace : WordTrace (prefixWord ++ tailWord_6995711) baseStart_6995711 baseEnd_6995711 := by
    simpa [prefixWord, tailWord_6995711, baseEnd_6995711] using wordTrace_append hprefix tailTrace_6995711
  have hstable : (prefixWord ++ tailWord_6995711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995711).length < 2 ^ (prefixWord ++ tailWord_6995711).sum := by decide
  have hdescent : baseEnd_6995711 < baseStart_6995711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995817 : List Nat := [1, 2, 1, 1, 1, 3, 1, 5, 1, 4, 3]
def baseStart_6995817 : Nat := 118140960795 + 6995817 * 2 ^ 59
def prefixEnd_6995817 : Nat := 4983230072969 + 3 ^ 40 * 6995817 * 2
def baseEnd_6995817 : Nat := 3592216691894960567514329

theorem tailTrace_6995817 : CollatzResearch.WordTrace tailWord_6995817 prefixEnd_6995817 3592216691894960567514329 := by
  unfold tailWord_6995817
  simp only [CollatzResearch.WordTrace]
  refine ⟨255158408096357274266585705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170105605397571516177723803 255158408096357274266585705)
  ·
    refine ⟨191368806072267955699939279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255158408096357274266585705 191368806072267955699939279)
    ·
      refine ⟨287053209108401933549908919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191368806072267955699939279 287053209108401933549908919)
      ·
        refine ⟨430579813662602900324863379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287053209108401933549908919 430579813662602900324863379)
        ·
          refine ⟨645869720493904350487295069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430579813662602900324863379 645869720493904350487295069)
          ·
            refine ⟨242201145185214131432735651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 645869720493904350487295069 242201145185214131432735651)
            ·
              refine ⟨363301717777821197149103477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242201145185214131432735651 363301717777821197149103477)
              ·
                refine ⟨34059536041670737232728451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 363301717777821197149103477 34059536041670737232728451)
                ·
                  refine ⟨51089304062506105849092677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34059536041670737232728451 51089304062506105849092677)
                  ·
                    refine ⟨9579244511719894846704877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51089304062506105849092677 9579244511719894846704877)
                    ·
                      refine ⟨3592216691894960567514329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9579244511719894846704877 3592216691894960567514329)
                      ·
                        rfl

theorem cell23_6995817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 4, 3].length) (baseStart_6995817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995817 prefixEnd_6995817 := by exact prefixLift 6995817
  have htrace : WordTrace (prefixWord ++ tailWord_6995817) baseStart_6995817 baseEnd_6995817 := by
    simpa [prefixWord, tailWord_6995817, baseEnd_6995817] using wordTrace_append hprefix tailTrace_6995817
  have hstable : (prefixWord ++ tailWord_6995817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995817).length < 2 ^ (prefixWord ++ tailWord_6995817).sum := by decide
  have hdescent : baseEnd_6995817 < baseStart_6995817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995834 : List Nat := [3, 1, 1, 1, 1, 1, 6, 2, 2, 2, 3]
def baseStart_6995834 : Nat := 118140960795 + 6995834 * 2 ^ 59
def prefixEnd_6995834 : Nat := 4983230072969 + 3 ^ 40 * 6995834 * 2
def baseEnd_6995834 : Nat := 3592225421066087001001751

theorem tailTrace_6995834 : CollatzResearch.WordTrace tailWord_6995834 prefixEnd_6995834 3592225421066087001001751 := by
  unfold tailWord_6995834
  simp only [CollatzResearch.WordTrace]
  refine ⟨63789757034323921542488639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170106018758197124113303037 63789757034323921542488639)
  ·
    refine ⟨95684635551485882313732959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63789757034323921542488639 95684635551485882313732959)
    ·
      refine ⟨143526953327228823470599439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95684635551485882313732959 143526953327228823470599439)
      ·
        refine ⟨215290429990843235205899159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143526953327228823470599439 215290429990843235205899159)
        ·
          refine ⟨322935644986264852808848739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215290429990843235205899159 322935644986264852808848739)
          ·
            refine ⟨484403467479397279213273109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322935644986264852808848739 484403467479397279213273109)
            ·
              refine ⟨22706412538096747463122177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 484403467479397279213273109 22706412538096747463122177)
              ·
                refine ⟨17029809403572560597341633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22706412538096747463122177 17029809403572560597341633)
                ·
                  refine ⟨12772357052679420448006225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17029809403572560597341633 12772357052679420448006225)
                  ·
                    refine ⟨9579267789509565336004669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12772357052679420448006225 9579267789509565336004669)
                    ·
                      refine ⟨3592225421066087001001751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9579267789509565336004669 3592225421066087001001751)
                      ·
                        rfl

theorem cell23_6995834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 2, 2, 3].length) (baseStart_6995834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995834 prefixEnd_6995834 := by exact prefixLift 6995834
  have htrace : WordTrace (prefixWord ++ tailWord_6995834) baseStart_6995834 baseEnd_6995834 := by
    simpa [prefixWord, tailWord_6995834, baseEnd_6995834] using wordTrace_append hprefix tailTrace_6995834
  have hstable : (prefixWord ++ tailWord_6995834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995834).length < 2 ^ (prefixWord ++ tailWord_6995834).sum := by decide
  have hdescent : baseEnd_6995834 < baseStart_6995834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995862 : List Nat := [5, 3, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_6995862 : Nat := 118140960795 + 6995862 * 2 ^ 59
def prefixEnd_6995862 : Nat := 4983230072969 + 3 ^ 40 * 6995862 * 2
def baseEnd_6995862 : Nat := 1197413266174804297150541

theorem tailTrace_6995862 : CollatzResearch.WordTrace tailWord_6995862 prefixEnd_6995862 1197413266174804297150541 := by
  unfold tailWord_6995862
  simp only [CollatzResearch.WordTrace]
  refine ⟨15947503086324640434498365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170106699587462831301315893 15947503086324640434498365)
  ·
    refine ⟨5980313657371740162936887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15947503086324640434498365 5980313657371740162936887)
    ·
      refine ⟨8970470486057610244405331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5980313657371740162936887 8970470486057610244405331)
      ·
        refine ⟨13455705729086415366607997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8970470486057610244405331 13455705729086415366607997)
        ·
          refine ⟨5045889648407405762477999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13455705729086415366607997 5045889648407405762477999)
          ·
            refine ⟨7568834472611108643716999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5045889648407405762477999 7568834472611108643716999)
            ·
              refine ⟨11353251708916662965575499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7568834472611108643716999 11353251708916662965575499)
              ·
                refine ⟨17029877563374994448363249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11353251708916662965575499 17029877563374994448363249)
                ·
                  refine ⟨12772408172531245836272437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17029877563374994448363249 12772408172531245836272437)
                  ·
                    refine ⟨1197413266174804297150541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12772408172531245836272437 1197413266174804297150541)
                    ·
                      rfl

theorem cell23_6995862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_6995862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995862 prefixEnd_6995862 := by exact prefixLift 6995862
  have htrace : WordTrace (prefixWord ++ tailWord_6995862) baseStart_6995862 baseEnd_6995862 := by
    simpa [prefixWord, tailWord_6995862, baseEnd_6995862] using wordTrace_append hprefix tailTrace_6995862
  have hstable : (prefixWord ++ tailWord_6995862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995862).length < 2 ^ (prefixWord ++ tailWord_6995862).sum := by decide
  have hdescent : baseEnd_6995862 < baseStart_6995862 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995868 : List Nat := [2, 2, 3, 3, 1, 3, 1, 1, 2, 2, 3]
def baseStart_6995868 : Nat := 118140960795 + 6995868 * 2 ^ 59
def prefixEnd_6995868 : Nat := 4983230072969 + 3 ^ 40 * 6995868 * 2
def baseEnd_6995868 : Nat := 3592242879408339867976595

theorem tailTrace_6995868 : CollatzResearch.WordTrace tailWord_6995868 prefixEnd_6995868 3592242879408339867976595 := by
  unfold tailWord_6995868
  simp only [CollatzResearch.WordTrace]
  refine ⟨127580134109586254988346129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170106845479448339984461505 127580134109586254988346129)
  ·
    refine ⟨95685100582189691241259597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127580134109586254988346129 95685100582189691241259597)
    ·
      refine ⟨35881912718321134215472349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95685100582189691241259597 35881912718321134215472349)
      ·
        refine ⟨13455717269370425330802131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35881912718321134215472349 13455717269370425330802131)
        ·
          refine ⟨20183575904055637996203197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13455717269370425330802131 20183575904055637996203197)
          ·
            refine ⟨7568840964020864248576199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20183575904055637996203197 7568840964020864248576199)
            ·
              refine ⟨11353261446031296372864299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7568840964020864248576199 11353261446031296372864299)
              ·
                refine ⟨17029892169046944559296449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11353261446031296372864299 17029892169046944559296449)
                ·
                  refine ⟨12772419126785208419472337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17029892169046944559296449 12772419126785208419472337)
                  ·
                    refine ⟨9579314345088906314604253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12772419126785208419472337 9579314345088906314604253)
                    ·
                      refine ⟨3592242879408339867976595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9579314345088906314604253 3592242879408339867976595)
                      ·
                        rfl

theorem cell23_6995868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_6995868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995868 prefixEnd_6995868 := by exact prefixLift 6995868
  have htrace : WordTrace (prefixWord ++ tailWord_6995868) baseStart_6995868 baseEnd_6995868 := by
    simpa [prefixWord, tailWord_6995868, baseEnd_6995868] using wordTrace_append hprefix tailTrace_6995868
  have hstable : (prefixWord ++ tailWord_6995868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995868).length < 2 ^ (prefixWord ++ tailWord_6995868).sum := by decide
  have hdescent : baseEnd_6995868 < baseStart_6995868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995914 : List Nat := [3, 1, 2, 1, 2, 1, 5, 1, 1, 6]
def baseStart_6995914 : Nat := 118140960795 + 6995914 * 2 ^ 59
def prefixEnd_6995914 : Nat := 4983230072969 + 3 ^ 40 * 6995914 * 2
def baseEnd_6995914 : Nat := 1197422166506148896000461

theorem tailTrace_6995914 : CollatzResearch.WordTrace tailWord_6995914 prefixEnd_6995914 1197422166506148896000461 := by
  unfold tailWord_6995914
  simp only [CollatzResearch.WordTrace]
  refine ⟨63790486494251464958216699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170107963984670573221911197 63790486494251464958216699)
  ·
    refine ⟨95685729741377197437325049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63790486494251464958216699 95685729741377197437325049)
    ·
      refine ⟨71764297306032898077993787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95685729741377197437325049 71764297306032898077993787)
      ·
        refine ⟨107646445959049347116990681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71764297306032898077993787 107646445959049347116990681)
        ·
          refine ⟨80734834469287010337743011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107646445959049347116990681 80734834469287010337743011)
          ·
            refine ⟨121102251703930515506614517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80734834469287010337743011 121102251703930515506614517)
            ·
              refine ⟨11353336097243485828745111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121102251703930515506614517 11353336097243485828745111)
              ·
                refine ⟨17030004145865228743117667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11353336097243485828745111 17030004145865228743117667)
                ·
                  refine ⟨25545006218797843114676501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17030004145865228743117667 25545006218797843114676501)
                  ·
                    refine ⟨1197422166506148896000461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25545006218797843114676501 1197422166506148896000461)
                    ·
                      rfl

theorem cell23_6995914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_6995914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995914 prefixEnd_6995914 := by exact prefixLift 6995914
  have htrace : WordTrace (prefixWord ++ tailWord_6995914) baseStart_6995914 baseEnd_6995914 := by
    simpa [prefixWord, tailWord_6995914, baseEnd_6995914] using wordTrace_append hprefix tailTrace_6995914
  have hstable : (prefixWord ++ tailWord_6995914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995914).length < 2 ^ (prefixWord ++ tailWord_6995914).sum := by decide
  have hdescent : baseEnd_6995914 < baseStart_6995914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995921 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 5, 2, 2]
def baseStart_6995921 : Nat := 118140960795 + 6995921 * 2 ^ 59
def prefixEnd_6995921 : Nat := 4983230072969 + 3 ^ 40 * 6995921 * 2
def baseEnd_6995921 : Nat := 3592270093883028160613851

theorem tailTrace_6995921 : CollatzResearch.WordTrace tailWord_6995921 prefixEnd_6995921 3592270093883028160613851 := by
  unfold tailWord_6995921
  simp only [CollatzResearch.WordTrace]
  refine ⟨255162201287980500028371617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170108134191987000018914411 255162201287980500028371617)
  ·
    refine ⟨191371650965985375021278713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255162201287980500028371617 191371650965985375021278713)
    ·
      refine ⟨143528738224489031265959035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191371650965985375021278713 143528738224489031265959035)
      ·
        refine ⟨215293107336733546898938553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143528738224489031265959035 215293107336733546898938553)
        ·
          refine ⟨161469830502550160174203915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215293107336733546898938553 161469830502550160174203915)
          ·
            refine ⟨242204745753825240261305873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161469830502550160174203915 242204745753825240261305873)
            ·
              refine ⟨181653559315368930195979405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242204745753825240261305873 181653559315368930195979405)
              ·
                refine ⟨68120084743263348823492277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181653559315368930195979405 68120084743263348823492277)
                ·
                  refine ⟨6386257944680938952202401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68120084743263348823492277 6386257944680938952202401)
                  ·
                    refine ⟨4789693458510704214151801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6386257944680938952202401 4789693458510704214151801)
                    ·
                      refine ⟨3592270093883028160613851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4789693458510704214151801 3592270093883028160613851)
                      ·
                        rfl

theorem cell23_6995921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 5, 2, 2].length) (baseStart_6995921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995921 prefixEnd_6995921 := by exact prefixLift 6995921
  have htrace : WordTrace (prefixWord ++ tailWord_6995921) baseStart_6995921 baseEnd_6995921 := by
    simpa [prefixWord, tailWord_6995921, baseEnd_6995921] using wordTrace_append hprefix tailTrace_6995921
  have hstable : (prefixWord ++ tailWord_6995921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995921).length < 2 ^ (prefixWord ++ tailWord_6995921).sum := by decide
  have hdescent : baseEnd_6995921 < baseStart_6995921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995924 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 3, 1, 5]
def baseStart_6995924 : Nat := 118140960795 + 6995924 * 2 ^ 59
def prefixEnd_6995924 : Nat := 4983230072969 + 3 ^ 40 * 6995924 * 2
def baseEnd_6995924 : Nat := 3592271634324991648876337

theorem tailTrace_6995924 : CollatzResearch.WordTrace tailWord_6995924 prefixEnd_6995924 3592271634324991648876337 := by
  unfold tailWord_6995924
  simp only [CollatzResearch.WordTrace]
  refine ⟨127581155353484815770365413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170108207137979754360487217 127581155353484815770365413)
  ·
    refine ⟨23921466628778402956943515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127581155353484815770365413 23921466628778402956943515)
    ·
      refine ⟨35882199943167604435415273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23921466628778402956943515 35882199943167604435415273)
      ·
        refine ⟨26911649957375703326561455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35882199943167604435415273 26911649957375703326561455)
        ·
          refine ⟨40367474936063554989842183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26911649957375703326561455 40367474936063554989842183)
          ·
            refine ⟨60551212404095332484763275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40367474936063554989842183 60551212404095332484763275)
            ·
              refine ⟨90826818606142998727144913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60551212404095332484763275 90826818606142998727144913)
              ·
                refine ⟨68120113954607249045358685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90826818606142998727144913 68120113954607249045358685)
                ·
                  refine ⟨25545042732977718392009507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68120113954607249045358685 25545042732977718392009507)
                  ·
                    refine ⟨38317564099466577588014261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25545042732977718392009507 38317564099466577588014261)
                    ·
                      refine ⟨3592271634324991648876337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38317564099466577588014261 3592271634324991648876337)
                      ·
                        rfl

theorem cell23_6995924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_6995924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995924 prefixEnd_6995924 := by exact prefixLift 6995924
  have htrace : WordTrace (prefixWord ++ tailWord_6995924) baseStart_6995924 baseEnd_6995924 := by
    simpa [prefixWord, tailWord_6995924, baseEnd_6995924] using wordTrace_append hprefix tailTrace_6995924
  have hstable : (prefixWord ++ tailWord_6995924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995924).length < 2 ^ (prefixWord ++ tailWord_6995924).sum := by decide
  have hdescent : baseEnd_6995924 < baseStart_6995924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995927 : List Nat := [1, 1, 3, 2, 1, 1, 5, 9]
def baseStart_6995927 : Nat := 118140960795 + 6995927 * 2 ^ 59
def prefixEnd_6995927 : Nat := 4983230072969 + 3 ^ 40 * 6995927 * 2
def baseEnd_6995927 : Nat := 133047154620998338412549

theorem tailTrace_6995927 : CollatzResearch.WordTrace tailWord_6995927 prefixEnd_6995927 133047154620998338412549 := by
  unfold tailWord_6995927
  simp only [CollatzResearch.WordTrace]
  refine ⟨255162420125958763053090035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170108280083972508702060023 255162420125958763053090035)
  ·
    refine ⟨382743630188938144579635053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255162420125958763053090035 382743630188938144579635053)
    ·
      refine ⟨143528861320851804217363145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 382743630188938144579635053 143528861320851804217363145)
      ·
        refine ⟨107646645990638853163022359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143528861320851804217363145 107646645990638853163022359)
        ·
          refine ⟨161469968985958279744533539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107646645990638853163022359 161469968985958279744533539)
          ·
            refine ⟨242204953478937419616800309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161469968985958279744533539 242204953478937419616800309)
            ·
              refine ⟨22706714388650383089075029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 242204953478937419616800309 22706714388650383089075029)
              ·
                refine ⟨133047154620998338412549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22706714388650383089075029 133047154620998338412549)
                ·
                  rfl

theorem cell23_6995927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 9].length) (baseStart_6995927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995927 prefixEnd_6995927 := by exact prefixLift 6995927
  have htrace : WordTrace (prefixWord ++ tailWord_6995927) baseStart_6995927 baseEnd_6995927 := by
    simpa [prefixWord, tailWord_6995927, baseEnd_6995927] using wordTrace_append hprefix tailTrace_6995927
  have hstable : (prefixWord ++ tailWord_6995927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995927).length < 2 ^ (prefixWord ++ tailWord_6995927).sum := by decide
  have hdescent : baseEnd_6995927 < baseStart_6995927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995949 : List Nat := [1, 5, 1, 4, 1, 1, 3, 2, 1, 1, 3]
def baseStart_6995949 : Nat := 118140960795 + 6995949 * 2 ^ 59
def prefixEnd_6995949 : Nat := 4983230072969 + 3 ^ 40 * 6995949 * 2
def baseEnd_6995949 : Nat := 3592284471341354051063723

theorem tailTrace_6995949 : CollatzResearch.WordTrace tailWord_6995949 prefixEnd_6995949 3592284471341354051063723 := by
  unfold tailWord_6995949
  simp only [CollatzResearch.WordTrace]
  refine ⟨255163222531879060810390901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170108815021252707206927267 255163222531879060810390901)
  ·
    refine ⟨23921552112363661950974147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 255163222531879060810390901 23921552112363661950974147)
    ·
      refine ⟨35882328168545492926461221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23921552112363661950974147 35882328168545492926461221)
      ·
        refine ⟨6727936531602279923711479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35882328168545492926461221 6727936531602279923711479)
        ·
          refine ⟨10091904797403419885567219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6727936531602279923711479 10091904797403419885567219)
          ·
            refine ⟨15137857196105129828350829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10091904797403419885567219 15137857196105129828350829)
            ·
              refine ⟨5676696448539423685631561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15137857196105129828350829 5676696448539423685631561)
              ·
                refine ⟨4257522336404567764223671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5676696448539423685631561 4257522336404567764223671)
                ·
                  refine ⟨6386283504606851646335507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4257522336404567764223671 6386283504606851646335507)
                  ·
                    refine ⟨9579425256910277469503261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6386283504606851646335507 9579425256910277469503261)
                    ·
                      refine ⟨3592284471341354051063723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9579425256910277469503261 3592284471341354051063723)
                      ·
                        rfl

theorem cell23_6995949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_6995949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995949 prefixEnd_6995949 := by exact prefixLift 6995949
  have htrace : WordTrace (prefixWord ++ tailWord_6995949) baseStart_6995949 baseEnd_6995949 := by
    simpa [prefixWord, tailWord_6995949, baseEnd_6995949] using wordTrace_append hprefix tailTrace_6995949
  have hstable : (prefixWord ++ tailWord_6995949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995949).length < 2 ^ (prefixWord ++ tailWord_6995949).sum := by decide
  have hdescent : baseEnd_6995949 < baseStart_6995949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995972 : List Nat := [2, 3, 2, 4, 2, 1, 1, 2, 1, 1, 4]
def baseStart_6995972 : Nat := 118140960795 + 6995972 * 2 ^ 59
def prefixEnd_6995972 : Nat := 4983230072969 + 3 ^ 40 * 6995972 * 2
def baseEnd_6995972 : Nat := 3592296281396407461076117

theorem tailTrace_6995972 : CollatzResearch.WordTrace tailWord_6995972 prefixEnd_6995972 3592296281396407461076117 := by
  unfold tailWord_6995972
  simp only [CollatzResearch.WordTrace]
  refine ⟨127582030705397867869239085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170109374273863823825652113 127582030705397867869239085)
  ·
    refine ⟨47843261514524200450964657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127582030705397867869239085 47843261514524200450964657)
    ·
      refine ⟨35882446135893150338223493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47843261514524200450964657 35882446135893150338223493)
      ·
        refine ⟨6727958650479965688416905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35882446135893150338223493 6727958650479965688416905)
        ·
          refine ⟨5045968987859974266312679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6727958650479965688416905 5045968987859974266312679)
          ·
            refine ⟨7568953481789961399469019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5045968987859974266312679 7568953481789961399469019)
            ·
              refine ⟨11353430222684942099203529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7568953481789961399469019 11353430222684942099203529)
              ·
                refine ⟨8515072667013706574402647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11353430222684942099203529 8515072667013706574402647)
                ·
                  refine ⟨12772609000520559861603971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8515072667013706574402647 12772609000520559861603971)
                  ·
                    refine ⟨19158913500780839792405957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12772609000520559861603971 19158913500780839792405957)
                    ·
                      refine ⟨3592296281396407461076117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19158913500780839792405957 3592296281396407461076117)
                      ·
                        rfl

theorem cell23_6995972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_6995972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995972 prefixEnd_6995972 := by exact prefixLift 6995972
  have htrace : WordTrace (prefixWord ++ tailWord_6995972) baseStart_6995972 baseEnd_6995972 := by
    simpa [prefixWord, tailWord_6995972, baseEnd_6995972] using wordTrace_append hprefix tailTrace_6995972
  have hstable : (prefixWord ++ tailWord_6995972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995972).length < 2 ^ (prefixWord ++ tailWord_6995972).sum := by decide
  have hdescent : baseEnd_6995972 < baseStart_6995972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6995977 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 10]
def baseStart_6995977 : Nat := 118140960795 + 6995977 * 2 ^ 59
def prefixEnd_6995977 : Nat := 4983230072969 + 3 ^ 40 * 6995977 * 2
def baseEnd_6995977 : Nat := 3592298848799679941513593

theorem tailTrace_6995977 : CollatzResearch.WordTrace tailWord_6995977 prefixEnd_6995977 3592298848799679941513593 := by
  unfold tailWord_6995977
  simp only [CollatzResearch.WordTrace]
  refine ⟨255164243775777621592410185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170109495850518414394940123 255164243775777621592410185)
  ·
    refine ⟨191373182831833216194307639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255164243775777621592410185 191373182831833216194307639)
    ·
      refine ⟨287059774247749824291461459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191373182831833216194307639 287059774247749824291461459)
      ·
        refine ⟨430589661371624736437192189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287059774247749824291461459 430589661371624736437192189)
        ·
          refine ⟨161471123014359276163947071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 430589661371624736437192189 161471123014359276163947071)
          ·
            refine ⟨242206684521538914245920607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161471123014359276163947071 242206684521538914245920607)
            ·
              refine ⟨363310026782308371368880911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242206684521538914245920607 363310026782308371368880911)
              ·
                refine ⟨544965040173462557053321367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363310026782308371368880911 544965040173462557053321367)
                ·
                  refine ⟨817447560260193835579982051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 544965040173462557053321367 817447560260193835579982051)
                  ·
                    refine ⟨1226171340390290753369973077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 817447560260193835579982051 1226171340390290753369973077)
                    ·
                      refine ⟨3592298848799679941513593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1226171340390290753369973077 3592298848799679941513593)
                      ·
                        rfl

theorem cell23_6995977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 10].length) (baseStart_6995977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6995977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6995977 prefixEnd_6995977 := by exact prefixLift 6995977
  have htrace : WordTrace (prefixWord ++ tailWord_6995977) baseStart_6995977 baseEnd_6995977 := by
    simpa [prefixWord, tailWord_6995977, baseEnd_6995977] using wordTrace_append hprefix tailTrace_6995977
  have hstable : (prefixWord ++ tailWord_6995977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6995977).length < 2 ^ (prefixWord ++ tailWord_6995977).sum := by decide
  have hdescent : baseEnd_6995977 < baseStart_6995977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6995977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996028 : List Nat := [2, 2, 2, 2, 2, 1, 4, 1, 1, 4, 2]
def baseStart_6996028 : Nat := 118140960795 + 6996028 * 2 ^ 59
def prefixEnd_6996028 : Nat := 4983230072969 + 3 ^ 40 * 6996028 * 2
def baseEnd_6996028 : Nat := 3592325036313059241975859

theorem tailTrace_6996028 : CollatzResearch.WordTrace tailWord_6996028 prefixEnd_6996028 3592325036313059241975859 := by
  unfold tailWord_6996028
  simp only [CollatzResearch.WordTrace]
  refine ⟨127583051949296428651258369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170110735932395238201677825 127583051949296428651258369)
  ·
    refine ⟨95687288961972321488443777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127583051949296428651258369 95687288961972321488443777)
    ·
      refine ⟨71765466721479241116332833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95687288961972321488443777 71765466721479241116332833)
      ·
        refine ⟨53824100041109430837249625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71765466721479241116332833 53824100041109430837249625)
        ·
          refine ⟨40368075030832073127937219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53824100041109430837249625 40368075030832073127937219)
          ·
            refine ⟨60552112546248109691905829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40368075030832073127937219 60552112546248109691905829)
            ·
              refine ⟨11353521102421520567232343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60552112546248109691905829 11353521102421520567232343)
              ·
                refine ⟨17030281653632280850848515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11353521102421520567232343 17030281653632280850848515)
                ·
                  refine ⟨25545422480448421276272773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17030281653632280850848515 25545422480448421276272773)
                  ·
                    refine ⟨4789766715084078989301145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25545422480448421276272773 4789766715084078989301145)
                    ·
                      refine ⟨3592325036313059241975859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4789766715084078989301145 3592325036313059241975859)
                      ·
                        rfl

theorem cell23_6996028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_6996028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996028 prefixEnd_6996028 := by exact prefixLift 6996028
  have htrace : WordTrace (prefixWord ++ tailWord_6996028) baseStart_6996028 baseEnd_6996028 := by
    simpa [prefixWord, tailWord_6996028, baseEnd_6996028] using wordTrace_append hprefix tailTrace_6996028
  have hstable : (prefixWord ++ tailWord_6996028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996028).length < 2 ^ (prefixWord ++ tailWord_6996028).sum := by decide
  have hdescent : baseEnd_6996028 < baseStart_6996028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996045 : List Nat := [1, 6, 1, 1, 1, 1, 2, 2, 4, 2, 2]
def baseStart_6996045 : Nat := 118140960795 + 6996045 * 2 ^ 59
def prefixEnd_6996045 : Nat := 4983230072969 + 3 ^ 40 * 6996045 * 2
def baseEnd_6996045 : Nat := 3592333765484185675463281

theorem tailTrace_6996045 : CollatzResearch.WordTrace tailWord_6996045 prefixEnd_6996045 3592333765484185675463281 := by
  unfold tailWord_6996045
  simp only [CollatzResearch.WordTrace]
  refine ⟨255166723939531269205885589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170111149293020846137257059 255166723939531269205885589)
  ·
    refine ⟨11960940184665528244025887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 255166723939531269205885589 11960940184665528244025887)
    ·
      refine ⟨17941410276998292366038831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11960940184665528244025887 17941410276998292366038831)
      ·
        refine ⟨26912115415497438549058247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17941410276998292366038831 26912115415497438549058247)
        ·
          refine ⟨40368173123246157823587371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26912115415497438549058247 40368173123246157823587371)
          ·
            refine ⟨60552259684869236735381057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40368173123246157823587371 60552259684869236735381057)
            ·
              refine ⟨45414194763651927551535793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60552259684869236735381057 45414194763651927551535793)
              ·
                refine ⟨34060646072738945663651845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45414194763651927551535793 34060646072738945663651845)
                ·
                  refine ⟨6386371138638552311934721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34060646072738945663651845 6386371138638552311934721)
                  ·
                    refine ⟨4789778353978914233951041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6386371138638552311934721 4789778353978914233951041)
                    ·
                      refine ⟨3592333765484185675463281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4789778353978914233951041 3592333765484185675463281)
                      ·
                        rfl

theorem cell23_6996045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_6996045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996045 prefixEnd_6996045 := by exact prefixLift 6996045
  have htrace : WordTrace (prefixWord ++ tailWord_6996045) baseStart_6996045 baseEnd_6996045 := by
    simpa [prefixWord, tailWord_6996045, baseEnd_6996045] using wordTrace_append hprefix tailTrace_6996045
  have hstable : (prefixWord ++ tailWord_6996045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996045).length < 2 ^ (prefixWord ++ tailWord_6996045).sum := by decide
  have hdescent : baseEnd_6996045 < baseStart_6996045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996101 : List Nat := [1, 3, 1, 1, 5, 1, 2, 1, 1, 3, 4]
def baseStart_6996101 : Nat := 118140960795 + 6996101 * 2 ^ 59
def prefixEnd_6996101 : Nat := 4983230072969 + 3 ^ 40 * 6996101 * 2
def baseEnd_6996101 : Nat := 3592362520400837456363023

theorem tailTrace_6996101 : CollatzResearch.WordTrace tailWord_6996101 prefixEnd_6996101 3592362520400837456363023 := by
  unfold tailWord_6996101
  simp only [CollatzResearch.WordTrace]
  refine ⟨255168766427328390769924157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170112510951552260513282771 255168766427328390769924157)
  ·
    refine ⟨95688287410248146538721559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255168766427328390769924157 95688287410248146538721559)
    ·
      refine ⟨143532431115372219808082339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95688287410248146538721559 143532431115372219808082339)
      ·
        refine ⟨215298646673058329712123509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143532431115372219808082339 215298646673058329712123509)
        ·
          refine ⟨20184248125599218410511579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 215298646673058329712123509 20184248125599218410511579)
          ·
            refine ⟨30276372188398827615767369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20184248125599218410511579 30276372188398827615767369)
            ·
              refine ⟨22707279141299120711825527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30276372188398827615767369 22707279141299120711825527)
              ·
                refine ⟨34060918711948681067738291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22707279141299120711825527 34060918711948681067738291)
                ·
                  refine ⟨51091378067923021601607437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34060918711948681067738291 51091378067923021601607437)
                  ·
                    refine ⟨19159266775471133100602789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51091378067923021601607437 19159266775471133100602789)
                    ·
                      refine ⟨3592362520400837456363023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19159266775471133100602789 3592362520400837456363023)
                      ·
                        rfl

theorem cell23_6996101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_6996101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996101 prefixEnd_6996101 := by exact prefixLift 6996101
  have htrace : WordTrace (prefixWord ++ tailWord_6996101) baseStart_6996101 baseEnd_6996101 := by
    simpa [prefixWord, tailWord_6996101, baseEnd_6996101] using wordTrace_append hprefix tailTrace_6996101
  have hstable : (prefixWord ++ tailWord_6996101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996101).length < 2 ^ (prefixWord ++ tailWord_6996101).sum := by decide
  have hdescent : baseEnd_6996101 < baseStart_6996101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996128 : List Nat := [2, 1, 1, 4, 2, 2, 3, 1, 3, 4]
def baseStart_6996128 : Nat := 118140960795 + 6996128 * 2 ^ 59
def prefixEnd_6996128 : Nat := 4983230072969 + 3 ^ 40 * 6996128 * 2
def baseEnd_6996128 : Nat := 1197458794792836283575133

theorem tailTrace_6996128 : CollatzResearch.WordTrace tailWord_6996128 prefixEnd_6996128 1197458794792836283575133 := by
  unfold tailWord_6996128
  simp only [CollatzResearch.WordTrace]
  refine ⟨127584875599115287190578519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170113167465487049587438025 127584875599115287190578519)
  ·
    refine ⟨191377313398672930785867779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127584875599115287190578519 191377313398672930785867779)
    ·
      refine ⟨287065970098009396178801669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191377313398672930785867779 287065970098009396178801669)
      ·
        refine ⟨53824869393376761783525313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 287065970098009396178801669 53824869393376761783525313)
        ·
          refine ⟨40368652045032571337643985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53824869393376761783525313 40368652045032571337643985)
          ·
            refine ⟨30276489033774428503232989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40368652045032571337643985 30276489033774428503232989)
            ·
              refine ⟨11353683387665410688712371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30276489033774428503232989 11353683387665410688712371)
              ·
                refine ⟨17030525081498116033068557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11353683387665410688712371 17030525081498116033068557)
                ·
                  refine ⟨6386446905561793512400709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17030525081498116033068557 6386446905561793512400709)
                  ·
                    refine ⟨1197458794792836283575133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6386446905561793512400709 1197458794792836283575133)
                    ·
                      rfl

theorem cell23_6996128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 3, 4].length) (baseStart_6996128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996128 prefixEnd_6996128 := by exact prefixLift 6996128
  have htrace : WordTrace (prefixWord ++ tailWord_6996128) baseStart_6996128 baseEnd_6996128 := by
    simpa [prefixWord, tailWord_6996128, baseEnd_6996128] using wordTrace_append hprefix tailTrace_6996128
  have hstable : (prefixWord ++ tailWord_6996128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996128).length < 2 ^ (prefixWord ++ tailWord_6996128).sum := by decide
  have hdescent : baseEnd_6996128 < baseStart_6996128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996225 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 5, 2, 2]
def baseStart_6996225 : Nat := 118140960795 + 6996225 * 2 ^ 59
def prefixEnd_6996225 : Nat := 4983230072969 + 3 ^ 40 * 6996225 * 2
def baseEnd_6996225 : Nat := 3592426192001994971212453

theorem tailTrace_6996225 : CollatzResearch.WordTrace tailWord_6996225 prefixEnd_6996225 3592426192001994971212453 := by
  unfold tailWord_6996225
  simp only [CollatzResearch.WordTrace]
  refine ⟨255173289078879159947438129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170115526052586106631625419 255173289078879159947438129)
  ·
    refine ⟨191379966809159369960578597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255173289078879159947438129 191379966809159369960578597)
    ·
      refine ⟨35883743776717381867608487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191379966809159369960578597 35883743776717381867608487)
      ·
        refine ⟨53825615665076072801412731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35883743776717381867608487 53825615665076072801412731)
        ·
          refine ⟨80738423497614109202119097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53825615665076072801412731 80738423497614109202119097)
          ·
            refine ⟨60553817623210581901589323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80738423497614109202119097 60553817623210581901589323)
            ·
              refine ⟨90830726434815872852383985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60553817623210581901589323 90830726434815872852383985)
              ·
                refine ⟨68123044826111904639287989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90830726434815872852383985 68123044826111904639287989)
                ·
                  refine ⟨6386535452447991059933249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68123044826111904639287989 6386535452447991059933249)
                  ·
                    refine ⟨4789901589335993294949937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6386535452447991059933249 4789901589335993294949937)
                    ·
                      refine ⟨3592426192001994971212453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4789901589335993294949937 3592426192001994971212453)
                      ·
                        rfl

theorem cell23_6996225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_6996225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996225 prefixEnd_6996225 := by exact prefixLift 6996225
  have htrace : WordTrace (prefixWord ++ tailWord_6996225) baseStart_6996225 baseEnd_6996225 := by
    simpa [prefixWord, tailWord_6996225, baseEnd_6996225] using wordTrace_append hprefix tailTrace_6996225
  have hstable : (prefixWord ++ tailWord_6996225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996225).length < 2 ^ (prefixWord ++ tailWord_6996225).sum := by decide
  have hdescent : baseEnd_6996225 < baseStart_6996225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996255 : List Nat := [1, 1, 2, 4, 3, 3, 1, 1, 1, 2, 4]
def baseStart_6996255 : Nat := 118140960795 + 6996255 * 2 ^ 59
def prefixEnd_6996255 : Nat := 4983230072969 + 3 ^ 40 * 6996255 * 2
def baseEnd_6996255 : Nat := 3592441596421629853837315

theorem tailTrace_6996255 : CollatzResearch.WordTrace tailWord_6996255 prefixEnd_6996255 3592441596421629853837315 := by
  unfold tailWord_6996255
  simp only [CollatzResearch.WordTrace]
  refine ⟨255174383268770475071030219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170116255512513650047353479 255174383268770475071030219)
  ·
    refine ⟨382761574903155712606545329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255174383268770475071030219 382761574903155712606545329)
    ·
      refine ⟨287071181177366784454908997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382761574903155712606545329 287071181177366784454908997)
      ·
        refine ⟨53825846470756272085295437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 287071181177366784454908997 53825846470756272085295437)
        ·
          refine ⟨20184692426533602031985789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53825846470756272085295437 20184692426533602031985789)
          ·
            refine ⟨7569259659950100761994671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20184692426533602031985789 7569259659950100761994671)
            ·
              refine ⟨11353889489925151142992007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7569259659950100761994671 11353889489925151142992007)
              ·
                refine ⟨17030834234887726714488011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11353889489925151142992007 17030834234887726714488011)
                ·
                  refine ⟨25546251352331590071732017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17030834234887726714488011 25546251352331590071732017)
                  ·
                    refine ⟨19159688514248692553799013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25546251352331590071732017 19159688514248692553799013)
                    ·
                      refine ⟨3592441596421629853837315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19159688514248692553799013 3592441596421629853837315)
                      ·
                        rfl

theorem cell23_6996255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_6996255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996255 prefixEnd_6996255 := by exact prefixLift 6996255
  have htrace : WordTrace (prefixWord ++ tailWord_6996255) baseStart_6996255 baseEnd_6996255 := by
    simpa [prefixWord, tailWord_6996255, baseEnd_6996255] using wordTrace_append hprefix tailTrace_6996255
  have hstable : (prefixWord ++ tailWord_6996255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996255).length < 2 ^ (prefixWord ++ tailWord_6996255).sum := by decide
  have hdescent : baseEnd_6996255 < baseStart_6996255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996271 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 5]
def baseStart_6996271 : Nat := 118140960795 + 6996271 * 2 ^ 59
def prefixEnd_6996271 : Nat := 4983230072969 + 3 ^ 40 * 6996271 * 2
def baseEnd_6996271 : Nat := 3592449812112101791237241

theorem tailTrace_6996271 : CollatzResearch.WordTrace tailWord_6996271 prefixEnd_6996271 3592449812112101791237241 := by
  unfold tailWord_6996271
  simp only [CollatzResearch.WordTrace]
  refine ⟨255174966836712509803612667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170116644557808339869075111 255174966836712509803612667)
  ·
    refine ⟨382762450255068764705419001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255174966836712509803612667 382762450255068764705419001)
    ·
      refine ⟨287071837691301573529064251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382762450255068764705419001 287071837691301573529064251)
      ·
        refine ⟨430607756536952360293596377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287071837691301573529064251 430607756536952360293596377)
        ·
          refine ⟨322955817402714270220197283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 430607756536952360293596377 322955817402714270220197283)
          ·
            refine ⟨484433726104071405330295925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322955817402714270220197283 484433726104071405330295925)
            ·
              refine ⟨45415661822256694249715243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 484433726104071405330295925 45415661822256694249715243)
              ·
                refine ⟨68123492733385041374572865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45415661822256694249715243 68123492733385041374572865)
                ·
                  refine ⟨51092619550038781030929649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68123492733385041374572865 51092619550038781030929649)
                  ·
                    refine ⟨38319464662529085773197237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51092619550038781030929649 38319464662529085773197237)
                    ·
                      refine ⟨3592449812112101791237241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38319464662529085773197237 3592449812112101791237241)
                      ·
                        rfl

theorem cell23_6996271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 5].length) (baseStart_6996271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996271 prefixEnd_6996271 := by exact prefixLift 6996271
  have htrace : WordTrace (prefixWord ++ tailWord_6996271) baseStart_6996271 baseEnd_6996271 := by
    simpa [prefixWord, tailWord_6996271, baseEnd_6996271] using wordTrace_append hprefix tailTrace_6996271
  have hstable : (prefixWord ++ tailWord_6996271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996271).length < 2 ^ (prefixWord ++ tailWord_6996271).sum := by decide
  have hdescent : baseEnd_6996271 < baseStart_6996271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996276 : List Nat := [2, 5, 1, 1, 1, 2, 3, 3, 1, 2, 2]
def baseStart_6996276 : Nat := 118140960795 + 6996276 * 2 ^ 59
def prefixEnd_6996276 : Nat := 4983230072969 + 3 ^ 40 * 6996276 * 2
def baseEnd_6996276 : Nat := 3592452379515374271674719

theorem tailTrace_6996276 : CollatzResearch.WordTrace tailWord_6996276 prefixEnd_6996276 3592452379515374271674719 := by
  unfold tailWord_6996276
  simp only [CollatzResearch.WordTrace]
  refine ⟨127587574600847197828772341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170116766134462930438363121 127587574600847197828772341)
  ·
    refine ⟨11961335118829424796447407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127587574600847197828772341 11961335118829424796447407)
    ·
      refine ⟨17942002678244137194671111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11961335118829424796447407 17942002678244137194671111)
      ·
        refine ⟨26913004017366205792006667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17942002678244137194671111 26913004017366205792006667)
        ·
          refine ⟨40369506026049308688010001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26913004017366205792006667 40369506026049308688010001)
          ·
            refine ⟨30277129519536981516007501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40369506026049308688010001 30277129519536981516007501)
            ·
              refine ⟨11353923569826368068502813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30277129519536981516007501 11353923569826368068502813)
              ·
                refine ⟨4257721338684888025688555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11353923569826368068502813 4257721338684888025688555)
                ·
                  refine ⟨6386582008027332038532833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4257721338684888025688555 6386582008027332038532833)
                  ·
                    refine ⟨4789936506020499028899625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6386582008027332038532833 4789936506020499028899625)
                    ·
                      refine ⟨3592452379515374271674719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4789936506020499028899625 3592452379515374271674719)
                      ·
                        rfl

theorem cell23_6996276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_6996276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996276 prefixEnd_6996276 := by exact prefixLift 6996276
  have htrace : WordTrace (prefixWord ++ tailWord_6996276) baseStart_6996276 baseEnd_6996276 := by
    simpa [prefixWord, tailWord_6996276, baseEnd_6996276] using wordTrace_append hprefix tailTrace_6996276
  have hstable : (prefixWord ++ tailWord_6996276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996276).length < 2 ^ (prefixWord ++ tailWord_6996276).sum := by decide
  have hdescent : baseEnd_6996276 < baseStart_6996276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996291 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 4, 6]
def baseStart_6996291 : Nat := 118140960795 + 6996291 * 2 ^ 59
def prefixEnd_6996291 : Nat := 4983230072969 + 3 ^ 40 * 6996291 * 2
def baseEnd_6996291 : Nat := 1197486693908397237662383

theorem tailTrace_6996291 : CollatzResearch.WordTrace tailWord_6996291 prefixEnd_6996291 1197486693908397237662383 := by
  unfold tailWord_6996291
  simp only [CollatzResearch.WordTrace]
  refine ⟨255175696296640053219340727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170117130864426702146227151 255175696296640053219340727)
  ·
    refine ⟨382763544444960079829011091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255175696296640053219340727 382763544444960079829011091)
    ·
      refine ⟨574145316667440119743516637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382763544444960079829011091 574145316667440119743516637)
      ·
        refine ⟨215304493750290044903818739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 574145316667440119743516637 215304493750290044903818739)
        ·
          refine ⟨322956740625435067355728109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215304493750290044903818739 322956740625435067355728109)
          ·
            refine ⟨121108777734538150258398041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 322956740625435067355728109 121108777734538150258398041)
            ·
              refine ⟨90831583300903612693798531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121108777734538150258398041 90831583300903612693798531)
              ·
                refine ⟨136247374951355419040697797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90831583300903612693798531 136247374951355419040697797)
                ·
                  refine ⟨25546382803379141070130837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136247374951355419040697797 25546382803379141070130837)
                  ·
                    refine ⟨1197486693908397237662383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25546382803379141070130837 1197486693908397237662383)
                    ·
                      rfl

theorem cell23_6996291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 6].length) (baseStart_6996291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996291 prefixEnd_6996291 := by exact prefixLift 6996291
  have htrace : WordTrace (prefixWord ++ tailWord_6996291) baseStart_6996291 baseEnd_6996291 := by
    simpa [prefixWord, tailWord_6996291, baseEnd_6996291] using wordTrace_append hprefix tailTrace_6996291
  have hstable : (prefixWord ++ tailWord_6996291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996291).length < 2 ^ (prefixWord ++ tailWord_6996291).sum := by decide
  have hdescent : baseEnd_6996291 < baseStart_6996291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996332 : List Nat := [2, 2, 1, 1, 6, 1, 1, 2, 1, 4, 2]
def baseStart_6996332 : Nat := 118140960795 + 6996332 * 2 ^ 59
def prefixEnd_6996332 : Nat := 4983230072969 + 3 ^ 40 * 6996332 * 2
def baseEnd_6996332 : Nat := 3592481134432026052574461

theorem tailTrace_6996332 : CollatzResearch.WordTrace tailWord_6996332 prefixEnd_6996332 3592481134432026052574461 := by
  unfold tailWord_6996332
  simp only [CollatzResearch.WordTrace]
  refine ⟨127588595844745758610791625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170118127792994344814388833 127588595844745758610791625)
  ·
    refine ⟨95691446883559318958093719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127588595844745758610791625 95691446883559318958093719)
    ·
      refine ⟨143537170325338978437140579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95691446883559318958093719 143537170325338978437140579)
      ·
        refine ⟨215305755488008467655710869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143537170325338978437140579 215305755488008467655710869)
        ·
          refine ⟨10092457288500396921361447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 215305755488008467655710869 10092457288500396921361447)
          ·
            refine ⟨15138685932750595382042171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10092457288500396921361447 15138685932750595382042171)
            ·
              refine ⟨22708028899125893073063257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15138685932750595382042171 22708028899125893073063257)
              ·
                refine ⟨17031021674344419804797443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22708028899125893073063257 17031021674344419804797443)
                ·
                  refine ⟨25546532511516629707196165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17031021674344419804797443 25546532511516629707196165)
                  ·
                    refine ⟨4789974845909368070099281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25546532511516629707196165 4789974845909368070099281)
                    ·
                      refine ⟨3592481134432026052574461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4789974845909368070099281 3592481134432026052574461)
                      ·
                        rfl

theorem cell23_6996332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 4, 2].length) (baseStart_6996332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996332 prefixEnd_6996332 := by exact prefixLift 6996332
  have htrace : WordTrace (prefixWord ++ tailWord_6996332) baseStart_6996332 baseEnd_6996332 := by
    simpa [prefixWord, tailWord_6996332, baseEnd_6996332] using wordTrace_append hprefix tailTrace_6996332
  have hstable : (prefixWord ++ tailWord_6996332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996332).length < 2 ^ (prefixWord ++ tailWord_6996332).sum := by decide
  have hdescent : baseEnd_6996332 < baseStart_6996332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996349 : List Nat := [1, 4, 1, 1, 2, 4, 2, 2, 2, 2, 2]
def baseStart_6996349 : Nat := 118140960795 + 6996349 * 2 ^ 59
def prefixEnd_6996349 : Nat := 4983230072969 + 3 ^ 40 * 6996349 * 2
def baseEnd_6996349 : Nat := 3592489863603152486061883

theorem tailTrace_6996349 : CollatzResearch.WordTrace tailWord_6996349 prefixEnd_6996349 3592489863603152486061883 := by
  unfold tailWord_6996349
  simp only [CollatzResearch.WordTrace]
  refine ⟨255177811730429929124952101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170118541153619952749968067 255177811730429929124952101)
  ·
    refine ⟨47845839699455611710928519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255177811730429929124952101 47845839699455611710928519)
    ·
      refine ⟨71768759549183417566392779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47845839699455611710928519 71768759549183417566392779)
      ·
        refine ⟨107653139323775126349589169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71768759549183417566392779 107653139323775126349589169)
        ·
          refine ⟨80739854492831344762191877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107653139323775126349589169 80739854492831344762191877)
          ·
            refine ⟨15138722717405877142910977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80739854492831344762191877 15138722717405877142910977)
            ·
              refine ⟨11354042038054407857183233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15138722717405877142910977 11354042038054407857183233)
              ·
                refine ⟨8515531528540805892887425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11354042038054407857183233 8515531528540805892887425)
                ·
                  refine ⟨6386648646405604419665569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8515531528540805892887425 6386648646405604419665569)
                  ·
                    refine ⟨4789986484804203314749177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6386648646405604419665569 4789986484804203314749177)
                    ·
                      refine ⟨3592489863603152486061883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4789986484804203314749177 3592489863603152486061883)
                      ·
                        rfl

theorem cell23_6996349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 2, 2, 2].length) (baseStart_6996349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996349 prefixEnd_6996349 := by exact prefixLift 6996349
  have htrace : WordTrace (prefixWord ++ tailWord_6996349) baseStart_6996349 baseEnd_6996349 := by
    simpa [prefixWord, tailWord_6996349, baseEnd_6996349] using wordTrace_append hprefix tailTrace_6996349
  have hstable : (prefixWord ++ tailWord_6996349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996349).length < 2 ^ (prefixWord ++ tailWord_6996349).sum := by decide
  have hdescent : baseEnd_6996349 < baseStart_6996349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996362 : List Nat := [3, 1, 2, 5, 1, 1, 1, 1, 2, 2, 4]
def baseStart_6996362 : Nat := 118140960795 + 6996362 * 2 ^ 59
def prefixEnd_6996362 : Nat := 4983230072969 + 3 ^ 40 * 6996362 * 2
def baseEnd_6996362 : Nat := 3592496538851660935199323

theorem tailTrace_6996362 : CollatzResearch.WordTrace tailWord_6996362 prefixEnd_6996362 3592496538851660935199323 := by
  unfold tailWord_6996362
  simp only [CollatzResearch.WordTrace]
  refine ⟨63794571469845708086293835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170118857252921888230116893 63794571469845708086293835)
  ·
    refine ⟨95691857204768562129440753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63794571469845708086293835 95691857204768562129440753)
    ·
      refine ⟨71768892903576421597080565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95691857204768562129440753 71768892903576421597080565)
      ·
        refine ⟨6728333709710289524726303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71768892903576421597080565 6728333709710289524726303)
        ·
          refine ⟨10092500564565434287089455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6728333709710289524726303 10092500564565434287089455)
          ·
            refine ⟨15138750846848151430634183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10092500564565434287089455 15138750846848151430634183)
            ·
              refine ⟨22708126270272227145951275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15138750846848151430634183 22708126270272227145951275)
              ·
                refine ⟨34062189405408340718926913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22708126270272227145951275 34062189405408340718926913)
                ·
                  refine ⟨25546642054056255539195185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34062189405408340718926913 25546642054056255539195185)
                  ·
                    refine ⟨19159981540542191654396389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25546642054056255539195185 19159981540542191654396389)
                    ·
                      refine ⟨3592496538851660935199323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19159981540542191654396389 3592496538851660935199323)
                      ·
                        rfl

theorem cell23_6996362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_6996362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996362 prefixEnd_6996362 := by exact prefixLift 6996362
  have htrace : WordTrace (prefixWord ++ tailWord_6996362) baseStart_6996362 baseEnd_6996362 := by
    simpa [prefixWord, tailWord_6996362, baseEnd_6996362] using wordTrace_append hprefix tailTrace_6996362
  have hstable : (prefixWord ++ tailWord_6996362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996362).length < 2 ^ (prefixWord ++ tailWord_6996362).sum := by decide
  have hdescent : baseEnd_6996362 < baseStart_6996362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996466 : List Nat := [3, 2, 1, 4, 3, 1, 1, 1, 3, 4]
def baseStart_6996466 : Nat := 118140960795 + 6996466 * 2 ^ 59
def prefixEnd_6996466 : Nat := 4983230072969 + 3 ^ 40 * 6996466 * 2
def baseEnd_6996466 : Nat := 1197516646946576176099615

theorem tailTrace_6996466 : CollatzResearch.WordTrace tailWord_6996466 prefixEnd_6996466 1197516646946576176099615 := by
  unfold tailWord_6996466
  simp only [CollatzResearch.WordTrace]
  refine ⟨63795519767751514526740313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170121386047337372071307501 63795519767751514526740313)
  ·
    refine ⟨47846639825813635895055235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63795519767751514526740313 47846639825813635895055235)
    ·
      refine ⟨71769959738720453842582853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47846639825813635895055235 71769959738720453842582853)
      ·
        refine ⟨13456867451010085095484285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71769959738720453842582853 13456867451010085095484285)
        ·
          refine ⟨5046325294128781910806607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13456867451010085095484285 5046325294128781910806607)
          ·
            refine ⟨7569487941193172866209911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5046325294128781910806607 7569487941193172866209911)
            ·
              refine ⟨11354231911789759299314867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7569487941193172866209911 11354231911789759299314867)
              ·
                refine ⟨17031347867684638948972301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11354231911789759299314867 17031347867684638948972301)
                ·
                  refine ⟨6386755450381739605864613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17031347867684638948972301 6386755450381739605864613)
                  ·
                    refine ⟨1197516646946576176099615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6386755450381739605864613 1197516646946576176099615)
                    ·
                      rfl

theorem cell23_6996466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_6996466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996466 prefixEnd_6996466 := by exact prefixLift 6996466
  have htrace : WordTrace (prefixWord ++ tailWord_6996466) baseStart_6996466 baseEnd_6996466 := by
    simpa [prefixWord, tailWord_6996466, baseEnd_6996466] using wordTrace_append hprefix tailTrace_6996466
  have hstable : (prefixWord ++ tailWord_6996466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996466).length < 2 ^ (prefixWord ++ tailWord_6996466).sum := by decide
  have hdescent : baseEnd_6996466 < baseStart_6996466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996492 : List Nat := [2, 2, 1, 2, 4, 1, 3, 2, 1, 5]
def baseStart_6996492 : Nat := 118140960795 + 6996492 * 2 ^ 59
def prefixEnd_6996492 : Nat := 4983230072969 + 3 ^ 40 * 6996492 * 2
def baseEnd_6996492 : Nat := 1197521097112248475524575

theorem tailTrace_6996492 : CollatzResearch.WordTrace tailWord_6996492 prefixEnd_6996492 1197521097112248475524575 := by
  unfold tailWord_6996492
  simp only [CollatzResearch.WordTrace]
  refine ⟨127591513684455932273703865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170122018245941243031605153 127591513684455932273703865)
  ·
    refine ⟨95693635263341949205277899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127591513684455932273703865 95693635263341949205277899)
    ·
      refine ⟨143540452895012923807916849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95693635263341949205277899 143540452895012923807916849)
      ·
        refine ⟨107655339671259692855937637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143540452895012923807916849 107655339671259692855937637)
        ·
          refine ⟨20185376188361192410488307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107655339671259692855937637 20185376188361192410488307)
          ·
            refine ⟨30278064282541788615732461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20185376188361192410488307 30278064282541788615732461)
            ·
              refine ⟨11354274105953170730899673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30278064282541788615732461 11354274105953170730899673)
              ·
                refine ⟨8515705579464878048174755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11354274105953170730899673 8515705579464878048174755)
                ·
                  refine ⟨12773558369197317072262133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8515705579464878048174755 12773558369197317072262133)
                  ·
                    refine ⟨1197521097112248475524575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12773558369197317072262133 1197521097112248475524575)
                    ·
                      rfl

theorem cell23_6996492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 1, 5].length) (baseStart_6996492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996492 prefixEnd_6996492 := by exact prefixLift 6996492
  have htrace : WordTrace (prefixWord ++ tailWord_6996492) baseStart_6996492 baseEnd_6996492 := by
    simpa [prefixWord, tailWord_6996492, baseEnd_6996492] using wordTrace_append hprefix tailTrace_6996492
  have hstable : (prefixWord ++ tailWord_6996492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996492).length < 2 ^ (prefixWord ++ tailWord_6996492).sum := by decide
  have hdescent : baseEnd_6996492 < baseStart_6996492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996495 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 1, 8, 2]
def baseStart_6996495 : Nat := 118140960795 + 6996495 * 2 ^ 59
def prefixEnd_6996495 : Nat := 4983230072969 + 3 ^ 40 * 6996495 * 2
def baseEnd_6996495 : Nat := 3592564831778708914836211

theorem tailTrace_6996495 : CollatzResearch.WordTrace tailWord_6996495 prefixEnd_6996495 3592564831778708914836211 := by
  unfold tailWord_6996495
  simp only [CollatzResearch.WordTrace]
  refine ⟨255183136787900996059766939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170122091191933997373177959 255183136787900996059766939)
  ·
    refine ⟨382774705181851494089650409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255183136787900996059766939 382774705181851494089650409)
    ·
      refine ⟨287081028886388620567237807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382774705181851494089650409 287081028886388620567237807)
      ·
        refine ⟨430621543329582930850856711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287081028886388620567237807 430621543329582930850856711)
        ·
          refine ⟨645932314994374396276285067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430621543329582930850856711 645932314994374396276285067)
          ·
            refine ⟨968898472491561594414427601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645932314994374396276285067 968898472491561594414427601)
            ·
              refine ⟨726673854368671195810820701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 968898472491561594414427601 726673854368671195810820701)
              ·
                refine ⟨272502695388251698429057763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 726673854368671195810820701 272502695388251698429057763)
                ·
                  refine ⟨408754043082377547643586645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 272502695388251698429057763 408754043082377547643586645)
                  ·
                    refine ⟨4790086442371611886448281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 408754043082377547643586645 4790086442371611886448281)
                    ·
                      refine ⟨3592564831778708914836211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4790086442371611886448281 3592564831778708914836211)
                      ·
                        rfl

theorem cell23_6996495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 8, 2].length) (baseStart_6996495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996495 prefixEnd_6996495 := by exact prefixLift 6996495
  have htrace : WordTrace (prefixWord ++ tailWord_6996495) baseStart_6996495 baseEnd_6996495 := by
    simpa [prefixWord, tailWord_6996495, baseEnd_6996495] using wordTrace_append hprefix tailTrace_6996495
  have hstable : (prefixWord ++ tailWord_6996495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996495).length < 2 ^ (prefixWord ++ tailWord_6996495).sum := by decide
  have hdescent : baseEnd_6996495 < baseStart_6996495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996509 : List Nat := [1, 4, 2, 2, 1, 3, 3, 1, 1, 5]
def baseStart_6996509 : Nat := 118140960795 + 6996509 * 2 ^ 59
def prefixEnd_6996509 : Nat := 4983230072969 + 3 ^ 40 * 6996509 * 2
def baseEnd_6996509 : Nat := 1197524006835957286687049

theorem tailTrace_6996509 : CollatzResearch.WordTrace tailWord_6996509 prefixEnd_6996509 1197524006835957286687049 := by
  unfold tailWord_6996509
  simp only [CollatzResearch.WordTrace]
  refine ⟨255183647409850276450776581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170122431606566850967184387 255183647409850276450776581)
  ·
    refine ⟨47846933889346926834520609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255183647409850276450776581 47846933889346926834520609)
    ·
      refine ⟨35885200417010195125890457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47846933889346926834520609 35885200417010195125890457)
      ·
        refine ⟨26913900312757646344417843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35885200417010195125890457 26913900312757646344417843)
        ·
          refine ⟨40370850469136469516626765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26913900312757646344417843 40370850469136469516626765)
          ·
            refine ⟨15139068925926176068735037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40370850469136469516626765 15139068925926176068735037)
            ·
              refine ⟨5677150847222316025775639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15139068925926176068735037 5677150847222316025775639)
              ·
                refine ⟨8515726270833474038663459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5677150847222316025775639 8515726270833474038663459)
                ·
                  refine ⟨12773589406250211057995189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8515726270833474038663459 12773589406250211057995189)
                  ·
                    refine ⟨1197524006835957286687049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12773589406250211057995189 1197524006835957286687049)
                    ·
                      rfl

theorem cell23_6996509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_6996509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996509 prefixEnd_6996509 := by exact prefixLift 6996509
  have htrace : WordTrace (prefixWord ++ tailWord_6996509) baseStart_6996509 baseEnd_6996509 := by
    simpa [prefixWord, tailWord_6996509, baseEnd_6996509] using wordTrace_append hprefix tailTrace_6996509
  have hstable : (prefixWord ++ tailWord_6996509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996509).length < 2 ^ (prefixWord ++ tailWord_6996509).sum := by decide
  have hdescent : baseEnd_6996509 < baseStart_6996509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996562 : List Nat := [3, 2, 2, 1, 2, 1, 1, 4, 1, 3, 3]
def baseStart_6996562 : Nat := 118140960795 + 6996562 * 2 ^ 59
def prefixEnd_6996562 : Nat := 4983230072969 + 3 ^ 40 * 6996562 * 2
def baseEnd_6996562 : Nat := 3592599234982560152698403

theorem tailTrace_6996562 : CollatzResearch.WordTrace tailWord_6996562 prefixEnd_6996562 3592599234982560152698403 := by
  unfold tailWord_6996562
  simp only [CollatzResearch.WordTrace]
  refine ⟨63796395119664566625613985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170123720319105511001637293 63796395119664566625613985)
  ·
    refine ⟨47847296339748424969210489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63796395119664566625613985 47847296339748424969210489)
    ·
      refine ⟨35885472254811318726907867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47847296339748424969210489 35885472254811318726907867)
      ·
        refine ⟨53828208382216978090361801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35885472254811318726907867 53828208382216978090361801)
        ·
          refine ⟨40371156286662733567771351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53828208382216978090361801 40371156286662733567771351)
          ·
            refine ⟨60556734429994100351657027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40371156286662733567771351 60556734429994100351657027)
            ·
              refine ⟨90835101644991150527485541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60556734429994100351657027 90835101644991150527485541)
              ·
                refine ⟨17031581558435840723903539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90835101644991150527485541 17031581558435840723903539)
                ·
                  refine ⟨25547372337653761085855309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17031581558435840723903539 25547372337653761085855309)
                  ·
                    refine ⟨9580264626620160407195741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25547372337653761085855309 9580264626620160407195741)
                    ·
                      refine ⟨3592599234982560152698403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9580264626620160407195741 3592599234982560152698403)
                      ·
                        rfl

theorem cell23_6996562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_6996562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996562 prefixEnd_6996562 := by exact prefixLift 6996562
  have htrace : WordTrace (prefixWord ++ tailWord_6996562) baseStart_6996562 baseEnd_6996562 := by
    simpa [prefixWord, tailWord_6996562, baseEnd_6996562] using wordTrace_append hprefix tailTrace_6996562
  have hstable : (prefixWord ++ tailWord_6996562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996562).length < 2 ^ (prefixWord ++ tailWord_6996562).sum := by decide
  have hdescent : baseEnd_6996562 < baseStart_6996562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996622 : List Nat := [4, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5]
def baseStart_6996622 : Nat := 118140960795 + 6996622 * 2 ^ 59
def prefixEnd_6996622 : Nat := 4983230072969 + 3 ^ 40 * 6996622 * 2
def baseEnd_6996622 : Nat := 3592630043821829917948127

theorem tailTrace_6996622 : CollatzResearch.WordTrace tailWord_6996622 prefixEnd_6996622 3592630043821829917948127 := by
  unfold tailWord_6996622
  simp only [CollatzResearch.WordTrace]
  refine ⟨31898471107305112093705015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170125179238960597833093413 31898471107305112093705015)
  ·
    refine ⟨47847706660957668140557523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31898471107305112093705015 47847706660957668140557523)
    ·
      refine ⟨71771559991436502210836285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47847706660957668140557523 71771559991436502210836285)
      ·
        refine ⟨26914334996788688329063607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71771559991436502210836285 26914334996788688329063607)
        ·
          refine ⟨40371502495183032493595411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26914334996788688329063607 40371502495183032493595411)
          ·
            refine ⟨60557253742774548740393117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40371502495183032493595411 60557253742774548740393117)
            ·
              refine ⟨22708970153540455777647419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60557253742774548740393117 22708970153540455777647419)
              ·
                refine ⟨34063455230310683666471129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22708970153540455777647419 34063455230310683666471129)
                ·
                  refine ⟨25547591422733012749853347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34063455230310683666471129 25547591422733012749853347)
                  ·
                    refine ⟨38321387134099519124780021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25547591422733012749853347 38321387134099519124780021)
                    ·
                      refine ⟨3592630043821829917948127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38321387134099519124780021 3592630043821829917948127)
                      ·
                        rfl

theorem cell23_6996622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_6996622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996622 prefixEnd_6996622 := by exact prefixLift 6996622
  have htrace : WordTrace (prefixWord ++ tailWord_6996622) baseStart_6996622 baseEnd_6996622 := by
    simpa [prefixWord, tailWord_6996622, baseEnd_6996622] using wordTrace_append hprefix tailTrace_6996622
  have hstable : (prefixWord ++ tailWord_6996622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996622).length < 2 ^ (prefixWord ++ tailWord_6996622).sum := by decide
  have hdescent : baseEnd_6996622 < baseStart_6996622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996636 : List Nat := [2, 2, 3, 2, 2, 1, 2, 1, 4, 2, 2]
def baseStart_6996636 : Nat := 118140960795 + 6996636 * 2 ^ 59
def prefixEnd_6996636 : Nat := 4983230072969 + 3 ^ 40 * 6996636 * 2
def baseEnd_6996636 : Nat := 3592637232550992863173063

theorem tailTrace_6996636 : CollatzResearch.WordTrace tailWord_6996636 prefixEnd_6996636 3592637232550992863173063 := by
  unfold tailWord_6996636
  simp only [CollatzResearch.WordTrace]
  refine ⟨127594139740195088570324881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170125519653593451427099841 127594139740195088570324881)
  ·
    refine ⟨95695604805146316427743661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127594139740195088570324881 95695604805146316427743661)
    ·
      refine ⟨35885851801929868660403873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95695604805146316427743661 35885851801929868660403873)
      ·
        refine ⟨26914388851447401495302905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35885851801929868660403873 26914388851447401495302905)
        ·
          refine ⟨20185791638585551121477179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26914388851447401495302905 20185791638585551121477179)
          ·
            refine ⟨30278687457878326682215769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20185791638585551121477179 30278687457878326682215769)
            ·
              refine ⟨22709015593408745011661827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30278687457878326682215769 22709015593408745011661827)
              ·
                refine ⟨34063523390113117517492741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22709015593408745011661827 34063523390113117517492741)
                ·
                  refine ⟨6386910635646209534529889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34063523390113117517492741 6386910635646209534529889)
                  ·
                    refine ⟨4790182976734657150897417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6386910635646209534529889 4790182976734657150897417)
                    ·
                      refine ⟨3592637232550992863173063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4790182976734657150897417 3592637232550992863173063)
                      ·
                        rfl

theorem cell23_6996636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_6996636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996636 prefixEnd_6996636 := by exact prefixLift 6996636
  have htrace : WordTrace (prefixWord ++ tailWord_6996636) baseStart_6996636 baseEnd_6996636 := by
    simpa [prefixWord, tailWord_6996636, baseEnd_6996636] using wordTrace_append hprefix tailTrace_6996636
  have hstable : (prefixWord ++ tailWord_6996636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996636).length < 2 ^ (prefixWord ++ tailWord_6996636).sum := by decide
  have hdescent : baseEnd_6996636 < baseStart_6996636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996647 : List Nat := [1, 1, 6, 3, 2, 1, 2, 1, 2, 1, 3]
def baseStart_6996647 : Nat := 118140960795 + 6996647 * 2 ^ 59
def prefixEnd_6996647 : Nat := 4983230072969 + 3 ^ 40 * 6996647 * 2
def baseEnd_6996647 : Nat := 3592642880838192320135513

theorem tailTrace_6996647 : CollatzResearch.WordTrace tailWord_6996647 prefixEnd_6996647 3592642880838192320135513 := by
  unfold tailWord_6996647
  simp only [CollatzResearch.WordTrace]
  refine ⟨255188680683350326019300195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170125787122233550679533463 255188680683350326019300195)
  ·
    refine ⟨382783021025025489028950293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255188680683350326019300195 382783021025025489028950293)
    ·
      refine ⟨17942954110548069798232045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 382783021025025489028950293 17942954110548069798232045)
      ·
        refine ⟨6728607791455526174337017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17942954110548069798232045 6728607791455526174337017)
        ·
          refine ⟨5046455843591644630752763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6728607791455526174337017 5046455843591644630752763)
          ·
            refine ⟨7569683765387466946129145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5046455843591644630752763 7569683765387466946129145)
            ·
              refine ⟨5677262824040600209596859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7569683765387466946129145 5677262824040600209596859)
              ·
                refine ⟨8515894236060900314395289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5677262824040600209596859 8515894236060900314395289)
                ·
                  refine ⟨6386920677045675235796467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8515894236060900314395289 6386920677045675235796467)
                  ·
                    refine ⟨9580381015568512853694701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6386920677045675235796467 9580381015568512853694701)
                    ·
                      refine ⟨3592642880838192320135513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9580381015568512853694701 3592642880838192320135513)
                      ·
                        rfl

theorem cell23_6996647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_6996647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996647 prefixEnd_6996647 := by exact prefixLift 6996647
  have htrace : WordTrace (prefixWord ++ tailWord_6996647) baseStart_6996647 baseEnd_6996647 := by
    simpa [prefixWord, tailWord_6996647, baseEnd_6996647] using wordTrace_append hprefix tailTrace_6996647
  have hstable : (prefixWord ++ tailWord_6996647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996647).length < 2 ^ (prefixWord ++ tailWord_6996647).sum := by decide
  have hdescent : baseEnd_6996647 < baseStart_6996647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996653 : List Nat := [1, 5, 2, 1, 1, 3, 1, 3, 2, 2, 2]
def baseStart_6996653 : Nat := 118140960795 + 6996653 * 2 ^ 59
def prefixEnd_6996653 : Nat := 4983230072969 + 3 ^ 40 * 6996653 * 2
def baseEnd_6996653 : Nat := 3592645961722119296660485

theorem tailTrace_6996653 : CollatzResearch.WordTrace tailWord_6996653 prefixEnd_6996653 3592645961722119296660485 := by
  unfold tailWord_6996653
  simp only [CollatzResearch.WordTrace]
  refine ⟨255188899521328589044018613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170125933014219059362679075 255188899521328589044018613)
  ·
    refine ⟨23923959330124555222876745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 255188899521328589044018613 23923959330124555222876745)
    ·
      refine ⟨17942969497593416417157559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23923959330124555222876745 17942969497593416417157559)
      ·
        refine ⟨26914454246390124625736339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17942969497593416417157559 26914454246390124625736339)
        ·
          refine ⟨40371681369585186938604509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26914454246390124625736339 40371681369585186938604509)
          ·
            refine ⟨15139380513594445101976691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40371681369585186938604509 15139380513594445101976691)
            ·
              refine ⟨22709070770391667652965037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15139380513594445101976691 22709070770391667652965037)
              ·
                refine ⟨8515901538896875369861889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22709070770391667652965037 8515901538896875369861889)
                ·
                  refine ⟨6386926154172656527396417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8515901538896875369861889 6386926154172656527396417)
                  ·
                    refine ⟨4790194615629492395547313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6386926154172656527396417 4790194615629492395547313)
                    ·
                      refine ⟨3592645961722119296660485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4790194615629492395547313 3592645961722119296660485)
                      ·
                        rfl

theorem cell23_6996653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_6996653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996653 prefixEnd_6996653 := by exact prefixLift 6996653
  have htrace : WordTrace (prefixWord ++ tailWord_6996653) baseStart_6996653 baseEnd_6996653 := by
    simpa [prefixWord, tailWord_6996653, baseEnd_6996653] using wordTrace_append hprefix tailTrace_6996653
  have hstable : (prefixWord ++ tailWord_6996653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996653).length < 2 ^ (prefixWord ++ tailWord_6996653).sum := by decide
  have hdescent : baseEnd_6996653 < baseStart_6996653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996665 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 3, 1, 7]
def baseStart_6996665 : Nat := 118140960795 + 6996665 * 2 ^ 59
def prefixEnd_6996665 : Nat := 4983230072969 + 3 ^ 40 * 6996665 * 2
def baseEnd_6996665 : Nat := 3592652123489973249710429

theorem tailTrace_6996665 : CollatzResearch.WordTrace tailWord_6996665 prefixEnd_6996665 3592652123489973249710429 := by
  unfold tailWord_6996665
  simp only [CollatzResearch.WordTrace]
  refine ⟨255189337197285115093455449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170126224798190076728970299 255189337197285115093455449)
  ·
    refine ⟨191392002897963836320091587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255189337197285115093455449 191392002897963836320091587)
    ·
      refine ⟨287088004346945754480137381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191392002897963836320091587 287088004346945754480137381)
      ·
        refine ⟨53829000815052328965025759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 287088004346945754480137381 53829000815052328965025759)
        ·
          refine ⟨80743501222578493447538639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53829000815052328965025759 80743501222578493447538639)
          ·
            refine ⟨121115251833867740171307959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80743501222578493447538639 121115251833867740171307959)
            ·
              refine ⟨181672877750801610256961939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121115251833867740171307959 181672877750801610256961939)
              ·
                refine ⟨272509316626202415385442909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181672877750801610256961939 272509316626202415385442909)
                ·
                  refine ⟨102190993734825905769541091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 272509316626202415385442909 102190993734825905769541091)
                  ·
                    refine ⟨153286490602238858654311637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102190993734825905769541091 153286490602238858654311637)
                    ·
                      refine ⟨3592652123489973249710429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 153286490602238858654311637 3592652123489973249710429)
                      ·
                        rfl

theorem cell23_6996665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_6996665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996665 prefixEnd_6996665 := by exact prefixLift 6996665
  have htrace : WordTrace (prefixWord ++ tailWord_6996665) baseStart_6996665 baseEnd_6996665 := by
    simpa [prefixWord, tailWord_6996665, baseEnd_6996665] using wordTrace_append hprefix tailTrace_6996665
  have hstable : (prefixWord ++ tailWord_6996665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996665).length < 2 ^ (prefixWord ++ tailWord_6996665).sum := by decide
  have hdescent : baseEnd_6996665 < baseStart_6996665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996672 : List Nat := [2, 1, 1, 2, 4, 2, 1, 3, 2, 5]
def baseStart_6996672 : Nat := 118140960795 + 6996672 * 2 ^ 59
def prefixEnd_6996672 : Nat := 4983230072969 + 3 ^ 40 * 6996672 * 2
def baseEnd_6996672 : Nat := 1197551905951518240774299

theorem tailTrace_6996672 : CollatzResearch.WordTrace tailWord_6996672 prefixEnd_6996672 1197551905951518240774299 := by
  unfold tailWord_6996672
  simp only [CollatzResearch.WordTrace]
  refine ⟨127594796254129877644480135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170126395005506503525973513 127594796254129877644480135)
  ·
    refine ⟨191392194381194816466720203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127594796254129877644480135 191392194381194816466720203)
    ·
      refine ⟨287088291571792224700080305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191392194381194816466720203 287088291571792224700080305)
      ·
        refine ⟨215316218678844168525060229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287088291571792224700080305 215316218678844168525060229)
        ·
          refine ⟨40371791002283281598448793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215316218678844168525060229 40371791002283281598448793)
          ·
            refine ⟨30278843251712461198836595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40371791002283281598448793 30278843251712461198836595)
            ·
              refine ⟨45418264877568691798254893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30278843251712461198836595 45418264877568691798254893)
              ·
                refine ⟨17031849329088259424345585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45418264877568691798254893 17031849329088259424345585)
                ·
                  refine ⟨12773886996816194568259189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17031849329088259424345585 12773886996816194568259189)
                  ·
                    refine ⟨1197551905951518240774299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12773886996816194568259189 1197551905951518240774299)
                    ·
                      rfl

theorem cell23_6996672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 2, 5].length) (baseStart_6996672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996672 prefixEnd_6996672 := by exact prefixLift 6996672
  have htrace : WordTrace (prefixWord ++ tailWord_6996672) baseStart_6996672 baseEnd_6996672 := by
    simpa [prefixWord, tailWord_6996672, baseEnd_6996672] using wordTrace_append hprefix tailTrace_6996672
  have hstable : (prefixWord ++ tailWord_6996672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996672).length < 2 ^ (prefixWord ++ tailWord_6996672).sum := by decide
  have hdescent : baseEnd_6996672 < baseStart_6996672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996682 : List Nat := [3, 1, 2, 1, 4, 1, 1, 2, 1, 2, 5]
def baseStart_6996682 : Nat := 118140960795 + 6996682 * 2 ^ 59
def prefixEnd_6996682 : Nat := 4983230072969 + 3 ^ 40 * 6996682 * 2
def baseEnd_6996682 : Nat := 3592660852661099683197851

theorem tailTrace_6996682 : CollatzResearch.WordTrace tailWord_6996682 prefixEnd_6996682 3592660852661099683197851 := by
  unfold tailWord_6996682
  simp only [CollatzResearch.WordTrace]
  refine ⟨63797489309555881749206075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170126638158815684664549533 63797489309555881749206075)
  ·
    refine ⟨95696233964333822623809113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63797489309555881749206075 95696233964333822623809113)
    ·
      refine ⟨71772175473250366967856835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95696233964333822623809113 71772175473250366967856835)
      ·
        refine ⟨107658263209875550451785253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71772175473250366967856835 107658263209875550451785253)
        ·
          refine ⟨20185924351851665709709735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107658263209875550451785253 20185924351851665709709735)
          ·
            refine ⟨30278886527777498564564603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20185924351851665709709735 30278886527777498564564603)
            ·
              refine ⟨45418329791666247846846905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30278886527777498564564603 45418329791666247846846905)
              ·
                refine ⟨34063747343749685885135179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45418329791666247846846905 34063747343749685885135179)
                ·
                  refine ⟨51095621015624528827702769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34063747343749685885135179 51095621015624528827702769)
                  ·
                    refine ⟨38321715761718396620777077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51095621015624528827702769 38321715761718396620777077)
                    ·
                      refine ⟨3592660852661099683197851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38321715761718396620777077 3592660852661099683197851)
                      ·
                        rfl

theorem cell23_6996682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_6996682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996682 prefixEnd_6996682 := by exact prefixLift 6996682
  have htrace : WordTrace (prefixWord ++ tailWord_6996682) baseStart_6996682 baseEnd_6996682 := by
    simpa [prefixWord, tailWord_6996682, baseEnd_6996682] using wordTrace_append hprefix tailTrace_6996682
  have hstable : (prefixWord ++ tailWord_6996682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996682).length < 2 ^ (prefixWord ++ tailWord_6996682).sum := by decide
  have hdescent : baseEnd_6996682 < baseStart_6996682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996709 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 1, 6, 2]
def baseStart_6996709 : Nat := 118140960795 + 6996709 * 2 ^ 59
def prefixEnd_6996709 : Nat := 4983230072969 + 3 ^ 40 * 6996709 * 2
def baseEnd_6996709 : Nat := 3592674716638771077560227

theorem tailTrace_6996709 : CollatzResearch.WordTrace tailWord_6996709 prefixEnd_6996709 3592674716638771077560227 := by
  unfold tailWord_6996709
  simp only [CollatzResearch.WordTrace]
  refine ⟨255190942009125710608057181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170127294672750473738704787 255190942009125710608057181)
  ·
    refine ⟨95696603253422141478021443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255190942009125710608057181 95696603253422141478021443)
    ·
      refine ⟨143544904880133212217032165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95696603253422141478021443 143544904880133212217032165)
      ·
        refine ⟨26914669665024977290693531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143544904880133212217032165 26914669665024977290693531)
        ·
          refine ⟨40372004497537465936040297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26914669665024977290693531 40372004497537465936040297)
          ·
            refine ⟨30279003373153099452030223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40372004497537465936040297 30279003373153099452030223)
            ·
              refine ⟨45418505059729649178045335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30279003373153099452030223 45418505059729649178045335)
              ·
                refine ⟨68127757589594473767068003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45418505059729649178045335 68127757589594473767068003)
                ·
                  refine ⟨102191636384391710650602005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68127757589594473767068003 102191636384391710650602005)
                  ·
                    refine ⟨4790232955518361436746969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 102191636384391710650602005 4790232955518361436746969)
                    ·
                      refine ⟨3592674716638771077560227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4790232955518361436746969 3592674716638771077560227)
                      ·
                        rfl

theorem cell23_6996709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_6996709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996709 prefixEnd_6996709 := by exact prefixLift 6996709
  have htrace : WordTrace (prefixWord ++ tailWord_6996709) baseStart_6996709 baseEnd_6996709 := by
    simpa [prefixWord, tailWord_6996709, baseEnd_6996709] using wordTrace_append hprefix tailTrace_6996709
  have hstable : (prefixWord ++ tailWord_6996709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996709).length < 2 ^ (prefixWord ++ tailWord_6996709).sum := by decide
  have hdescent : baseEnd_6996709 < baseStart_6996709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996715 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 10]
def baseStart_6996715 : Nat := 118140960795 + 6996715 * 2 ^ 59
def prefixEnd_6996715 : Nat := 4983230072969 + 3 ^ 40 * 6996715 * 2
def baseEnd_6996715 : Nat := 399186421946966450453911

theorem tailTrace_6996715 : CollatzResearch.WordTrace tailWord_6996715 prefixEnd_6996715 399186421946966450453911 := by
  unfold tailWord_6996715
  simp only [CollatzResearch.WordTrace]
  refine ⟨255191160847103973632775599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170127440564735982421850399 255191160847103973632775599)
  ·
    refine ⟨382786741270655960449163399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255191160847103973632775599 382786741270655960449163399)
    ·
      refine ⟨574180111905983940673745099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382786741270655960449163399 574180111905983940673745099)
      ·
        refine ⟨861270167858975911010617649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574180111905983940673745099 861270167858975911010617649)
        ·
          refine ⟨645952625894231933257963237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 861270167858975911010617649 645952625894231933257963237)
          ·
            refine ⟨121116117355168487485868107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 645952625894231933257963237 121116117355168487485868107)
            ·
              refine ⟨181674176032752731228802161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121116117355168487485868107 181674176032752731228802161)
              ·
                refine ⟨136255632024564548421601621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181674176032752731228802161 136255632024564548421601621)
                ·
                  refine ⟨399186421946966450453911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 136255632024564548421601621 399186421946966450453911)
                  ·
                    rfl

theorem cell23_6996715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 10].length) (baseStart_6996715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996715 prefixEnd_6996715 := by exact prefixLift 6996715
  have htrace : WordTrace (prefixWord ++ tailWord_6996715) baseStart_6996715 baseEnd_6996715 := by
    simpa [prefixWord, tailWord_6996715, baseEnd_6996715] using wordTrace_append hprefix tailTrace_6996715
  have hstable : (prefixWord ++ tailWord_6996715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996715).length < 2 ^ (prefixWord ++ tailWord_6996715).sum := by decide
  have hdescent : baseEnd_6996715 < baseStart_6996715 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996719 : List Nat := [1, 1, 2, 1, 5, 3, 1, 2, 3, 4]
def baseStart_6996719 : Nat := 118140960795 + 6996719 * 2 ^ 59
def prefixEnd_6996719 : Nat := 4983230072969 + 3 ^ 40 * 6996719 * 2
def baseEnd_6996719 : Nat := 1197559950481772012811727

theorem tailTrace_6996719 : CollatzResearch.WordTrace tailWord_6996719 prefixEnd_6996719 1197559950481772012811727 := by
  unfold tailWord_6996719
  simp only [CollatzResearch.WordTrace]
  refine ⟨255191306739089482315921211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170127537826059654877280807 255191306739089482315921211)
  ·
    refine ⟨382786960108634223473881817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255191306739089482315921211 382786960108634223473881817)
    ·
      refine ⟨287090220081475667605411363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382786960108634223473881817 287090220081475667605411363)
      ·
        refine ⟨430635330122213501408117045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287090220081475667605411363 430635330122213501408117045)
        ·
          refine ⟨40372062198957515757010973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 430635330122213501408117045 40372062198957515757010973)
          ·
            refine ⟨15139523324609068408879115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40372062198957515757010973 15139523324609068408879115)
            ·
              refine ⟨22709284986913602613318673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15139523324609068408879115 22709284986913602613318673)
              ·
                refine ⟨17031963740185201959989005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22709284986913602613318673 17031963740185201959989005)
                ·
                  refine ⟨6386986402569450734995877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17031963740185201959989005 6386986402569450734995877)
                  ·
                    refine ⟨1197559950481772012811727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6386986402569450734995877 1197559950481772012811727)
                    ·
                      rfl

theorem cell23_6996719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 3, 4].length) (baseStart_6996719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996719 prefixEnd_6996719 := by exact prefixLift 6996719
  have htrace : WordTrace (prefixWord ++ tailWord_6996719) baseStart_6996719 baseEnd_6996719 := by
    simpa [prefixWord, tailWord_6996719, baseEnd_6996719] using wordTrace_append hprefix tailTrace_6996719
  have hstable : (prefixWord ++ tailWord_6996719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996719).length < 2 ^ (prefixWord ++ tailWord_6996719).sum := by decide
  have hdescent : baseEnd_6996719 < baseStart_6996719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996769 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 3, 5, 2]
def baseStart_6996769 : Nat := 118140960795 + 6996769 * 2 ^ 59
def prefixEnd_6996769 : Nat := 4983230072969 + 3 ^ 40 * 6996769 * 2
def baseEnd_6996769 : Nat := 3592705525478040842809951

theorem tailTrace_6996769 : CollatzResearch.WordTrace tailWord_6996769 prefixEnd_6996769 3592705525478040842809951 := by
  unfold tailWord_6996769
  simp only [CollatzResearch.WordTrace]
  refine ⟨255193130388908340855241361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170128753592605560570160907 255193130388908340855241361)
  ·
    refine ⟨191394847791681255641431021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255193130388908340855241361 191394847791681255641431021)
    ·
      refine ⟨71773067921880470865536633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191394847791681255641431021 71773067921880470865536633)
      ·
        refine ⟨53829800941410353149152475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71773067921880470865536633 53829800941410353149152475)
        ·
          refine ⟨80744701412115529723728713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53829800941410353149152475 80744701412115529723728713)
          ·
            refine ⟨60558526059086647292796535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80744701412115529723728713 60558526059086647292796535)
            ·
              refine ⟨90837789088629970939194803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60558526059086647292796535 90837789088629970939194803)
              ·
                refine ⟨136256683632944956408792205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90837789088629970939194803 136256683632944956408792205)
                ·
                  refine ⟨51096256362354358653297077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136256683632944956408792205 51096256362354358653297077)
                  ·
                    refine ⟨4790274033970721123746601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51096256362354358653297077 4790274033970721123746601)
                    ·
                      refine ⟨3592705525478040842809951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4790274033970721123746601 3592705525478040842809951)
                      ·
                        rfl

theorem cell23_6996769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_6996769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996769 prefixEnd_6996769 := by exact prefixLift 6996769
  have htrace : WordTrace (prefixWord ++ tailWord_6996769) baseStart_6996769 baseEnd_6996769 := by
    simpa [prefixWord, tailWord_6996769, baseEnd_6996769] using wordTrace_append hprefix tailTrace_6996769
  have hstable : (prefixWord ++ tailWord_6996769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996769).length < 2 ^ (prefixWord ++ tailWord_6996769).sum := by decide
  have hdescent : baseEnd_6996769 < baseStart_6996769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996776 : List Nat := [2, 1, 5, 1, 1, 1, 1, 4, 3, 1, 3]
def baseStart_6996776 : Nat := 118140960795 + 6996776 * 2 ^ 59
def prefixEnd_6996776 : Nat := 4983230072969 + 3 ^ 40 * 6996776 * 2
def baseEnd_6996776 : Nat := 3592709119842622315422419

theorem tailTrace_6996776 : CollatzResearch.WordTrace tailWord_6996776 prefixEnd_6996776 3592709119842622315422419 := by
  unfold tailWord_6996776
  simp only [CollatzResearch.WordTrace]
  refine ⟨127596692849941490525373091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170128923799921987367164121 127596692849941490525373091)
  ·
    refine ⟨191395039274912235788059637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127596692849941490525373091 191395039274912235788059637)
    ·
      refine ⟨17943284932023022105130591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 191395039274912235788059637 17943284932023022105130591)
      ·
        refine ⟨26914927398034533157695887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17943284932023022105130591 26914927398034533157695887)
        ·
          refine ⟨40372391097051799736543831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26914927398034533157695887 40372391097051799736543831)
          ·
            refine ⟨60558586645577699604815747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40372391097051799736543831 60558586645577699604815747)
            ·
              refine ⟨90837879968366549407223621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60558586645577699604815747 90837879968366549407223621)
              ·
                refine ⟨17032102494068728013854429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90837879968366549407223621 17032102494068728013854429)
                ·
                  refine ⟨6387038435275773005195411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17032102494068728013854429 6387038435275773005195411)
                  ·
                    refine ⟨9580557652913659507793117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6387038435275773005195411 9580557652913659507793117)
                    ·
                      refine ⟨3592709119842622315422419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9580557652913659507793117 3592709119842622315422419)
                      ·
                        rfl

theorem cell23_6996776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_6996776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996776 prefixEnd_6996776 := by exact prefixLift 6996776
  have htrace : WordTrace (prefixWord ++ tailWord_6996776) baseStart_6996776 baseEnd_6996776 := by
    simpa [prefixWord, tailWord_6996776, baseEnd_6996776] using wordTrace_append hprefix tailTrace_6996776
  have hstable : (prefixWord ++ tailWord_6996776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996776).length < 2 ^ (prefixWord ++ tailWord_6996776).sum := by decide
  have hdescent : baseEnd_6996776 < baseStart_6996776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996786 : List Nat := [3, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2]
def baseStart_6996786 : Nat := 118140960795 + 6996786 * 2 ^ 59
def prefixEnd_6996786 : Nat := 4983230072969 + 3 ^ 40 * 6996786 * 2
def baseEnd_6996786 : Nat := 3592714254649167276297373

theorem tailTrace_6996786 : CollatzResearch.WordTrace tailWord_6996786 prefixEnd_6996786 3592714254649167276297373 := by
  unfold tailWord_6996786
  simp only [CollatzResearch.WordTrace]
  refine ⟨63798437607461688189652553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170129166953231168505740141 63798437607461688189652553)
  ·
    refine ⟨47848828205596266142239415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63798437607461688189652553 47848828205596266142239415)
    ·
      refine ⟨71773242308394399213359123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47848828205596266142239415 71773242308394399213359123)
      ·
        refine ⟨107659863462591598820038685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71773242308394399213359123 107659863462591598820038685)
        ·
          refine ⟨40372448798471849557514507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107659863462591598820038685 40372448798471849557514507)
          ·
            refine ⟨60558673197707774336271761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40372448798471849557514507 60558673197707774336271761)
            ·
              refine ⟨45419004898280830752203821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60558673197707774336271761 45419004898280830752203821)
              ·
                refine ⟨17032126836855311532076433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45419004898280830752203821 17032126836855311532076433)
                ·
                  refine ⟨12774095127641483649057325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17032126836855311532076433 12774095127641483649057325)
                  ·
                    refine ⟨4790285672865556368396497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12774095127641483649057325 4790285672865556368396497)
                    ·
                      refine ⟨3592714254649167276297373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4790285672865556368396497 3592714254649167276297373)
                      ·
                        rfl

theorem cell23_6996786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2].length) (baseStart_6996786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996786 prefixEnd_6996786 := by exact prefixLift 6996786
  have htrace : WordTrace (prefixWord ++ tailWord_6996786) baseStart_6996786 baseEnd_6996786 := by
    simpa [prefixWord, tailWord_6996786, baseEnd_6996786] using wordTrace_append hprefix tailTrace_6996786
  have hstable : (prefixWord ++ tailWord_6996786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996786).length < 2 ^ (prefixWord ++ tailWord_6996786).sum := by decide
  have hdescent : baseEnd_6996786 < baseStart_6996786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996792 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 3, 6]
def baseStart_6996792 : Nat := 118140960795 + 6996792 * 2 ^ 59
def prefixEnd_6996792 : Nat := 4983230072969 + 3 ^ 40 * 6996792 * 2
def baseEnd_6996792 : Nat := 1197572445177698084274115

theorem tailTrace_6996792 : CollatzResearch.WordTrace tailWord_6996792 prefixEnd_6996792 1197572445177698084274115 := by
  unfold tailWord_6996792
  simp only [CollatzResearch.WordTrace]
  refine ⟨127596984633912507891664315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170129312845216677188885753 127596984633912507891664315)
  ·
    refine ⟨191395476950868761837496473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127596984633912507891664315 191395476950868761837496473)
    ·
      refine ⟨143546607713151571378122355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191395476950868761837496473 143546607713151571378122355)
      ·
        refine ⟨215319911569727357067183533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143546607713151571378122355 215319911569727357067183533)
        ·
          refine ⟨80744966838647758900193825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215319911569727357067183533 80744966838647758900193825)
          ·
            refine ⟨60558725128985819175145369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80744966838647758900193825 60558725128985819175145369)
            ·
              refine ⟨45419043846739364381359027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60558725128985819175145369 45419043846739364381359027)
              ·
                refine ⟨68128565770109046572038541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45419043846739364381359027 68128565770109046572038541)
                ·
                  refine ⟨25548212163790892464514453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68128565770109046572038541 25548212163790892464514453)
                  ·
                    refine ⟨1197572445177698084274115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25548212163790892464514453 1197572445177698084274115)
                    ·
                      rfl

theorem cell23_6996792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 3, 6].length) (baseStart_6996792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996792 prefixEnd_6996792 := by exact prefixLift 6996792
  have htrace : WordTrace (prefixWord ++ tailWord_6996792) baseStart_6996792 baseEnd_6996792 := by
    simpa [prefixWord, tailWord_6996792, baseEnd_6996792] using wordTrace_append hprefix tailTrace_6996792
  have hstable : (prefixWord ++ tailWord_6996792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996792).length < 2 ^ (prefixWord ++ tailWord_6996792).sum := by decide
  have hdescent : baseEnd_6996792 < baseStart_6996792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996809 : List Nat := [1, 2, 1, 1, 2, 5, 2, 1, 4, 4]
def baseStart_6996809 : Nat := 118140960795 + 6996809 * 2 ^ 59
def prefixEnd_6996809 : Nat := 4983230072969 + 3 ^ 40 * 6996809 * 2
def baseEnd_6996809 : Nat := 1197575354901406895436589

theorem tailTrace_6996809 : CollatzResearch.WordTrace tailWord_6996809 prefixEnd_6996809 1197575354901406895436589 := by
  unfold tailWord_6996809
  simp only [CollatzResearch.WordTrace]
  refine ⟨255194589308763427686697481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170129726205842285124464987 255194589308763427686697481)
  ·
    refine ⟨191395941981572570765023111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255194589308763427686697481 191395941981572570765023111)
    ·
      refine ⟨287093912972358856147534667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191395941981572570765023111 287093912972358856147534667)
      ·
        refine ⟨430640869458538284221302001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287093912972358856147534667 430640869458538284221302001)
        ·
          refine ⟨322980652093903713165976501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 430640869458538284221302001 322980652093903713165976501)
          ·
            refine ⟨30279436133803473109310297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 322980652093903713165976501 30279436133803473109310297)
            ·
              refine ⟨22709577100352604831982723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30279436133803473109310297 22709577100352604831982723)
              ·
                refine ⟨34064365650528907247974085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22709577100352604831982723 34064365650528907247974085)
                ·
                  refine ⟨6387068559474170108995141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34064365650528907247974085 6387068559474170108995141)
                  ·
                    refine ⟨1197575354901406895436589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6387068559474170108995141 1197575354901406895436589)
                    ·
                      rfl

theorem cell23_6996809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 4, 4].length) (baseStart_6996809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996809 prefixEnd_6996809 := by exact prefixLift 6996809
  have htrace : WordTrace (prefixWord ++ tailWord_6996809) baseStart_6996809 baseEnd_6996809 := by
    simpa [prefixWord, tailWord_6996809, baseEnd_6996809] using wordTrace_append hprefix tailTrace_6996809
  have hstable : (prefixWord ++ tailWord_6996809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996809).length < 2 ^ (prefixWord ++ tailWord_6996809).sum := by decide
  have hdescent : baseEnd_6996809 < baseStart_6996809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996826 : List Nat := [3, 1, 1, 2, 1, 5, 1, 3, 2, 4]
def baseStart_6996826 : Nat := 118140960795 + 6996826 * 2 ^ 59
def prefixEnd_6996826 : Nat := 4983230072969 + 3 ^ 40 * 6996826 * 2
def baseEnd_6996826 : Nat := 1197578264625115706599063

theorem tailTrace_6996826 : CollatzResearch.WordTrace tailWord_6996826 prefixEnd_6996826 1197578264625115706599063 := by
  unfold tailWord_6996826
  simp only [CollatzResearch.WordTrace]
  refine ⟨63798802337425459897516583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170130139566467893060044221 63798802337425459897516583)
  ·
    refine ⟨95698203506138189846274875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63798802337425459897516583 95698203506138189846274875)
    ·
      refine ⟨143547305259207284769412313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95698203506138189846274875 143547305259207284769412313)
      ·
        refine ⟨107660478944405463577059235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143547305259207284769412313 107660478944405463577059235)
        ·
          refine ⟨161490718416608195365588853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107660478944405463577059235 161490718416608195365588853)
          ·
            refine ⟨15139754851557018315523955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 161490718416608195365588853 15139754851557018315523955)
            ·
              refine ⟨22709632277335527473285933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15139754851557018315523955 22709632277335527473285933)
              ·
                refine ⟨8516112104000822802482225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22709632277335527473285933 8516112104000822802482225)
                ·
                  refine ⟨6387084078000617101861669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8516112104000822802482225 6387084078000617101861669)
                  ·
                    refine ⟨1197578264625115706599063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6387084078000617101861669 1197578264625115706599063)
                    ·
                      rfl

theorem cell23_6996826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 2, 4].length) (baseStart_6996826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996826 prefixEnd_6996826 := by exact prefixLift 6996826
  have htrace : WordTrace (prefixWord ++ tailWord_6996826) baseStart_6996826 baseEnd_6996826 := by
    simpa [prefixWord, tailWord_6996826, baseEnd_6996826] using wordTrace_append hprefix tailTrace_6996826
  have hstable : (prefixWord ++ tailWord_6996826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996826).length < 2 ^ (prefixWord ++ tailWord_6996826).sum := by decide
  have hdescent : baseEnd_6996826 < baseStart_6996826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996836 : List Nat := [2, 3, 1, 1, 4, 2, 1, 1, 3, 2, 3]
def baseStart_6996836 : Nat := 118140960795 + 6996836 * 2 ^ 59
def prefixEnd_6996836 : Nat := 4983230072969 + 3 ^ 40 * 6996836 * 2
def baseEnd_6996836 : Nat := 3592739928681892080672143

theorem tailTrace_6996836 : CollatzResearch.WordTrace tailWord_6996836 prefixEnd_6996836 3592739928681892080672143 := by
  unfold tailWord_6996836
  simp only [CollatzResearch.WordTrace]
  refine ⟨127597787039832805648965181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170130382719777074198620241 127597787039832805648965181)
  ·
    refine ⟨47849170139937302118361943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127597787039832805648965181 47849170139937302118361943)
    ·
      refine ⟨71773755209905953177542915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47849170139937302118361943 71773755209905953177542915)
      ·
        refine ⟨107660632814858929766314373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71773755209905953177542915 107660632814858929766314373)
        ·
          refine ⟨20186368652786049331183945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107660632814858929766314373 20186368652786049331183945)
          ·
            refine ⟨15139776489589536998387959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20186368652786049331183945 15139776489589536998387959)
            ·
              refine ⟨22709664734384305497581939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15139776489589536998387959 22709664734384305497581939)
              ·
                refine ⟨34064497101576458246372909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22709664734384305497581939 34064497101576458246372909)
                ·
                  refine ⟨12774186413091171842389841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34064497101576458246372909 12774186413091171842389841)
                  ·
                    refine ⟨9580639809818378881792381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12774186413091171842389841 9580639809818378881792381)
                    ·
                      refine ⟨3592739928681892080672143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9580639809818378881792381 3592739928681892080672143)
                      ·
                        rfl

theorem cell23_6996836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_6996836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996836 prefixEnd_6996836 := by exact prefixLift 6996836
  have htrace : WordTrace (prefixWord ++ tailWord_6996836) baseStart_6996836 baseEnd_6996836 := by
    simpa [prefixWord, tailWord_6996836, baseEnd_6996836] using wordTrace_append hprefix tailTrace_6996836
  have hstable : (prefixWord ++ tailWord_6996836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996836).length < 2 ^ (prefixWord ++ tailWord_6996836).sum := by decide
  have hdescent : baseEnd_6996836 < baseStart_6996836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996849 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 3, 3, 3]
def baseStart_6996849 : Nat := 118140960795 + 6996849 * 2 ^ 59
def prefixEnd_6996849 : Nat := 4983230072969 + 3 ^ 40 * 6996849 * 2
def baseEnd_6996849 : Nat := 3592746603930400529809583

theorem tailTrace_6996849 : CollatzResearch.WordTrace tailWord_6996849 prefixEnd_6996849 3592746603930400529809583 := by
  unfold tailWord_6996849
  simp only [CollatzResearch.WordTrace]
  refine ⟨255196048228618514518153601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170130698819079009678769067 255196048228618514518153601)
  ·
    refine ⟨191397036171463885888615201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255196048228618514518153601 191397036171463885888615201)
    ·
      refine ⟨143547777128597914416461401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191397036171463885888615201 143547777128597914416461401)
      ·
        refine ⟨107660832846448435812346051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143547777128597914416461401 107660832846448435812346051)
        ·
          refine ⟨161491249269672653718519077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107660832846448435812346051 161491249269672653718519077)
          ·
            refine ⟨30279609238063622572222327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161491249269672653718519077 30279609238063622572222327)
            ·
              refine ⟨45419413857095433858333491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30279609238063622572222327 45419413857095433858333491)
              ·
                refine ⟨68129120785643150787500237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45419413857095433858333491 68129120785643150787500237)
                ·
                  refine ⟨25548420294616181545312589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68129120785643150787500237 25548420294616181545312589)
                  ·
                    refine ⟨9580657610481068079492221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25548420294616181545312589 9580657610481068079492221)
                    ·
                      refine ⟨3592746603930400529809583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9580657610481068079492221 3592746603930400529809583)
                      ·
                        rfl

theorem cell23_6996849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_6996849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996849 prefixEnd_6996849 := by exact prefixLift 6996849
  have htrace : WordTrace (prefixWord ++ tailWord_6996849) baseStart_6996849 baseEnd_6996849 := by
    simpa [prefixWord, tailWord_6996849, baseEnd_6996849] using wordTrace_append hprefix tailTrace_6996849
  have hstable : (prefixWord ++ tailWord_6996849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996849).length < 2 ^ (prefixWord ++ tailWord_6996849).sum := by decide
  have hdescent : baseEnd_6996849 < baseStart_6996849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996876 : List Nat := [2, 2, 1, 2, 1, 2, 3, 2, 3, 3, 2]
def baseStart_6996876 : Nat := 118140960795 + 6996876 * 2 ^ 59
def prefixEnd_6996876 : Nat := 4983230072969 + 3 ^ 40 * 6996876 * 2
def baseEnd_6996876 : Nat := 3592760467908071924171959

theorem tailTrace_6996876 : CollatzResearch.WordTrace tailWord_6996876 prefixEnd_6996876 3592760467908071924171959 := by
  unfold tailWord_6996876
  simp only [CollatzResearch.WordTrace]
  refine ⟨127598516499760349064693241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170131355333013798752924321 127598516499760349064693241)
  ·
    refine ⟨95698887374820261798519931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127598516499760349064693241 95698887374820261798519931)
    ·
      refine ⟨143548331062230392697779897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95698887374820261798519931 143548331062230392697779897)
      ·
        refine ⟨107661248296672794523334923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143548331062230392697779897 107661248296672794523334923)
        ·
          refine ⟨161491872445009191785002385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107661248296672794523334923 161491872445009191785002385)
          ·
            refine ⟨121118904333756893838751789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161491872445009191785002385 121118904333756893838751789)
            ·
              refine ⟨45419589125158835189531921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121118904333756893838751789 45419589125158835189531921)
              ·
                refine ⟨34064691843869126392148941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45419589125158835189531921 34064691843869126392148941)
                ·
                  refine ⟨12774259441450922397055853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34064691843869126392148941 12774259441450922397055853)
                  ·
                    refine ⟨4790347290544095898895945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12774259441450922397055853 4790347290544095898895945)
                    ·
                      refine ⟨3592760467908071924171959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4790347290544095898895945 3592760467908071924171959)
                      ·
                        rfl

theorem cell23_6996876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 3, 3, 2].length) (baseStart_6996876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996876 prefixEnd_6996876 := by exact prefixLift 6996876
  have htrace : WordTrace (prefixWord ++ tailWord_6996876) baseStart_6996876 baseEnd_6996876 := by
    simpa [prefixWord, tailWord_6996876, baseEnd_6996876] using wordTrace_append hprefix tailTrace_6996876
  have hstable : (prefixWord ++ tailWord_6996876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996876).length < 2 ^ (prefixWord ++ tailWord_6996876).sum := by decide
  have hdescent : baseEnd_6996876 < baseStart_6996876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996893 : List Nat := [1, 4, 2, 1, 2, 1, 2, 4, 1, 3, 2]
def baseStart_6996893 : Nat := 118140960795 + 6996893 * 2 ^ 59
def prefixEnd_6996893 : Nat := 4983230072969 + 3 ^ 40 * 6996893 * 2
def baseEnd_6996893 : Nat := 3592769197079198357659381

theorem tailTrace_6996893 : CollatzResearch.WordTrace tailWord_6996893 prefixEnd_6996893 3592769197079198357659381 := by
  unfold tailWord_6996893
  simp only [CollatzResearch.WordTrace]
  refine ⟨255197653040459110032755333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170131768693639406688503555 255197653040459110032755333)
  ·
    refine ⟨47849559945086083131141625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255197653040459110032755333 47849559945086083131141625)
    ·
      refine ⟨35887169958814562348356219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47849559945086083131141625 35887169958814562348356219)
      ·
        refine ⟨53830754938221843522534329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35887169958814562348356219 53830754938221843522534329)
        ·
          refine ⟨40373066203666382641900747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53830754938221843522534329 40373066203666382641900747)
          ·
            refine ⟨60559599305499573962851121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40373066203666382641900747 60559599305499573962851121)
            ·
              refine ⟨45419699479124680472138341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60559599305499573962851121 45419699479124680472138341)
              ·
                refine ⟨8516193652335877588525939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45419699479124680472138341 8516193652335877588525939)
                ·
                  refine ⟨12774290478503816382788909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8516193652335877588525939 12774290478503816382788909)
                  ·
                    refine ⟨4790358929438931143545841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12774290478503816382788909 4790358929438931143545841)
                    ·
                      refine ⟨3592769197079198357659381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4790358929438931143545841 3592769197079198357659381)
                      ·
                        rfl

theorem cell23_6996893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_6996893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996893 prefixEnd_6996893 := by exact prefixLift 6996893
  have htrace : WordTrace (prefixWord ++ tailWord_6996893) baseStart_6996893 baseEnd_6996893 := by
    simpa [prefixWord, tailWord_6996893, baseEnd_6996893] using wordTrace_append hprefix tailTrace_6996893
  have hstable : (prefixWord ++ tailWord_6996893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996893).length < 2 ^ (prefixWord ++ tailWord_6996893).sum := by decide
  have hdescent : baseEnd_6996893 < baseStart_6996893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996919 : List Nat := [1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 4]
def baseStart_6996919 : Nat := 118140960795 + 6996919 * 2 ^ 59
def prefixEnd_6996919 : Nat := 4983230072969 + 3 ^ 40 * 6996919 * 2
def baseEnd_6996919 : Nat := 3592782547576215255934261

theorem tailTrace_6996919 : CollatzResearch.WordTrace tailWord_6996919 prefixEnd_6996919 3592782547576215255934261 := by
  unfold tailWord_6996919
  simp only [CollatzResearch.WordTrace]
  refine ⟨255198601338364916473201811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170132400892243277648801207 255198601338364916473201811)
  ·
    refine ⟨382797902007547374709802717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255198601338364916473201811 382797902007547374709802717)
    ·
      refine ⟨143549213252830265516176019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 382797902007547374709802717 143549213252830265516176019)
      ·
        refine ⟨215323819879245398274264029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143549213252830265516176019 215323819879245398274264029)
        ·
          refine ⟨80746432454717024352849011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215323819879245398274264029 80746432454717024352849011)
          ·
            refine ⟨121119648682075536529273517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80746432454717024352849011 121119648682075536529273517)
            ·
              refine ⟨45419868255778326198477569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121119648682075536529273517 45419868255778326198477569)
              ·
                refine ⟨34064901191833744648858177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45419868255778326198477569 34064901191833744648858177)
                ·
                  refine ⟨25548675893875308486643633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34064901191833744648858177 25548675893875308486643633)
                  ·
                    refine ⟨19161506920406481364982725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25548675893875308486643633 19161506920406481364982725)
                    ·
                      refine ⟨3592782547576215255934261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19161506920406481364982725 3592782547576215255934261)
                      ·
                        rfl

theorem cell23_6996919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_6996919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996919 prefixEnd_6996919 := by exact prefixLift 6996919
  have htrace : WordTrace (prefixWord ++ tailWord_6996919) baseStart_6996919 baseEnd_6996919 := by
    simpa [prefixWord, tailWord_6996919, baseEnd_6996919] using wordTrace_append hprefix tailTrace_6996919
  have hstable : (prefixWord ++ tailWord_6996919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996919).length < 2 ^ (prefixWord ++ tailWord_6996919).sum := by decide
  have hdescent : baseEnd_6996919 < baseStart_6996919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6996946 : List Nat := [3, 2, 2, 3, 1, 1, 2, 2, 7]
def baseStart_6996946 : Nat := 118140960795 + 6996946 * 2 ^ 59
def prefixEnd_6996946 : Nat := 4983230072969 + 3 ^ 40 * 6996946 * 2
def baseEnd_6996946 : Nat := 399199601283765183366293

theorem tailTrace_6996946 : CollatzResearch.WordTrace tailWord_6996946 prefixEnd_6996946 399199601283765183366293 := by
  unfold tailWord_6996946
  simp only [CollatzResearch.WordTrace]
  refine ⟨63799896527316775021108673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170133057406178066722956461 63799896527316775021108673)
  ·
    refine ⟨47849922395487581265831505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63799896527316775021108673 47849922395487581265831505)
    ·
      refine ⟨35887441796615685949373629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47849922395487581265831505 35887441796615685949373629)
      ·
        refine ⟨13457790673730882231015111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35887441796615685949373629 13457790673730882231015111)
        ·
          refine ⟨20186686010596323346522667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13457790673730882231015111 20186686010596323346522667)
          ·
            refine ⟨30280029015894485019784001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20186686010596323346522667 30280029015894485019784001)
            ·
              refine ⟨22710021761920863764838001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30280029015894485019784001 22710021761920863764838001)
              ·
                refine ⟨17032516321440647823628501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22710021761920863764838001 17032516321440647823628501)
                ·
                  refine ⟨399199601283765183366293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17032516321440647823628501 399199601283765183366293)
                  ·
                    rfl

theorem cell23_6996946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 7].length) (baseStart_6996946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6996946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6996946 prefixEnd_6996946 := by exact prefixLift 6996946
  have htrace : WordTrace (prefixWord ++ tailWord_6996946) baseStart_6996946 baseEnd_6996946 := by
    simpa [prefixWord, tailWord_6996946, baseEnd_6996946] using wordTrace_append hprefix tailTrace_6996946
  have hstable : (prefixWord ++ tailWord_6996946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6996946).length < 2 ^ (prefixWord ++ tailWord_6996946).sum := by decide
  have hdescent : baseEnd_6996946 < baseStart_6996946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6996946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997009 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 4]
def baseStart_6997009 : Nat := 118140960795 + 6997009 * 2 ^ 59
def prefixEnd_6997009 : Nat := 4983230072969 + 3 ^ 40 * 6997009 * 2
def baseEnd_6997009 : Nat := 3592828760835119903808847

theorem tailTrace_6997009 : CollatzResearch.WordTrace tailWord_6997009 prefixEnd_6997009 3592828760835119903808847 := by
  unfold tailWord_6997009
  simp only [CollatzResearch.WordTrace]
  refine ⟨255201883908038861843978081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170134589272025907895985387 255201883908038861843978081)
  ·
    refine ⟨191401412931029146382983561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255201883908038861843978081 191401412931029146382983561)
    ·
      refine ⟨143551059698271859787237671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191401412931029146382983561 143551059698271859787237671)
      ·
        refine ⟨215326589547407789680856507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143551059698271859787237671 215326589547407789680856507)
        ·
          refine ⟨322989884321111684521284761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215326589547407789680856507 322989884321111684521284761)
          ·
            refine ⟨242242413240833763390963571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322989884321111684521284761 242242413240833763390963571)
            ·
              refine ⟨363363619861250645086445357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242242413240833763390963571 363363619861250645086445357)
              ·
                refine ⟨136261357447968991907417009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 363363619861250645086445357 136261357447968991907417009)
                ·
                  refine ⟨102196018085976743930562757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136261357447968991907417009 102196018085976743930562757)
                  ·
                    refine ⟨19161753391120639486980517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102196018085976743930562757 19161753391120639486980517)
                    ·
                      refine ⟨3592828760835119903808847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19161753391120639486980517 3592828760835119903808847)
                      ·
                        rfl

theorem cell23_6997009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_6997009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997009 prefixEnd_6997009 := by exact prefixLift 6997009
  have htrace : WordTrace (prefixWord ++ tailWord_6997009) baseStart_6997009 baseEnd_6997009 := by
    simpa [prefixWord, tailWord_6997009, baseEnd_6997009] using wordTrace_append hprefix tailTrace_6997009
  have hstable : (prefixWord ++ tailWord_6997009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997009).length < 2 ^ (prefixWord ++ tailWord_6997009).sum := by decide
  have hdescent : baseEnd_6997009 < baseStart_6997009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997013 : List Nat := [1, 3, 2, 1, 4, 2, 2, 1, 2, 1, 4]
def baseStart_6997013 : Nat := 118140960795 + 6997013 * 2 ^ 59
def prefixEnd_6997013 : Nat := 4983230072969 + 3 ^ 40 * 6997013 * 2
def baseEnd_6997013 : Nat := 3592830814757737888158829

theorem tailTrace_6997013 : CollatzResearch.WordTrace tailWord_6997013 prefixEnd_6997013 3592830814757737888158829 := by
  unfold tailWord_6997013
  simp only [CollatzResearch.WordTrace]
  refine ⟨255202029800024370527123693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170134686533349580351415795 255202029800024370527123693)
  ·
    refine ⟨95700761175009138947671385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255202029800024370527123693 95700761175009138947671385)
    ·
      refine ⟨71775570881256854210753539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95700761175009138947671385 71775570881256854210753539)
      ·
        refine ⟨107663356321885281316130309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71775570881256854210753539 107663356321885281316130309)
        ·
          refine ⟨20186879310353490246774433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107663356321885281316130309 20186879310353490246774433)
          ·
            refine ⟨15140159482765117685080825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20186879310353490246774433 15140159482765117685080825)
            ·
              refine ⟨11355119612073838263810619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15140159482765117685080825 11355119612073838263810619)
              ·
                refine ⟨17032679418110757395715929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11355119612073838263810619 17032679418110757395715929)
                ·
                  refine ⟨12774509563583068046786947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17032679418110757395715929 12774509563583068046786947)
                  ·
                    refine ⟨19161764345374602070180421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12774509563583068046786947 19161764345374602070180421)
                    ·
                      refine ⟨3592830814757737888158829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19161764345374602070180421 3592830814757737888158829)
                      ·
                        rfl

theorem cell23_6997013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_6997013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997013 prefixEnd_6997013 := by exact prefixLift 6997013
  have htrace : WordTrace (prefixWord ++ tailWord_6997013) baseStart_6997013 baseEnd_6997013 := by
    simpa [prefixWord, tailWord_6997013, baseEnd_6997013] using wordTrace_append hprefix tailTrace_6997013
  have hstable : (prefixWord ++ tailWord_6997013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997013).length < 2 ^ (prefixWord ++ tailWord_6997013).sum := by decide
  have hdescent : baseEnd_6997013 < baseStart_6997013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997036 : List Nat := [2, 2, 1, 1, 1, 2, 6, 2, 6]
def baseStart_6997036 : Nat := 118140960795 + 6997036 * 2 ^ 59
def prefixEnd_6997036 : Nat := 4983230072969 + 3 ^ 40 * 6997036 * 2
def baseEnd_6997036 : Nat := 399204736090310144241247

theorem tailTrace_6997036 : CollatzResearch.WordTrace tailWord_6997036 prefixEnd_6997036 399204736090310144241247 := by
  unfold tailWord_6997036
  simp only [CollatzResearch.WordTrace]
  refine ⟨127601434339470522727605481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170135245785960696970140641 127601434339470522727605481)
  ·
    refine ⟨95701075754602892045704111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127601434339470522727605481 95701075754602892045704111)
    ·
      refine ⟨143551613631904338068556167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95701075754602892045704111 143551613631904338068556167)
      ·
        refine ⟨215327420447856507102834251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143551613631904338068556167 215327420447856507102834251)
        ·
          refine ⟨322991130671784760654251377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215327420447856507102834251 322991130671784760654251377)
          ·
            refine ⟨242243348003838570490688533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322991130671784760654251377 242243348003838570490688533)
            ·
              refine ⟨11355156937679932991751025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 242243348003838570490688533 11355156937679932991751025)
              ·
                refine ⟨8516367703259949743813269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11355156937679932991751025 8516367703259949743813269)
                ·
                  refine ⟨399204736090310144241247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8516367703259949743813269 399204736090310144241247)
                  ·
                    rfl

theorem cell23_6997036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 6].length) (baseStart_6997036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997036 prefixEnd_6997036 := by exact prefixLift 6997036
  have htrace : WordTrace (prefixWord ++ tailWord_6997036) baseStart_6997036 baseEnd_6997036 := by
    simpa [prefixWord, tailWord_6997036, baseEnd_6997036] using wordTrace_append hprefix tailTrace_6997036
  have hstable : (prefixWord ++ tailWord_6997036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997036).length < 2 ^ (prefixWord ++ tailWord_6997036).sum := by decide
  have hdescent : baseEnd_6997036 < baseStart_6997036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997059 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 7]
def baseStart_6997059 : Nat := 118140960795 + 6997059 * 2 ^ 59
def prefixEnd_6997059 : Nat := 4983230072969 + 3 ^ 40 * 6997059 * 2
def baseEnd_6997059 : Nat := 3592854434867844708183617

theorem tailTrace_6997059 : CollatzResearch.WordTrace tailWord_6997059 prefixEnd_6997059 3592854434867844708183617 := by
  unfold tailWord_6997059
  simp only [CollatzResearch.WordTrace]
  refine ⟨255203707557857720383298231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170135805038571813588865487 255203707557857720383298231)
  ·
    refine ⟨382805561336786580574947347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255203707557857720383298231 382805561336786580574947347)
    ·
      refine ⟨574208342005179870862421021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382805561336786580574947347 574208342005179870862421021)
      ·
        refine ⟨215328128251942451573407883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 574208342005179870862421021 215328128251942451573407883)
        ·
          refine ⟨322992192377913677360111825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215328128251942451573407883 322992192377913677360111825)
          ·
            refine ⟨242244144283435258020083869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322992192377913677360111825 242244144283435258020083869)
            ·
              refine ⟨90841554106288221757531451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242244144283435258020083869 90841554106288221757531451)
              ·
                refine ⟨136262331159432332636297177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90841554106288221757531451 136262331159432332636297177)
                ·
                  refine ⟨102196748369574249477222883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136262331159432332636297177 102196748369574249477222883)
                  ·
                    refine ⟨153295122554361374215834325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102196748369574249477222883 153295122554361374215834325)
                    ·
                      refine ⟨3592854434867844708183617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 153295122554361374215834325 3592854434867844708183617)
                      ·
                        rfl

theorem cell23_6997059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_6997059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997059 prefixEnd_6997059 := by exact prefixLift 6997059
  have htrace : WordTrace (prefixWord ++ tailWord_6997059) baseStart_6997059 baseEnd_6997059 := by
    simpa [prefixWord, tailWord_6997059, baseEnd_6997059] using wordTrace_append hprefix tailTrace_6997059
  have hstable : (prefixWord ++ tailWord_6997059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997059).length < 2 ^ (prefixWord ++ tailWord_6997059).sum := by decide
  have hdescent : baseEnd_6997059 < baseStart_6997059 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997063 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 5, 1, 3]
def baseStart_6997063 : Nat := 118140960795 + 6997063 * 2 ^ 59
def prefixEnd_6997063 : Nat := 4983230072969 + 3 ^ 40 * 6997063 * 2
def baseEnd_6997063 : Nat := 3592856488790462692533599

theorem tailTrace_6997063 : CollatzResearch.WordTrace tailWord_6997063 prefixEnd_6997063 3592856488790462692533599 := by
  unfold tailWord_6997063
  simp only [CollatzResearch.WordTrace]
  refine ⟨255203853449843229066443843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170135902299895486044295895 255203853449843229066443843)
  ·
    refine ⟨382805780174764843599665765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255203853449843229066443843 382805780174764843599665765)
    ·
      refine ⟨71776083782768408174937331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 382805780174764843599665765 71776083782768408174937331)
      ·
        refine ⟨107664125674152612262405997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71776083782768408174937331 107664125674152612262405997)
        ·
          refine ⟨40374047127807229598402249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107664125674152612262405997 40374047127807229598402249)
          ·
            refine ⟨30280535345855422198801687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40374047127807229598402249 30280535345855422198801687)
            ·
              refine ⟨45420803018783133298202531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30280535345855422198801687 45420803018783133298202531)
              ·
                refine ⟨68131204528174699947303797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45420803018783133298202531 68131204528174699947303797)
                ·
                  refine ⟨6387300424516378120059731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68131204528174699947303797 6387300424516378120059731)
                  ·
                    refine ⟨9580950636774567180089597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6387300424516378120059731 9580950636774567180089597)
                    ·
                      refine ⟨3592856488790462692533599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9580950636774567180089597 3592856488790462692533599)
                      ·
                        rfl

theorem cell23_6997063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_6997063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997063 prefixEnd_6997063 := by exact prefixLift 6997063
  have htrace : WordTrace (prefixWord ++ tailWord_6997063) baseStart_6997063 baseEnd_6997063 := by
    simpa [prefixWord, tailWord_6997063, baseEnd_6997063] using wordTrace_append hprefix tailTrace_6997063
  have hstable : (prefixWord ++ tailWord_6997063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997063).length < 2 ^ (prefixWord ++ tailWord_6997063).sum := by decide
  have hdescent : baseEnd_6997063 < baseStart_6997063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997066 : List Nat := [3, 1, 2, 1, 1, 2, 4, 1, 3, 5]
def baseStart_6997066 : Nat := 118140960795 + 6997066 * 2 ^ 59
def prefixEnd_6997066 : Nat := 4983230072969 + 3 ^ 40 * 6997066 * 2
def baseEnd_6997066 : Nat := 1197619343077475393598695

theorem tailTrace_6997066 : CollatzResearch.WordTrace tailWord_6997066 prefixEnd_6997066 1197619343077475393598695 := by
  unfold tailWord_6997066
  simp only [CollatzResearch.WordTrace]
  refine ⟨63800990717208090144700763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170135975245888240385868701 63800990717208090144700763)
  ·
    refine ⟨95701486075812135217051145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63800990717208090144700763 95701486075812135217051145)
    ·
      refine ⟨71776114556859101412788359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95701486075812135217051145 71776114556859101412788359)
      ·
        refine ⟨107664171835288652119182539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71776114556859101412788359 107664171835288652119182539)
        ·
          refine ⟨161496257752932978178773809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107664171835288652119182539 161496257752932978178773809)
          ·
            refine ⟨121122193314699733634080357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161496257752932978178773809 121122193314699733634080357)
            ·
              refine ⟨22710411246506200056390067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121122193314699733634080357 22710411246506200056390067)
              ·
                refine ⟨34065616869759300084585101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22710411246506200056390067 34065616869759300084585101)
                ·
                  refine ⟨12774606326159737531719413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34065616869759300084585101 12774606326159737531719413)
                  ·
                    refine ⟨1197619343077475393598695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12774606326159737531719413 1197619343077475393598695)
                    ·
                      rfl

theorem cell23_6997066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_6997066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997066 prefixEnd_6997066 := by exact prefixLift 6997066
  have htrace : WordTrace (prefixWord ++ tailWord_6997066) baseStart_6997066 baseEnd_6997066 := by
    simpa [prefixWord, tailWord_6997066, baseEnd_6997066] using wordTrace_append hprefix tailTrace_6997066
  have hstable : (prefixWord ++ tailWord_6997066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997066).length < 2 ^ (prefixWord ++ tailWord_6997066).sum := by decide
  have hdescent : baseEnd_6997066 < baseStart_6997066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997116 : List Nat := [2, 2, 2, 1, 1, 3, 3, 1, 1, 1, 6]
def baseStart_6997116 : Nat := 118140960795 + 6997116 * 2 ^ 59
def prefixEnd_6997116 : Nat := 4983230072969 + 3 ^ 40 * 6997116 * 2
def baseEnd_6997116 : Nat := 3592883703265150985170855

theorem tailTrace_6997116 : CollatzResearch.WordTrace tailWord_6997116 prefixEnd_6997116 3592883703265150985170855 := by
  unfold tailWord_6997116
  simp only [CollatzResearch.WordTrace]
  refine ⟨127602893259325609559061601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170137191012434146078748801 127602893259325609559061601)
  ·
    refine ⟨95702169944494207169296201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127602893259325609559061601 95702169944494207169296201)
    ·
      refine ⟨71776627458370655376972151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95702169944494207169296201 71776627458370655376972151)
      ·
        refine ⟨107664941187555983065458227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71776627458370655376972151 107664941187555983065458227)
        ·
          refine ⟨161497411781333974598187341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107664941187555983065458227 161497411781333974598187341)
          ·
            refine ⟨60561529418000240474320253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161497411781333974598187341 60561529418000240474320253)
            ·
              refine ⟨22710573531750090177870095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60561529418000240474320253 22710573531750090177870095)
              ·
                refine ⟨34065860297625135266805143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22710573531750090177870095 34065860297625135266805143)
                ·
                  refine ⟨51098790446437702900207715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34065860297625135266805143 51098790446437702900207715)
                  ·
                    refine ⟨76648185669656554350311573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51098790446437702900207715 76648185669656554350311573)
                    ·
                      refine ⟨3592883703265150985170855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76648185669656554350311573 3592883703265150985170855)
                      ·
                        rfl

theorem cell23_6997116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_6997116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997116 prefixEnd_6997116 := by exact prefixLift 6997116
  have htrace : WordTrace (prefixWord ++ tailWord_6997116) baseStart_6997116 baseEnd_6997116 := by
    simpa [prefixWord, tailWord_6997116, baseEnd_6997116] using wordTrace_append hprefix tailTrace_6997116
  have hstable : (prefixWord ++ tailWord_6997116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997116).length < 2 ^ (prefixWord ++ tailWord_6997116).sum := by decide
  have hdescent : baseEnd_6997116 < baseStart_6997116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997120 : List Nat := [2, 1, 1, 2, 1, 3, 4, 2, 3, 2, 2]
def baseStart_6997120 : Nat := 118140960795 + 6997120 * 2 ^ 59
def prefixEnd_6997120 : Nat := 4983230072969 + 3 ^ 40 * 6997120 * 2
def baseEnd_6997120 : Nat := 3592885757187768969520837

theorem tailTrace_6997120 : CollatzResearch.WordTrace tailWord_6997120 prefixEnd_6997120 3592885757187768969520837 := by
  unfold tailWord_6997120
  simp only [CollatzResearch.WordTrace]
  refine ⟨127602966205318363900634407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170137288273757818534179209 127602966205318363900634407)
  ·
    refine ⟨191404449307977545850951611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127602966205318363900634407 191404449307977545850951611)
    ·
      refine ⟨287106673961966318776427417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191404449307977545850951611 287106673961966318776427417)
      ·
        refine ⟨215330005471474739082320563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287106673961966318776427417 215330005471474739082320563)
        ·
          refine ⟨322995008207212108623480845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215330005471474739082320563 322995008207212108623480845)
          ·
            refine ⟨121123128077704540733805317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 322995008207212108623480845 121123128077704540733805317)
            ·
              refine ⟨22710586514569601387588497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121123128077704540733805317 22710586514569601387588497)
              ·
                refine ⟨17032939885927201040691373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22710586514569601387588497 17032939885927201040691373)
                ·
                  refine ⟨6387352457222700390259265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17032939885927201040691373 6387352457222700390259265)
                  ·
                    refine ⟨4790514342917025292694449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6387352457222700390259265 4790514342917025292694449)
                    ·
                      refine ⟨3592885757187768969520837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4790514342917025292694449 3592885757187768969520837)
                      ·
                        rfl

theorem cell23_6997120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 3, 2, 2].length) (baseStart_6997120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997120 prefixEnd_6997120 := by exact prefixLift 6997120
  have htrace : WordTrace (prefixWord ++ tailWord_6997120) baseStart_6997120 baseEnd_6997120 := by
    simpa [prefixWord, tailWord_6997120, baseEnd_6997120] using wordTrace_append hprefix tailTrace_6997120
  have hstable : (prefixWord ++ tailWord_6997120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997120).length < 2 ^ (prefixWord ++ tailWord_6997120).sum := by decide
  have hdescent : baseEnd_6997120 < baseStart_6997120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997174 : List Nat := [5, 1, 3, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_6997174 : Nat := 118140960795 + 6997174 * 2 ^ 59
def prefixEnd_6997174 : Nat := 4983230072969 + 3 ^ 40 * 6997174 * 2
def baseEnd_6997174 : Nat := 3592913485143111758245589

theorem tailTrace_6997174 : CollatzResearch.WordTrace tailWord_6997174 prefixEnd_6997174 3592913485143111758245589 := by
  unfold tailWord_6997174
  simp only [CollatzResearch.WordTrace]
  refine ⟨15950493872027568438983411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170138601301627396682489717 15950493872027568438983411)
  ·
    refine ⟨23925740808041352658475117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15950493872027568438983411 23925740808041352658475117)
    ·
      refine ⟨8972152803015507246928169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23925740808041352658475117 8972152803015507246928169)
      ·
        refine ⟨6729114602261630435196127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8972152803015507246928169 6729114602261630435196127)
        ·
          refine ⟨10093671903392445652794191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6729114602261630435196127 10093671903392445652794191)
          ·
            refine ⟨15140507855088668479191287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10093671903392445652794191 15140507855088668479191287)
            ·
              refine ⟨22710761782633002718786931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15140507855088668479191287 22710761782633002718786931)
              ·
                refine ⟨34066142673949504078180397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22710761782633002718786931 34066142673949504078180397)
                ·
                  refine ⟨12774803502731064029317649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34066142673949504078180397 12774803502731064029317649)
                  ·
                    refine ⟨9581102627048298021988237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12774803502731064029317649 9581102627048298021988237)
                    ·
                      refine ⟨3592913485143111758245589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9581102627048298021988237 3592913485143111758245589)
                      ·
                        rfl

theorem cell23_6997174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_6997174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997174 prefixEnd_6997174 := by exact prefixLift 6997174
  have htrace : WordTrace (prefixWord ++ tailWord_6997174) baseStart_6997174 baseEnd_6997174 := by
    simpa [prefixWord, tailWord_6997174, baseEnd_6997174] using wordTrace_append hprefix tailTrace_6997174
  have hstable : (prefixWord ++ tailWord_6997174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997174).length < 2 ^ (prefixWord ++ tailWord_6997174).sum := by decide
  have hdescent : baseEnd_6997174 < baseStart_6997174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997176 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 4, 3, 4]
def baseStart_6997176 : Nat := 118140960795 + 6997176 * 2 ^ 59
def prefixEnd_6997176 : Nat := 4983230072969 + 3 ^ 40 * 6997176 * 2
def baseEnd_6997176 : Nat := 3592914512104420750420579

theorem tailTrace_6997176 : CollatzResearch.WordTrace tailWord_6997176 prefixEnd_6997176 3592914512104420750420579 := by
  unfold tailWord_6997176
  simp only [CollatzResearch.WordTrace]
  refine ⟨127603987449216924682653691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170138649932289232910204921 127603987449216924682653691)
  ·
    refine ⟨191405981173825387023980537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127603987449216924682653691 191405981173825387023980537)
    ·
      refine ⟨143554485880369040267985403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191405981173825387023980537 143554485880369040267985403)
      ·
        refine ⟨215331728820553560401978105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143554485880369040267985403 215331728820553560401978105)
        ·
          refine ⟨161498796615415170301483579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215331728820553560401978105 161498796615415170301483579)
          ·
            refine ⟨242248194923122755452225369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161498796615415170301483579 242248194923122755452225369)
            ·
              refine ⟨181686146192342066589169027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242248194923122755452225369 181686146192342066589169027)
              ·
                refine ⟨272529219288513099883753541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181686146192342066589169027 272529219288513099883753541)
                ·
                  refine ⟨51099228616596206228203789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272529219288513099883753541 51099228616596206228203789)
                  ·
                    refine ⟨19162210731223577335576421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51099228616596206228203789 19162210731223577335576421)
                    ·
                      refine ⟨3592914512104420750420579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19162210731223577335576421 3592914512104420750420579)
                      ·
                        rfl

theorem cell23_6997176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_6997176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997176 prefixEnd_6997176 := by exact prefixLift 6997176
  have htrace : WordTrace (prefixWord ++ tailWord_6997176) baseStart_6997176 baseEnd_6997176 := by
    simpa [prefixWord, tailWord_6997176, baseEnd_6997176] using wordTrace_append hprefix tailTrace_6997176
  have hstable : (prefixWord ++ tailWord_6997176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997176).length < 2 ^ (prefixWord ++ tailWord_6997176).sum := by decide
  have hdescent : baseEnd_6997176 < baseStart_6997176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997227 : List Nat := [1, 1, 1, 1, 2, 6, 2, 3, 2, 2, 2]
def baseStart_6997227 : Nat := 118140960795 + 6997227 * 2 ^ 59
def prefixEnd_6997227 : Nat := 4983230072969 + 3 ^ 40 * 6997227 * 2
def baseEnd_6997227 : Nat := 3592940699617800050882845

theorem tailTrace_6997227 : CollatzResearch.WordTrace tailWord_6997227 prefixEnd_6997227 3592940699617800050882845 := by
  unfold tailWord_6997227
  simp only [CollatzResearch.WordTrace]
  refine ⟨255209835021249085075413935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170139890014166056716942623 255209835021249085075413935)
  ·
    refine ⟨382814752531873627613120903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255209835021249085075413935 382814752531873627613120903)
    ·
      refine ⟨574222128797810441419681355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382814752531873627613120903 574222128797810441419681355)
      ·
        refine ⟨861333193196715662129522033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574222128797810441419681355 861333193196715662129522033)
        ·
          refine ⟨645999894897536746597141525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 861333193196715662129522033 645999894897536746597141525)
          ·
            refine ⟨30281245073322034996741009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 645999894897536746597141525 30281245073322034996741009)
            ·
              refine ⟨22710933804991526247555757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30281245073322034996741009 22710933804991526247555757)
              ·
                refine ⟨8516600176871822342833409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22710933804991526247555757 8516600176871822342833409)
                ·
                  refine ⟨6387450132653866757125057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8516600176871822342833409 6387450132653866757125057)
                  ·
                    refine ⟨4790587599490400067843793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6387450132653866757125057 4790587599490400067843793)
                    ·
                      refine ⟨3592940699617800050882845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4790587599490400067843793 3592940699617800050882845)
                      ·
                        rfl

theorem cell23_6997227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 2, 2, 2].length) (baseStart_6997227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997227 prefixEnd_6997227 := by exact prefixLift 6997227
  have htrace : WordTrace (prefixWord ++ tailWord_6997227) baseStart_6997227 baseEnd_6997227 := by
    simpa [prefixWord, tailWord_6997227, baseEnd_6997227] using wordTrace_append hprefix tailTrace_6997227
  have hstable : (prefixWord ++ tailWord_6997227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997227).length < 2 ^ (prefixWord ++ tailWord_6997227).sum := by decide
  have hdescent : baseEnd_6997227 < baseStart_6997227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997278 : List Nat := [4, 3, 2, 1, 3, 1, 1, 1, 1, 4, 2]
def baseStart_6997278 : Nat := 118140960795 + 6997278 * 2 ^ 59
def prefixEnd_6997278 : Nat := 4983230072969 + 3 ^ 40 * 6997278 * 2
def baseEnd_6997278 : Nat := 3592966887131179351345111

theorem tailTrace_6997278 : CollatzResearch.WordTrace tailWord_6997278 prefixEnd_6997278 3592966887131179351345111 := by
  unfold tailWord_6997278
  simp only [CollatzResearch.WordTrace]
  refine ⟨31901461893008040098190061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170141130096042880523680325 31901461893008040098190061)
  ·
    refine ⟨11963048209878015036821273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31901461893008040098190061 11963048209878015036821273)
    ·
      refine ⟨8972286157408511277615955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11963048209878015036821273 8972286157408511277615955)
      ·
        refine ⟨13458429236112766916423933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8972286157408511277615955 13458429236112766916423933)
        ·
          refine ⟨5046910963542287593658975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13458429236112766916423933 5046910963542287593658975)
          ·
            refine ⟨7570366445313431390488463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5046910963542287593658975 7570366445313431390488463)
            ·
              refine ⟨11355549667970147085732695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7570366445313431390488463 11355549667970147085732695)
              ·
                refine ⟨17033324501955220628599043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11355549667970147085732695 17033324501955220628599043)
                ·
                  refine ⟨25549986752932830942898565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17033324501955220628599043 25549986752932830942898565)
                  ·
                    refine ⟨4790622516174905801793481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25549986752932830942898565 4790622516174905801793481)
                    ·
                      refine ⟨3592966887131179351345111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4790622516174905801793481 3592966887131179351345111)
                      ·
                        rfl

theorem cell23_6997278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_6997278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997278 prefixEnd_6997278 := by exact prefixLift 6997278
  have htrace : WordTrace (prefixWord ++ tailWord_6997278) baseStart_6997278 baseEnd_6997278 := by
    simpa [prefixWord, tailWord_6997278, baseEnd_6997278] using wordTrace_append hprefix tailTrace_6997278
  have hstable : (prefixWord ++ tailWord_6997278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997278).length < 2 ^ (prefixWord ++ tailWord_6997278).sum := by decide
  have hdescent : baseEnd_6997278 < baseStart_6997278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997283 : List Nat := [1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 4]
def baseStart_6997283 : Nat := 118140960795 + 6997283 * 2 ^ 59
def prefixEnd_6997283 : Nat := 4983230072969 + 3 ^ 40 * 6997283 * 2
def baseEnd_6997283 : Nat := 3592969454534451831782587

theorem tailTrace_6997283 : CollatzResearch.WordTrace tailWord_6997283 prefixEnd_6997283 3592969454534451831782587 := by
  unfold tailWord_6997283
  simp only [CollatzResearch.WordTrace]
  refine ⟨255211877509046206639452503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170141251672697471092968335 255211877509046206639452503)
  ·
    refine ⟨382817816263569309959178755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255211877509046206639452503 382817816263569309959178755)
    ·
      refine ⟨574226724395353964938768133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382817816263569309959178755 574226724395353964938768133)
      ·
        refine ⟨107667510824128868426019025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 574226724395353964938768133 107667510824128868426019025)
        ·
          refine ⟨80750633118096651319514269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107667510824128868426019025 80750633118096651319514269)
          ·
            refine ⟨30281487419286244244817851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80750633118096651319514269 30281487419286244244817851)
            ·
              refine ⟨45422231128929366367226777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30281487419286244244817851 45422231128929366367226777)
              ·
                refine ⟨34066673346697024775420083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45422231128929366367226777 34066673346697024775420083)
                ·
                  refine ⟨51100010020045537163130125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34066673346697024775420083 51100010020045537163130125)
                  ·
                    refine ⟨19162503757517076436173797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51100010020045537163130125 19162503757517076436173797)
                    ·
                      refine ⟨3592969454534451831782587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19162503757517076436173797 3592969454534451831782587)
                      ·
                        rfl

theorem cell23_6997283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_6997283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997283 prefixEnd_6997283 := by exact prefixLift 6997283
  have htrace : WordTrace (prefixWord ++ tailWord_6997283) baseStart_6997283 baseEnd_6997283 := by
    simpa [prefixWord, tailWord_6997283, baseEnd_6997283] using wordTrace_append hprefix tailTrace_6997283
  have hstable : (prefixWord ++ tailWord_6997283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997283).length < 2 ^ (prefixWord ++ tailWord_6997283).sum := by decide
  have hdescent : baseEnd_6997283 < baseStart_6997283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997300 : List Nat := [2, 5, 1, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_6997300 : Nat := 118140960795 + 6997300 * 2 ^ 59
def prefixEnd_6997300 : Nat := 4983230072969 + 3 ^ 40 * 6997300 * 2
def baseEnd_6997300 : Nat := 3592978183705578265270009

theorem tailTrace_6997300 : CollatzResearch.WordTrace tailWord_6997300 prefixEnd_6997300 3592978183705578265270009 := by
  unfold tailWord_6997300
  simp only [CollatzResearch.WordTrace]
  refine ⟨127606248774992309271410677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170141665033323079028547569 127606248774992309271410677)
  ·
    refine ⟨11963085822655528994194751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127606248774992309271410677 11963085822655528994194751)
    ·
      refine ⟨17944628733983293491292127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11963085822655528994194751 17944628733983293491292127)
      ·
        refine ⟨26916943100974940236938191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17944628733983293491292127 26916943100974940236938191)
        ·
          refine ⟨40375414651462410355407287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26916943100974940236938191 40375414651462410355407287)
          ·
            refine ⟨60563121977193615533110931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40375414651462410355407287 60563121977193615533110931)
            ·
              refine ⟨90844682965790423299666397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60563121977193615533110931 90844682965790423299666397)
              ·
                refine ⟨34066756112171408737374899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90844682965790423299666397 34066756112171408737374899)
                ·
                  refine ⟨51100134168257113106062349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34066756112171408737374899 51100134168257113106062349)
                  ·
                    refine ⟨19162550313096417414773381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51100134168257113106062349 19162550313096417414773381)
                    ·
                      refine ⟨3592978183705578265270009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19162550313096417414773381 3592978183705578265270009)
                      ·
                        rfl

theorem cell23_6997300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_6997300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997300 prefixEnd_6997300 := by exact prefixLift 6997300
  have htrace : WordTrace (prefixWord ++ tailWord_6997300) baseStart_6997300 baseEnd_6997300 := by
    simpa [prefixWord, tailWord_6997300, baseEnd_6997300] using wordTrace_append hprefix tailTrace_6997300
  have hstable : (prefixWord ++ tailWord_6997300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997300).length < 2 ^ (prefixWord ++ tailWord_6997300).sum := by decide
  have hdescent : baseEnd_6997300 < baseStart_6997300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997318 : List Nat := [6, 1, 1, 3, 1, 1, 3, 2, 5]
def baseStart_6997318 : Nat := 118140960795 + 6997318 * 2 ^ 59
def prefixEnd_6997318 : Nat := 4983230072969 + 3 ^ 40 * 6997318 * 2
def baseEnd_6997318 : Nat := 399220825150817688316103

theorem tailTrace_6997318 : CollatzResearch.WordTrace tailWord_6997318 prefixEnd_6997318 399220825150817688316103 := by
  unfold tailWord_6997318
  simp only [CollatzResearch.WordTrace]
  refine ⟨7975411064497481488030519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 170142102709279605077984405 7975411064497481488030519)
  ·
    refine ⟨11963116596746222232045779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7975411064497481488030519 11963116596746222232045779)
    ·
      refine ⟨17944674895119333348068669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11963116596746222232045779 17944674895119333348068669)
      ·
        refine ⟨6729253085669750005525751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17944674895119333348068669 6729253085669750005525751)
        ·
          refine ⟨10093879628504625008288627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6729253085669750005525751 10093879628504625008288627)
          ·
            refine ⟨15140819442756937512432941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10093879628504625008288627 15140819442756937512432941)
            ·
              refine ⟨5677807291033851567162353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15140819442756937512432941 5677807291033851567162353)
              ·
                refine ⟨4258355468275388675371765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5677807291033851567162353 4258355468275388675371765)
                ·
                  refine ⟨399220825150817688316103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4258355468275388675371765 399220825150817688316103)
                  ·
                    rfl

theorem cell23_6997318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_6997318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997318 prefixEnd_6997318 := by exact prefixLift 6997318
  have htrace : WordTrace (prefixWord ++ tailWord_6997318) baseStart_6997318 baseEnd_6997318 := by
    simpa [prefixWord, tailWord_6997318, baseEnd_6997318] using wordTrace_append hprefix tailTrace_6997318
  have hstable : (prefixWord ++ tailWord_6997318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997318).length < 2 ^ (prefixWord ++ tailWord_6997318).sum := by decide
  have hdescent : baseEnd_6997318 < baseStart_6997318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997354 : List Nat := [3, 1, 3, 3, 2, 1, 2, 1, 2, 2, 3]
def baseStart_6997354 : Nat := 118140960795 + 6997354 * 2 ^ 59
def prefixEnd_6997354 : Nat := 4983230072969 + 3 ^ 40 * 6997354 * 2
def baseEnd_6997354 : Nat := 3593005911660921053994761

theorem tailTrace_6997354 : CollatzResearch.WordTrace tailWord_6997354 prefixEnd_6997354 3593005911660921053994761 := by
  unfold tailWord_6997354
  simp only [CollatzResearch.WordTrace]
  refine ⟨63803616772947246441321779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170142978061192657176858077 63803616772947246441321779)
  ·
    refine ⟨95705425159420869661982669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63803616772947246441321779 95705425159420869661982669)
    ·
      refine ⟨35889534434782826123243501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95705425159420869661982669 35889534434782826123243501)
      ·
        refine ⟨13458575413043559796216313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35889534434782826123243501 13458575413043559796216313)
        ·
          refine ⟨10093931559782669847162235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13458575413043559796216313 10093931559782669847162235)
          ·
            refine ⟨15140897339674004770743353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10093931559782669847162235 15140897339674004770743353)
            ·
              refine ⟨11355673004755503578057515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15140897339674004770743353 11355673004755503578057515)
              ·
                refine ⟨17033509507133255367086273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11355673004755503578057515 17033509507133255367086273)
                ·
                  refine ⟨12775132130349941525314705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17033509507133255367086273 12775132130349941525314705)
                  ·
                    refine ⟨9581349097762456143986029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12775132130349941525314705 9581349097762456143986029)
                    ·
                      refine ⟨3593005911660921053994761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9581349097762456143986029 3593005911660921053994761)
                      ·
                        rfl

theorem cell23_6997354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_6997354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997354 prefixEnd_6997354 := by exact prefixLift 6997354
  have htrace : WordTrace (prefixWord ++ tailWord_6997354) baseStart_6997354 baseEnd_6997354 := by
    simpa [prefixWord, tailWord_6997354, baseEnd_6997354] using wordTrace_append hprefix tailTrace_6997354
  have hstable : (prefixWord ++ tailWord_6997354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997354).length < 2 ^ (prefixWord ++ tailWord_6997354).sum := by decide
  have hdescent : baseEnd_6997354 < baseStart_6997354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997378 : List Nat := [3, 4, 2, 1, 1, 1, 4, 2, 1, 4]
def baseStart_6997378 : Nat := 118140960795 + 6997378 * 2 ^ 59
def prefixEnd_6997378 : Nat := 4983230072969 + 3 ^ 40 * 6997378 * 2
def baseEnd_6997378 : Nat := 1197672745065542986698217

theorem tailTrace_6997378 : CollatzResearch.WordTrace tailWord_6997378 prefixEnd_6997378 1197672745065542986698217 := by
  unfold tailWord_6997378
  simp only [CollatzResearch.WordTrace]
  refine ⟨63803835610925509466040197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170143561629134691909440525 63803835610925509466040197)
  ·
    refine ⟨11963219177048533024882537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63803835610925509466040197 11963219177048533024882537)
    ·
      refine ⟨8972414382786399768661903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11963219177048533024882537 8972414382786399768661903)
      ·
        refine ⟨13458621574179599652992855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8972414382786399768661903 13458621574179599652992855)
        ·
          refine ⟨20187932361269399479489283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13458621574179599652992855 20187932361269399479489283)
          ·
            refine ⟨30281898541904099219233925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20187932361269399479489283 30281898541904099219233925)
            ·
              refine ⟨5677855976607018603606361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30281898541904099219233925 5677855976607018603606361)
              ·
                refine ⟨4258391982455263952704771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5677855976607018603606361 4258391982455263952704771)
                ·
                  refine ⟨6387587973682895929057157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4258391982455263952704771 6387587973682895929057157)
                  ·
                    refine ⟨1197672745065542986698217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6387587973682895929057157 1197672745065542986698217)
                    ·
                      rfl

theorem cell23_6997378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_6997378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997378 prefixEnd_6997378 := by exact prefixLift 6997378
  have htrace : WordTrace (prefixWord ++ tailWord_6997378) baseStart_6997378 baseEnd_6997378 := by
    simpa [prefixWord, tailWord_6997378, baseEnd_6997378] using wordTrace_append hprefix tailTrace_6997378
  have hstable : (prefixWord ++ tailWord_6997378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997378).length < 2 ^ (prefixWord ++ tailWord_6997378).sum := by decide
  have hdescent : baseEnd_6997378 < baseStart_6997378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997420 : List Nat := [2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 4]
def baseStart_6997420 : Nat := 118140960795 + 6997420 * 2 ^ 59
def prefixEnd_6997420 : Nat := 4983230072969 + 3 ^ 40 * 6997420 * 2
def baseEnd_6997420 : Nat := 3593039801384117795769457

theorem tailTrace_6997420 : CollatzResearch.WordTrace tailWord_6997420 prefixEnd_6997420 3593039801384117795769457 := by
  unfold tailWord_6997420
  simp only [CollatzResearch.WordTrace]
  refine ⟨127608437154774939518594857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170144582873033252691459809 127608437154774939518594857)
  ·
    refine ⟨95706327866081204638946143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127608437154774939518594857 95706327866081204638946143)
    ·
      refine ⟨143559491799121806958419215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95706327866081204638946143 143559491799121806958419215)
      ·
        refine ⟨215339237698682710437628823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143559491799121806958419215 215339237698682710437628823)
        ·
          refine ⟨323008856548024065656443235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215339237698682710437628823 323008856548024065656443235)
          ·
            refine ⟨484513284822036098484664853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323008856548024065656443235 484513284822036098484664853)
            ·
              refine ⟨22711560226032942116468665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 484513284822036098484664853 22711560226032942116468665)
              ·
                refine ⟨17033670169524706587351499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22711560226032942116468665 17033670169524706587351499)
                ·
                  refine ⟨25550505254287059881027249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17033670169524706587351499 25550505254287059881027249)
                  ·
                    refine ⟨19162878940715294910770437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25550505254287059881027249 19162878940715294910770437)
                    ·
                      refine ⟨3593039801384117795769457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19162878940715294910770437 3593039801384117795769457)
                      ·
                        rfl

theorem cell23_6997420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_6997420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997420 prefixEnd_6997420 := by exact prefixLift 6997420
  have htrace : WordTrace (prefixWord ++ tailWord_6997420) baseStart_6997420 baseEnd_6997420 := by
    simpa [prefixWord, tailWord_6997420, baseEnd_6997420] using wordTrace_append hprefix tailTrace_6997420
  have hstable : (prefixWord ++ tailWord_6997420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997420).length < 2 ^ (prefixWord ++ tailWord_6997420).sum := by decide
  have hdescent : baseEnd_6997420 < baseStart_6997420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997421 : List Nat := [1, 5, 2, 2, 1, 3, 2, 1, 1, 5]
def baseStart_6997421 : Nat := 118140960795 + 6997421 * 2 ^ 59
def prefixEnd_6997421 : Nat := 4983230072969 + 3 ^ 40 * 6997421 * 2
def baseEnd_6997421 : Nat := 1197680104954924097285651

theorem tailTrace_6997421 : CollatzResearch.WordTrace tailWord_6997421 prefixEnd_6997421 1197680104954924097285651 := by
  unfold tailWord_6997421
  simp only [CollatzResearch.WordTrace]
  refine ⟨255216910782546256207976117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170144607188364170805317411 255216910782546256207976117)
  ·
    refine ⟨23926585385863711519497761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 255216910782546256207976117 23926585385863711519497761)
    ·
      refine ⟨17944939039397783639623321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23926585385863711519497761 17944939039397783639623321)
      ·
        refine ⟨13458704279548337729717491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17944939039397783639623321 13458704279548337729717491)
        ·
          refine ⟨20188056419322506594576237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13458704279548337729717491 20188056419322506594576237)
          ·
            refine ⟨7570521157245939972966089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20188056419322506594576237 7570521157245939972966089)
            ·
              refine ⟨5677890867934454979724567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7570521157245939972966089 5677890867934454979724567)
              ·
                refine ⟨8516836301901682469586851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5677890867934454979724567 8516836301901682469586851)
                ·
                  refine ⟨12775254452852523704380277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8516836301901682469586851 12775254452852523704380277)
                  ·
                    refine ⟨1197680104954924097285651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12775254452852523704380277 1197680104954924097285651)
                    ·
                      rfl

theorem cell23_6997421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_6997421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997421 prefixEnd_6997421 := by exact prefixLift 6997421
  have htrace : WordTrace (prefixWord ++ tailWord_6997421) baseStart_6997421 baseEnd_6997421 := by
    simpa [prefixWord, tailWord_6997421, baseEnd_6997421] using wordTrace_append hprefix tailTrace_6997421
  have hstable : (prefixWord ++ tailWord_6997421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997421).length < 2 ^ (prefixWord ++ tailWord_6997421).sum := by decide
  have hdescent : baseEnd_6997421 < baseStart_6997421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997440 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 3]
def baseStart_6997440 : Nat := 118140960795 + 6997440 * 2 ^ 59
def prefixEnd_6997440 : Nat := 4983230072969 + 3 ^ 40 * 6997440 * 2
def baseEnd_6997440 : Nat := 3593050070997207717519365

theorem tailTrace_6997440 : CollatzResearch.WordTrace tailWord_6997440 prefixEnd_6997440 3593050070997207717519365 := by
  unfold tailWord_6997440
  simp only [CollatzResearch.WordTrace]
  refine ⟨127608801884738711226458887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170145069179651614968611849 127608801884738711226458887)
  ·
    refine ⟨191413202827108066839688331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127608801884738711226458887 191413202827108066839688331)
    ·
      refine ⟨287119804240662100259532497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191413202827108066839688331 287119804240662100259532497)
      ·
        refine ⟨215339853180496575194649373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287119804240662100259532497 215339853180496575194649373)
        ·
          refine ⟨80752444942686215697993515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215339853180496575194649373 80752444942686215697993515)
          ·
            refine ⟨121128667414029323546990273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80752444942686215697993515 121128667414029323546990273)
            ·
              refine ⟨90846500560521992660242705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121128667414029323546990273 90846500560521992660242705)
              ·
                refine ⟨68134875420391494495182029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90846500560521992660242705 68134875420391494495182029)
                ·
                  refine ⟨25550578282646810435693261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68134875420391494495182029 25550578282646810435693261)
                  ·
                    refine ⟨9581466855992553913384973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25550578282646810435693261 9581466855992553913384973)
                    ·
                      refine ⟨3593050070997207717519365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9581466855992553913384973 3593050070997207717519365)
                      ·
                        rfl

theorem cell23_6997440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 3].length) (baseStart_6997440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997440 prefixEnd_6997440 := by exact prefixLift 6997440
  have htrace : WordTrace (prefixWord ++ tailWord_6997440) baseStart_6997440 baseEnd_6997440 := by
    simpa [prefixWord, tailWord_6997440, baseEnd_6997440] using wordTrace_append hprefix tailTrace_6997440
  have hstable : (prefixWord ++ tailWord_6997440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997440).length < 2 ^ (prefixWord ++ tailWord_6997440).sum := by decide
  have hdescent : baseEnd_6997440 < baseStart_6997440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997443 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 1, 9]
def baseStart_6997443 : Nat := 118140960795 + 6997443 * 2 ^ 59
def prefixEnd_6997443 : Nat := 4983230072969 + 3 ^ 40 * 6997443 * 2
def baseEnd_6997443 : Nat := 1197683870479723735260617

theorem tailTrace_6997443 : CollatzResearch.WordTrace tailWord_6997443 prefixEnd_6997443 1197683870479723735260617 := by
  unfold tailWord_6997443
  simp only [CollatzResearch.WordTrace]
  refine ⟨255217713188466553965276983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170145142125644369310184655 255217713188466553965276983)
  ·
    refine ⟨382826569782699830947915475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255217713188466553965276983 382826569782699830947915475)
    ·
      refine ⟨574239854674049746421873213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382826569782699830947915475 574239854674049746421873213)
      ·
        refine ⟨215339945502768654908202455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 574239854674049746421873213 215339945502768654908202455)
        ·
          refine ⟨323009918254152982362303683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215339945502768654908202455 323009918254152982362303683)
          ·
            refine ⟨484514877381229473543455525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323009918254152982362303683 484514877381229473543455525)
            ·
              refine ⟨90846539508980526289397911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 484514877381229473543455525 90846539508980526289397911)
              ·
                refine ⟨136269809263470789434096867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90846539508980526289397911 136269809263470789434096867)
                ·
                  refine ⟨204404713895206184151145301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136269809263470789434096867 204404713895206184151145301)
                  ·
                    refine ⟨1197683870479723735260617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 204404713895206184151145301 1197683870479723735260617)
                    ·
                      rfl

theorem cell23_6997443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 9].length) (baseStart_6997443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997443 prefixEnd_6997443 := by exact prefixLift 6997443
  have htrace : WordTrace (prefixWord ++ tailWord_6997443) baseStart_6997443 baseEnd_6997443 := by
    simpa [prefixWord, tailWord_6997443, baseEnd_6997443] using wordTrace_append hprefix tailTrace_6997443
  have hstable : (prefixWord ++ tailWord_6997443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997443).length < 2 ^ (prefixWord ++ tailWord_6997443).sum := by decide
  have hdescent : baseEnd_6997443 < baseStart_6997443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997518 : List Nat := [4, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2]
def baseStart_6997518 : Nat := 118140960795 + 6997518 * 2 ^ 59
def prefixEnd_6997518 : Nat := 4983230072969 + 3 ^ 40 * 6997518 * 2
def baseEnd_6997518 : Nat := 3593090122488258412344007

theorem tailTrace_6997518 : CollatzResearch.WordTrace tailWord_6997518 prefixEnd_6997518 3593090122488258412344007 := by
  unfold tailWord_6997518
  simp only [CollatzResearch.WordTrace]
  refine ⟨31902556082899355221782151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170146965775463227849504805 31902556082899355221782151)
  ·
    refine ⟨47853834124349032832673227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31902556082899355221782151 47853834124349032832673227)
    ·
      refine ⟨71780751186523549249009841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47853834124349032832673227 71780751186523549249009841)
      ·
        refine ⟨53835563389892661936757381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71780751186523549249009841 53835563389892661936757381)
        ·
          refine ⟨10094168135604874113142009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53835563389892661936757381 10094168135604874113142009)
          ·
            refine ⟨7570626101703655584856507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10094168135604874113142009 7570626101703655584856507)
            ·
              refine ⟨11355939152555483377284761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7570626101703655584856507 11355939152555483377284761)
              ·
                refine ⟨8516954364416612532963571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11355939152555483377284761 8516954364416612532963571)
                ·
                  refine ⟨12775431546624918799445357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8516954364416612532963571 12775431546624918799445357)
                  ·
                    refine ⟨4790786829984344549792009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12775431546624918799445357 4790786829984344549792009)
                    ·
                      refine ⟨3593090122488258412344007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4790786829984344549792009 3593090122488258412344007)
                      ·
                        rfl

theorem cell23_6997518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_6997518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997518 prefixEnd_6997518 := by exact prefixLift 6997518
  have htrace : WordTrace (prefixWord ++ tailWord_6997518) baseStart_6997518 baseEnd_6997518 := by
    simpa [prefixWord, tailWord_6997518, baseEnd_6997518] using wordTrace_append hprefix tailTrace_6997518
  have hstable : (prefixWord ++ tailWord_6997518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997518).length < 2 ^ (prefixWord ++ tailWord_6997518).sum := by decide
  have hdescent : baseEnd_6997518 < baseStart_6997518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997564 : List Nat := [2, 2, 2, 2, 4, 1, 1, 1, 2, 3, 3]
def baseStart_6997564 : Nat := 118140960795 + 6997564 * 2 ^ 59
def prefixEnd_6997564 : Nat := 4983230072969 + 3 ^ 40 * 6997564 * 2
def baseEnd_6997564 : Nat := 3593113742598365232368795

theorem tailTrace_6997564 : CollatzResearch.WordTrace tailWord_6997564 prefixEnd_6997564 3593113742598365232368795 := by
  unfold tailWord_6997564
  simp only [CollatzResearch.WordTrace]
  refine ⟨127611063210514095815215873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170148084280685461086954497 127611063210514095815215873)
  ·
    refine ⟨95708297407885571861411905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127611063210514095815215873 95708297407885571861411905)
    ·
      refine ⟨71781223055914178896058929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95708297407885571861411905 71781223055914178896058929)
      ·
        refine ⟨53835917291935634172044197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71781223055914178896058929 53835917291935634172044197)
        ·
          refine ⟨10094234492237931407258287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53835917291935634172044197 10094234492237931407258287)
          ·
            refine ⟨15141351738356897110887431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10094234492237931407258287 15141351738356897110887431)
            ·
              refine ⟨22712027607535345666331147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15141351738356897110887431 22712027607535345666331147)
              ·
                refine ⟨34068041411303018499496721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22712027607535345666331147 34068041411303018499496721)
                ·
                  refine ⟨25551031058477263874622541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34068041411303018499496721 25551031058477263874622541)
                  ·
                    refine ⟨9581636646928973952983453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25551031058477263874622541 9581636646928973952983453)
                    ·
                      refine ⟨3593113742598365232368795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9581636646928973952983453 3593113742598365232368795)
                      ·
                        rfl

theorem cell23_6997564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_6997564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997564 prefixEnd_6997564 := by exact prefixLift 6997564
  have htrace : WordTrace (prefixWord ++ tailWord_6997564) baseStart_6997564 baseEnd_6997564 := by
    simpa [prefixWord, tailWord_6997564, baseEnd_6997564] using wordTrace_append hprefix tailTrace_6997564
  have hstable : (prefixWord ++ tailWord_6997564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997564).length < 2 ^ (prefixWord ++ tailWord_6997564).sum := by decide
  have hdescent : baseEnd_6997564 < baseStart_6997564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997604 : List Nat := [2, 3, 1, 1, 2, 3, 1, 2, 2, 4, 2]
def baseStart_6997604 : Nat := 118140960795 + 6997604 * 2 ^ 59
def prefixEnd_6997604 : Nat := 4983230072969 + 3 ^ 40 * 6997604 * 2
def baseEnd_6997604 : Nat := 3593134281824545075868611

theorem tailTrace_6997604 : CollatzResearch.WordTrace tailWord_6997604 prefixEnd_6997604 3593134281824545075868611 := by
  unfold tailWord_6997604
  simp only [CollatzResearch.WordTrace]
  refine ⟨127611792670441639230943933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170149056893922185641258577 127611792670441639230943933)
  ·
    refine ⟨47854422251415614711603975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127611792670441639230943933 47854422251415614711603975)
    ·
      refine ⟨71781633377123422067405963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47854422251415614711603975 71781633377123422067405963)
      ·
        refine ⟨107672450065685133101108945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71781633377123422067405963 107672450065685133101108945)
        ·
          refine ⟨80754337549263849825831709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107672450065685133101108945 80754337549263849825831709)
          ·
            refine ⟨30282876580973943684686891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80754337549263849825831709 30282876580973943684686891)
            ·
              refine ⟨45424314871460915527030337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30282876580973943684686891 45424314871460915527030337)
              ·
                refine ⟨34068236153595686645272753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45424314871460915527030337 34068236153595686645272753)
                ·
                  refine ⟨25551177115196764983954565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34068236153595686645272753 25551177115196764983954565)
                  ·
                    refine ⟨4790845709099393434491481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25551177115196764983954565 4790845709099393434491481)
                    ·
                      refine ⟨3593134281824545075868611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4790845709099393434491481 3593134281824545075868611)
                      ·
                        rfl

theorem cell23_6997604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 2, 4, 2].length) (baseStart_6997604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997604 prefixEnd_6997604 := by exact prefixLift 6997604
  have htrace : WordTrace (prefixWord ++ tailWord_6997604) baseStart_6997604 baseEnd_6997604 := by
    simpa [prefixWord, tailWord_6997604, baseEnd_6997604] using wordTrace_append hprefix tailTrace_6997604
  have hstable : (prefixWord ++ tailWord_6997604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997604).length < 2 ^ (prefixWord ++ tailWord_6997604).sum := by decide
  have hdescent : baseEnd_6997604 < baseStart_6997604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997621 : List Nat := [1, 3, 4, 2, 1, 1, 2, 1, 2, 4, 2]
def baseStart_6997621 : Nat := 118140960795 + 6997621 * 2 ^ 59
def prefixEnd_6997621 : Nat := 4983230072969 + 3 ^ 40 * 6997621 * 2
def baseEnd_6997621 : Nat := 3593143010995671509356033

theorem tailTrace_6997621 : CollatzResearch.WordTrace tailWord_6997621 prefixEnd_6997621 3593143010995671509356033 := by
  unfold tailWord_6997621
  simp only [CollatzResearch.WordTrace]
  refine ⟨255224205381821690365256717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170149470254547793576837811 255224205381821690365256717)
  ·
    refine ⟨95709077018183133886971269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255224205381821690365256717 95709077018183133886971269)
    ·
      refine ⟨17945451940909337603807113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95709077018183133886971269 17945451940909337603807113)
      ·
        refine ⟨13459088955682003202855335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17945451940909337603807113 13459088955682003202855335)
        ·
          refine ⟨20188633433523004804283003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13459088955682003202855335 20188633433523004804283003)
          ·
            refine ⟨30282950150284507206424505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20188633433523004804283003 30282950150284507206424505)
            ·
              refine ⟨22712212612713380404818379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30282950150284507206424505 22712212612713380404818379)
              ·
                refine ⟨34068318919070070607227569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22712212612713380404818379 34068318919070070607227569)
                ·
                  refine ⟨25551239189302552955420677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34068318919070070607227569 25551239189302552955420677)
                  ·
                    refine ⟨4790857347994228679141377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25551239189302552955420677 4790857347994228679141377)
                    ·
                      refine ⟨3593143010995671509356033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4790857347994228679141377 3593143010995671509356033)
                      ·
                        rfl

theorem cell23_6997621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_6997621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997621 prefixEnd_6997621 := by exact prefixLift 6997621
  have htrace : WordTrace (prefixWord ++ tailWord_6997621) baseStart_6997621 baseEnd_6997621 := by
    simpa [prefixWord, tailWord_6997621, baseEnd_6997621] using wordTrace_append hprefix tailTrace_6997621
  have hstable : (prefixWord ++ tailWord_6997621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997621).length < 2 ^ (prefixWord ++ tailWord_6997621).sum := by decide
  have hdescent : baseEnd_6997621 < baseStart_6997621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997637 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 2, 5, 3]
def baseStart_6997637 : Nat := 118140960795 + 6997637 * 2 ^ 59
def prefixEnd_6997637 : Nat := 4983230072969 + 3 ^ 40 * 6997637 * 2
def baseEnd_6997637 : Nat := 3593151226686143446755959

theorem tailTrace_6997637 : CollatzResearch.WordTrace tailWord_6997637 prefixEnd_6997637 3593151226686143446755959 := by
  unfold tailWord_6997637
  simp only [CollatzResearch.WordTrace]
  refine ⟨255224788949763725097839165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170149859299842483398559443 255224788949763725097839165)
  ·
    refine ⟨95709295856161396911689687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255224788949763725097839165 95709295856161396911689687)
    ·
      refine ⟨143563943784242095367534531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95709295856161396911689687 143563943784242095367534531)
      ·
        refine ⟨215345915676363143051301797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143563943784242095367534531 215345915676363143051301797)
        ·
          refine ⟨40377359189318089322119087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215345915676363143051301797 40377359189318089322119087)
          ·
            refine ⟨60566038783977133983178631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40377359189318089322119087 60566038783977133983178631)
            ·
              refine ⟨90849058175965700974767947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60566038783977133983178631 90849058175965700974767947)
              ·
                refine ⟨136273587263948551462151921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90849058175965700974767947 136273587263948551462151921)
                ·
                  refine ⟨102205190447961413596613941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136273587263948551462151921 102205190447961413596613941)
                  ·
                    refine ⟨9581736604496382524682557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102205190447961413596613941 9581736604496382524682557)
                    ·
                      refine ⟨3593151226686143446755959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9581736604496382524682557 3593151226686143446755959)
                      ·
                        rfl

theorem cell23_6997637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 5, 3].length) (baseStart_6997637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997637 prefixEnd_6997637 := by exact prefixLift 6997637
  have htrace : WordTrace (prefixWord ++ tailWord_6997637) baseStart_6997637 baseEnd_6997637 := by
    simpa [prefixWord, tailWord_6997637, baseEnd_6997637] using wordTrace_append hprefix tailTrace_6997637
  have hstable : (prefixWord ++ tailWord_6997637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997637).length < 2 ^ (prefixWord ++ tailWord_6997637).sum := by decide
  have hdescent : baseEnd_6997637 < baseStart_6997637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997708 : List Nat := [2, 2, 1, 5, 2, 1, 3, 1, 1, 5]
def baseStart_6997708 : Nat := 118140960795 + 6997708 * 2 ^ 59
def prefixEnd_6997708 : Nat := 4983230072969 + 3 ^ 40 * 6997708 * 2
def baseEnd_6997708 : Nat := 1197729227937537556322711

theorem tailTrace_6997708 : CollatzResearch.WordTrace tailWord_6997708 prefixEnd_6997708 1197729227937537556322711 := by
  unfold tailWord_6997708
  simp only [CollatzResearch.WordTrace]
  refine ⟨127613689266253252111836889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170151585688337669482449185 127613689266253252111836889)
  ·
    refine ⟨95710266949689939083877667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127613689266253252111836889 95710266949689939083877667)
    ·
      refine ⟨143565400424534908625816501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95710266949689939083877667 143565400424534908625816501)
      ·
        refine ⟨13459256289800147683670297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143565400424534908625816501 13459256289800147683670297)
        ·
          refine ⟨10094442217350110762752723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13459256289800147683670297 10094442217350110762752723)
          ·
            refine ⟨15141663326025166144129085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10094442217350110762752723 15141663326025166144129085)
            ·
              refine ⟨5678123747259437304048407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15141663326025166144129085 5678123747259437304048407)
              ·
                refine ⟨8517185620889155956072611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5678123747259437304048407 8517185620889155956072611)
                ·
                  refine ⟨12775778431333733934108917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8517185620889155956072611 12775778431333733934108917)
                  ·
                    refine ⟨1197729227937537556322711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12775778431333733934108917 1197729227937537556322711)
                    ·
                      rfl

theorem cell23_6997708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 1, 5].length) (baseStart_6997708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997708 prefixEnd_6997708 := by exact prefixLift 6997708
  have htrace : WordTrace (prefixWord ++ tailWord_6997708) baseStart_6997708 baseEnd_6997708 := by
    simpa [prefixWord, tailWord_6997708, baseEnd_6997708] using wordTrace_append hprefix tailTrace_6997708
  have hstable : (prefixWord ++ tailWord_6997708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997708).length < 2 ^ (prefixWord ++ tailWord_6997708).sum := by decide
  have hdescent : baseEnd_6997708 < baseStart_6997708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997721 : List Nat := [1, 2, 1, 2, 3, 4, 2, 2, 2, 4]
def baseStart_6997721 : Nat := 118140960795 + 6997721 * 2 ^ 59
def prefixEnd_6997721 : Nat := 4983230072969 + 3 ^ 40 * 6997721 * 2
def baseEnd_6997721 : Nat := 1197731453020373706035191

theorem tailTrace_6997721 : CollatzResearch.WordTrace tailWord_6997721 prefixEnd_6997721 1197731453020373706035191 := by
  unfold tailWord_6997721
  simp only [CollatzResearch.WordTrace]
  refine ⟨255227852681459407443897017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170151901787639604962598011 255227852681459407443897017)
  ·
    refine ⟨191420889511094555582922763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255227852681459407443897017 191420889511094555582922763)
    ·
      refine ⟨287131334266641833374384145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191420889511094555582922763 287131334266641833374384145)
      ·
        refine ⟨215348500699981375030788109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287131334266641833374384145 215348500699981375030788109)
        ·
          refine ⟨80755687762493015636545541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215348500699981375030788109 80755687762493015636545541)
          ·
            refine ⟨15141691455467440431852289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80755687762493015636545541 15141691455467440431852289)
            ·
              refine ⟨11356268591600580323889217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15141691455467440431852289 11356268591600580323889217)
              ·
                refine ⟨8517201443700435242916913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11356268591600580323889217 8517201443700435242916913)
                ·
                  refine ⟨6387901082775326432187685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8517201443700435242916913 6387901082775326432187685)
                  ·
                    refine ⟨1197731453020373706035191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6387901082775326432187685 1197731453020373706035191)
                    ·
                      rfl

theorem cell23_6997721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 2, 4].length) (baseStart_6997721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997721 prefixEnd_6997721 := by exact prefixLift 6997721
  have htrace : WordTrace (prefixWord ++ tailWord_6997721) baseStart_6997721 baseEnd_6997721 := by
    simpa [prefixWord, tailWord_6997721, baseEnd_6997721] using wordTrace_append hprefix tailTrace_6997721
  have hstable : (prefixWord ++ tailWord_6997721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997721).length < 2 ^ (prefixWord ++ tailWord_6997721).sum := by decide
  have hdescent : baseEnd_6997721 < baseStart_6997721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997741 : List Nat := [1, 5, 1, 2, 1, 3, 2, 1, 1, 2, 4]
def baseStart_6997741 : Nat := 118140960795 + 6997741 * 2 ^ 59
def prefixEnd_6997741 : Nat := 4983230072969 + 3 ^ 40 * 6997741 * 2
def baseEnd_6997741 : Nat := 3593204628674211039855481

theorem tailTrace_6997741 : CollatzResearch.WordTrace tailWord_6997741 prefixEnd_6997741 3593204628674211039855481 := by
  unfold tailWord_6997741
  simp only [CollatzResearch.WordTrace]
  refine ⟨255228582141386950859625077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170152388094257967239750051 255228582141386950859625077)
  ·
    refine ⟨23927679575755026643089851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 255228582141386950859625077 23927679575755026643089851)
    ·
      refine ⟨35891519363632539964634777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23927679575755026643089851 35891519363632539964634777)
      ·
        refine ⟨26918639522724404973476083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35891519363632539964634777 26918639522724404973476083)
        ·
          refine ⟨40377959284086607460214125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26918639522724404973476083 40377959284086607460214125)
          ·
            refine ⟨15141734731532477797580297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40377959284086607460214125 15141734731532477797580297)
            ·
              refine ⟨11356301048649358348185223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15141734731532477797580297 11356301048649358348185223)
              ·
                refine ⟨17034451572974037522277835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11356301048649358348185223 17034451572974037522277835)
                ·
                  refine ⟨25551677359461056283416753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17034451572974037522277835 25551677359461056283416753)
                  ·
                    refine ⟨19163758019595792212562565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25551677359461056283416753 19163758019595792212562565)
                    ·
                      refine ⟨3593204628674211039855481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19163758019595792212562565 3593204628674211039855481)
                      ·
                        rfl

theorem cell23_6997741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_6997741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997741 prefixEnd_6997741 := by exact prefixLift 6997741
  have htrace : WordTrace (prefixWord ++ tailWord_6997741) baseStart_6997741 baseEnd_6997741 := by
    simpa [prefixWord, tailWord_6997741, baseEnd_6997741] using wordTrace_append hprefix tailTrace_6997741
  have hstable : (prefixWord ++ tailWord_6997741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997741).length < 2 ^ (prefixWord ++ tailWord_6997741).sum := by decide
  have hdescent : baseEnd_6997741 < baseStart_6997741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997762 : List Nat := [3, 4, 1, 1, 1, 1, 4, 3, 1, 2, 2]
def baseStart_6997762 : Nat := 118140960795 + 6997762 * 2 ^ 59
def prefixEnd_6997762 : Nat := 4983230072969 + 3 ^ 40 * 6997762 * 2
def baseEnd_6997762 : Nat := 3593215411767955457692885

theorem tailTrace_6997762 : CollatzResearch.WordTrace tailWord_6997762 prefixEnd_6997762 3593215411767955457692885 := by
  unfold tailWord_6997762
  simp only [CollatzResearch.WordTrace]
  refine ⟨63807337018577717861534885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170152898716207247630759693 63807337018577717861534885)
  ·
    refine ⟨11963875690983322099037791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63807337018577717861534885 11963875690983322099037791)
    ·
      refine ⟨17945813536474983148556687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11963875690983322099037791 17945813536474983148556687)
      ·
        refine ⟨26918720304712474722835031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17945813536474983148556687 26918720304712474722835031)
        ·
          refine ⟨40378080457068712084252547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26918720304712474722835031 40378080457068712084252547)
          ·
            refine ⟨60567120685603068126378821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40378080457068712084252547 60567120685603068126378821)
            ·
              refine ⟨11356335128550575273696029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60567120685603068126378821 11356335128550575273696029)
              ·
                refine ⟨4258625673206465727636011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11356335128550575273696029 4258625673206465727636011)
                ·
                  refine ⟨6387938509809698591454017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4258625673206465727636011 6387938509809698591454017)
                  ·
                    refine ⟨4790953882357273943590513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6387938509809698591454017 4790953882357273943590513)
                    ·
                      refine ⟨3593215411767955457692885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4790953882357273943590513 3593215411767955457692885)
                      ·
                        rfl

theorem cell23_6997762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_6997762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997762 prefixEnd_6997762 := by exact prefixLift 6997762
  have htrace : WordTrace (prefixWord ++ tailWord_6997762) baseStart_6997762 baseEnd_6997762 := by
    simpa [prefixWord, tailWord_6997762, baseEnd_6997762] using wordTrace_append hprefix tailTrace_6997762
  have hstable : (prefixWord ++ tailWord_6997762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997762).length < 2 ^ (prefixWord ++ tailWord_6997762).sum := by decide
  have hdescent : baseEnd_6997762 < baseStart_6997762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997787 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 5]
def baseStart_6997787 : Nat := 118140960795 + 6997787 * 2 ^ 59
def prefixEnd_6997787 : Nat := 4983230072969 + 3 ^ 40 * 6997787 * 2
def baseEnd_6997787 : Nat := 3593228248784317859880269

theorem tailTrace_6997787 : CollatzResearch.WordTrace tailWord_6997787 prefixEnd_6997787 3593228248784317859880269 := by
  unfold tailWord_6997787
  simp only [CollatzResearch.WordTrace]
  refine ⟨255230259899220300715799615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170153506599480200477199743 255230259899220300715799615)
  ·
    refine ⟨382845389848830451073699423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255230259899220300715799615 382845389848830451073699423)
    ·
      refine ⟨574268084773245676610549135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382845389848830451073699423 574268084773245676610549135)
      ·
        refine ⟨861402127159868514915823703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574268084773245676610549135 861402127159868514915823703)
        ·
          refine ⟨1292103190739802772373735555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 861402127159868514915823703 1292103190739802772373735555)
          ·
            refine ⟨1938154786109704158560603333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1292103190739802772373735555 1938154786109704158560603333)
            ·
              refine ⟨363404022395569529730113125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1938154786109704158560603333 363404022395569529730113125)
              ·
                refine ⟨68138254199169286824396211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 363404022395569529730113125 68138254199169286824396211)
                ·
                  refine ⟨102207381298753930236594317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68138254199169286824396211 102207381298753930236594317)
                  ·
                    refine ⟨38327767987032723838722869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102207381298753930236594317 38327767987032723838722869)
                    ·
                      refine ⟨3593228248784317859880269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38327767987032723838722869 3593228248784317859880269)
                      ·
                        rfl

theorem cell23_6997787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 5].length) (baseStart_6997787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997787 prefixEnd_6997787 := by exact prefixLift 6997787
  have htrace : WordTrace (prefixWord ++ tailWord_6997787) baseStart_6997787 baseEnd_6997787 := by
    simpa [prefixWord, tailWord_6997787, baseEnd_6997787] using wordTrace_append hprefix tailTrace_6997787
  have hstable : (prefixWord ++ tailWord_6997787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997787).length < 2 ^ (prefixWord ++ tailWord_6997787).sum := by decide
  have hdescent : baseEnd_6997787 < baseStart_6997787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997794 : List Nat := [3, 3, 1, 1, 2, 1, 1, 3, 2, 6]
def baseStart_6997794 : Nat := 118140960795 + 6997794 * 2 ^ 59
def prefixEnd_6997794 : Nat := 4983230072969 + 3 ^ 40 * 6997794 * 2
def baseEnd_6997794 : Nat := 1197743947716299777497579

theorem tailTrace_6997794 : CollatzResearch.WordTrace tailWord_6997794 prefixEnd_6997794 1197743947716299777497579 := by
  unfold tailWord_6997794
  simp only [CollatzResearch.WordTrace]
  refine ⟨63807628802548735227826109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170153676806796627274202957 63807628802548735227826109)
  ·
    refine ⟨23927860800955775710434791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63807628802548735227826109 23927860800955775710434791)
    ·
      refine ⟨35891791201433663565652187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23927860800955775710434791 35891791201433663565652187)
      ·
        refine ⟨53837686802150495348478281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35891791201433663565652187 53837686802150495348478281)
        ·
          refine ⟨40378265101612871511358711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53837686802150495348478281 40378265101612871511358711)
          ·
            refine ⟨60567397652419307267038067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40378265101612871511358711 60567397652419307267038067)
            ·
              refine ⟨90851096478628960900557101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60567397652419307267038067 90851096478628960900557101)
              ·
                refine ⟨34069161179485860337708913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90851096478628960900557101 34069161179485860337708913)
                ·
                  refine ⟨25551870884614395253281685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34069161179485860337708913 25551870884614395253281685)
                  ·
                    refine ⟨1197743947716299777497579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25551870884614395253281685 1197743947716299777497579)
                    ·
                      rfl

theorem cell23_6997794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_6997794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997794 prefixEnd_6997794 := by exact prefixLift 6997794
  have htrace : WordTrace (prefixWord ++ tailWord_6997794) baseStart_6997794 baseEnd_6997794 := by
    simpa [prefixWord, tailWord_6997794, baseEnd_6997794] using wordTrace_append hprefix tailTrace_6997794
  have hstable : (prefixWord ++ tailWord_6997794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997794).length < 2 ^ (prefixWord ++ tailWord_6997794).sum := by decide
  have hdescent : baseEnd_6997794 < baseStart_6997794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6997801 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 8, 2, 2]
def baseStart_6997801 : Nat := 118140960795 + 6997801 * 2 ^ 59
def prefixEnd_6997801 : Nat := 4983230072969 + 3 ^ 40 * 6997801 * 2
def baseEnd_6997801 : Nat := 3593235437513480805105205

theorem tailTrace_6997801 : CollatzResearch.WordTrace tailWord_6997801 prefixEnd_6997801 3593235437513480805105205 := by
  unfold tailWord_6997801
  simp only [CollatzResearch.WordTrace]
  refine ⟨255230770521169581106809257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170153847014113054071206171 255230770521169581106809257)
  ·
    refine ⟨191423077890877185830106943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255230770521169581106809257 191423077890877185830106943)
    ·
      refine ⟨287134616836315778745160415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191423077890877185830106943 287134616836315778745160415)
      ·
        refine ⟨430701925254473668117740623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287134616836315778745160415 430701925254473668117740623)
        ·
          refine ⟨646052887881710502176610935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430701925254473668117740623 646052887881710502176610935)
          ·
            refine ⟨969079331822565753264916403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646052887881710502176610935 969079331822565753264916403)
            ·
              refine ⟨1453618997733848629897374605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 969079331822565753264916403 1453618997733848629897374605)
              ·
                refine ⟨545107124150193236211515477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1453618997733848629897374605 545107124150193236211515477)
                ·
                  refine ⟨6387974111135076986853697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 545107124150193236211515477 6387974111135076986853697)
                  ·
                    refine ⟨4790980583351307740140273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6387974111135076986853697 4790980583351307740140273)
                    ·
                      refine ⟨3593235437513480805105205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4790980583351307740140273 3593235437513480805105205)
                      ·
                        rfl

theorem cell23_6997801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 8, 2, 2].length) (baseStart_6997801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6997801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6997801 prefixEnd_6997801 := by exact prefixLift 6997801
  have htrace : WordTrace (prefixWord ++ tailWord_6997801) baseStart_6997801 baseEnd_6997801 := by
    simpa [prefixWord, tailWord_6997801, baseEnd_6997801] using wordTrace_append hprefix tailTrace_6997801
  have hstable : (prefixWord ++ tailWord_6997801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6997801).length < 2 ^ (prefixWord ++ tailWord_6997801).sum := by decide
  have hdescent : baseEnd_6997801 < baseStart_6997801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6997801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
