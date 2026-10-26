import V185TrunkScan22Chunk107

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_968864 : List Nat := [2, 1, 1, 4, 2, 3, 1, 2, 2, 4]
def baseStart_968864 : Nat := 118140960795 + 968864 * 2 ^ 59
def prefixEnd_968864 : Nat := 4983230072969 + 3 ^ 40 * 968864 * 2
def baseEnd_968864 : Nat := 331661947225201699229521

theorem tailTrace_968864 : CollatzResearch.WordTrace tailWord_968864 prefixEnd_968864 331661947225201699229521 := by
  unfold tailWord_968864
  simp only [CollatzResearch.WordTrace]
  refine ⟨17668686580989335821332823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23558248774652447761777097 17668686580989335821332823)
  ·
    refine ⟨26503029871484003731999235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17668686580989335821332823 26503029871484003731999235)
    ·
      refine ⟨39754544807226005597998853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26503029871484003731999235 39754544807226005597998853)
      ·
        refine ⟨7453977151354876049624785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39754544807226005597998853 7453977151354876049624785)
        ·
          refine ⟨5590482863516157037218589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7453977151354876049624785 5590482863516157037218589)
          ·
            refine ⟨2096431073818558888956971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5590482863516157037218589 2096431073818558888956971)
            ·
              refine ⟨3144646610727838333435457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2096431073818558888956971 3144646610727838333435457)
              ·
                refine ⟨2358484958045878750076593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3144646610727838333435457 2358484958045878750076593)
                ·
                  refine ⟨1768863718534409062557445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2358484958045878750076593 1768863718534409062557445)
                  ·
                    refine ⟨331661947225201699229521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1768863718534409062557445 331661947225201699229521)
                    ·
                      rfl

theorem cell22_968864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 2, 4].length) (baseStart_968864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968864 prefixEnd_968864 := by exact prefixLift 968864
  have htrace : WordTrace (prefixWord ++ tailWord_968864) baseStart_968864 baseEnd_968864 := by
    simpa [prefixWord, tailWord_968864, baseEnd_968864] using wordTrace_append hprefix tailTrace_968864
  have hstable : (prefixWord ++ tailWord_968864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968864).length < 2 ^ (prefixWord ++ tailWord_968864).sum := by decide
  have hdescent : baseEnd_968864 < baseStart_968864 := by decide
  rcases family_descends (prefixWord ++ tailWord_968864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968866 : List Nat := [3, 3, 1, 3, 1, 1, 2, 1, 4, 3]
def baseStart_968866 : Nat := 118140960795 + 968866 * 2 ^ 59
def prefixEnd_968866 : Nat := 4983230072969 + 3 ^ 40 * 968866 * 2
def baseEnd_968866 : Nat := 331662631866074360679515

theorem tailTrace_968866 : CollatzResearch.WordTrace tailWord_968866 prefixEnd_968866 331662631866074360679515 := by
  unfold tailWord_968866
  simp only [CollatzResearch.WordTrace]
  refine ⟨8834361526992856496059613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23558297405314283989492301 8834361526992856496059613)
  ·
    refine ⟨3312885572622321186022355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8834361526992856496059613 3312885572622321186022355)
    ·
      refine ⟨4969328358933481779033533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3312885572622321186022355 4969328358933481779033533)
      ·
        refine ⟨1863498134600055667137575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4969328358933481779033533 1863498134600055667137575)
        ·
          refine ⟨2795247201900083500706363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1863498134600055667137575 2795247201900083500706363)
          ·
            refine ⟨4192870802850125251059545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2795247201900083500706363 4192870802850125251059545)
            ·
              refine ⟨3144653102137593938294659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4192870802850125251059545 3144653102137593938294659)
              ·
                refine ⟨4716979653206390907441989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3144653102137593938294659 4716979653206390907441989)
                ·
                  refine ⟨884433684976198295145373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4716979653206390907441989 884433684976198295145373)
                  ·
                    refine ⟨331662631866074360679515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 884433684976198295145373 331662631866074360679515)
                    ·
                      rfl

theorem cell22_968866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_968866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968866 prefixEnd_968866 := by exact prefixLift 968866
  have htrace : WordTrace (prefixWord ++ tailWord_968866) baseStart_968866 baseEnd_968866 := by
    simpa [prefixWord, tailWord_968866, baseEnd_968866] using wordTrace_append hprefix tailTrace_968866
  have hstable : (prefixWord ++ tailWord_968866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968866).length < 2 ^ (prefixWord ++ tailWord_968866).sum := by decide
  have hdescent : baseEnd_968866 < baseStart_968866 := by decide
  rcases family_descends (prefixWord ++ tailWord_968866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968868 : List Nat := [2, 3, 1, 2, 4, 1, 3, 2, 4]
def baseStart_968868 : Nat := 118140960795 + 968868 * 2 ^ 59
def prefixEnd_968868 : Nat := 4983230072969 + 3 ^ 40 * 968868 * 2
def baseEnd_968868 : Nat := 110554438835649007376503

theorem tailTrace_968868 : CollatzResearch.WordTrace tailWord_968868 prefixEnd_968868 110554438835649007376503 := by
  unfold tailWord_968868
  simp only [CollatzResearch.WordTrace]
  refine ⟨17668759526982090162905629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23558346035976120217207505 17668759526982090162905629)
  ·
    refine ⟨6625784822618283811089611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17668759526982090162905629 6625784822618283811089611)
    ·
      refine ⟨9938677233927425716634417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6625784822618283811089611 9938677233927425716634417)
      ·
        refine ⟨7454007925445569287475813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9938677233927425716634417 7454007925445569287475813)
        ·
          refine ⟨1397626486021044241401715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7454007925445569287475813 1397626486021044241401715)
          ·
            refine ⟨2096439729031566362102573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397626486021044241401715 2096439729031566362102573)
            ·
              refine ⟨786164898386837385788465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2096439729031566362102573 786164898386837385788465)
              ·
                refine ⟨589623673790128039341349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 786164898386837385788465 589623673790128039341349)
                ·
                  refine ⟨110554438835649007376503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 589623673790128039341349 110554438835649007376503)
                  ·
                    rfl

theorem cell22_968868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_968868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968868 prefixEnd_968868 := by exact prefixLift 968868
  have htrace : WordTrace (prefixWord ++ tailWord_968868) baseStart_968868 baseEnd_968868 := by
    simpa [prefixWord, tailWord_968868, baseEnd_968868] using wordTrace_append hprefix tailTrace_968868
  have hstable : (prefixWord ++ tailWord_968868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968868).length < 2 ^ (prefixWord ++ tailWord_968868).sum := by decide
  have hdescent : baseEnd_968868 < baseStart_968868 := by decide
  rcases family_descends (prefixWord ++ tailWord_968868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968898 : List Nat := [3, 5, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_968898 : Nat := 118140960795 + 968898 * 2 ^ 59
def prefixEnd_968898 : Nat := 4983230072969 + 3 ^ 40 * 968898 * 2
def baseEnd_968898 : Nat := 331673586120036943879417

theorem tailTrace_968898 : CollatzResearch.WordTrace tailWord_968898 prefixEnd_968898 331673586120036943879417 := by
  unfold tailWord_968898
  simp only [CollatzResearch.WordTrace]
  refine ⟨8834653310963873862350837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23559075495903663632935565 8834653310963873862350837)
  ·
    refine ⟨828248747902863174595391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8834653310963873862350837 828248747902863174595391)
    ·
      refine ⟨1242373121854294761893087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 828248747902863174595391 1242373121854294761893087)
      ·
        refine ⟨1863559682781442142839631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1242373121854294761893087 1863559682781442142839631)
        ·
          refine ⟨2795339524172163214259447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1863559682781442142839631 2795339524172163214259447)
          ·
            refine ⟨4193009286258244821389171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2795339524172163214259447 4193009286258244821389171)
            ·
              refine ⟨6289513929387367232083757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4193009286258244821389171 6289513929387367232083757)
              ·
                refine ⟨2358567723520262712031409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6289513929387367232083757 2358567723520262712031409)
                ·
                  refine ⟨1768925792640197034023557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2358567723520262712031409 1768925792640197034023557)
                  ·
                    refine ⟨331673586120036943879417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1768925792640197034023557 331673586120036943879417)
                    ·
                      rfl

theorem cell22_968898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_968898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968898 prefixEnd_968898 := by exact prefixLift 968898
  have htrace : WordTrace (prefixWord ++ tailWord_968898) baseStart_968898 baseEnd_968898 := by
    simpa [prefixWord, tailWord_968898, baseEnd_968898] using wordTrace_append hprefix tailTrace_968898
  have hstable : (prefixWord ++ tailWord_968898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968898).length < 2 ^ (prefixWord ++ tailWord_968898).sum := by decide
  have hdescent : baseEnd_968898 < baseStart_968898 := by decide
  rcases family_descends (prefixWord ++ tailWord_968898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968911 : List Nat := [1, 1, 2, 1, 1, 3, 4, 5, 1, 3]
def baseStart_968911 : Nat := 118140960795 + 968911 * 2 ^ 59
def prefixEnd_968911 : Nat := 4983230072969 + 3 ^ 40 * 968911 * 2
def baseEnd_968911 : Nat := 331678036285709243304377

theorem tailTrace_968911 : CollatzResearch.WordTrace tailWord_968911 prefixEnd_968911 331678036285709243304377 := by
  unfold tailWord_968911
  simp only [CollatzResearch.WordTrace]
  refine ⟨35339087392808398669626587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23559391595205599113084391 35339087392808398669626587)
  ·
    refine ⟨53008631089212598004439881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35339087392808398669626587 53008631089212598004439881)
    ·
      refine ⟨39756473316909448503329911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53008631089212598004439881 39756473316909448503329911)
      ·
        refine ⟨59634709975364172754994867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39756473316909448503329911 59634709975364172754994867)
        ·
          refine ⟨89452064963046259132492301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59634709975364172754994867 89452064963046259132492301)
          ·
            refine ⟨33544524361142347174684613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89452064963046259132492301 33544524361142347174684613)
            ·
              refine ⟨6289598317714190095253365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33544524361142347174684613 6289598317714190095253365)
              ·
                refine ⟨589649842285705321430003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6289598317714190095253365 589649842285705321430003)
                ·
                  refine ⟨884474763428557982145005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 589649842285705321430003 884474763428557982145005)
                  ·
                    refine ⟨331678036285709243304377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 884474763428557982145005 331678036285709243304377)
                    ·
                      rfl

theorem cell22_968911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 5, 1, 3].length) (baseStart_968911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968911 prefixEnd_968911 := by exact prefixLift 968911
  have htrace : WordTrace (prefixWord ++ tailWord_968911) baseStart_968911 baseEnd_968911 := by
    simpa [prefixWord, tailWord_968911, baseEnd_968911] using wordTrace_append hprefix tailTrace_968911
  have hstable : (prefixWord ++ tailWord_968911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968911).length < 2 ^ (prefixWord ++ tailWord_968911).sum := by decide
  have hdescent : baseEnd_968911 < baseStart_968911 := by decide
  rcases family_descends (prefixWord ++ tailWord_968911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968930 : List Nat := [3, 3, 4, 1, 1, 2, 1, 7]
def baseStart_968930 : Nat := 118140960795 + 968930 * 2 ^ 59
def prefixEnd_968930 : Nat := 4983230072969 + 3 ^ 40 * 968930 * 2
def baseEnd_968930 : Nat := 36853837819333280786591

theorem tailTrace_968930 : CollatzResearch.WordTrace tailWord_968930 prefixEnd_968930 36853837819333280786591 := by
  unfold tailWord_968930
  simp only [CollatzResearch.WordTrace]
  refine ⟨8834945094934891228642061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23559853586493043276378829 8834945094934891228642061)
  ·
    refine ⟨3313104410600584210740773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8834945094934891228642061 3313104410600584210740773)
    ·
      refine ⟨621207076987609539513895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3313104410600584210740773 621207076987609539513895)
      ·
        refine ⟨931810615481414309270843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621207076987609539513895 931810615481414309270843)
        ·
          refine ⟨1397715923222121463906265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 931810615481414309270843 1397715923222121463906265)
          ·
            refine ⟨1048286942416591097929699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1397715923222121463906265 1048286942416591097929699)
            ·
              refine ⟨1572430413624886646894549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1048286942416591097929699 1572430413624886646894549)
              ·
                refine ⟨36853837819333280786591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1572430413624886646894549 36853837819333280786591)
                ·
                  rfl

theorem cell22_968930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 7].length) (baseStart_968930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968930 prefixEnd_968930 := by exact prefixLift 968930
  have htrace : WordTrace (prefixWord ++ tailWord_968930) baseStart_968930 baseEnd_968930 := by
    simpa [prefixWord, tailWord_968930, baseEnd_968930] using wordTrace_append hprefix tailTrace_968930
  have hstable : (prefixWord ++ tailWord_968930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968930).length < 2 ^ (prefixWord ++ tailWord_968930).sum := by decide
  have hdescent : baseEnd_968930 < baseStart_968930 := by decide
  rcases family_descends (prefixWord ++ tailWord_968930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968954 : List Nat := [3, 1, 1, 1, 1, 5, 2, 1, 3, 4]
def baseStart_968954 : Nat := 118140960795 + 968954 * 2 ^ 59
def prefixEnd_968954 : Nat := 4983230072969 + 3 ^ 40 * 968954 * 2
def baseEnd_968954 : Nat := 331692756064471464479245

theorem tailTrace_968954 : CollatzResearch.WordTrace tailWord_968954 prefixEnd_968954 331692756064471464479245 := by
  unfold tailWord_968954
  simp only [CollatzResearch.WordTrace]
  refine ⟨8835163932913154253360479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23560437154435078008961277 8835163932913154253360479)
  ·
    refine ⟨13252745899369731380040719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8835163932913154253360479 13252745899369731380040719)
    ·
      refine ⟨19879118849054597070061079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13252745899369731380040719 19879118849054597070061079)
      ·
        refine ⟨29818678273581895605091619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19879118849054597070061079 29818678273581895605091619)
        ·
          refine ⟨44728017410372843407637429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29818678273581895605091619 44728017410372843407637429)
          ·
            refine ⟨4193251632222454069466009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44728017410372843407637429 4193251632222454069466009)
            ·
              refine ⟨3144938724166840552099507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4193251632222454069466009 3144938724166840552099507)
              ·
                refine ⟨4717408086250260828149261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3144938724166840552099507 4717408086250260828149261)
                ·
                  refine ⟨1769028032343847810555973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4717408086250260828149261 1769028032343847810555973)
                  ·
                    refine ⟨331692756064471464479245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1769028032343847810555973 331692756064471464479245)
                    ·
                      rfl

theorem cell22_968954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_968954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968954 prefixEnd_968954 := by exact prefixLift 968954
  have htrace : WordTrace (prefixWord ++ tailWord_968954) baseStart_968954 baseEnd_968954 := by
    simpa [prefixWord, tailWord_968954, baseEnd_968954] using wordTrace_append hprefix tailTrace_968954
  have hstable : (prefixWord ++ tailWord_968954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968954).length < 2 ^ (prefixWord ++ tailWord_968954).sum := by decide
  have hdescent : baseEnd_968954 < baseStart_968954 := by decide
  rcases family_descends (prefixWord ++ tailWord_968954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968986 : List Nat := [3, 1, 1, 3, 4, 1, 2, 1, 6]
def baseStart_968986 : Nat := 118140960795 + 968986 * 2 ^ 59
def prefixEnd_968986 : Nat := 4983230072969 + 3 ^ 40 * 968986 * 2
def baseEnd_968986 : Nat := 110567903439478015893049

theorem tailTrace_968986 : CollatzResearch.WordTrace tailWord_968986 prefixEnd_968986 110567903439478015893049 := by
  unfold tailWord_968986
  simp only [CollatzResearch.WordTrace]
  refine ⟨8835455716884171619651703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23561215245024457652404541 8835455716884171619651703)
  ·
    refine ⟨13253183575326257429477555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8835455716884171619651703 13253183575326257429477555)
    ·
      refine ⟨19879775362989386144216333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13253183575326257429477555 19879775362989386144216333)
      ·
        refine ⟨7454915761121019804081125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19879775362989386144216333 7454915761121019804081125)
        ·
          refine ⟨1397796705210191213265211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7454915761121019804081125 1397796705210191213265211)
          ·
            refine ⟨2096695057815286819897817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397796705210191213265211 2096695057815286819897817)
            ·
              refine ⟨1572521293361465114923363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2096695057815286819897817 1572521293361465114923363)
              ·
                refine ⟨2358781940042197672385045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1572521293361465114923363 2358781940042197672385045)
                ·
                  refine ⟨110567903439478015893049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2358781940042197672385045 110567903439478015893049)
                  ·
                    rfl

theorem cell22_968986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 6].length) (baseStart_968986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968986 prefixEnd_968986 := by exact prefixLift 968986
  have htrace : WordTrace (prefixWord ++ tailWord_968986) baseStart_968986 baseEnd_968986 := by
    simpa [prefixWord, tailWord_968986, baseEnd_968986] using wordTrace_append hprefix tailTrace_968986
  have hstable : (prefixWord ++ tailWord_968986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968986).length < 2 ^ (prefixWord ++ tailWord_968986).sum := by decide
  have hdescent : baseEnd_968986 < baseStart_968986 := by decide
  rcases family_descends (prefixWord ++ tailWord_968986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969005 : List Nat := [1, 5, 3, 1, 2, 1, 2, 2, 1, 4]
def baseStart_969005 : Nat := 118140960795 + 969005 * 2 ^ 59
def prefixEnd_969005 : Nat := 4983230072969 + 3 ^ 40 * 969005 * 2
def baseEnd_969005 : Nat := 331710214406724331454089

theorem tailTrace_969005 : CollatzResearch.WordTrace tailWord_969005 prefixEnd_969005 331710214406724331454089 := by
  unfold tailWord_969005
  simp only [CollatzResearch.WordTrace]
  refine ⟨35342515854467852723548469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23561677236311901815698979 35342515854467852723548469)
  ·
    refine ⟨3313360861356361192832669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35342515854467852723548469 3313360861356361192832669)
    ·
      refine ⟨1242510323008635447312251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3313360861356361192832669 1242510323008635447312251)
      ·
        refine ⟨1863765484512953170968377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1242510323008635447312251 1863765484512953170968377)
        ·
          refine ⟨1397824113384714878226283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1863765484512953170968377 1397824113384714878226283)
          ·
            refine ⟨2096736170077072317339425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397824113384714878226283 2096736170077072317339425)
            ·
              refine ⟨1572552127557804238004569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2096736170077072317339425 1572552127557804238004569)
              ·
                refine ⟨1179414095668353178503427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1572552127557804238004569 1179414095668353178503427)
                ·
                  refine ⟨1769121143502529767755141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1179414095668353178503427 1769121143502529767755141)
                  ·
                    refine ⟨331710214406724331454089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1769121143502529767755141 331710214406724331454089)
                    ·
                      rfl

theorem cell22_969005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_969005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_969005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_969005 prefixEnd_969005 := by exact prefixLift 969005
  have htrace : WordTrace (prefixWord ++ tailWord_969005) baseStart_969005 baseEnd_969005 := by
    simpa [prefixWord, tailWord_969005, baseEnd_969005] using wordTrace_append hprefix tailTrace_969005
  have hstable : (prefixWord ++ tailWord_969005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969005).length < 2 ^ (prefixWord ++ tailWord_969005).sum := by decide
  have hdescent : baseEnd_969005 < baseStart_969005 := by decide
  rcases family_descends (prefixWord ++ tailWord_969005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969097 : List Nat := [1, 2, 1, 1, 6, 3, 2, 2, 1, 3]
def baseStart_969097 : Nat := 118140960795 + 969097 * 2 ^ 59
def prefixEnd_969097 : Nat := 4983230072969 + 3 ^ 40 * 969097 * 2
def baseEnd_969097 : Nat := 331741707886866758153807

theorem tailTrace_969097 : CollatzResearch.WordTrace tailWord_969097 prefixEnd_969097 331741707886866758153807 := by
  unfold tailWord_969097
  simp only [CollatzResearch.WordTrace]
  refine ⟨35345871370134552435897545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23563914246756368290598363 35345871370134552435897545)
  ·
    refine ⟨26509403527600914326923159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35345871370134552435897545 26509403527600914326923159)
    ·
      refine ⟨39764105291401371490384739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26509403527600914326923159 39764105291401371490384739)
      ·
        refine ⟨59646157937102057235577109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39764105291401371490384739 59646157937102057235577109)
        ·
          refine ⟨2795913653301658932917677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 59646157937102057235577109 2795913653301658932917677)
          ·
            refine ⟨1048467619988122099844129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2795913653301658932917677 1048467619988122099844129)
            ·
              refine ⟨786350714991091574883097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1048467619988122099844129 786350714991091574883097)
              ·
                refine ⟨589763036243318681162323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 786350714991091574883097 589763036243318681162323)
                ·
                  refine ⟨884644554364978021743485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 589763036243318681162323 884644554364978021743485)
                  ·
                    refine ⟨331741707886866758153807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 884644554364978021743485 331741707886866758153807)
                    ·
                      rfl

theorem cell22_969097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 2, 1, 3].length) (baseStart_969097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_969097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_969097 prefixEnd_969097 := by exact prefixLift 969097
  have htrace : WordTrace (prefixWord ++ tailWord_969097) baseStart_969097 baseEnd_969097 := by
    simpa [prefixWord, tailWord_969097, baseEnd_969097] using wordTrace_append hprefix tailTrace_969097
  have hstable : (prefixWord ++ tailWord_969097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969097).length < 2 ^ (prefixWord ++ tailWord_969097).sum := by decide
  have hdescent : baseEnd_969097 < baseStart_969097 := by decide
  rcases family_descends (prefixWord ++ tailWord_969097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969108 : List Nat := [2, 4, 2, 1, 3, 1, 1, 1, 2, 5]
def baseStart_969108 : Nat := 118140960795 + 969108 * 2 ^ 59
def prefixEnd_969108 : Nat := 4983230072969 + 3 ^ 40 * 969108 * 2
def baseEnd_969108 : Nat := 331745473411666396128773

theorem tailTrace_969108 : CollatzResearch.WordTrace tailWord_969108 prefixEnd_969108 331745473411666396128773 := by
  unfold tailWord_969108
  simp only [CollatzResearch.WordTrace]
  refine ⟨17673136286547350657273989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23564181715396467543031985 17673136286547350657273989)
  ·
    refine ⟨3313713053727628248238873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17673136286547350657273989 3313713053727628248238873)
    ·
      refine ⟨2485284790295721186179155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3313713053727628248238873 2485284790295721186179155)
      ·
        refine ⟨3727927185443581779268733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2485284790295721186179155 3727927185443581779268733)
        ·
          refine ⟨1397972694541343167225775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3727927185443581779268733 1397972694541343167225775)
          ·
            refine ⟨2096959041812014750838663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397972694541343167225775 2096959041812014750838663)
            ·
              refine ⟨3145438562718022126257995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2096959041812014750838663 3145438562718022126257995)
              ·
                refine ⟨4718157844077033189386993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3145438562718022126257995 4718157844077033189386993)
                ·
                  refine ⟨3538618383057774892040245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4718157844077033189386993 3538618383057774892040245)
                  ·
                    refine ⟨331745473411666396128773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3538618383057774892040245 331745473411666396128773)
                    ·
                      rfl

theorem cell22_969108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_969108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_969108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_969108 prefixEnd_969108 := by exact prefixLift 969108
  have htrace : WordTrace (prefixWord ++ tailWord_969108) baseStart_969108 baseEnd_969108 := by
    simpa [prefixWord, tailWord_969108, baseEnd_969108] using wordTrace_append hprefix tailTrace_969108
  have hstable : (prefixWord ++ tailWord_969108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969108).length < 2 ^ (prefixWord ++ tailWord_969108).sum := by decide
  have hdescent : baseEnd_969108 < baseStart_969108 := by decide
  rcases family_descends (prefixWord ++ tailWord_969108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969138 : List Nat := [3, 2, 1, 1, 1, 1, 6, 3, 4]
def baseStart_969138 : Nat := 118140960795 + 969138 * 2 ^ 59
def prefixEnd_969138 : Nat := 4983230072969 + 3 ^ 40 * 969138 * 2
def baseEnd_969138 : Nat := 110585247674918772626227

theorem tailTrace_969138 : CollatzResearch.WordTrace tailWord_969138 prefixEnd_969138 110585247674918772626227 := by
  unfold tailWord_969138
  simp only [CollatzResearch.WordTrace]
  refine ⟨8836841690746504109535017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23564911175324010958760045 8836841690746504109535017)
  ·
    refine ⟨6627631268059878082151263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8836841690746504109535017 6627631268059878082151263)
    ·
      refine ⟨9941446902089817123226895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6627631268059878082151263 9941446902089817123226895)
      ·
        refine ⟨14912170353134725684840343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9941446902089817123226895 14912170353134725684840343)
        ·
          refine ⟨22368255529702088527260515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14912170353134725684840343 22368255529702088527260515)
          ·
            refine ⟨33552383294553132790890773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22368255529702088527260515 33552383294553132790890773)
            ·
              refine ⟨1572767966932178099573005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33552383294553132790890773 1572767966932178099573005)
              ·
                refine ⟨589787987599566787339877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1572767966932178099573005 589787987599566787339877)
                ·
                  refine ⟨110585247674918772626227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 589787987599566787339877 110585247674918772626227)
                  ·
                    rfl

theorem cell22_969138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_969138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_969138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_969138 prefixEnd_969138 := by exact prefixLift 969138
  have htrace : WordTrace (prefixWord ++ tailWord_969138) baseStart_969138 baseEnd_969138 := by
    simpa [prefixWord, tailWord_969138, baseEnd_969138] using wordTrace_append hprefix tailTrace_969138
  have hstable : (prefixWord ++ tailWord_969138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969138).length < 2 ^ (prefixWord ++ tailWord_969138).sum := by decide
  have hdescent : baseEnd_969138 < baseStart_969138 := by decide
  rcases family_descends (prefixWord ++ tailWord_969138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969181 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 2, 7]
def baseStart_969181 : Nat := 118140960795 + 969181 * 2 ^ 59
def prefixEnd_969181 : Nat := 4983230072969 + 3 ^ 40 * 969181 * 2
def baseEnd_969181 : Nat := 331770462803518539053549

theorem tailTrace_969181 : CollatzResearch.WordTrace tailWord_969181 prefixEnd_969181 331770462803518539053549 := by
  unfold tailWord_969181
  simp only [CollatzResearch.WordTrace]
  refine ⟨35348935101830234781955397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23565956734553489854636931 35348935101830234781955397)
  ·
    refine ⟨6627925331593169021616637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35348935101830234781955397 6627925331593169021616637)
    ·
      refine ⟨2485471999347438383106239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6627925331593169021616637 2485471999347438383106239)
      ·
        refine ⟨3728207999021157574659359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2485471999347438383106239 3728207999021157574659359)
        ·
          refine ⟨5592311998531736361989039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3728207999021157574659359 5592311998531736361989039)
          ·
            refine ⟨8388467997797604542983559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5592311998531736361989039 8388467997797604542983559)
            ·
              refine ⟨12582701996696406814475339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8388467997797604542983559 12582701996696406814475339)
              ·
                refine ⟨18874052995044610221713009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12582701996696406814475339 18874052995044610221713009)
                ·
                  refine ⟨14155539746283457666284757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18874052995044610221713009 14155539746283457666284757)
                  ·
                    refine ⟨331770462803518539053549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14155539746283457666284757 331770462803518539053549)
                    ·
                      rfl

theorem cell22_969181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_969181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_969181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_969181 prefixEnd_969181 := by exact prefixLift 969181
  have htrace : WordTrace (prefixWord ++ tailWord_969181) baseStart_969181 baseEnd_969181 := by
    simpa [prefixWord, tailWord_969181, baseEnd_969181] using wordTrace_append hprefix tailTrace_969181
  have hstable : (prefixWord ++ tailWord_969181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969181).length < 2 ^ (prefixWord ++ tailWord_969181).sum := by decide
  have hdescent : baseEnd_969181 < baseStart_969181 := by decide
  rcases family_descends (prefixWord ++ tailWord_969181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969183 : List Nat := [1, 1, 2, 3, 3, 4, 2, 6]
def baseStart_969183 : Nat := 118140960795 + 969183 * 2 ^ 59
def prefixEnd_969183 : Nat := 4983230072969 + 3 ^ 40 * 969183 * 2
def baseEnd_969183 : Nat := 36863460827154577833727

theorem tailTrace_969183 : CollatzResearch.WordTrace tailWord_969183 prefixEnd_969183 36863460827154577833727 := by
  unfold tailWord_969183
  simp only [CollatzResearch.WordTrace]
  refine ⟨35349008047822989123528203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23566005365215326082352135 35349008047822989123528203)
  ·
    refine ⟨53023512071734483685292305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35349008047822989123528203 53023512071734483685292305)
    ·
      refine ⟨39767634053800862763969229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53023512071734483685292305 39767634053800862763969229)
      ·
        refine ⟨14912862770175323536488461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39767634053800862763969229 14912862770175323536488461)
        ·
          refine ⟨5592323538815746326183173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14912862770175323536488461 5592323538815746326183173)
          ·
            refine ⟨1048560663527952436159345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5592323538815746326183173 1048560663527952436159345)
            ·
              refine ⟨786420497645964327119509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1048560663527952436159345 786420497645964327119509)
              ·
                refine ⟨36863460827154577833727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 786420497645964327119509 36863460827154577833727)
                ·
                  rfl

theorem cell22_969183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 6].length) (baseStart_969183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_969183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_969183 prefixEnd_969183 := by exact prefixLift 969183
  have htrace : WordTrace (prefixWord ++ tailWord_969183) baseStart_969183 baseEnd_969183 := by
    simpa [prefixWord, tailWord_969183, baseEnd_969183] using wordTrace_append hprefix tailTrace_969183
  have hstable : (prefixWord ++ tailWord_969183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969183).length < 2 ^ (prefixWord ++ tailWord_969183).sum := by decide
  have hdescent : baseEnd_969183 < baseStart_969183 := by decide
  rcases family_descends (prefixWord ++ tailWord_969183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969226 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 1, 7]
def baseStart_969226 : Nat := 118140960795 + 969226 * 2 ^ 59
def prefixEnd_969226 : Nat := 4983230072969 + 3 ^ 40 * 969226 * 2
def baseEnd_969226 : Nat := 331785867223153421678411

theorem tailTrace_969226 : CollatzResearch.WordTrace tailWord_969226 prefixEnd_969226 331785867223153421678411 := by
  unfold tailWord_969226
  simp only [CollatzResearch.WordTrace]
  refine ⟨8837644096666801866835883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23567050924444804978229021 8837644096666801866835883)
  ·
    refine ⟨13256466145000202800253825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8837644096666801866835883 13256466145000202800253825)
    ·
      refine ⟨9942349608750152100190369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13256466145000202800253825 9942349608750152100190369)
      ·
        refine ⟨7456762206562614075142777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9942349608750152100190369 7456762206562614075142777)
        ·
          refine ⟨5592571654921960556357083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7456762206562614075142777 5592571654921960556357083)
          ·
            refine ⟨8388857482382940834535625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5592571654921960556357083 8388857482382940834535625)
            ·
              refine ⟨6291643111787205625901719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8388857482382940834535625 6291643111787205625901719)
              ·
                refine ⟨9437464667680808438852579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6291643111787205625901719 9437464667680808438852579)
                ·
                  refine ⟨14156197001521212658278869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9437464667680808438852579 14156197001521212658278869)
                  ·
                    refine ⟨331785867223153421678411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14156197001521212658278869 331785867223153421678411)
                    ·
                      rfl

theorem cell22_969226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_969226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_969226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_969226 prefixEnd_969226 := by exact prefixLift 969226
  have htrace : WordTrace (prefixWord ++ tailWord_969226) baseStart_969226 baseEnd_969226 := by
    simpa [prefixWord, tailWord_969226, baseEnd_969226] using wordTrace_append hprefix tailTrace_969226
  have hstable : (prefixWord ++ tailWord_969226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969226).length < 2 ^ (prefixWord ++ tailWord_969226).sum := by decide
  have hdescent : baseEnd_969226 < baseStart_969226 := by decide
  rcases family_descends (prefixWord ++ tailWord_969226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969228 : List Nat := [2, 2, 1, 2, 4, 2, 1, 3, 5]
def baseStart_969228 : Nat := 118140960795 + 969228 * 2 ^ 59
def prefixEnd_969228 : Nat := 4983230072969 + 3 ^ 40 * 969228 * 2
def baseEnd_969228 : Nat := 110595517288008694376135

theorem tailTrace_969228 : CollatzResearch.WordTrace tailWord_969228 prefixEnd_969228 110595517288008694376135 := by
  unfold tailWord_969228
  simp only [CollatzResearch.WordTrace]
  refine ⟨17675324666329980904458169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23567099555106641205944225 17675324666329980904458169)
  ·
    refine ⟨13256493499747485678343627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17675324666329980904458169 13256493499747485678343627)
    ·
      refine ⟨19884740249621228517515441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13256493499747485678343627 19884740249621228517515441)
      ·
        refine ⟨14913555187215921388136581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19884740249621228517515441 14913555187215921388136581)
        ·
          refine ⟨2796291597602985260275609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14913555187215921388136581 2796291597602985260275609)
          ·
            refine ⟨2097218698202238945206707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2796291597602985260275609 2097218698202238945206707)
            ·
              refine ⟨3145828047303358417810061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2097218698202238945206707 3145828047303358417810061)
              ·
                refine ⟨1179685517738759406678773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3145828047303358417810061 1179685517738759406678773)
                ·
                  refine ⟨110595517288008694376135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1179685517738759406678773 110595517288008694376135)
                  ·
                    rfl

theorem cell22_969228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 5].length) (baseStart_969228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_969228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_969228 prefixEnd_969228 := by exact prefixLift 969228
  have htrace : WordTrace (prefixWord ++ tailWord_969228) baseStart_969228 baseEnd_969228 := by
    simpa [prefixWord, tailWord_969228, baseEnd_969228] using wordTrace_append hprefix tailTrace_969228
  have hstable : (prefixWord ++ tailWord_969228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969228).length < 2 ^ (prefixWord ++ tailWord_969228).sum := by decide
  have hdescent : baseEnd_969228 < baseStart_969228 := by decide
  rcases family_descends (prefixWord ++ tailWord_969228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969241 : List Nat := [1, 2, 1, 2, 1, 1, 2, 5, 3, 4]
def baseStart_969241 : Nat := 118140960795 + 969241 * 2 ^ 59
def prefixEnd_969241 : Nat := 4983230072969 + 3 ^ 40 * 969241 * 2
def baseEnd_969241 : Nat := 331791002029698382553365

theorem tailTrace_969241 : CollatzResearch.WordTrace tailWord_969241 prefixEnd_969241 331791002029698382553365 := by
  unfold tailWord_969241
  simp only [CollatzResearch.WordTrace]
  refine ⟨35351123481612865029139577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23567415654408576686093051 35351123481612865029139577)
  ·
    refine ⟨26513342611209648771854683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35351123481612865029139577 26513342611209648771854683)
    ·
      refine ⟨39770013916814473157782025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26513342611209648771854683 39770013916814473157782025)
      ·
        refine ⟨29827510437610854868336519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39770013916814473157782025 29827510437610854868336519)
        ·
          refine ⟨44741265656416282302504779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29827510437610854868336519 44741265656416282302504779)
          ·
            refine ⟨67111898484624423453757169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44741265656416282302504779 67111898484624423453757169)
            ·
              refine ⟨50333923863468317590317877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67111898484624423453757169 50333923863468317590317877)
              ·
                refine ⟨4718805362200154774092301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50333923863468317590317877 4718805362200154774092301)
                ·
                  refine ⟨1769552010825058040284613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4718805362200154774092301 1769552010825058040284613)
                  ·
                    refine ⟨331791002029698382553365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1769552010825058040284613 331791002029698382553365)
                    ·
                      rfl

theorem cell22_969241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 4].length) (baseStart_969241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_969241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_969241 prefixEnd_969241 := by exact prefixLift 969241
  have htrace : WordTrace (prefixWord ++ tailWord_969241) baseStart_969241 baseEnd_969241 := by
    simpa [prefixWord, tailWord_969241, baseEnd_969241] using wordTrace_append hprefix tailTrace_969241
  have hstable : (prefixWord ++ tailWord_969241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969241).length < 2 ^ (prefixWord ++ tailWord_969241).sum := by decide
  have hdescent : baseEnd_969241 < baseStart_969241 := by decide
  rcases family_descends (prefixWord ++ tailWord_969241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969271 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 3, 5]
def baseStart_969271 : Nat := 118140960795 + 969271 * 2 ^ 59
def prefixEnd_969271 : Nat := 4983230072969 + 3 ^ 40 * 969271 * 2
def baseEnd_969271 : Nat := 331801271642788304303273

theorem tailTrace_969271 : CollatzResearch.WordTrace tailWord_969271 prefixEnd_969271 331801271642788304303273 := by
  unfold tailWord_969271
  simp only [CollatzResearch.WordTrace]
  refine ⟨35352217671504180152731667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23568145114336120101821111 35352217671504180152731667)
  ·
    refine ⟨53028326507256270229097501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35352217671504180152731667 53028326507256270229097501)
    ·
      refine ⟨19885622440221101335911563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53028326507256270229097501 19885622440221101335911563)
      ·
        refine ⟨29828433660331652003867345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19885622440221101335911563 29828433660331652003867345)
        ·
          refine ⟨22371325245248739002900509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29828433660331652003867345 22371325245248739002900509)
          ·
            refine ⟨8389246966968277126087691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22371325245248739002900509 8389246966968277126087691)
            ·
              refine ⟨12583870450452415689131537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8389246966968277126087691 12583870450452415689131537)
              ·
                refine ⟨9437902837839311766848653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12583870450452415689131537 9437902837839311766848653)
                ·
                  refine ⟨3539213564189741912568245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9437902837839311766848653 3539213564189741912568245)
                  ·
                    refine ⟨331801271642788304303273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3539213564189741912568245 331801271642788304303273)
                    ·
                      rfl

theorem cell22_969271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_969271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_969271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_969271 prefixEnd_969271 := by exact prefixLift 969271
  have htrace : WordTrace (prefixWord ++ tailWord_969271) baseStart_969271 baseEnd_969271 := by
    simpa [prefixWord, tailWord_969271, baseEnd_969271] using wordTrace_append hprefix tailTrace_969271
  have hstable : (prefixWord ++ tailWord_969271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969271).length < 2 ^ (prefixWord ++ tailWord_969271).sum := by decide
  have hdescent : baseEnd_969271 < baseStart_969271 := by decide
  rcases family_descends (prefixWord ++ tailWord_969271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969301 : List Nat := [1, 3, 2, 2, 1, 1, 2, 10]
def baseStart_969301 : Nat := 118140960795 + 969301 * 2 ^ 59
def prefixEnd_969301 : Nat := 4983230072969 + 3 ^ 40 * 969301 * 2
def baseEnd_969301 : Nat := 36867949028430914005909

theorem tailTrace_969301 : CollatzResearch.WordTrace tailWord_969301 prefixEnd_969301 36867949028430914005909 := by
  unfold tailWord_969301
  simp only [CollatzResearch.WordTrace]
  refine ⟨35353311861395495276323757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23568874574263663517549171 35353311861395495276323757)
  ·
    refine ⟨13257491948023310728621409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35353311861395495276323757 13257491948023310728621409)
    ·
      refine ⟨9943118961017483046466057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13257491948023310728621409 9943118961017483046466057)
      ·
        refine ⟨7457339220763112284849543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9943118961017483046466057 7457339220763112284849543)
        ·
          refine ⟨11186008831144668427274315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7457339220763112284849543 11186008831144668427274315)
          ·
            refine ⟨16779013246717002640911473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11186008831144668427274315 16779013246717002640911473)
            ·
              refine ⟨12584259935037751980683605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16779013246717002640911473 12584259935037751980683605)
              ·
                refine ⟨36867949028430914005909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12584259935037751980683605 36867949028430914005909)
                ·
                  rfl

theorem cell22_969301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 10].length) (baseStart_969301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_969301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_969301 prefixEnd_969301 := by exact prefixLift 969301
  have htrace : WordTrace (prefixWord ++ tailWord_969301) baseStart_969301 baseEnd_969301 := by
    simpa [prefixWord, tailWord_969301, baseEnd_969301] using wordTrace_append hprefix tailTrace_969301
  have hstable : (prefixWord ++ tailWord_969301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969301).length < 2 ^ (prefixWord ++ tailWord_969301).sum := by decide
  have hdescent : baseEnd_969301 < baseStart_969301 := by decide
  rcases family_descends (prefixWord ++ tailWord_969301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969331 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 2, 6]
def baseStart_969331 : Nat := 118140960795 + 969331 * 2 ^ 59
def prefixEnd_969331 : Nat := 4983230072969 + 3 ^ 40 * 969331 * 2
def baseEnd_969331 : Nat := 331821810868968147803089

theorem tailTrace_969331 : CollatzResearch.WordTrace tailWord_969331 prefixEnd_969331 331821810868968147803089 := by
  unfold tailWord_969331
  simp only [CollatzResearch.WordTrace]
  refine ⟨35354406051286810399915847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23569604034191206933277231 35354406051286810399915847)
  ·
    refine ⟨53031609076930215599873771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35354406051286810399915847 53031609076930215599873771)
    ·
      refine ⟨79547413615395323399810657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53031609076930215599873771 79547413615395323399810657)
      ·
        refine ⟨59660560211546492549857993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79547413615395323399810657 59660560211546492549857993)
        ·
          refine ⟨44745420158659869412393495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59660560211546492549857993 44745420158659869412393495)
          ·
            refine ⟨67118130237989804118590243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44745420158659869412393495 67118130237989804118590243)
            ·
              refine ⟨100677195356984706177885365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67118130237989804118590243 100677195356984706177885365)
              ·
                refine ⟨9438487064717316204176753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100677195356984706177885365 9438487064717316204176753)
                ·
                  refine ⟨7078865298537987153132565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9438487064717316204176753 7078865298537987153132565)
                  ·
                    refine ⟨331821810868968147803089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7078865298537987153132565 331821810868968147803089)
                    ·
                      rfl

theorem cell22_969331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 6].length) (baseStart_969331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_969331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_969331 prefixEnd_969331 := by exact prefixLift 969331
  have htrace : WordTrace (prefixWord ++ tailWord_969331) baseStart_969331 baseEnd_969331 := by
    simpa [prefixWord, tailWord_969331, baseEnd_969331] using wordTrace_append hprefix tailTrace_969331
  have hstable : (prefixWord ++ tailWord_969331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969331).length < 2 ^ (prefixWord ++ tailWord_969331).sum := by decide
  have hdescent : baseEnd_969331 < baseStart_969331 := by decide
  rcases family_descends (prefixWord ++ tailWord_969331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969397 : List Nat := [1, 3, 3, 3, 1, 1, 4, 1, 5]
def baseStart_969397 : Nat := 118140960795 + 969397 * 2 ^ 59
def prefixEnd_969397 : Nat := 4983230072969 + 3 ^ 40 * 969397 * 2
def baseEnd_969397 : Nat := 110614801339255325217629

theorem tailTrace_969397 : CollatzResearch.WordTrace tailWord_969397 prefixEnd_969397 110614801339255325217629 := by
  unfold tailWord_969397
  simp only [CollatzResearch.WordTrace]
  refine ⟨35356813269047703671818445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23571208846031802447878963 35356813269047703671818445)
  ·
    refine ⟨13258804975892888876931917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35356813269047703671818445 13258804975892888876931917)
    ·
      refine ⟨4972051865959833328849469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13258804975892888876931917 4972051865959833328849469)
      ·
        refine ⟨1864519449734937498318551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4972051865959833328849469 1864519449734937498318551)
        ·
          refine ⟨2796779174602406247477827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1864519449734937498318551 2796779174602406247477827)
          ·
            refine ⟨4195168761903609371216741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2796779174602406247477827 4195168761903609371216741)
            ·
              refine ⟨786594142856926757103139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4195168761903609371216741 786594142856926757103139)
              ·
                refine ⟨1179891214285390135654709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 786594142856926757103139 1179891214285390135654709)
                ·
                  refine ⟨110614801339255325217629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1179891214285390135654709 110614801339255325217629)
                  ·
                    rfl

theorem cell22_969397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 5].length) (baseStart_969397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_969397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_969397 prefixEnd_969397 := by exact prefixLift 969397
  have htrace : WordTrace (prefixWord ++ tailWord_969397) baseStart_969397 baseEnd_969397 := by
    simpa [prefixWord, tailWord_969397, baseEnd_969397] using wordTrace_append hprefix tailTrace_969397
  have hstable : (prefixWord ++ tailWord_969397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969397).length < 2 ^ (prefixWord ++ tailWord_969397).sum := by decide
  have hdescent : baseEnd_969397 < baseStart_969397 := by decide
  rcases family_descends (prefixWord ++ tailWord_969397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969425 : List Nat := [1, 2, 2, 1, 2, 3, 2, 5, 4]
def baseStart_969425 : Nat := 118140960795 + 969425 * 2 ^ 59
def prefixEnd_969425 : Nat := 4983230072969 + 3 ^ 40 * 969425 * 2
def baseEnd_969425 : Nat := 110617996329994411984267

theorem tailTrace_969425 : CollatzResearch.WordTrace tailWord_969425 prefixEnd_969425 110617996329994411984267 := by
  unfold tailWord_969425
  simp only [CollatzResearch.WordTrace]
  refine ⟨35357834512946264453837729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23571889675297509635891819 35357834512946264453837729)
  ·
    refine ⟨26518375884709698340378297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35357834512946264453837729 26518375884709698340378297)
    ·
      refine ⟨19888781913532273755283723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26518375884709698340378297 19888781913532273755283723)
      ·
        refine ⟨29833172870298410632925585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19888781913532273755283723 29833172870298410632925585)
        ·
          refine ⟨22374879652723807974694189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29833172870298410632925585 22374879652723807974694189)
          ·
            refine ⟨8390579869771427990510321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22374879652723807974694189 8390579869771427990510321)
            ·
              refine ⟨6292934902328570992882741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8390579869771427990510321 6292934902328570992882741)
              ·
                refine ⟨589962647093303530582757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6292934902328570992882741 589962647093303530582757)
                ·
                  refine ⟨110617996329994411984267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 589962647093303530582757 110617996329994411984267)
                  ·
                    rfl

theorem cell22_969425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 5, 4].length) (baseStart_969425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_969425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_969425 prefixEnd_969425 := by exact prefixLift 969425
  have htrace : WordTrace (prefixWord ++ tailWord_969425) baseStart_969425 baseEnd_969425 := by
    simpa [prefixWord, tailWord_969425, baseEnd_969425] using wordTrace_append hprefix tailTrace_969425
  have hstable : (prefixWord ++ tailWord_969425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969425).length < 2 ^ (prefixWord ++ tailWord_969425).sum := by decide
  have hdescent : baseEnd_969425 < baseStart_969425 := by decide
  rcases family_descends (prefixWord ++ tailWord_969425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969607 : List Nat := [1, 1, 4, 2, 3, 1, 2, 2, 2, 4]
def baseStart_969607 : Nat := 118140960795 + 969607 * 2 ^ 59
def prefixEnd_969607 : Nat := 4983230072969 + 3 ^ 40 * 969607 * 2
def baseEnd_969607 : Nat := 331916291309395427902243

theorem tailTrace_969607 : CollatzResearch.WordTrace tailWord_969607 prefixEnd_969607 331916291309395427902243 := by
  unfold tailWord_969607
  simp only [CollatzResearch.WordTrace]
  refine ⟨35364472598286909536963075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23576315065524606357975383 35364472598286909536963075)
  ·
    refine ⟨53046708897430364305444613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35364472598286909536963075 53046708897430364305444613)
    ·
      refine ⟨9946257918268193307270865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53046708897430364305444613 9946257918268193307270865)
      ·
        refine ⟨7459693438701144980453149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9946257918268193307270865 7459693438701144980453149)
        ·
          refine ⟨2797385039512929367669931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7459693438701144980453149 2797385039512929367669931)
          ·
            refine ⟨4196077559269394051504897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2797385039512929367669931 4196077559269394051504897)
            ·
              refine ⟨3147058169452045538628673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4196077559269394051504897 3147058169452045538628673)
              ·
                refine ⟨2360293627089034153971505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3147058169452045538628673 2360293627089034153971505)
                ·
                  refine ⟨1770220220316775615478629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2360293627089034153971505 1770220220316775615478629)
                  ·
                    refine ⟨331916291309395427902243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1770220220316775615478629 331916291309395427902243)
                    ·
                      rfl

theorem cell22_969607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_969607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_969607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_969607 prefixEnd_969607 := by exact prefixLift 969607
  have htrace : WordTrace (prefixWord ++ tailWord_969607) baseStart_969607 baseEnd_969607 := by
    simpa [prefixWord, tailWord_969607, baseEnd_969607] using wordTrace_append hprefix tailTrace_969607
  have hstable : (prefixWord ++ tailWord_969607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969607).length < 2 ^ (prefixWord ++ tailWord_969607).sum := by decide
  have hdescent : baseEnd_969607 < baseStart_969607 := by decide
  rcases family_descends (prefixWord ++ tailWord_969607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969609 : List Nat := [1, 2, 1, 1, 5, 3, 2, 2, 2, 3]
def baseStart_969609 : Nat := 118140960795 + 969609 * 2 ^ 59
def prefixEnd_969609 : Nat := 4983230072969 + 3 ^ 40 * 969609 * 2
def baseEnd_969609 : Nat := 331916975950268089352237

theorem tailTrace_969609 : CollatzResearch.WordTrace tailWord_969609 prefixEnd_969609 331916975950268089352237 := by
  unfold tailWord_969609
  simp only [CollatzResearch.WordTrace]
  refine ⟨35364545544279663878535881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23576363696186442585690587 35364545544279663878535881)
  ·
    refine ⟨26523409158209747908901911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35364545544279663878535881 26523409158209747908901911)
    ·
      refine ⟨39785113737314621863352867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26523409158209747908901911 39785113737314621863352867)
      ·
        refine ⟨59677670605971932795029301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39785113737314621863352867 59677670605971932795029301)
        ·
          refine ⟨5594781619309868699533997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59677670605971932795029301 5594781619309868699533997)
          ·
            refine ⟨2098043107241200762325249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5594781619309868699533997 2098043107241200762325249)
            ·
              refine ⟨1573532330430900571743937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2098043107241200762325249 1573532330430900571743937)
              ·
                refine ⟨1180149247823175428807953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1573532330430900571743937 1180149247823175428807953)
                ·
                  refine ⟨885111935867381571605965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1180149247823175428807953 885111935867381571605965)
                  ·
                    refine ⟨331916975950268089352237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 885111935867381571605965 331916975950268089352237)
                    ·
                      rfl

theorem cell22_969609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 2, 3].length) (baseStart_969609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_969609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_969609 prefixEnd_969609 := by exact prefixLift 969609
  have htrace : WordTrace (prefixWord ++ tailWord_969609) baseStart_969609 baseEnd_969609 := by
    simpa [prefixWord, tailWord_969609, baseEnd_969609] using wordTrace_append hprefix tailTrace_969609
  have hstable : (prefixWord ++ tailWord_969609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969609).length < 2 ^ (prefixWord ++ tailWord_969609).sum := by decide
  have hdescent : baseEnd_969609 < baseStart_969609 := by decide
  rcases family_descends (prefixWord ++ tailWord_969609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969639 : List Nat := [1, 1, 6, 1, 3, 1, 3, 6]
def baseStart_969639 : Nat := 118140960795 + 969639 * 2 ^ 59
def prefixEnd_969639 : Nat := 4983230072969 + 3 ^ 40 * 969639 * 2
def baseEnd_969639 : Nat := 36880805062595334566905

theorem tailTrace_969639 : CollatzResearch.WordTrace tailWord_969639 prefixEnd_969639 36880805062595334566905 := by
  unfold tailWord_969639
  simp only [CollatzResearch.WordTrace]
  refine ⟨35365639734170979002127971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23577093156113986001418647 35365639734170979002127971)
  ·
    refine ⟨53048459601256468503191957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35365639734170979002127971 53048459601256468503191957)
    ·
      refine ⟨2486646543808896961087123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53048459601256468503191957 2486646543808896961087123)
      ·
        refine ⟨3729969815713345441630685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2486646543808896961087123 3729969815713345441630685)
        ·
          refine ⟨1398738680892504540611507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3729969815713345441630685 1398738680892504540611507)
          ·
            refine ⟨2098108021338756810917261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1398738680892504540611507 2098108021338756810917261)
            ·
              refine ⟨786790508002033804093973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2098108021338756810917261 786790508002033804093973)
              ·
                refine ⟨36880805062595334566905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 786790508002033804093973 36880805062595334566905)
                ·
                  rfl

theorem cell22_969639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 6].length) (baseStart_969639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_969639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_969639 prefixEnd_969639 := by exact prefixLift 969639
  have htrace : WordTrace (prefixWord ++ tailWord_969639) baseStart_969639 baseEnd_969639 := by
    simpa [prefixWord, tailWord_969639, baseEnd_969639] using wordTrace_append hprefix tailTrace_969639
  have hstable : (prefixWord ++ tailWord_969639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969639).length < 2 ^ (prefixWord ++ tailWord_969639).sum := by decide
  have hdescent : baseEnd_969639 < baseStart_969639 := by decide
  rcases family_descends (prefixWord ++ tailWord_969639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969677 : List Nat := [1, 6, 3, 1, 1, 1, 3, 1, 2, 3]
def baseStart_969677 : Nat := 118140960795 + 969677 * 2 ^ 59
def prefixEnd_969677 : Nat := 4983230072969 + 3 ^ 40 * 969677 * 2
def baseEnd_969677 : Nat := 331940253739938578652029

theorem tailTrace_969677 : CollatzResearch.WordTrace tailWord_969677 prefixEnd_969677 331940253739938578652029 := by
  unfold tailWord_969677
  simp only [CollatzResearch.WordTrace]
  refine ⟨35367025708033311492011285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23578017138688874328007523 35367025708033311492011285)
  ·
    refine ⟨1657829330064061476188029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35367025708033311492011285 1657829330064061476188029)
    ·
      refine ⟨621685998774023053570511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1657829330064061476188029 621685998774023053570511)
      ·
        refine ⟨932528998161034580355767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621685998774023053570511 932528998161034580355767)
        ·
          refine ⟨1398793497241551870533651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 932528998161034580355767 1398793497241551870533651)
          ·
            refine ⟨2098190245862327805800477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1398793497241551870533651 2098190245862327805800477)
            ·
              refine ⟨786821342198372927175179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2098190245862327805800477 786821342198372927175179)
              ·
                refine ⟨1180232013297559390762769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 786821342198372927175179 1180232013297559390762769)
                ·
                  refine ⟨885174009973169543072077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1180232013297559390762769 885174009973169543072077)
                  ·
                    refine ⟨331940253739938578652029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 885174009973169543072077 331940253739938578652029)
                    ·
                      rfl

theorem cell22_969677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_969677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_969677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_969677 prefixEnd_969677 := by exact prefixLift 969677
  have htrace : WordTrace (prefixWord ++ tailWord_969677) baseStart_969677 baseEnd_969677 := by
    simpa [prefixWord, tailWord_969677, baseEnd_969677] using wordTrace_append hprefix tailTrace_969677
  have hstable : (prefixWord ++ tailWord_969677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969677).length < 2 ^ (prefixWord ++ tailWord_969677).sum := by decide
  have hdescent : baseEnd_969677 < baseStart_969677 := by decide
  rcases family_descends (prefixWord ++ tailWord_969677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969729 : List Nat := [1, 2, 4, 1, 2, 4, 1, 1, 6]
def baseStart_969729 : Nat := 118140960795 + 969729 * 2 ^ 59
def prefixEnd_969729 : Nat := 4983230072969 + 3 ^ 40 * 969729 * 2
def baseEnd_969729 : Nat := 110652684800875925450623

theorem tailTrace_969729 : CollatzResearch.WordTrace tailWord_969729 prefixEnd_969729 110652684800875925450623 := by
  unfold tailWord_969729
  simp only [CollatzResearch.WordTrace]
  refine ⟨35368922303844924372904241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23579281535896616248602827 35368922303844924372904241)
  ·
    refine ⟨26526691727883693279678181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35368922303844924372904241 26526691727883693279678181)
    ·
      refine ⟨4973754698978192489939659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26526691727883693279678181 4973754698978192489939659)
      ·
        refine ⟨7460632048467288734909489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4973754698978192489939659 7460632048467288734909489)
        ·
          refine ⟨5595474036350466551182117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7460632048467288734909489 5595474036350466551182117)
          ·
            refine ⟨1049151381815712478346647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5595474036350466551182117 1049151381815712478346647)
            ·
              refine ⟨1573727072723568717519971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1049151381815712478346647 1573727072723568717519971)
              ·
                refine ⟨2360590609085353076279957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1573727072723568717519971 2360590609085353076279957)
                ·
                  refine ⟨110652684800875925450623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2360590609085353076279957 110652684800875925450623)
                  ·
                    rfl

theorem cell22_969729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 6].length) (baseStart_969729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_969729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_969729 prefixEnd_969729 := by exact prefixLift 969729
  have htrace : WordTrace (prefixWord ++ tailWord_969729) baseStart_969729 baseEnd_969729 := by
    simpa [prefixWord, tailWord_969729, baseEnd_969729] using wordTrace_append hprefix tailTrace_969729
  have hstable : (prefixWord ++ tailWord_969729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969729).length < 2 ^ (prefixWord ++ tailWord_969729).sum := by decide
  have hdescent : baseEnd_969729 < baseStart_969729 := by decide
  rcases family_descends (prefixWord ++ tailWord_969729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969759 : List Nat := [1, 1, 2, 4, 1, 4, 2, 1, 2, 4]
def baseStart_969759 : Nat := 118140960795 + 969759 * 2 ^ 59
def prefixEnd_969759 : Nat := 4983230072969 + 3 ^ 40 * 969759 * 2
def baseEnd_969759 : Nat := 331968324015717698101777

theorem tailTrace_969759 : CollatzResearch.WordTrace tailWord_969759 prefixEnd_969759 331968324015717698101777 := by
  unfold tailWord_969759
  simp only [CollatzResearch.WordTrace]
  refine ⟨35370016493736239496496331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23580010995824159664330887 35370016493736239496496331)
  ·
    refine ⟨53055024740604359244744497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35370016493736239496496331 53055024740604359244744497)
    ·
      refine ⟨39791268555453269433558373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53055024740604359244744497 39791268555453269433558373)
      ·
        refine ⟨7460862854147488018792195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39791268555453269433558373 7460862854147488018792195)
        ·
          refine ⟨11191294281221232028188293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7460862854147488018792195 11191294281221232028188293)
          ·
            refine ⟨2098367677728981005285305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11191294281221232028188293 2098367677728981005285305)
            ·
              refine ⟨1573775758296735753963979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2098367677728981005285305 1573775758296735753963979)
              ·
                refine ⟨2360663637445103630945969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1573775758296735753963979 2360663637445103630945969)
                ·
                  refine ⟨1770497728083827723209477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2360663637445103630945969 1770497728083827723209477)
                  ·
                    refine ⟨331968324015717698101777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1770497728083827723209477 331968324015717698101777)
                    ·
                      rfl

theorem cell22_969759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 4].length) (baseStart_969759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_969759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_969759 prefixEnd_969759 := by exact prefixLift 969759
  have htrace : WordTrace (prefixWord ++ tailWord_969759) baseStart_969759 baseEnd_969759 := by
    simpa [prefixWord, tailWord_969759, baseEnd_969759] using wordTrace_append hprefix tailTrace_969759
  have hstable : (prefixWord ++ tailWord_969759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969759).length < 2 ^ (prefixWord ++ tailWord_969759).sum := by decide
  have hdescent : baseEnd_969759 < baseStart_969759 := by decide
  rcases family_descends (prefixWord ++ tailWord_969759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969780 : List Nat := [2, 5, 1, 2, 1, 3, 2, 2, 4]
def baseStart_969780 : Nat := 118140960795 + 969780 * 2 ^ 59
def prefixEnd_969780 : Nat := 4983230072969 + 3 ^ 40 * 969780 * 2
def baseEnd_969780 : Nat := 110658504248293547775571

theorem tailTrace_969780 : CollatzResearch.WordTrace tailWord_969780 prefixEnd_969780 110658504248293547775571 := by
  unfold tailWord_969780
  simp only [CollatzResearch.WordTrace]
  refine ⟨17685391213330080041505397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23580521617773440055340529 17685391213330080041505397)
  ·
    refine ⟨1658005426249695003891131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17685391213330080041505397 1658005426249695003891131)
    ·
      refine ⟨2487008139374542505836697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1658005426249695003891131 2487008139374542505836697)
      ·
        refine ⟨1865256104530906879377523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2487008139374542505836697 1865256104530906879377523)
        ·
          refine ⟨2797884156796360319066285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1865256104530906879377523 2797884156796360319066285)
          ·
            refine ⟨1049206558798635119649857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2797884156796360319066285 1049206558798635119649857)
            ·
              refine ⟨786904919098976339737393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1049206558798635119649857 786904919098976339737393)
              ·
                refine ⟨590178689324232254803045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 786904919098976339737393 590178689324232254803045)
                ·
                  refine ⟨110658504248293547775571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 590178689324232254803045 110658504248293547775571)
                  ·
                    rfl

theorem cell22_969780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_969780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_969780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_969780 prefixEnd_969780 := by exact prefixLift 969780
  have htrace : WordTrace (prefixWord ++ tailWord_969780) baseStart_969780 baseEnd_969780 := by
    simpa [prefixWord, tailWord_969780, baseEnd_969780] using wordTrace_append hprefix tailTrace_969780
  have hstable : (prefixWord ++ tailWord_969780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969780).length < 2 ^ (prefixWord ++ tailWord_969780).sum := by decide
  have hdescent : baseEnd_969780 < baseStart_969780 := by decide
  rcases family_descends (prefixWord ++ tailWord_969780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969834 : List Nat := [3, 1, 3, 2, 2, 1, 1, 2, 2, 5]
def baseStart_969834 : Nat := 118140960795 + 969834 * 2 ^ 59
def prefixEnd_969834 : Nat := 4983230072969 + 3 ^ 40 * 969834 * 2
def baseEnd_969834 : Nat := 331993998048442502476547

theorem tailTrace_969834 : CollatzResearch.WordTrace tailWord_969834 prefixEnd_969834 331993998048442502476547 := by
  unfold tailWord_969834
  simp only [CollatzResearch.WordTrace]
  refine ⟨8843187992116131826369139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23581834645643018203651037 8843187992116131826369139)
  ·
    refine ⟨13264781988174197739553709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8843187992116131826369139 13264781988174197739553709)
    ·
      refine ⟨4974293245565324152332641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13264781988174197739553709 4974293245565324152332641)
      ·
        refine ⟨3730719934173993114249481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4974293245565324152332641 3730719934173993114249481)
        ·
          refine ⟨2798039950630494835687111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3730719934173993114249481 2798039950630494835687111)
          ·
            refine ⟨4197059925945742253530667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2798039950630494835687111 4197059925945742253530667)
            ·
              refine ⟨6295589888918613380296001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4197059925945742253530667 6295589888918613380296001)
              ·
                refine ⟨4721692416688960035222001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6295589888918613380296001 4721692416688960035222001)
                ·
                  refine ⟨3541269312516720026416501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4721692416688960035222001 3541269312516720026416501)
                  ·
                    refine ⟨331993998048442502476547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3541269312516720026416501 331993998048442502476547)
                    ·
                      rfl

theorem cell22_969834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_969834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_969834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_969834 prefixEnd_969834 := by exact prefixLift 969834
  have htrace : WordTrace (prefixWord ++ tailWord_969834) baseStart_969834 baseEnd_969834 := by
    simpa [prefixWord, tailWord_969834, baseEnd_969834] using wordTrace_append hprefix tailTrace_969834
  have hstable : (prefixWord ++ tailWord_969834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969834).length < 2 ^ (prefixWord ++ tailWord_969834).sum := by decide
  have hdescent : baseEnd_969834 < baseStart_969834 := by decide
  rcases family_descends (prefixWord ++ tailWord_969834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969866 : List Nat := [3, 1, 2, 3, 1, 1, 4, 2, 1, 4]
def baseStart_969866 : Nat := 118140960795 + 969866 * 2 ^ 59
def prefixEnd_969866 : Nat := 4983230072969 + 3 ^ 40 * 969866 * 2
def baseEnd_969866 : Nat := 332004952302405085676449

theorem tailTrace_969866 : CollatzResearch.WordTrace tailWord_969866 prefixEnd_969866 332004952302405085676449 := by
  unfold tailWord_969866
  simp only [CollatzResearch.WordTrace]
  refine ⟨8843479776087149192660363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23582612736232397847094301 8843479776087149192660363)
  ·
    refine ⟨13265219664130723788990545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8843479776087149192660363 13265219664130723788990545)
    ·
      refine ⟨9948914748098042841742909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13265219664130723788990545 9948914748098042841742909)
      ·
        refine ⟨3730843030536766065653591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9948914748098042841742909 3730843030536766065653591)
        ·
          refine ⟨5596264545805149098480387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3730843030536766065653591 5596264545805149098480387)
          ·
            refine ⟨8394396818707723647720581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5596264545805149098480387 8394396818707723647720581)
            ·
              refine ⟨1573949403507698183947609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8394396818707723647720581 1573949403507698183947609)
              ·
                refine ⟨1180462052630773637960707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1573949403507698183947609 1180462052630773637960707)
                ·
                  refine ⟨1770693078946160456941061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1180462052630773637960707 1770693078946160456941061)
                  ·
                    refine ⟨332004952302405085676449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1770693078946160456941061 332004952302405085676449)
                    ·
                      rfl

theorem cell22_969866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_969866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_969866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_969866 prefixEnd_969866 := by exact prefixLift 969866
  have htrace : WordTrace (prefixWord ++ tailWord_969866) baseStart_969866 baseEnd_969866 := by
    simpa [prefixWord, tailWord_969866, baseEnd_969866] using wordTrace_append hprefix tailTrace_969866
  have hstable : (prefixWord ++ tailWord_969866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969866).length < 2 ^ (prefixWord ++ tailWord_969866).sum := by decide
  have hdescent : baseEnd_969866 < baseStart_969866 := by decide
  rcases family_descends (prefixWord ++ tailWord_969866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969898 : List Nat := [3, 1, 5, 1, 1, 3, 1, 1, 6]
def baseStart_969898 : Nat := 118140960795 + 969898 * 2 ^ 59
def prefixEnd_969898 : Nat := 4983230072969 + 3 ^ 40 * 969898 * 2
def baseEnd_969898 : Nat := 110671968852122556292117

theorem tailTrace_969898 : CollatzResearch.WordTrace tailWord_969898 prefixEnd_969898 110671968852122556292117 := by
  unfold tailWord_969898
  simp only [CollatzResearch.WordTrace]
  refine ⟨8843771560058166558951587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23583390826821777490537565 8843771560058166558951587)
  ·
    refine ⟨13265657340087249838427381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8843771560058166558951587 13265657340087249838427381)
    ·
      refine ⟨1243655375633179672352567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13265657340087249838427381 1243655375633179672352567)
      ·
        refine ⟨1865483063449769508528851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1243655375633179672352567 1865483063449769508528851)
        ·
          refine ⟨2798224595174654262793277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1865483063449769508528851 2798224595174654262793277)
          ·
            refine ⟨1049334223190495348547479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2798224595174654262793277 1049334223190495348547479)
            ·
              refine ⟨1574001334785743022821219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1049334223190495348547479 1574001334785743022821219)
              ·
                refine ⟨2361002002178614534231829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1574001334785743022821219 2361002002178614534231829)
                ·
                  refine ⟨110671968852122556292117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2361002002178614534231829 110671968852122556292117)
                  ·
                    rfl

theorem cell22_969898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 6].length) (baseStart_969898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_969898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_969898 prefixEnd_969898 := by exact prefixLift 969898
  have htrace : WordTrace (prefixWord ++ tailWord_969898) baseStart_969898 baseEnd_969898 := by
    simpa [prefixWord, tailWord_969898, baseEnd_969898] using wordTrace_append hprefix tailTrace_969898
  have hstable : (prefixWord ++ tailWord_969898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969898).length < 2 ^ (prefixWord ++ tailWord_969898).sum := by decide
  have hdescent : baseEnd_969898 < baseStart_969898 := by decide
  rcases family_descends (prefixWord ++ tailWord_969898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969913 : List Nat := [1, 2, 1, 4, 1, 3, 4, 1, 2, 3]
def baseStart_969913 : Nat := 118140960795 + 969913 * 2 ^ 59
def prefixEnd_969913 : Nat := 4983230072969 + 3 ^ 40 * 969913 * 2
def baseEnd_969913 : Nat := 332021041362912629751305

theorem tailTrace_969913 : CollatzResearch.WordTrace tailWord_969913 prefixEnd_969913 332021041362912629751305 := by
  unfold tailWord_969913
  simp only [CollatzResearch.WordTrace]
  refine ⟨35375633335178323797602393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23583755556785549198401595 35375633335178323797602393)
  ·
    refine ⟨26531725001383742848201795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35375633335178323797602393 26531725001383742848201795)
    ·
      refine ⟨39797587502075614272302693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26531725001383742848201795 39797587502075614272302693)
      ·
        refine ⟨7462047656639177676056755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39797587502075614272302693 7462047656639177676056755)
        ·
          refine ⟨11193071484958766514085133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7462047656639177676056755 11193071484958766514085133)
          ·
            refine ⟨4197401806859537442781925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11193071484958766514085133 4197401806859537442781925)
            ·
              refine ⟨787012838786163270521611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4197401806859537442781925 787012838786163270521611)
              ·
                refine ⟨1180519258179244905782417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 787012838786163270521611 1180519258179244905782417)
                ·
                  refine ⟨885389443634433679336813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1180519258179244905782417 885389443634433679336813)
                  ·
                    refine ⟨332021041362912629751305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 885389443634433679336813 332021041362912629751305)
                    ·
                      rfl

theorem cell22_969913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 2, 3].length) (baseStart_969913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_969913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_969913 prefixEnd_969913 := by exact prefixLift 969913
  have htrace : WordTrace (prefixWord ++ tailWord_969913) baseStart_969913 baseEnd_969913 := by
    simpa [prefixWord, tailWord_969913, baseEnd_969913] using wordTrace_append hprefix tailTrace_969913
  have hstable : (prefixWord ++ tailWord_969913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969913).length < 2 ^ (prefixWord ++ tailWord_969913).sum := by decide
  have hdescent : baseEnd_969913 < baseStart_969913 := by decide
  rcases family_descends (prefixWord ++ tailWord_969913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970001 : List Nat := [1, 2, 2, 1, 1, 4, 3, 3, 1, 4]
def baseStart_970001 : Nat := 118140960795 + 970001 * 2 ^ 59
def prefixEnd_970001 : Nat := 4983230072969 + 3 ^ 40 * 970001 * 2
def baseEnd_970001 : Nat := 332051165561309733551035

theorem tailTrace_970001 : CollatzResearch.WordTrace tailWord_970001 prefixEnd_970001 332051165561309733551035 := by
  unfold tailWord_970001
  simp only [CollatzResearch.WordTrace]
  refine ⟨35378842958859514826805857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23585895305906343217870571 35378842958859514826805857)
  ·
    refine ⟨26534132219144636120104393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35378842958859514826805857 26534132219144636120104393)
    ·
      refine ⟨19900599164358477090078295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26534132219144636120104393 19900599164358477090078295)
      ·
        refine ⟨29850898746537715635117443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19900599164358477090078295 29850898746537715635117443)
        ·
          refine ⟨44776348119806573452676165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29850898746537715635117443 44776348119806573452676165)
          ·
            refine ⟨8395565272463732522376781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44776348119806573452676165 8395565272463732522376781)
            ·
              refine ⟨3148336977173899695891293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8395565272463732522376781 3148336977173899695891293)
              ·
                refine ⟨1180626366440212385959235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3148336977173899695891293 1180626366440212385959235)
                ·
                  refine ⟨1770939549660318578938853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1180626366440212385959235 1770939549660318578938853)
                  ·
                    refine ⟨332051165561309733551035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1770939549660318578938853 332051165561309733551035)
                    ·
                      rfl

theorem cell22_970001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_970001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970001 prefixEnd_970001 := by exact prefixLift 970001
  have htrace : WordTrace (prefixWord ++ tailWord_970001) baseStart_970001 baseEnd_970001 := by
    simpa [prefixWord, tailWord_970001, baseEnd_970001] using wordTrace_append hprefix tailTrace_970001
  have hstable : (prefixWord ++ tailWord_970001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970001).length < 2 ^ (prefixWord ++ tailWord_970001).sum := by decide
  have hdescent : baseEnd_970001 < baseStart_970001 := by decide
  rcases family_descends (prefixWord ++ tailWord_970001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970046 : List Nat := [4, 2, 1, 2, 1, 1, 1, 3, 1, 6]
def baseStart_970046 : Nat := 118140960795 + 970046 * 2 ^ 59
def prefixEnd_970046 : Nat := 4983230072969 + 3 ^ 40 * 970046 * 2
def baseEnd_970046 : Nat := 332066569980944616175897

theorem tailTrace_970046 : CollatzResearch.WordTrace tailWord_970046 prefixEnd_970046 332066569980944616175897 := by
  unfold tailWord_970046
  simp only [CollatzResearch.WordTrace]
  refine ⟨4422560530462060939024249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23586989495797658341462661 4422560530462060939024249)
  ·
    refine ⟨3316920397846545704268187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4422560530462060939024249 3316920397846545704268187)
    ·
      refine ⟨4975380596769818556402281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3316920397846545704268187 4975380596769818556402281)
      ·
        refine ⟨3731535447577363917301711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4975380596769818556402281 3731535447577363917301711)
        ·
          refine ⟨5597303171366045875952567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3731535447577363917301711 5597303171366045875952567)
          ·
            refine ⟨8395954757049068813928851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5597303171366045875952567 8395954757049068813928851)
            ·
              refine ⟨12593932135573603220893277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8395954757049068813928851 12593932135573603220893277)
              ·
                refine ⟨4722724550840101207834979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12593932135573603220893277 4722724550840101207834979)
                ·
                  refine ⟨7084086826260151811752469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4722724550840101207834979 7084086826260151811752469)
                  ·
                    refine ⟨332066569980944616175897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7084086826260151811752469 332066569980944616175897)
                    ·
                      rfl

theorem cell22_970046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_970046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970046 prefixEnd_970046 := by exact prefixLift 970046
  have htrace : WordTrace (prefixWord ++ tailWord_970046) baseStart_970046 baseEnd_970046 := by
    simpa [prefixWord, tailWord_970046, baseEnd_970046] using wordTrace_append hprefix tailTrace_970046
  have hstable : (prefixWord ++ tailWord_970046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970046).length < 2 ^ (prefixWord ++ tailWord_970046).sum := by decide
  have hdescent : baseEnd_970046 < baseStart_970046 := by decide
  rcases family_descends (prefixWord ++ tailWord_970046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970089 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 9]
def baseStart_970089 : Nat := 118140960795 + 970089 * 2 ^ 59
def prefixEnd_970089 : Nat := 4983230072969 + 3 ^ 40 * 970089 * 2
def baseEnd_970089 : Nat := 110693763253235612450255

theorem tailTrace_970089 : CollatzResearch.WordTrace tailWord_970089 prefixEnd_970089 110693763253235612450255 := by
  unfold tailWord_970089
  simp only [CollatzResearch.WordTrace]
  refine ⟨35382052582540705856009321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23588035055027137237339547 35382052582540705856009321)
  ·
    refine ⟨26536539436905529392006991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35382052582540705856009321 26536539436905529392006991)
    ·
      refine ⟨39804809155358294088010487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26536539436905529392006991 39804809155358294088010487)
      ·
        refine ⟨59707213733037441132015731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39804809155358294088010487 59707213733037441132015731)
        ·
          refine ⟨89560820599556161698023597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59707213733037441132015731 89560820599556161698023597)
          ·
            refine ⟨33585307724833560636758849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89560820599556161698023597 33585307724833560636758849)
            ·
              refine ⟨25188980793625170477569137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33585307724833560636758849 25188980793625170477569137)
              ·
                refine ⟨18891735595218877858176853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25188980793625170477569137 18891735595218877858176853)
                ·
                  refine ⟨110693763253235612450255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18891735595218877858176853 110693763253235612450255)
                  ·
                    rfl

theorem cell22_970089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 9].length) (baseStart_970089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970089 prefixEnd_970089 := by exact prefixLift 970089
  have htrace : WordTrace (prefixWord ++ tailWord_970089) baseStart_970089 baseEnd_970089 := by
    simpa [prefixWord, tailWord_970089, baseEnd_970089] using wordTrace_append hprefix tailTrace_970089
  have hstable : (prefixWord ++ tailWord_970089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970089).length < 2 ^ (prefixWord ++ tailWord_970089).sum := by decide
  have hdescent : baseEnd_970089 < baseStart_970089 := by decide
  rcases family_descends (prefixWord ++ tailWord_970089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970168 : List Nat := [2, 1, 2, 1, 2, 2, 3, 5, 4]
def baseStart_970168 : Nat := 118140960795 + 970168 * 2 ^ 59
def prefixEnd_970168 : Nat := 4983230072969 + 3 ^ 40 * 970168 * 2
def baseEnd_970168 : Nat := 110702777691392321541841

theorem tailTrace_970168 : CollatzResearch.WordTrace tailWord_970168 prefixEnd_970168 110702777691392321541841 := by
  unfold tailWord_970168
  simp only [CollatzResearch.WordTrace]
  refine ⟨17692466974627251174067579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23589955966169668232090105 17692466974627251174067579)
  ·
    refine ⟨26538700461940876761101369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17692466974627251174067579 26538700461940876761101369)
    ·
      refine ⟨19904025346455657570826027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26538700461940876761101369 19904025346455657570826027)
      ·
        refine ⟨29856038019683486356239041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19904025346455657570826027 29856038019683486356239041)
        ·
          refine ⟨22392028514762614767179281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29856038019683486356239041 22392028514762614767179281)
          ·
            refine ⟨16794021386071961075384461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22392028514762614767179281 16794021386071961075384461)
            ·
              refine ⟨6297758019776985403269173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16794021386071961075384461 6297758019776985403269173)
              ·
                refine ⟨590414814354092381556485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6297758019776985403269173 590414814354092381556485)
                ·
                  refine ⟨110702777691392321541841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 590414814354092381556485 110702777691392321541841)
                  ·
                    rfl

theorem cell22_970168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 5, 4].length) (baseStart_970168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970168 prefixEnd_970168 := by exact prefixLift 970168
  have htrace : WordTrace (prefixWord ++ tailWord_970168) baseStart_970168 baseEnd_970168 := by
    simpa [prefixWord, tailWord_970168, baseEnd_970168] using wordTrace_append hprefix tailTrace_970168
  have hstable : (prefixWord ++ tailWord_970168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970168).length < 2 ^ (prefixWord ++ tailWord_970168).sum := by decide
  have hdescent : baseEnd_970168 < baseStart_970168 := by decide
  rcases family_descends (prefixWord ++ tailWord_970168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970183 : List Nat := [1, 1, 4, 1, 1, 3, 3, 1, 4, 3]
def baseStart_970183 : Nat := 118140960795 + 970183 * 2 ^ 59
def prefixEnd_970183 : Nat := 4983230072969 + 3 ^ 40 * 970183 * 2
def baseEnd_970183 : Nat := 332113467880721925500477

theorem tailTrace_970183 : CollatzResearch.WordTrace tailWord_970183 prefixEnd_970183 332113467880721925500477 := by
  unfold tailWord_970183
  simp only [CollatzResearch.WordTrace]
  refine ⟨35385481044200159909931203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23590320696133439939954135 35385481044200159909931203)
  ·
    refine ⟨53078221566300239864896805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35385481044200159909931203 53078221566300239864896805)
    ·
      refine ⟨9952166543681294974668151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53078221566300239864896805 9952166543681294974668151)
      ·
        refine ⟨14928249815521942462002227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9952166543681294974668151 14928249815521942462002227)
        ·
          refine ⟨22392374723282913693003341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14928249815521942462002227 22392374723282913693003341)
          ·
            refine ⟨8397140521231092634876253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22392374723282913693003341 8397140521231092634876253)
            ·
              refine ⟨3148927695461659738078595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8397140521231092634876253 3148927695461659738078595)
              ·
                refine ⟨4723391543192489607117893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3148927695461659738078595 4723391543192489607117893)
                ·
                  refine ⟨885635914348591801334605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4723391543192489607117893 885635914348591801334605)
                  ·
                    refine ⟨332113467880721925500477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 885635914348591801334605 332113467880721925500477)
                    ·
                      rfl

theorem cell22_970183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_970183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970183 prefixEnd_970183 := by exact prefixLift 970183
  have htrace : WordTrace (prefixWord ++ tailWord_970183) baseStart_970183 baseEnd_970183 := by
    simpa [prefixWord, tailWord_970183, baseEnd_970183] using wordTrace_append hprefix tailTrace_970183
  have hstable : (prefixWord ++ tailWord_970183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970183).length < 2 ^ (prefixWord ++ tailWord_970183).sum := by decide
  have hdescent : baseEnd_970183 < baseStart_970183 := by decide
  rcases family_descends (prefixWord ++ tailWord_970183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970213 : List Nat := [1, 3, 1, 5, 1, 2, 1, 8]
def baseStart_970213 : Nat := 118140960795 + 970213 * 2 ^ 59
def prefixEnd_970213 : Nat := 4983230072969 + 3 ^ 40 * 970213 * 2
def baseEnd_970213 : Nat := 36902637499312427472265

theorem tailTrace_970213 : CollatzResearch.WordTrace tailWord_970213 prefixEnd_970213 36902637499312427472265 := by
  unfold tailWord_970213
  simp only [CollatzResearch.WordTrace]
  refine ⟨35386575234091475033523293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23591050156060983355682195 35386575234091475033523293)
  ·
    refine ⟨13269965712784303137571235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35386575234091475033523293 13269965712784303137571235)
    ·
      refine ⟨19904948569176454706356853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13269965712784303137571235 19904948569176454706356853)
      ·
        refine ⟨1866088928360292628720955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19904948569176454706356853 1866088928360292628720955)
        ·
          refine ⟨2799133392540438943081433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1866088928360292628720955 2799133392540438943081433)
          ·
            refine ⟨2099350044405329207311075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2799133392540438943081433 2099350044405329207311075)
            ·
              refine ⟨3149025066607993810966613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2099350044405329207311075 3149025066607993810966613)
              ·
                refine ⟨36902637499312427472265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3149025066607993810966613 36902637499312427472265)
                ·
                  rfl

theorem cell22_970213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 8].length) (baseStart_970213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970213 prefixEnd_970213 := by exact prefixLift 970213
  have htrace : WordTrace (prefixWord ++ tailWord_970213) baseStart_970213 baseEnd_970213 := by
    simpa [prefixWord, tailWord_970213, baseEnd_970213] using wordTrace_append hprefix tailTrace_970213
  have hstable : (prefixWord ++ tailWord_970213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970213).length < 2 ^ (prefixWord ++ tailWord_970213).sum := by decide
  have hdescent : baseEnd_970213 < baseStart_970213 := by decide
  rcases family_descends (prefixWord ++ tailWord_970213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970352 : List Nat := [2, 1, 1, 1, 6, 1, 3, 2, 2, 3]
def baseStart_970352 : Nat := 118140960795 + 970352 * 2 ^ 59
def prefixEnd_970352 : Nat := 4983230072969 + 3 ^ 40 * 970352 * 2
def baseEnd_970352 : Nat := 332171320034461818024959

theorem tailTrace_970352 : CollatzResearch.WordTrace tailWord_970352 prefixEnd_970352 332171320034461818024959 := by
  unfold tailWord_970352
  simp only [CollatzResearch.WordTrace]
  refine ⟨17695822490293950886416655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23594429987058601181888873 17695822490293950886416655)
  ·
    refine ⟨26543733735440926329624983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17695822490293950886416655 26543733735440926329624983)
    ·
      refine ⟨39815600603161389494437475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26543733735440926329624983 39815600603161389494437475)
      ·
        refine ⟨59723400904742084241656213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39815600603161389494437475 59723400904742084241656213)
        ·
          refine ⟨2799534417409785198827635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 59723400904742084241656213 2799534417409785198827635)
          ·
            refine ⟨4199301626114677798241453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2799534417409785198827635 4199301626114677798241453)
            ·
              refine ⟨1574738109793004174340545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4199301626114677798241453 1574738109793004174340545)
              ·
                refine ⟨1181053582344753130755409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1574738109793004174340545 1181053582344753130755409)
                ·
                  refine ⟨885790186758564848066557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1181053582344753130755409 885790186758564848066557)
                  ·
                    refine ⟨332171320034461818024959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 885790186758564848066557 332171320034461818024959)
                    ·
                      rfl

theorem cell22_970352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 2, 3].length) (baseStart_970352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970352 prefixEnd_970352 := by exact prefixLift 970352
  have htrace : WordTrace (prefixWord ++ tailWord_970352) baseStart_970352 baseEnd_970352 := by
    simpa [prefixWord, tailWord_970352, baseEnd_970352] using wordTrace_append hprefix tailTrace_970352
  have hstable : (prefixWord ++ tailWord_970352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970352).length < 2 ^ (prefixWord ++ tailWord_970352).sum := by decide
  have hdescent : baseEnd_970352 < baseStart_970352 := by decide
  rcases family_descends (prefixWord ++ tailWord_970352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970369 : List Nat := [1, 2, 4, 2, 1, 3, 3, 1, 2, 3]
def baseStart_970369 : Nat := 118140960795 + 970369 * 2 ^ 59
def prefixEnd_970369 : Nat := 4983230072969 + 3 ^ 40 * 970369 * 2
def baseEnd_970369 : Nat := 332177139481879440349907

theorem tailTrace_970369 : CollatzResearch.WordTrace tailWord_970369 prefixEnd_970369 332177139481879440349907 := by
  unfold tailWord_970369
  simp only [CollatzResearch.WordTrace]
  refine ⟨35392265021526313676202161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23594843347684209117468107 35392265021526313676202161)
  ·
    refine ⟨26544198766144735257151621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35392265021526313676202161 26544198766144735257151621)
    ·
      refine ⟨4977037268652137860715929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26544198766144735257151621 4977037268652137860715929)
      ·
        refine ⟨3732777951489103395536947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4977037268652137860715929 3732777951489103395536947)
        ·
          refine ⟨5599166927233655093305421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3732777951489103395536947 5599166927233655093305421)
          ·
            refine ⟨2099687597712620659989533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5599166927233655093305421 2099687597712620659989533)
            ·
              refine ⟨787382849142232747496075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2099687597712620659989533 787382849142232747496075)
              ·
                refine ⟨1181074273713349121244113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 787382849142232747496075 1181074273713349121244113)
                ·
                  refine ⟨885805705285011840933085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1181074273713349121244113 885805705285011840933085)
                  ·
                    refine ⟨332177139481879440349907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 885805705285011840933085 332177139481879440349907)
                    ·
                      rfl

theorem cell22_970369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_970369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970369 prefixEnd_970369 := by exact prefixLift 970369
  have htrace : WordTrace (prefixWord ++ tailWord_970369) baseStart_970369 baseEnd_970369 := by
    simpa [prefixWord, tailWord_970369, baseEnd_970369] using wordTrace_append hprefix tailTrace_970369
  have hstable : (prefixWord ++ tailWord_970369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970369).length < 2 ^ (prefixWord ++ tailWord_970369).sum := by decide
  have hdescent : baseEnd_970369 < baseStart_970369 := by decide
  rcases family_descends (prefixWord ++ tailWord_970369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970380 : List Nat := [2, 2, 1, 2, 1, 1, 3, 4, 3, 3]
def baseStart_970380 : Nat := 118140960795 + 970380 * 2 ^ 59
def prefixEnd_970380 : Nat := 4983230072969 + 3 ^ 40 * 970380 * 2
def baseEnd_970380 : Nat := 332180905006679078324873

theorem tailTrace_970380 : CollatzResearch.WordTrace tailWord_970380 prefixEnd_970380 332180905006679078324873 := by
  unfold tailWord_970380
  simp only [CollatzResearch.WordTrace]
  refine ⟨17696333112243231277426297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23595110816324308369901729 17696333112243231277426297)
  ·
    refine ⟨13272249834182423458069723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17696333112243231277426297 13272249834182423458069723)
    ·
      refine ⟨19908374751273635187104585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13272249834182423458069723 19908374751273635187104585)
      ·
        refine ⟨14931281063455226390328439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19908374751273635187104585 14931281063455226390328439)
        ·
          refine ⟨22396921595182839585492659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14931281063455226390328439 22396921595182839585492659)
          ·
            refine ⟨33595382392774259378238989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22396921595182839585492659 33595382392774259378238989)
            ·
              refine ⟨12598268397290347266839621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33595382392774259378238989 12598268397290347266839621)
              ·
                refine ⟨2362175324491940112532429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12598268397290347266839621 2362175324491940112532429)
                ·
                  refine ⟨885815746684477542199661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2362175324491940112532429 885815746684477542199661)
                  ·
                    refine ⟨332180905006679078324873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 885815746684477542199661 332180905006679078324873)
                    ·
                      rfl

theorem cell22_970380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 3, 3].length) (baseStart_970380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970380 prefixEnd_970380 := by exact prefixLift 970380
  have htrace : WordTrace (prefixWord ++ tailWord_970380) baseStart_970380 baseEnd_970380 := by
    simpa [prefixWord, tailWord_970380, baseEnd_970380] using wordTrace_append hprefix tailTrace_970380
  have hstable : (prefixWord ++ tailWord_970380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970380).length < 2 ^ (prefixWord ++ tailWord_970380).sum := by decide
  have hdescent : baseEnd_970380 < baseStart_970380 := by decide
  rcases family_descends (prefixWord ++ tailWord_970380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970382 : List Nat := [4, 1, 1, 3, 1, 4, 2, 6]
def baseStart_970382 : Nat := 118140960795 + 970382 * 2 ^ 59
def prefixEnd_970382 : Nat := 4983230072969 + 3 ^ 40 * 970382 * 2
def baseEnd_970382 : Nat := 36909065516394637752763

theorem tailTrace_970382 : CollatzResearch.WordTrace tailWord_970382 prefixEnd_970382 36909065516394637752763 := by
  unfold tailWord_970382
  simp only [CollatzResearch.WordTrace]
  refine ⟨4424092396309902112053175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23595159446986144597616933 4424092396309902112053175)
  ·
    refine ⟨6636138594464853168079763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4424092396309902112053175 6636138594464853168079763)
    ·
      refine ⟨9954207891697279752119645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6636138594464853168079763 9954207891697279752119645)
      ·
        refine ⟨3732827959386479907044867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9954207891697279752119645 3732827959386479907044867)
        ·
          refine ⟨5599241939079719860567301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3732827959386479907044867 5599241939079719860567301)
          ·
            refine ⟨1049857863577447473856369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5599241939079719860567301 1049857863577447473856369)
            ·
              refine ⟨787393397683085605392277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1049857863577447473856369 787393397683085605392277)
              ·
                refine ⟨36909065516394637752763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 787393397683085605392277 36909065516394637752763)
                ·
                  rfl

theorem cell22_970382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 6].length) (baseStart_970382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970382 prefixEnd_970382 := by exact prefixLift 970382
  have htrace : WordTrace (prefixWord ++ tailWord_970382) baseStart_970382 baseEnd_970382 := by
    simpa [prefixWord, tailWord_970382, baseEnd_970382] using wordTrace_append hprefix tailTrace_970382
  have hstable : (prefixWord ++ tailWord_970382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970382).length < 2 ^ (prefixWord ++ tailWord_970382).sum := by decide
  have hdescent : baseEnd_970382 < baseStart_970382 := by decide
  rcases family_descends (prefixWord ++ tailWord_970382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970440 : List Nat := [2, 1, 3, 1, 2, 2, 3, 1, 3, 4]
def baseStart_970440 : Nat := 118140960795 + 970440 * 2 ^ 59
def prefixEnd_970440 : Nat := 4983230072969 + 3 ^ 40 * 970440 * 2
def baseEnd_970440 : Nat := 332201444232858921824689

theorem tailTrace_970440 : CollatzResearch.WordTrace tailWord_970440 prefixEnd_970440 332201444232858921824689 := by
  unfold tailWord_970440
  simp only [CollatzResearch.WordTrace]
  refine ⟨17697427302134546401018387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23596569736179395201357849 17697427302134546401018387)
  ·
    refine ⟨26546140953201819601527581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17697427302134546401018387 26546140953201819601527581)
    ·
      refine ⟨9954802857450682350572843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26546140953201819601527581 9954802857450682350572843)
      ·
        refine ⟨14932204286176023525859265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9954802857450682350572843 14932204286176023525859265)
        ·
          refine ⟨11199153214632017644394449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14932204286176023525859265 11199153214632017644394449)
          ·
            refine ⟨8399364910974013233295837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11199153214632017644394449 8399364910974013233295837)
            ·
              refine ⟨3149761841615254962485939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8399364910974013233295837 3149761841615254962485939)
              ·
                refine ⟨4724642762422882443728909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3149761841615254962485939 4724642762422882443728909)
                ·
                  refine ⟨1771741035908580916398341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4724642762422882443728909 1771741035908580916398341)
                  ·
                    refine ⟨332201444232858921824689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1771741035908580916398341 332201444232858921824689)
                    ·
                      rfl

theorem cell22_970440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_970440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970440 prefixEnd_970440 := by exact prefixLift 970440
  have htrace : WordTrace (prefixWord ++ tailWord_970440) baseStart_970440 baseEnd_970440 := by
    simpa [prefixWord, tailWord_970440, baseEnd_970440] using wordTrace_append hprefix tailTrace_970440
  have hstable : (prefixWord ++ tailWord_970440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970440).length < 2 ^ (prefixWord ++ tailWord_970440).sum := by decide
  have hdescent : baseEnd_970440 < baseStart_970440 := by decide
  rcases family_descends (prefixWord ++ tailWord_970440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970487 : List Nat := [1, 1, 3, 1, 1, 1, 6, 3, 2, 3]
def baseStart_970487 : Nat := 118140960795 + 970487 * 2 ^ 59
def prefixEnd_970487 : Nat := 4983230072969 + 3 ^ 40 * 970487 * 2
def baseEnd_970487 : Nat := 332217533293366465899545

theorem tailTrace_970487 : CollatzResearch.WordTrace tailWord_970487 prefixEnd_970487 332217533293366465899545 := by
  unfold tailWord_970487
  simp only [CollatzResearch.WordTrace]
  refine ⟨35396568835098819828997715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23597712556732546552665143 35396568835098819828997715)
  ·
    refine ⟨53094853252648229743496573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35396568835098819828997715 53094853252648229743496573)
    ·
      refine ⟨19910569969743086153811215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53094853252648229743496573 19910569969743086153811215)
      ·
        refine ⟨29865854954614629230716823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19910569969743086153811215 29865854954614629230716823)
        ·
          refine ⟨44798782431921943846075235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29865854954614629230716823 44798782431921943846075235)
          ·
            refine ⟨67198173647882915769112853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44798782431921943846075235 67198173647882915769112853)
            ·
              refine ⟨3149914389744511676677165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67198173647882915769112853 3149914389744511676677165)
              ·
                refine ⟨1181217896154191878753937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3149914389744511676677165 1181217896154191878753937)
                ·
                  refine ⟨885913422115643909065453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1181217896154191878753937 885913422115643909065453)
                  ·
                    refine ⟨332217533293366465899545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 885913422115643909065453 332217533293366465899545)
                    ·
                      rfl

theorem cell22_970487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 2, 3].length) (baseStart_970487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970487 prefixEnd_970487 := by exact prefixLift 970487
  have htrace : WordTrace (prefixWord ++ tailWord_970487) baseStart_970487 baseEnd_970487 := by
    simpa [prefixWord, tailWord_970487, baseEnd_970487] using wordTrace_append hprefix tailTrace_970487
  have hstable : (prefixWord ++ tailWord_970487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970487).length < 2 ^ (prefixWord ++ tailWord_970487).sum := by decide
  have hdescent : baseEnd_970487 < baseStart_970487 := by decide
  rcases family_descends (prefixWord ++ tailWord_970487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970583 : List Nat := [1, 1, 3, 2, 5, 1, 3, 2, 1, 3]
def baseStart_970583 : Nat := 118140960795 + 970583 * 2 ^ 59
def prefixEnd_970583 : Nat := 4983230072969 + 3 ^ 40 * 970583 * 2
def baseEnd_970583 : Nat := 332250396055254215499251

theorem tailTrace_970583 : CollatzResearch.WordTrace tailWord_970583 prefixEnd_970583 332250396055254215499251 := by
  unfold tailWord_970583
  simp only [CollatzResearch.WordTrace]
  refine ⟨35400070242751028224492403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23600046828500685482994935 35400070242751028224492403)
  ·
    refine ⟨53100105364126542336738605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35400070242751028224492403 53100105364126542336738605)
    ·
      refine ⟨19912539511547453376276977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53100105364126542336738605 19912539511547453376276977)
      ·
        refine ⟨14934404633660590032207733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19912539511547453376276977 14934404633660590032207733)
        ·
          refine ⟨1400100434405680315519475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14934404633660590032207733 1400100434405680315519475)
          ·
            refine ⟨2100150651608520473279213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1400100434405680315519475 2100150651608520473279213)
            ·
              refine ⟨787556494353195177479705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2100150651608520473279213 787556494353195177479705)
              ·
                refine ⟨590667370764896383109779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 787556494353195177479705 590667370764896383109779)
                ·
                  refine ⟨886001056147344574664669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 590667370764896383109779 886001056147344574664669)
                  ·
                    refine ⟨332250396055254215499251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 886001056147344574664669 332250396055254215499251)
                    ·
                      rfl

theorem cell22_970583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 2, 1, 3].length) (baseStart_970583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970583 prefixEnd_970583 := by exact prefixLift 970583
  have htrace : WordTrace (prefixWord ++ tailWord_970583) baseStart_970583 baseEnd_970583 := by
    simpa [prefixWord, tailWord_970583, baseEnd_970583] using wordTrace_append hprefix tailTrace_970583
  have hstable : (prefixWord ++ tailWord_970583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970583).length < 2 ^ (prefixWord ++ tailWord_970583).sum := by decide
  have hdescent : baseEnd_970583 < baseStart_970583 := by decide
  rcases family_descends (prefixWord ++ tailWord_970583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970596 : List Nat := [2, 3, 1, 1, 5, 2, 2, 1, 5]
def baseStart_970596 : Nat := 118140960795 + 970596 * 2 ^ 59
def prefixEnd_970596 : Nat := 4983230072969 + 3 ^ 40 * 970596 * 2
def baseEnd_970596 : Nat := 110751615406975504974737

theorem tailTrace_970596 : CollatzResearch.WordTrace tailWord_970596 prefixEnd_970596 110751615406975504974737 := by
  unfold tailWord_970596
  simp only [CollatzResearch.WordTrace]
  refine ⟨17700272195851965722357821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23600362927802620963143761 17700272195851965722357821)
  ·
    refine ⟨6637602073444487145884183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17700272195851965722357821 6637602073444487145884183)
    ·
      refine ⟨9956403110166730718826275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6637602073444487145884183 9956403110166730718826275)
      ·
        refine ⟨14934604665250096078239413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9956403110166730718826275 14934604665250096078239413)
        ·
          refine ⟨1400119187367196507334945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14934604665250096078239413 1400119187367196507334945)
          ·
            refine ⟨1050089390525397380501209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1400119187367196507334945 1050089390525397380501209)
            ·
              refine ⟨787567042894048035375907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1050089390525397380501209 787567042894048035375907)
              ·
                refine ⟨1181350564341072053063861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 787567042894048035375907 1181350564341072053063861)
                ·
                  refine ⟨110751615406975504974737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1181350564341072053063861 110751615406975504974737)
                  ·
                    rfl

theorem cell22_970596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_970596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970596 prefixEnd_970596 := by exact prefixLift 970596
  have htrace : WordTrace (prefixWord ++ tailWord_970596) baseStart_970596 baseEnd_970596 := by
    simpa [prefixWord, tailWord_970596, baseEnd_970596] using wordTrace_append hprefix tailTrace_970596
  have hstable : (prefixWord ++ tailWord_970596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970596).length < 2 ^ (prefixWord ++ tailWord_970596).sum := by decide
  have hdescent : baseEnd_970596 < baseStart_970596 := by decide
  rcases family_descends (prefixWord ++ tailWord_970596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970712 : List Nat := [2, 1, 2, 2, 2, 2, 1, 3, 2, 5]
def baseStart_970712 : Nat := 118140960795 + 970712 * 2 ^ 59
def prefixEnd_970712 : Nat := 4983230072969 + 3 ^ 40 * 970712 * 2
def baseEnd_970712 : Nat := 332294555391540879023855

theorem tailTrace_970712 : CollatzResearch.WordTrace tailWord_970712 prefixEnd_970712 332294555391540879023855 := by
  unfold tailWord_970712
  simp only [CollatzResearch.WordTrace]
  refine ⟨17702387629641841627969195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23603183506189122170625593 17702387629641841627969195)
  ·
    refine ⟨26553581444462762441953793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17702387629641841627969195 26553581444462762441953793)
    ·
      refine ⟨19915186083347071831465345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26553581444462762441953793 19915186083347071831465345)
      ·
        refine ⟨14936389562510303873599009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19915186083347071831465345 14936389562510303873599009)
        ·
          refine ⟨11202292171882727905199257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14936389562510303873599009 11202292171882727905199257)
          ·
            refine ⟨8401719128912045928899443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11202292171882727905199257 8401719128912045928899443)
            ·
              refine ⟨12602578693368068893349165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8401719128912045928899443 12602578693368068893349165)
              ·
                refine ⟨4725967010013025835005937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12602578693368068893349165 4725967010013025835005937)
                ·
                  refine ⟨3544475257509769376254453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4725967010013025835005937 3544475257509769376254453)
                  ·
                    refine ⟨332294555391540879023855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3544475257509769376254453 332294555391540879023855)
                    ·
                      rfl

theorem cell22_970712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_970712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970712 prefixEnd_970712 := by exact prefixLift 970712
  have htrace : WordTrace (prefixWord ++ tailWord_970712) baseStart_970712 baseEnd_970712 := by
    simpa [prefixWord, tailWord_970712, baseEnd_970712] using wordTrace_append hprefix tailTrace_970712
  have hstable : (prefixWord ++ tailWord_970712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970712).length < 2 ^ (prefixWord ++ tailWord_970712).sum := by decide
  have hdescent : baseEnd_970712 < baseStart_970712 := by decide
  rcases family_descends (prefixWord ++ tailWord_970712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970744 : List Nat := [2, 1, 2, 1, 1, 3, 4, 3, 1, 4]
def baseStart_970744 : Nat := 118140960795 + 970744 * 2 ^ 59
def prefixEnd_970744 : Nat := 4983230072969 + 3 ^ 40 * 970744 * 2
def baseEnd_970744 : Nat := 332305509645503462223757

theorem tailTrace_970744 : CollatzResearch.WordTrace tailWord_970744 prefixEnd_970744 332305509645503462223757 := by
  unfold tailWord_970744
  simp only [CollatzResearch.WordTrace]
  refine ⟨17702971197583876360551643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23603961596778501814068857 17702971197583876360551643)
  ·
    refine ⟨26554456796375814540827465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17702971197583876360551643 26554456796375814540827465)
    ·
      refine ⟨19915842597281860905620599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26554456796375814540827465 19915842597281860905620599)
      ·
        refine ⟨29873763895922791358430899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19915842597281860905620599 29873763895922791358430899)
        ·
          refine ⟨44810645843884187037646349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29873763895922791358430899 44810645843884187037646349)
          ·
            refine ⟨16803992191456570139117381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44810645843884187037646349 16803992191456570139117381)
            ·
              refine ⟨3150748535898106901084509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16803992191456570139117381 3150748535898106901084509)
              ·
                refine ⟨1181530700961790087906691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3150748535898106901084509 1181530700961790087906691)
                ·
                  refine ⟨1772296051442685131860037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1181530700961790087906691 1772296051442685131860037)
                  ·
                    refine ⟨332305509645503462223757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1772296051442685131860037 332305509645503462223757)
                    ·
                      rfl

theorem cell22_970744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_970744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970744 prefixEnd_970744 := by exact prefixLift 970744
  have htrace : WordTrace (prefixWord ++ tailWord_970744) baseStart_970744 baseEnd_970744 := by
    simpa [prefixWord, tailWord_970744, baseEnd_970744] using wordTrace_append hprefix tailTrace_970744
  have hstable : (prefixWord ++ tailWord_970744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970744).length < 2 ^ (prefixWord ++ tailWord_970744).sum := by decide
  have hdescent : baseEnd_970744 < baseStart_970744 := by decide
  rcases family_descends (prefixWord ++ tailWord_970744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970759 : List Nat := [1, 1, 4, 3, 1, 2, 3, 1, 6]
def baseStart_970759 : Nat := 118140960795 + 970759 * 2 ^ 59
def prefixEnd_970759 : Nat := 4983230072969 + 3 ^ 40 * 970759 * 2
def baseEnd_970759 : Nat := 110770214817349474366237

theorem tailTrace_970759 : CollatzResearch.WordTrace tailWord_970759 prefixEnd_970759 110770214817349474366237 := by
  unfold tailWord_970759
  simp only [CollatzResearch.WordTrace]
  refine ⟨35406489490113410282899331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23604326326742273521932887 35406489490113410282899331)
  ·
    refine ⟨53109734235170115424348997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35406489490113410282899331 53109734235170115424348997)
    ·
      refine ⟨9958075169094396642065437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53109734235170115424348997 9958075169094396642065437)
      ·
        refine ⟨3734278188410398740774539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9958075169094396642065437 3734278188410398740774539)
        ·
          refine ⟨5601417282615598111161809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3734278188410398740774539 5601417282615598111161809)
          ·
            refine ⟨4201062961961698583371357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5601417282615598111161809 4201062961961698583371357)
            ·
              refine ⟨1575398610735636968764259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4201062961961698583371357 1575398610735636968764259)
              ·
                refine ⟨2363097916103455453146389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1575398610735636968764259 2363097916103455453146389)
                ·
                  refine ⟨110770214817349474366237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2363097916103455453146389 110770214817349474366237)
                  ·
                    rfl

theorem cell22_970759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 6].length) (baseStart_970759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970759 prefixEnd_970759 := by exact prefixLift 970759
  have htrace : WordTrace (prefixWord ++ tailWord_970759) baseStart_970759 baseEnd_970759 := by
    simpa [prefixWord, tailWord_970759, baseEnd_970759] using wordTrace_append hprefix tailTrace_970759
  have hstable : (prefixWord ++ tailWord_970759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970759).length < 2 ^ (prefixWord ++ tailWord_970759).sum := by decide
  have hdescent : baseEnd_970759 < baseStart_970759 := by decide
  rcases family_descends (prefixWord ++ tailWord_970759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970765 : List Nat := [1, 7, 1, 2, 1, 1, 1, 3, 5]
def baseStart_970765 : Nat := 118140960795 + 970765 * 2 ^ 59
def prefixEnd_970765 : Nat := 4983230072969 + 3 ^ 40 * 970765 * 2
def baseEnd_970765 : Nat := 110770899458222135816231

theorem tailTrace_970765 : CollatzResearch.WordTrace tailWord_970765 prefixEnd_970765 110770899458222135816231 := by
  unfold tailWord_970765
  simp only [CollatzResearch.WordTrace]
  refine ⟨35406708328091673307617749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23604472218727782205078499 35406708328091673307617749)
  ·
    refine ⟨829844726439648593147291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 35406708328091673307617749 829844726439648593147291)
    ·
      refine ⟨1244767089659472889720937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 829844726439648593147291 1244767089659472889720937)
      ·
        refine ⟨933575317244604667290703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1244767089659472889720937 933575317244604667290703)
        ·
          refine ⟨1400362975866907000936055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 933575317244604667290703 1400362975866907000936055)
          ·
            refine ⟨2100544463800360501404083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1400362975866907000936055 2100544463800360501404083)
            ·
              refine ⟨3150816695700540752106125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2100544463800360501404083 3150816695700540752106125)
              ·
                refine ⟨1181556260887702782039797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3150816695700540752106125 1181556260887702782039797)
                ·
                  refine ⟨110770899458222135816231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1181556260887702782039797 110770899458222135816231)
                  ·
                    rfl

theorem cell22_970765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_970765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970765 prefixEnd_970765 := by exact prefixLift 970765
  have htrace : WordTrace (prefixWord ++ tailWord_970765) baseStart_970765 baseEnd_970765 := by
    simpa [prefixWord, tailWord_970765, baseEnd_970765] using wordTrace_append hprefix tailTrace_970765
  have hstable : (prefixWord ++ tailWord_970765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970765).length < 2 ^ (prefixWord ++ tailWord_970765).sum := by decide
  have hdescent : baseEnd_970765 < baseStart_970765 := by decide
  rcases family_descends (prefixWord ++ tailWord_970765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970787 : List Nat := [1, 1, 1, 4, 3, 1, 1, 10]
def baseStart_970787 : Nat := 118140960795 + 970787 * 2 ^ 59
def prefixEnd_970787 : Nat := 4983230072969 + 3 ^ 40 * 970787 * 2
def baseEnd_970787 : Nat := 36924469936029520377625

theorem tailTrace_970787 : CollatzResearch.WordTrace tailWord_970787 prefixEnd_970787 36924469936029520377625 := by
  unfold tailWord_970787
  simp only [CollatzResearch.WordTrace]
  refine ⟨35407510734011971064918615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23605007156007980709945743 35407510734011971064918615)
  ·
    refine ⟨53111266101017956597377923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35407510734011971064918615 53111266101017956597377923)
    ·
      refine ⟨79666899151526934896066885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53111266101017956597377923 79666899151526934896066885)
      ·
        refine ⟨14937543590911300293012541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79666899151526934896066885 14937543590911300293012541)
        ·
          refine ⟨5601578846591737609879703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14937543590911300293012541 5601578846591737609879703)
          ·
            refine ⟨8402368269887606414819555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5601578846591737609879703 8402368269887606414819555)
            ·
              refine ⟨12603552404831409622229333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8402368269887606414819555 12603552404831409622229333)
              ·
                refine ⟨36924469936029520377625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12603552404831409622229333 36924469936029520377625)
                ·
                  rfl

theorem cell22_970787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 10].length) (baseStart_970787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970787 prefixEnd_970787 := by exact prefixLift 970787
  have htrace : WordTrace (prefixWord ++ tailWord_970787) baseStart_970787 baseEnd_970787 := by
    simpa [prefixWord, tailWord_970787, baseEnd_970787] using wordTrace_append hprefix tailTrace_970787
  have hstable : (prefixWord ++ tailWord_970787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970787).length < 2 ^ (prefixWord ++ tailWord_970787).sum := by decide
  have hdescent : baseEnd_970787 < baseStart_970787 := by decide
  rcases family_descends (prefixWord ++ tailWord_970787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970789 : List Nat := [1, 3, 1, 2, 2, 3, 1, 3, 2, 4]
def baseStart_970789 : Nat := 118140960795 + 970789 * 2 ^ 59
def prefixEnd_970789 : Nat := 4983230072969 + 3 ^ 40 * 970789 * 2
def baseEnd_970789 : Nat := 332320914065138344848619

theorem tailTrace_970789 : CollatzResearch.WordTrace tailWord_970789 prefixEnd_970789 332320914065138344848619 := by
  unfold tailWord_970789
  simp only [CollatzResearch.WordTrace]
  refine ⟨35407583680004725406491421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23605055786669816937660947 35407583680004725406491421)
  ·
    refine ⟨13277843880001772027434283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35407583680004725406491421 13277843880001772027434283)
    ·
      refine ⟨19916765820002658041151425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13277843880001772027434283 19916765820002658041151425)
      ·
        refine ⟨14937574365001993530863569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19916765820002658041151425 14937574365001993530863569)
        ·
          refine ⟨11203180773751495148147677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14937574365001993530863569 11203180773751495148147677)
          ·
            refine ⟨4201192790156810680555379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11203180773751495148147677 4201192790156810680555379)
            ·
              refine ⟨6301789185235216020833069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4201192790156810680555379 6301789185235216020833069)
              ·
                refine ⟨2363170944463206007812401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6301789185235216020833069 2363170944463206007812401)
                ·
                  refine ⟨1772378208347404505859301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2363170944463206007812401 1772378208347404505859301)
                  ·
                    refine ⟨332320914065138344848619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1772378208347404505859301 332320914065138344848619)
                    ·
                      rfl

theorem cell22_970789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_970789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970789 prefixEnd_970789 := by exact prefixLift 970789
  have htrace : WordTrace (prefixWord ++ tailWord_970789) baseStart_970789 baseEnd_970789 := by
    simpa [prefixWord, tailWord_970789, baseEnd_970789] using wordTrace_append hprefix tailTrace_970789
  have hstable : (prefixWord ++ tailWord_970789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970789).length < 2 ^ (prefixWord ++ tailWord_970789).sum := by decide
  have hdescent : baseEnd_970789 < baseStart_970789 := by decide
  rcases family_descends (prefixWord ++ tailWord_970789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970804 : List Nat := [2, 5, 1, 2, 12]
def baseStart_970804 : Nat := 118140960795 + 970804 * 2 ^ 59
def prefixEnd_970804 : Nat := 4983230072969 + 3 ^ 40 * 970804 * 2
def baseEnd_970804 : Nat := 1367596908936968336311

theorem tailTrace_970804 : CollatzResearch.WordTrace tailWord_970804 prefixEnd_970804 1367596908936968336311 := by
  unfold tailWord_970804
  simp only [CollatzResearch.WordTrace]
  refine ⟨17704065387475191484143733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23605420516633588645524977 17704065387475191484143733)
  ·
    refine ⟨1659756130075799201638475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17704065387475191484143733 1659756130075799201638475)
    ·
      refine ⟨2489634195113698802457713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1659756130075799201638475 2489634195113698802457713)
      ·
        refine ⟨1867225646335274101843285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2489634195113698802457713 1867225646335274101843285)
        ·
          refine ⟨1367596908936968336311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 1867225646335274101843285 1367596908936968336311)
          ·
            rfl

theorem cell22_970804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 12].length) (baseStart_970804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970804 prefixEnd_970804 := by exact prefixLift 970804
  have htrace : WordTrace (prefixWord ++ tailWord_970804) baseStart_970804 baseEnd_970804 := by
    simpa [prefixWord, tailWord_970804, baseEnd_970804] using wordTrace_append hprefix tailTrace_970804
  have hstable : (prefixWord ++ tailWord_970804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970804).length < 2 ^ (prefixWord ++ tailWord_970804).sum := by decide
  have hdescent : baseEnd_970804 < baseStart_970804 := by decide
  rcases family_descends (prefixWord ++ tailWord_970804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970806 : List Nat := [5, 1, 2, 1, 1, 1, 1, 4, 2, 4]
def baseStart_970806 : Nat := 118140960795 + 970806 * 2 ^ 59
def prefixEnd_970806 : Nat := 4983230072969 + 3 ^ 40 * 970806 * 2
def baseEnd_970806 : Nat := 332326733512555967173567

theorem tailTrace_970806 : CollatzResearch.WordTrace tailWord_970806 prefixEnd_970806 332326733512555967173567 := by
  unfold tailWord_970806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2213012732558946081866267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23605469147295424873240181 2213012732558946081866267)
  ·
    refine ⟨3319519098838419122799401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2213012732558946081866267 3319519098838419122799401)
    ·
      refine ⟨2489639324128814342099551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3319519098838419122799401 2489639324128814342099551)
      ·
        refine ⟨3734458986193221513149327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2489639324128814342099551 3734458986193221513149327)
        ·
          refine ⟨5601688479289832269723991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3734458986193221513149327 5601688479289832269723991)
          ·
            refine ⟨8402532718934748404585987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5601688479289832269723991 8402532718934748404585987)
            ·
              refine ⟨12603799078402122606878981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8402532718934748404585987 12603799078402122606878981)
              ·
                refine ⟨2363212327200397988789809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12603799078402122606878981 2363212327200397988789809)
                ·
                  refine ⟨1772409245400298491592357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2363212327200397988789809 1772409245400298491592357)
                  ·
                    refine ⟨332326733512555967173567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1772409245400298491592357 332326733512555967173567)
                    ·
                      rfl

theorem cell22_970806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_970806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970806 prefixEnd_970806 := by exact prefixLift 970806
  have htrace : WordTrace (prefixWord ++ tailWord_970806) baseStart_970806 baseEnd_970806 := by
    simpa [prefixWord, tailWord_970806, baseEnd_970806] using wordTrace_append hprefix tailTrace_970806
  have hstable : (prefixWord ++ tailWord_970806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970806).length < 2 ^ (prefixWord ++ tailWord_970806).sum := by decide
  have hdescent : baseEnd_970806 < baseStart_970806 := by decide
  rcases family_descends (prefixWord ++ tailWord_970806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970808 : List Nat := [2, 1, 2, 1, 6, 1, 2, 2, 2, 3]
def baseStart_970808 : Nat := 118140960795 + 970808 * 2 ^ 59
def prefixEnd_970808 : Nat := 4983230072969 + 3 ^ 40 * 970808 * 2
def baseEnd_970808 : Nat := 332327418153428628623561

theorem tailTrace_970808 : CollatzResearch.WordTrace tailWord_970808 prefixEnd_970808 332327418153428628623561 := by
  unfold tailWord_970808
  simp only [CollatzResearch.WordTrace]
  refine ⟨17704138333467945825716539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23605517777957261100955385 17704138333467945825716539)
  ·
    refine ⟨26556207500201918738574809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17704138333467945825716539 26556207500201918738574809)
    ·
      refine ⟨19917155625151439053931107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26556207500201918738574809 19917155625151439053931107)
      ·
        refine ⟨29875733437727158580896661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19917155625151439053931107 29875733437727158580896661)
        ·
          refine ⟨1400425004893460558479531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29875733437727158580896661 1400425004893460558479531)
          ·
            refine ⟨2100637507340190837719297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1400425004893460558479531 2100637507340190837719297)
            ·
              refine ⟨1575478130505143128289473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2100637507340190837719297 1575478130505143128289473)
              ·
                refine ⟨1181608597878857346217105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1575478130505143128289473 1181608597878857346217105)
                ·
                  refine ⟨886206448409143009662829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1181608597878857346217105 886206448409143009662829)
                  ·
                    refine ⟨332327418153428628623561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 886206448409143009662829 332327418153428628623561)
                    ·
                      rfl

theorem cell22_970808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 2, 3].length) (baseStart_970808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970808 prefixEnd_970808 := by exact prefixLift 970808
  have htrace : WordTrace (prefixWord ++ tailWord_970808) baseStart_970808 baseEnd_970808 := by
    simpa [prefixWord, tailWord_970808, baseEnd_970808] using wordTrace_append hprefix tailTrace_970808
  have hstable : (prefixWord ++ tailWord_970808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970808).length < 2 ^ (prefixWord ++ tailWord_970808).sum := by decide
  have hdescent : baseEnd_970808 < baseStart_970808 := by decide
  rcases family_descends (prefixWord ++ tailWord_970808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970832 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 11]
def baseStart_970832 : Nat := 118140960795 + 970832 * 2 ^ 59
def prefixEnd_970832 : Nat := 4983230072969 + 3 ^ 40 * 970832 * 2
def baseEnd_970832 : Nat := 110778544614633522007829

theorem tailTrace_970832 : CollatzResearch.WordTrace tailWord_970832 prefixEnd_970832 110778544614633522007829 := by
  unfold tailWord_970832
  simp only [CollatzResearch.WordTrace]
  refine ⟨17704576009424471875153375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23606101345899295833537833 17704576009424471875153375)
  ·
    refine ⟨26556864014136707812730063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17704576009424471875153375 26556864014136707812730063)
    ·
      refine ⟨39835296021205061719095095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26556864014136707812730063 39835296021205061719095095)
      ·
        refine ⟨59752944031807592578642643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39835296021205061719095095 59752944031807592578642643)
        ·
          refine ⟨89629416047711388867963965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59752944031807592578642643 89629416047711388867963965)
          ·
            refine ⟨33611031017891770825486487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89629416047711388867963965 33611031017891770825486487)
            ·
              refine ⟨50416546526837656238229731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33611031017891770825486487 50416546526837656238229731)
              ·
                refine ⟨75624819790256484357344597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50416546526837656238229731 75624819790256484357344597)
                ·
                  refine ⟨110778544614633522007829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 75624819790256484357344597 110778544614633522007829)
                  ·
                    rfl

theorem cell22_970832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 11].length) (baseStart_970832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970832 prefixEnd_970832 := by exact prefixLift 970832
  have htrace : WordTrace (prefixWord ++ tailWord_970832) baseStart_970832 baseEnd_970832 := by
    simpa [prefixWord, tailWord_970832, baseEnd_970832] using wordTrace_append hprefix tailTrace_970832
  have hstable : (prefixWord ++ tailWord_970832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970832).length < 2 ^ (prefixWord ++ tailWord_970832).sum := by decide
  have hdescent : baseEnd_970832 < baseStart_970832 := by decide
  rcases family_descends (prefixWord ++ tailWord_970832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970853 : List Nat := [1, 3, 1, 3, 2, 2, 1, 5, 1, 3]
def baseStart_970853 : Nat := 118140960795 + 970853 * 2 ^ 59
def prefixEnd_970853 : Nat := 4983230072969 + 3 ^ 40 * 970853 * 2
def baseEnd_970853 : Nat := 332342822573063511248423

theorem tailTrace_970853 : CollatzResearch.WordTrace tailWord_970853 prefixEnd_970853 332342822573063511248423 := by
  unfold tailWord_970853
  simp only [CollatzResearch.WordTrace]
  refine ⟨35409917951772864336821213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23606611967848576224547475 35409917951772864336821213)
  ·
    refine ⟨13278719231914824126307955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35409917951772864336821213 13278719231914824126307955)
    ·
      refine ⟨19918078847872236189461933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13278719231914824126307955 19918078847872236189461933)
      ·
        refine ⟨7469279567952088571048225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19918078847872236189461933 7469279567952088571048225)
        ·
          refine ⟨5601959675964066428286169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7469279567952088571048225 5601959675964066428286169)
          ·
            refine ⟨4201469756973049821214627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5601959675964066428286169 4201469756973049821214627)
            ·
              refine ⟨6302204635459574731821941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4201469756973049821214627 6302204635459574731821941)
              ·
                refine ⟨590831684574335131108307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6302204635459574731821941 590831684574335131108307)
                ·
                  refine ⟨886247526861502696662461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 590831684574335131108307 886247526861502696662461)
                  ·
                    refine ⟨332342822573063511248423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 886247526861502696662461 332342822573063511248423)
                    ·
                      rfl

theorem cell22_970853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 5, 1, 3].length) (baseStart_970853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970853 prefixEnd_970853 := by exact prefixLift 970853
  have htrace : WordTrace (prefixWord ++ tailWord_970853) baseStart_970853 baseEnd_970853 := by
    simpa [prefixWord, tailWord_970853, baseEnd_970853] using wordTrace_append hprefix tailTrace_970853
  have hstable : (prefixWord ++ tailWord_970853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970853).length < 2 ^ (prefixWord ++ tailWord_970853).sum := by decide
  have hdescent : baseEnd_970853 < baseStart_970853 := by decide
  rcases family_descends (prefixWord ++ tailWord_970853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970864 : List Nat := [2, 1, 1, 1, 5, 2, 1, 2, 2, 5]
def baseStart_970864 : Nat := 118140960795 + 970864 * 2 ^ 59
def prefixEnd_970864 : Nat := 4983230072969 + 3 ^ 40 * 970864 * 2
def baseEnd_970864 : Nat := 332346588097863149223389

theorem tailTrace_970864 : CollatzResearch.WordTrace tailWord_970864 prefixEnd_970864 332346588097863149223389 := by
  unfold tailWord_970864
  simp only [CollatzResearch.WordTrace]
  refine ⟨17705159577366506607735823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23606879436488675476981097 17705159577366506607735823)
  ·
    refine ⟨26557739366049759911603735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17705159577366506607735823 26557739366049759911603735)
    ·
      refine ⟨39836609049074639867405603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26557739366049759911603735 39836609049074639867405603)
      ·
        refine ⟨59754913573611959801108405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39836609049074639867405603 59754913573611959801108405)
        ·
          refine ⟨5602023147526121231353913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59754913573611959801108405 5602023147526121231353913)
          ·
            refine ⟨4201517360644590923515435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5602023147526121231353913 4201517360644590923515435)
            ·
              refine ⟨6302276040966886385273153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4201517360644590923515435 6302276040966886385273153)
              ·
                refine ⟨4726707030725164788954865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6302276040966886385273153 4726707030725164788954865)
                ·
                  refine ⟨3545030273043873591716149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4726707030725164788954865 3545030273043873591716149)
                  ·
                    refine ⟨332346588097863149223389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3545030273043873591716149 332346588097863149223389)
                    ·
                      rfl

theorem cell22_970864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 2, 5].length) (baseStart_970864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970864 prefixEnd_970864 := by exact prefixLift 970864
  have htrace : WordTrace (prefixWord ++ tailWord_970864) baseStart_970864 baseEnd_970864 := by
    simpa [prefixWord, tailWord_970864, baseEnd_970864] using wordTrace_append hprefix tailTrace_970864
  have hstable : (prefixWord ++ tailWord_970864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970864).length < 2 ^ (prefixWord ++ tailWord_970864).sum := by decide
  have hdescent : baseEnd_970864 < baseStart_970864 := by decide
  rcases family_descends (prefixWord ++ tailWord_970864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970866 : List Nat := [3, 2, 1, 2, 2, 2, 3, 2, 5]
def baseStart_970866 : Nat := 118140960795 + 970866 * 2 ^ 59
def prefixEnd_970866 : Nat := 4983230072969 + 3 ^ 40 * 970866 * 2
def baseEnd_970866 : Nat := 110782424246245270224461

theorem tailTrace_970866 : CollatzResearch.WordTrace tailWord_970866 prefixEnd_970866 110782424246245270224461 := by
  unfold tailWord_970866
  simp only [CollatzResearch.WordTrace]
  refine ⟨8852598025181441889261113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23606928067150511704696301 8852598025181441889261113)
  ·
    refine ⟨6639448518886081416945835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8852598025181441889261113 6639448518886081416945835)
    ·
      refine ⟨9959172778329122125418753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6639448518886081416945835 9959172778329122125418753)
      ·
        refine ⟨7469379583746841594064065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9959172778329122125418753 7469379583746841594064065)
        ·
          refine ⟨5602034687810131195548049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7469379583746841594064065 5602034687810131195548049)
          ·
            refine ⟨4201526015857598396661037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5602034687810131195548049 4201526015857598396661037)
            ·
              refine ⟨1575572255946599398747889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4201526015857598396661037 1575572255946599398747889)
              ·
                refine ⟨1181679191959949549060917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1575572255946599398747889 1181679191959949549060917)
                ·
                  refine ⟨110782424246245270224461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1181679191959949549060917 110782424246245270224461)
                  ·
                    rfl

theorem cell22_970866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_970866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970866 prefixEnd_970866 := by exact prefixLift 970866
  have htrace : WordTrace (prefixWord ++ tailWord_970866) baseStart_970866 baseEnd_970866 := by
    simpa [prefixWord, tailWord_970866, baseEnd_970866] using wordTrace_append hprefix tailTrace_970866
  have hstable : (prefixWord ++ tailWord_970866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970866).length < 2 ^ (prefixWord ++ tailWord_970866).sum := by decide
  have hdescent : baseEnd_970866 < baseStart_970866 := by decide
  rcases family_descends (prefixWord ++ tailWord_970866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970870 : List Nat := [5, 1, 1, 2, 1, 2, 2, 4, 1, 3]
def baseStart_970870 : Nat := 118140960795 + 970870 * 2 ^ 59
def prefixEnd_970870 : Nat := 4983230072969 + 3 ^ 40 * 970870 * 2
def baseEnd_970870 : Nat := 332348642020481133573371

theorem tailTrace_970870 : CollatzResearch.WordTrace tailWord_970870 prefixEnd_970870 332348642020481133573371 := by
  unfold tailWord_970870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2213158624544454765011879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23607025328474184160126709 2213158624544454765011879)
  ·
    refine ⟨3319737936816682147517819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2213158624544454765011879 3319737936816682147517819)
    ·
      refine ⟨4979606905225023221276729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3319737936816682147517819 4979606905225023221276729)
      ·
        refine ⟨3734705178918767415957547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4979606905225023221276729 3734705178918767415957547)
        ·
          refine ⟨5602057768378151123936321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3734705178918767415957547 5602057768378151123936321)
          ·
            refine ⟨4201543326283613342952241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5602057768378151123936321 4201543326283613342952241)
            ·
              refine ⟨3151157494712710007214181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4201543326283613342952241 3151157494712710007214181)
              ·
                refine ⟨590842030258633126352659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3151157494712710007214181 590842030258633126352659)
                ·
                  refine ⟨886263045387949689528989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 590842030258633126352659 886263045387949689528989)
                  ·
                    refine ⟨332348642020481133573371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 886263045387949689528989 332348642020481133573371)
                    ·
                      rfl

theorem cell22_970870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_970870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970870 prefixEnd_970870 := by exact prefixLift 970870
  have htrace : WordTrace (prefixWord ++ tailWord_970870) baseStart_970870 baseEnd_970870 := by
    simpa [prefixWord, tailWord_970870, baseEnd_970870] using wordTrace_append hprefix tailTrace_970870
  have hstable : (prefixWord ++ tailWord_970870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970870).length < 2 ^ (prefixWord ++ tailWord_970870).sum := by decide
  have hdescent : baseEnd_970870 < baseStart_970870 := by decide
  rcases family_descends (prefixWord ++ tailWord_970870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970896 : List Nat := [2, 1, 1, 1, 1, 1, 8, 2, 1, 4]
def baseStart_970896 : Nat := 118140960795 + 970896 * 2 ^ 59
def prefixEnd_970896 : Nat := 4983230072969 + 3 ^ 40 * 970896 * 2
def baseEnd_970896 : Nat := 332357542351825732423291

theorem tailTrace_970896 : CollatzResearch.WordTrace tailWord_970896 prefixEnd_970896 332357542351825732423291 := by
  unfold tailWord_970896
  simp only [CollatzResearch.WordTrace]
  refine ⟨17705743145308541340318271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23607657527078055120424361 17705743145308541340318271)
  ·
    refine ⟨26558614717962812010477407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17705743145308541340318271 26558614717962812010477407)
    ·
      refine ⟨39837922076944218015716111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26558614717962812010477407 39837922076944218015716111)
      ·
        refine ⟨59756883115416327023574167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39837922076944218015716111 59756883115416327023574167)
        ·
          refine ⟨89635324673124490535361251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59756883115416327023574167 89635324673124490535361251)
          ·
            refine ⟨134452987009686735803041877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89635324673124490535361251 134452987009686735803041877)
            ·
              refine ⟨1575620941519766435191897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 134452987009686735803041877 1575620941519766435191897)
              ·
                refine ⟨1181715706139824826393923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1575620941519766435191897 1181715706139824826393923)
                ·
                  refine ⟨1772573559209737239590885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1181715706139824826393923 1772573559209737239590885)
                  ·
                    refine ⟨332357542351825732423291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1772573559209737239590885 332357542351825732423291)
                    ·
                      rfl

theorem cell22_970896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 1, 4].length) (baseStart_970896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970896 prefixEnd_970896 := by exact prefixLift 970896
  have htrace : WordTrace (prefixWord ++ tailWord_970896) baseStart_970896 baseEnd_970896 := by
    simpa [prefixWord, tailWord_970896, baseEnd_970896] using wordTrace_append hprefix tailTrace_970896
  have hstable : (prefixWord ++ tailWord_970896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970896).length < 2 ^ (prefixWord ++ tailWord_970896).sum := by decide
  have hdescent : baseEnd_970896 < baseStart_970896 := by decide
  rcases family_descends (prefixWord ++ tailWord_970896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970939 : List Nat := [1, 1, 1, 1, 1, 2, 8, 7]
def baseStart_970939 : Nat := 118140960795 + 970939 * 2 ^ 59
def prefixEnd_970939 : Nat := 4983230072969 + 3 ^ 40 * 970939 * 2
def baseEnd_970939 : Nat := 36930251347843105955351

theorem tailTrace_970939 : CollatzResearch.WordTrace tailWord_970939 prefixEnd_970939 36930251347843105955351 := by
  unfold tailWord_970939
  simp only [CollatzResearch.WordTrace]
  refine ⟨35413054629461301024451871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23608703086307534016301247 35413054629461301024451871)
  ·
    refine ⟨53119581944191951536677807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35413054629461301024451871 53119581944191951536677807)
    ·
      refine ⟨79679372916287927305016711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53119581944191951536677807 79679372916287927305016711)
      ·
        refine ⟨119519059374431890957525067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79679372916287927305016711 119519059374431890957525067)
        ·
          refine ⟨179278589061647836436287601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119519059374431890957525067 179278589061647836436287601)
          ·
            refine ⟨134458941796235877327215701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179278589061647836436287601 134458941796235877327215701)
            ·
              refine ⟨1575690724174639187428309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 134458941796235877327215701 1575690724174639187428309)
              ·
                refine ⟨36930251347843105955351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1575690724174639187428309 36930251347843105955351)
                ·
                  rfl

theorem cell22_970939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 7].length) (baseStart_970939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970939 prefixEnd_970939 := by exact prefixLift 970939
  have htrace : WordTrace (prefixWord ++ tailWord_970939) baseStart_970939 baseEnd_970939 := by
    simpa [prefixWord, tailWord_970939, baseEnd_970939] using wordTrace_append hprefix tailTrace_970939
  have hstable : (prefixWord ++ tailWord_970939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970939).length < 2 ^ (prefixWord ++ tailWord_970939).sum := by decide
  have hdescent : baseEnd_970939 < baseStart_970939 := by decide
  rcases family_descends (prefixWord ++ tailWord_970939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970958 : List Nat := [4, 1, 1, 1, 4, 2, 2, 1, 2, 4]
def baseStart_970958 : Nat := 118140960795 + 970958 * 2 ^ 59
def prefixEnd_970958 : Nat := 4983230072969 + 3 ^ 40 * 970958 * 2
def baseEnd_970958 : Nat := 332378766218878237373101

theorem tailTrace_970958 : CollatzResearch.WordTrace tailWord_970958 prefixEnd_970958 332378766218878237373101 := by
  unfold tailWord_970958
  simp only [CollatzResearch.WordTrace]
  refine ⟨4426718452049058408674191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23609165077594978179595685 4426718452049058408674191)
  ·
    refine ⟨6640077678073587613011287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4426718452049058408674191 6640077678073587613011287)
    ·
      refine ⟨9960116517110381419516931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6640077678073587613011287 9960116517110381419516931)
      ·
        refine ⟨14940174775665572129275397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9960116517110381419516931 14940174775665572129275397)
        ·
          refine ⟨2801282770437294774239137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14940174775665572129275397 2801282770437294774239137)
          ·
            refine ⟨2100962077827971080679353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2801282770437294774239137 2100962077827971080679353)
            ·
              refine ⟨1575721558370978310509515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2100962077827971080679353 1575721558370978310509515)
              ·
                refine ⟨2363582337556467465764273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1575721558370978310509515 2363582337556467465764273)
                ·
                  refine ⟨1772686753167350599323205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2363582337556467465764273 1772686753167350599323205)
                  ·
                    refine ⟨332378766218878237373101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1772686753167350599323205 332378766218878237373101)
                    ·
                      rfl

theorem cell22_970958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_970958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970958 prefixEnd_970958 := by exact prefixLift 970958
  have htrace : WordTrace (prefixWord ++ tailWord_970958) baseStart_970958 baseEnd_970958 := by
    simpa [prefixWord, tailWord_970958, baseEnd_970958] using wordTrace_append hprefix tailTrace_970958
  have hstable : (prefixWord ++ tailWord_970958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970958).length < 2 ^ (prefixWord ++ tailWord_970958).sum := by decide
  have hdescent : baseEnd_970958 < baseStart_970958 := by decide
  rcases family_descends (prefixWord ++ tailWord_970958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970979 : List Nat := [1, 1, 1, 8, 2, 1, 2, 2, 4]
def baseStart_970979 : Nat := 118140960795 + 970979 * 2 ^ 59
def prefixEnd_970979 : Nat := 4983230072969 + 3 ^ 40 * 970979 * 2
def baseEnd_970979 : Nat := 110795318316013727532679

theorem tailTrace_970979 : CollatzResearch.WordTrace tailWord_970979 prefixEnd_970979 110795318316013727532679 := by
  unfold tailWord_970979
  simp only [CollatzResearch.WordTrace]
  refine ⟨35414513549316387855907991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23609675699544258570605327 35414513549316387855907991)
  ·
    refine ⟨53121770323974581783861987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35414513549316387855907991 53121770323974581783861987)
    ·
      refine ⟨79682655485961872675792981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53121770323974581783861987 79682655485961872675792981)
      ·
        refine ⟨933781118976115695419449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 79682655485961872675792981 933781118976115695419449)
        ·
          refine ⟨700335839232086771564587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 933781118976115695419449 700335839232086771564587)
          ·
            refine ⟨1050503758848130157346881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700335839232086771564587 1050503758848130157346881)
            ·
              refine ⟨787877819136097618010161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1050503758848130157346881 787877819136097618010161)
              ·
                refine ⟨590908364352073213507621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 787877819136097618010161 590908364352073213507621)
                ·
                  refine ⟨110795318316013727532679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 590908364352073213507621 110795318316013727532679)
                  ·
                    rfl

theorem cell22_970979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 2, 4].length) (baseStart_970979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_970979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_970979 prefixEnd_970979 := by exact prefixLift 970979
  have htrace : WordTrace (prefixWord ++ tailWord_970979) baseStart_970979 baseEnd_970979 := by
    simpa [prefixWord, tailWord_970979, baseEnd_970979] using wordTrace_append hprefix tailTrace_970979
  have hstable : (prefixWord ++ tailWord_970979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970979).length < 2 ^ (prefixWord ++ tailWord_970979).sum := by decide
  have hdescent : baseEnd_970979 < baseStart_970979 := by decide
  rcases family_descends (prefixWord ++ tailWord_970979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971065 : List Nat := [1, 2, 1, 6, 1, 2, 2, 2, 1, 4]
def baseStart_971065 : Nat := 118140960795 + 971065 * 2 ^ 59
def prefixEnd_971065 : Nat := 4983230072969 + 3 ^ 40 * 971065 * 2
def baseEnd_971065 : Nat := 332415394505565624947773

theorem tailTrace_971065 : CollatzResearch.WordTrace tailWord_971065 prefixEnd_971065 332415394505565624947773 := by
  unfold tailWord_971065
  simp only [CollatzResearch.WordTrace]
  refine ⟨35417650227004824543538649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23611766818003216362359099 35417650227004824543538649)
  ·
    refine ⟨26563237670253618407653987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35417650227004824543538649 26563237670253618407653987)
    ·
      refine ⟨39844856505380427611480981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26563237670253618407653987 39844856505380427611480981)
      ·
        refine ⟨1867727648689707544288171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39844856505380427611480981 1867727648689707544288171)
        ·
          refine ⟨2801591473034561316432257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1867727648689707544288171 2801591473034561316432257)
          ·
            refine ⟨2101193604775920987324193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2801591473034561316432257 2101193604775920987324193)
            ·
              refine ⟨1575895203581940740493145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2101193604775920987324193 1575895203581940740493145)
              ·
                refine ⟨1181921402686455555369859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1575895203581940740493145 1181921402686455555369859)
                ·
                  refine ⟨1772882104029683333054789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1181921402686455555369859 1772882104029683333054789)
                  ·
                    refine ⟨332415394505565624947773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1772882104029683333054789 332415394505565624947773)
                    ·
                      rfl

theorem cell22_971065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 4].length) (baseStart_971065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_971065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_971065 prefixEnd_971065 := by exact prefixLift 971065
  have htrace : WordTrace (prefixWord ++ tailWord_971065) baseStart_971065 baseEnd_971065 := by
    simpa [prefixWord, tailWord_971065, baseEnd_971065] using wordTrace_append hprefix tailTrace_971065
  have hstable : (prefixWord ++ tailWord_971065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971065).length < 2 ^ (prefixWord ++ tailWord_971065).sum := by decide
  have hdescent : baseEnd_971065 < baseStart_971065 := by decide
  rcases family_descends (prefixWord ++ tailWord_971065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971112 : List Nat := [2, 1, 4, 2, 2, 1, 4, 1, 2, 3]
def baseStart_971112 : Nat := 118140960795 + 971112 * 2 ^ 59
def prefixEnd_971112 : Nat := 4983230072969 + 3 ^ 40 * 971112 * 2
def baseEnd_971112 : Nat := 332431483566073169022629

theorem tailTrace_971112 : CollatzResearch.WordTrace tailWord_971112 prefixEnd_971112 332431483566073169022629 := by
  unfold tailWord_971112
  simp only [CollatzResearch.WordTrace]
  refine ⟨17709682228917275785249795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23612909638556367713666393 17709682228917275785249795)
  ·
    refine ⟨26564523343375913677874693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17709682228917275785249795 26564523343375913677874693)
    ·
      refine ⟨4980848126882983814601505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26564523343375913677874693 4980848126882983814601505)
      ·
        refine ⟨3735636095162237860951129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4980848126882983814601505 3735636095162237860951129)
        ·
          refine ⟨2801727071371678395713347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3735636095162237860951129 2801727071371678395713347)
          ·
            refine ⟨4202590607057517593570021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2801727071371678395713347 4202590607057517593570021)
            ·
              refine ⟨787985738823284548794379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4202590607057517593570021 787985738823284548794379)
              ·
                refine ⟨1181978608234926823191569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 787985738823284548794379 1181978608234926823191569)
                ·
                  refine ⟨886483956176195117393677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1181978608234926823191569 886483956176195117393677)
                  ·
                    refine ⟨332431483566073169022629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 886483956176195117393677 332431483566073169022629)
                    ·
                      rfl

theorem cell22_971112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_971112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_971112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_971112 prefixEnd_971112 := by exact prefixLift 971112
  have htrace : WordTrace (prefixWord ++ tailWord_971112) baseStart_971112 baseEnd_971112 := by
    simpa [prefixWord, tailWord_971112, baseEnd_971112] using wordTrace_append hprefix tailTrace_971112
  have hstable : (prefixWord ++ tailWord_971112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971112).length < 2 ^ (prefixWord ++ tailWord_971112).sum := by decide
  have hdescent : baseEnd_971112 < baseStart_971112 := by decide
  rcases family_descends (prefixWord ++ tailWord_971112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971168 : List Nat := [2, 1, 1, 4, 1, 4, 1, 1, 2, 5]
def baseStart_971168 : Nat := 118140960795 + 971168 * 2 ^ 59
def prefixEnd_971168 : Nat := 4983230072969 + 3 ^ 40 * 971168 * 2
def baseEnd_971168 : Nat := 332450653510507689622457

theorem tailTrace_971168 : CollatzResearch.WordTrace tailWord_971168 prefixEnd_971168 332450653510507689622457 := by
  unfold tailWord_971168
  simp only [CollatzResearch.WordTrace]
  refine ⟨17710703472815836567269079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23614271297087782089692105 17710703472815836567269079)
  ·
    refine ⟨26566055209223754850903619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17710703472815836567269079 26566055209223754850903619)
    ·
      refine ⟨39849082813835632276355429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26566055209223754850903619 39849082813835632276355429)
      ·
        refine ⟨7471703027594181051816643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39849082813835632276355429 7471703027594181051816643)
        ·
          refine ⟨11207554541391271577724965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7471703027594181051816643 11207554541391271577724965)
          ·
            refine ⟨2101416476510863420823431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11207554541391271577724965 2101416476510863420823431)
            ·
              refine ⟨3152124714766295131235147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2101416476510863420823431 3152124714766295131235147)
              ·
                refine ⟨4728187072149442696852721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3152124714766295131235147 4728187072149442696852721)
                ·
                  refine ⟨3546140304112082022639541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4728187072149442696852721 3546140304112082022639541)
                  ·
                    refine ⟨332450653510507689622457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3546140304112082022639541 332450653510507689622457)
                    ·
                      rfl

theorem cell22_971168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 2, 5].length) (baseStart_971168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_971168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_971168 prefixEnd_971168 := by exact prefixLift 971168
  have htrace : WordTrace (prefixWord ++ tailWord_971168) baseStart_971168 baseEnd_971168 := by
    simpa [prefixWord, tailWord_971168, baseEnd_971168] using wordTrace_append hprefix tailTrace_971168
  have hstable : (prefixWord ++ tailWord_971168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971168).length < 2 ^ (prefixWord ++ tailWord_971168).sum := by decide
  have hdescent : baseEnd_971168 < baseStart_971168 := by decide
  rcases family_descends (prefixWord ++ tailWord_971168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971204 : List Nat := [2, 3, 3, 2, 3, 1, 1, 2, 5]
def baseStart_971204 : Nat := 118140960795 + 971204 * 2 ^ 59
def prefixEnd_971204 : Nat := 4983230072969 + 3 ^ 40 * 971204 * 2
def baseEnd_971204 : Nat := 110820992348738531907449

theorem tailTrace_971204 : CollatzResearch.WordTrace tailWord_971204 prefixEnd_971204 110820992348738531907449 := by
  unfold tailWord_971204
  simp only [CollatzResearch.WordTrace]
  refine ⟨17711359986750625641424333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23615146649000834188565777 17711359986750625641424333)
  ·
    refine ⟨6641759995031484615534125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17711359986750625641424333 6641759995031484615534125)
    ·
      refine ⟨2490659998136806730825297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6641759995031484615534125 2490659998136806730825297)
      ·
        refine ⟨1867994998602605048118973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2490659998136806730825297 1867994998602605048118973)
        ·
          refine ⟨700498124475976893044615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1867994998602605048118973 700498124475976893044615)
          ·
            refine ⟨1050747186713965339566923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700498124475976893044615 1050747186713965339566923)
            ·
              refine ⟨1576120780070948009350385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1050747186713965339566923 1576120780070948009350385)
              ·
                refine ⟨1182090585053211007012789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1576120780070948009350385 1182090585053211007012789)
                ·
                  refine ⟨110820992348738531907449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1182090585053211007012789 110820992348738531907449)
                  ·
                    rfl

theorem cell22_971204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_971204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_971204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_971204 prefixEnd_971204 := by exact prefixLift 971204
  have htrace : WordTrace (prefixWord ++ tailWord_971204) baseStart_971204 baseEnd_971204 := by
    simpa [prefixWord, tailWord_971204, baseEnd_971204] using wordTrace_append hprefix tailTrace_971204
  have hstable : (prefixWord ++ tailWord_971204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971204).length < 2 ^ (prefixWord ++ tailWord_971204).sum := by decide
  have hdescent : baseEnd_971204 < baseStart_971204 := by decide
  rcases family_descends (prefixWord ++ tailWord_971204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971245 : List Nat := [1, 5, 1, 3, 1, 1, 2, 1, 1, 6]
def baseStart_971245 : Nat := 118140960795 + 971245 * 2 ^ 59
def prefixEnd_971245 : Nat := 4983230072969 + 3 ^ 40 * 971245 * 2
def baseEnd_971245 : Nat := 332477012184105155447221

theorem tailTrace_971245 : CollatzResearch.WordTrace tailWord_971245 prefixEnd_971245 332477012184105155447221 := by
  unfold tailWord_971245
  simp only [CollatzResearch.WordTrace]
  refine ⟨35424215366352715285091189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23616143577568476856727459 35424215366352715285091189)
  ·
    refine ⟨3321020190595567057977299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35424215366352715285091189 3321020190595567057977299)
    ·
      refine ⟨4981530285893350586965949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3321020190595567057977299 4981530285893350586965949)
      ·
        refine ⟨1868073857210006470112231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4981530285893350586965949 1868073857210006470112231)
        ·
          refine ⟨2802110785815009705168347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1868073857210006470112231 2802110785815009705168347)
          ·
            refine ⟨4203166178722514557752521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2802110785815009705168347 4203166178722514557752521)
            ·
              refine ⟨3152374634041885918314391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4203166178722514557752521 3152374634041885918314391)
              ·
                refine ⟨4728561951062828877471587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3152374634041885918314391 4728561951062828877471587)
                ·
                  refine ⟨7092842926594243316207381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4728561951062828877471587 7092842926594243316207381)
                  ·
                    refine ⟨332477012184105155447221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7092842926594243316207381 332477012184105155447221)
                    ·
                      rfl

theorem cell22_971245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_971245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_971245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_971245 prefixEnd_971245 := by exact prefixLift 971245
  have htrace : WordTrace (prefixWord ++ tailWord_971245) baseStart_971245 baseEnd_971245 := by
    simpa [prefixWord, tailWord_971245, baseEnd_971245] using wordTrace_append hprefix tailTrace_971245
  have hstable : (prefixWord ++ tailWord_971245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971245).length < 2 ^ (prefixWord ++ tailWord_971245).sum := by decide
  have hdescent : baseEnd_971245 < baseStart_971245 := by decide
  rcases family_descends (prefixWord ++ tailWord_971245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971266 : List Nat := [3, 4, 1, 2, 2, 1, 3, 2, 4]
def baseStart_971266 : Nat := 118140960795 + 971266 * 2 ^ 59
def prefixEnd_971266 : Nat := 4983230072969 + 3 ^ 40 * 971266 * 2
def baseEnd_971266 : Nat := 110828066971089366890719

theorem tailTrace_971266 : CollatzResearch.WordTrace tailWord_971266 prefixEnd_971266 110828066971089366890719 := by
  unfold tailWord_971266
  simp only [CollatzResearch.WordTrace]
  refine ⟨8856245324819158967901413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23616654199517757247737101 8856245324819158967901413)
  ·
    refine ⟨1660545998403592306481515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8856245324819158967901413 1660545998403592306481515)
    ·
      refine ⟨2490818997605388459722273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1660545998403592306481515 2490818997605388459722273)
      ·
        refine ⟨1868114248204041344791705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2490818997605388459722273 1868114248204041344791705)
        ·
          refine ⟨1401085686153031008593779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1868114248204041344791705 1401085686153031008593779)
          ·
            refine ⟨2101628529229546512890669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1401085686153031008593779 2101628529229546512890669)
            ·
              refine ⟨788110698461079942334001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2101628529229546512890669 788110698461079942334001)
              ·
                refine ⟨591083023845809956750501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 788110698461079942334001 591083023845809956750501)
                ·
                  refine ⟨110828066971089366890719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 591083023845809956750501 110828066971089366890719)
                  ·
                    rfl

theorem cell22_971266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_971266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_971266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_971266 prefixEnd_971266 := by exact prefixLift 971266
  have htrace : WordTrace (prefixWord ++ tailWord_971266) baseStart_971266 baseEnd_971266 := by
    simpa [prefixWord, tailWord_971266, baseEnd_971266] using wordTrace_append hprefix tailTrace_971266
  have hstable : (prefixWord ++ tailWord_971266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971266).length < 2 ^ (prefixWord ++ tailWord_971266).sum := by decide
  have hdescent : baseEnd_971266 < baseStart_971266 := by decide
  rcases family_descends (prefixWord ++ tailWord_971266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971277 : List Nat := [1, 7, 1, 1, 1, 1, 1, 9]
def baseStart_971277 : Nat := 118140960795 + 971277 * 2 ^ 59
def prefixEnd_971277 : Nat := 4983230072969 + 3 ^ 40 * 971277 * 2
def baseEnd_971277 : Nat := 36943107382007526516347

theorem tailTrace_971277 : CollatzResearch.WordTrace tailWord_971277 prefixEnd_971277 36943107382007526516347 := by
  unfold tailWord_971277
  simp only [CollatzResearch.WordTrace]
  refine ⟨35425382502236784750256085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23616921668157856500170723 35425382502236784750256085)
  ·
    refine ⟨830282402396174642584127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 35425382502236784750256085 830282402396174642584127)
    ·
      refine ⟨1245423603594261963876191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 830282402396174642584127 1245423603594261963876191)
      ·
        refine ⟨1868135405391392945814287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1245423603594261963876191 1868135405391392945814287)
        ·
          refine ⟨2802203108087089418721431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1868135405391392945814287 2802203108087089418721431)
          ·
            refine ⟨4203304662130634128082147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2802203108087089418721431 4203304662130634128082147)
            ·
              refine ⟨6304956993195951192123221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4203304662130634128082147 6304956993195951192123221)
              ·
                refine ⟨36943107382007526516347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6304956993195951192123221 36943107382007526516347)
                ·
                  rfl

theorem cell22_971277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 9].length) (baseStart_971277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_971277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_971277 prefixEnd_971277 := by exact prefixLift 971277
  have htrace : WordTrace (prefixWord ++ tailWord_971277) baseStart_971277 baseEnd_971277 := by
    simpa [prefixWord, tailWord_971277, baseEnd_971277] using wordTrace_append hprefix tailTrace_971277
  have hstable : (prefixWord ++ tailWord_971277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971277).length < 2 ^ (prefixWord ++ tailWord_971277).sum := by decide
  have hdescent : baseEnd_971277 < baseStart_971277 := by decide
  rcases family_descends (prefixWord ++ tailWord_971277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971335 : List Nat := [1, 1, 4, 1, 4, 1, 1, 2, 3, 4]
def baseStart_971335 : Nat := 118140960795 + 971335 * 2 ^ 59
def prefixEnd_971335 : Nat := 4983230072969 + 3 ^ 40 * 971335 * 2
def baseEnd_971335 : Nat := 332507821023374920696945

theorem tailTrace_971335 : CollatzResearch.WordTrace tailWord_971335 prefixEnd_971335 332507821023374920696945 := by
  unfold tailWord_971335
  simp only [CollatzResearch.WordTrace]
  refine ⟨35427497936026660655867459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23618331957351107103911639 35427497936026660655867459)
  ·
    refine ⟨53141246904039990983801189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35427497936026660655867459 53141246904039990983801189)
    ·
      refine ⟨9963983794507498309462723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53141246904039990983801189 9963983794507498309462723)
      ·
        refine ⟨14945975691761247464194085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9963983794507498309462723 14945975691761247464194085)
        ·
          refine ⟨2802370442205233899536391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14945975691761247464194085 2802370442205233899536391)
          ·
            refine ⟨4203555663307850849304587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2802370442205233899536391 4203555663307850849304587)
            ·
              refine ⟨6305333494961776273956881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4203555663307850849304587 6305333494961776273956881)
              ·
                refine ⟨4729000121221332205467661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6305333494961776273956881 4729000121221332205467661)
                ·
                  refine ⟨1773375045457999577050373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4729000121221332205467661 1773375045457999577050373)
                  ·
                    refine ⟨332507821023374920696945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1773375045457999577050373 332507821023374920696945)
                    ·
                      rfl

theorem cell22_971335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_971335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_971335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_971335 prefixEnd_971335 := by exact prefixLift 971335
  have htrace : WordTrace (prefixWord ++ tailWord_971335) baseStart_971335 baseEnd_971335 := by
    simpa [prefixWord, tailWord_971335, baseEnd_971335] using wordTrace_append hprefix tailTrace_971335
  have hstable : (prefixWord ++ tailWord_971335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971335).length < 2 ^ (prefixWord ++ tailWord_971335).sum := by decide
  have hdescent : baseEnd_971335 < baseStart_971335 := by decide
  rcases family_descends (prefixWord ++ tailWord_971335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971399 : List Nat := [1, 1, 4, 2, 1, 2, 5, 1, 2, 3]
def baseStart_971399 : Nat := 118140960795 + 971399 * 2 ^ 59
def prefixEnd_971399 : Nat := 4983230072969 + 3 ^ 40 * 971399 * 2
def baseEnd_971399 : Nat := 332529729531300087096749

theorem tailTrace_971399 : CollatzResearch.WordTrace tailWord_971399 prefixEnd_971399 332529729531300087096749 := by
  unfold tailWord_971399
  simp only [CollatzResearch.WordTrace]
  refine ⟨35429832207794799586197251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23619888138529866390798167 35429832207794799586197251)
  ·
    refine ⟨53144748311692199379295877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35429832207794799586197251 53144748311692199379295877)
    ·
      refine ⟨9964640308442287383617977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53144748311692199379295877 9964640308442287383617977)
      ·
        refine ⟨7473480231331715537713483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9964640308442287383617977 7473480231331715537713483)
        ·
          refine ⟨11210220346997573306570225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7473480231331715537713483 11210220346997573306570225)
          ·
            refine ⟨8407665260248179979927669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11210220346997573306570225 8407665260248179979927669)
            ·
              refine ⟨788218618148266873118219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8407665260248179979927669 788218618148266873118219)
              ·
                refine ⟨1182327927222400309677329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 788218618148266873118219 1182327927222400309677329)
                ·
                  refine ⟨886745945416800232257997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1182327927222400309677329 886745945416800232257997)
                  ·
                    refine ⟨332529729531300087096749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 886745945416800232257997 332529729531300087096749)
                    ·
                      rfl

theorem cell22_971399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_971399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_971399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_971399 prefixEnd_971399 := by exact prefixLift 971399
  have htrace : WordTrace (prefixWord ++ tailWord_971399) baseStart_971399 baseEnd_971399 := by
    simpa [prefixWord, tailWord_971399, baseEnd_971399] using wordTrace_append hprefix tailTrace_971399
  have hstable : (prefixWord ++ tailWord_971399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971399).length < 2 ^ (prefixWord ++ tailWord_971399).sum := by decide
  have hdescent : baseEnd_971399 < baseStart_971399 := by decide
  rcases family_descends (prefixWord ++ tailWord_971399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971412 : List Nat := [2, 4, 2, 2, 1, 2, 1, 8]
def baseStart_971412 : Nat := 118140960795 + 971412 * 2 ^ 59
def prefixEnd_971412 : Nat := 4983230072969 + 3 ^ 40 * 971412 * 2
def baseEnd_971412 : Nat := 36948242188552487391301

theorem tailTrace_971412 : CollatzResearch.WordTrace tailWord_971412 prefixEnd_971412 36948242188552487391301 := by
  unfold tailWord_971412
  simp only [CollatzResearch.WordTrace]
  refine ⟨17715153178373851403210245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23620204237831801870946993 17715153178373851403210245)
  ·
    refine ⟨3321591220945097138101921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17715153178373851403210245 3321591220945097138101921)
    ·
      refine ⟨2491193415708822853576441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3321591220945097138101921 2491193415708822853576441)
      ·
        refine ⟨1868395061781617140182331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2491193415708822853576441 1868395061781617140182331)
        ·
          refine ⟨2802592592672425710273497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1868395061781617140182331 2802592592672425710273497)
          ·
            refine ⟨2101944444504319282705123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2802592592672425710273497 2101944444504319282705123)
            ·
              refine ⟨3152916666756478924057685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2101944444504319282705123 3152916666756478924057685)
              ·
                refine ⟨36948242188552487391301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3152916666756478924057685 36948242188552487391301)
                ·
                  rfl

theorem cell22_971412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 8].length) (baseStart_971412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_971412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_971412 prefixEnd_971412 := by exact prefixLift 971412
  have htrace : WordTrace (prefixWord ++ tailWord_971412) baseStart_971412 baseEnd_971412 := by
    simpa [prefixWord, tailWord_971412, baseEnd_971412] using wordTrace_append hprefix tailTrace_971412
  have hstable : (prefixWord ++ tailWord_971412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971412).length < 2 ^ (prefixWord ++ tailWord_971412).sum := by decide
  have hdescent : baseEnd_971412 < baseStart_971412 := by decide
  rcases family_descends (prefixWord ++ tailWord_971412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971418 : List Nat := [3, 1, 1, 6, 2, 1, 1, 3, 4]
def baseStart_971418 : Nat := 118140960795 + 971418 * 2 ^ 59
def prefixEnd_971418 : Nat := 4983230072969 + 3 ^ 40 * 971418 * 2
def baseEnd_971418 : Nat := 110845411206530123623897

theorem tailTrace_971418 : CollatzResearch.WordTrace tailWord_971418 prefixEnd_971418 110845411206530123623897 := by
  unfold tailWord_971418
  simp only [CollatzResearch.WordTrace]
  refine ⟨8857631298681491457784727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23620350129817310554092605 8857631298681491457784727)
  ·
    refine ⟨13286446948022237186677091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8857631298681491457784727 13286446948022237186677091)
    ·
      refine ⟨19929670422033355780015637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13286446948022237186677091 19929670422033355780015637)
      ·
        refine ⟨934203301032813552188233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19929670422033355780015637 934203301032813552188233)
        ·
          refine ⟨700652475774610164141175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 934203301032813552188233 700652475774610164141175)
          ·
            refine ⟨1050978713661915246211763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700652475774610164141175 1050978713661915246211763)
            ·
              refine ⟨1576468070492872869317645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1050978713661915246211763 1576468070492872869317645)
              ·
                refine ⟨591175526434827325994117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1576468070492872869317645 591175526434827325994117)
                ·
                  refine ⟨110845411206530123623897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 591175526434827325994117 110845411206530123623897)
                  ·
                    rfl

theorem cell22_971418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 3, 4].length) (baseStart_971418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_971418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_971418 prefixEnd_971418 := by exact prefixLift 971418
  have htrace : WordTrace (prefixWord ++ tailWord_971418) baseStart_971418 baseEnd_971418 := by
    simpa [prefixWord, tailWord_971418, baseEnd_971418] using wordTrace_append hprefix tailTrace_971418
  have hstable : (prefixWord ++ tailWord_971418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971418).length < 2 ^ (prefixWord ++ tailWord_971418).sum := by decide
  have hdescent : baseEnd_971418 < baseStart_971418 := by decide
  rcases family_descends (prefixWord ++ tailWord_971418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971440 : List Nat := [2, 1, 1, 1, 2, 1, 3, 6, 5]
def baseStart_971440 : Nat := 118140960795 + 971440 * 2 ^ 59
def prefixEnd_971440 : Nat := 4983230072969 + 3 ^ 40 * 971440 * 2
def baseEnd_971440 : Nat := 110847921556396548940541

theorem tailTrace_971440 : CollatzResearch.WordTrace tailWord_971440 prefixEnd_971440 110847921556396548940541 := by
  unfold tailWord_971440
  simp only [CollatzResearch.WordTrace]
  refine ⟨17715663800323131794219887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23620885067097509058959849 17715663800323131794219887)
  ·
    refine ⟨26573495700484697691329831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17715663800323131794219887 26573495700484697691329831)
    ·
      refine ⟨39860243550727046536994747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26573495700484697691329831 39860243550727046536994747)
      ·
        refine ⟨59790365326090569805492121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39860243550727046536994747 59790365326090569805492121)
        ·
          refine ⟨44842773994567927354119091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59790365326090569805492121 44842773994567927354119091)
          ·
            refine ⟨67264160991851891031178637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44842773994567927354119091 67264160991851891031178637)
            ·
              refine ⟨25224060371944459136691989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67264160991851891031178637 25224060371944459136691989)
              ·
                refine ⟨1182377829934896522032437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25224060371944459136691989 1182377829934896522032437)
                ·
                  refine ⟨110847921556396548940541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1182377829934896522032437 110847921556396548940541)
                  ·
                    rfl

theorem cell22_971440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 5].length) (baseStart_971440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_971440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_971440 prefixEnd_971440 := by exact prefixLift 971440
  have htrace : WordTrace (prefixWord ++ tailWord_971440) baseStart_971440 baseEnd_971440 := by
    simpa [prefixWord, tailWord_971440, baseEnd_971440] using wordTrace_append hprefix tailTrace_971440
  have hstable : (prefixWord ++ tailWord_971440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971440).length < 2 ^ (prefixWord ++ tailWord_971440).sum := by decide
  have hdescent : baseEnd_971440 < baseStart_971440 := by decide
  rcases family_descends (prefixWord ++ tailWord_971440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971500 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 5, 5]
def baseStart_971500 : Nat := 118140960795 + 971500 * 2 ^ 59
def prefixEnd_971500 : Nat := 4983230072969 + 3 ^ 40 * 971500 * 2
def baseEnd_971500 : Nat := 332564303895369490321439

theorem tailTrace_971500 : CollatzResearch.WordTrace tailWord_971500 prefixEnd_971500 332564303895369490321439 := by
  unfold tailWord_971500
  simp only [CollatzResearch.WordTrace]
  refine ⟨17716757990214446917811977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23622343986952595890415969 17716757990214446917811977)
  ·
    refine ⟨13287568492660835188358983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17716757990214446917811977 13287568492660835188358983)
    ·
      refine ⟨19931352738991252782538475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13287568492660835188358983 19931352738991252782538475)
      ·
        refine ⟨29897029108486879173807713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19931352738991252782538475 29897029108486879173807713)
        ·
          refine ⟨22422771831365159380355785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29897029108486879173807713 22422771831365159380355785)
          ·
            refine ⟨16817078873523869535266839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22422771831365159380355785 16817078873523869535266839)
            ·
              refine ⟨25225618310285804302900259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16817078873523869535266839 25225618310285804302900259)
              ·
                refine ⟨37838427465428706454350389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25225618310285804302900259 37838427465428706454350389)
                ·
                  refine ⟨3547352574883941230095349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37838427465428706454350389 3547352574883941230095349)
                  ·
                    refine ⟨332564303895369490321439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3547352574883941230095349 332564303895369490321439)
                    ·
                      rfl

theorem cell22_971500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_971500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_971500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_971500 prefixEnd_971500 := by exact prefixLift 971500
  have htrace : WordTrace (prefixWord ++ tailWord_971500) baseStart_971500 baseEnd_971500 := by
    simpa [prefixWord, tailWord_971500, baseEnd_971500] using wordTrace_append hprefix tailTrace_971500
  have hstable : (prefixWord ++ tailWord_971500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971500).length < 2 ^ (prefixWord ++ tailWord_971500).sum := by decide
  have hdescent : baseEnd_971500 < baseStart_971500 := by decide
  rcases family_descends (prefixWord ++ tailWord_971500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971517 : List Nat := [1, 4, 1, 1, 1, 1, 6, 1, 1, 5]
def baseStart_971517 : Nat := 118140960795 + 971517 * 2 ^ 59
def prefixEnd_971517 : Nat := 4983230072969 + 3 ^ 40 * 971517 * 2
def baseEnd_971517 : Nat := 332570123342787112646387

theorem tailTrace_971517 : CollatzResearch.WordTrace tailWord_971517 prefixEnd_971517 332570123342787112646387 := by
  unfold tailWord_971517
  simp only [CollatzResearch.WordTrace]
  refine ⟨35434136021367305738992805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23622757347578203825995203 35434136021367305738992805)
  ·
    refine ⟨6643900504006369826061151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35434136021367305738992805 6643900504006369826061151)
    ·
      refine ⟨9965850756009554739091727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6643900504006369826061151 9965850756009554739091727)
      ·
        refine ⟨14948776134014332108637591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9965850756009554739091727 14948776134014332108637591)
        ·
          refine ⟨22423164201021498162956387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14948776134014332108637591 22423164201021498162956387)
          ·
            refine ⟨33634746301532247244434581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22423164201021498162956387 33634746301532247244434581)
            ·
              refine ⟨1576628732884324089582871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33634746301532247244434581 1576628732884324089582871)
              ·
                refine ⟨2364943099326486134374307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1576628732884324089582871 2364943099326486134374307)
                ·
                  refine ⟨3547414648989729201561461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2364943099326486134374307 3547414648989729201561461)
                  ·
                    refine ⟨332570123342787112646387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3547414648989729201561461 332570123342787112646387)
                    ·
                      rfl

theorem cell22_971517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_971517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_971517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_971517 prefixEnd_971517 := by exact prefixLift 971517
  have htrace : WordTrace (prefixWord ++ tailWord_971517) baseStart_971517 baseEnd_971517 := by
    simpa [prefixWord, tailWord_971517, baseEnd_971517] using wordTrace_append hprefix tailTrace_971517
  have hstable : (prefixWord ++ tailWord_971517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971517).length < 2 ^ (prefixWord ++ tailWord_971517).sum := by decide
  have hdescent : baseEnd_971517 < baseStart_971517 := by decide
  rcases family_descends (prefixWord ++ tailWord_971517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971551 : List Nat := [1, 1, 2, 4, 2, 4, 1, 2, 2, 3]
def baseStart_971551 : Nat := 118140960795 + 971551 * 2 ^ 59
def prefixEnd_971551 : Nat := 4983230072969 + 3 ^ 40 * 971551 * 2
def baseEnd_971551 : Nat := 332581762237622357296283

theorem tailTrace_971551 : CollatzResearch.WordTrace tailWord_971551 prefixEnd_971551 332581762237622357296283 := by
  unfold tailWord_971551
  simp only [CollatzResearch.WordTrace]
  refine ⟨35435376103244129545730507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23623584068829419697153671 35435376103244129545730507)
  ·
    refine ⟨53153064154866194318595761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35435376103244129545730507 53153064154866194318595761)
    ·
      refine ⟨39864798116149645738946821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53153064154866194318595761 39864798116149645738946821)
      ·
        refine ⟨7474649646778058576052529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39864798116149645738946821 7474649646778058576052529)
        ·
          refine ⟨5605987235083543932039397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7474649646778058576052529 5605987235083543932039397)
          ·
            refine ⟨1051122606578164487257387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5605987235083543932039397 1051122606578164487257387)
            ·
              refine ⟨1576683909867246730886081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1051122606578164487257387 1576683909867246730886081)
              ·
                refine ⟨1182512932400435048164561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1576683909867246730886081 1182512932400435048164561)
                ·
                  refine ⟨886884699300326286123421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1182512932400435048164561 886884699300326286123421)
                  ·
                    refine ⟨332581762237622357296283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 886884699300326286123421 332581762237622357296283)
                    ·
                      rfl

theorem cell22_971551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 2, 3].length) (baseStart_971551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_971551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_971551 prefixEnd_971551 := by exact prefixLift 971551
  have htrace : WordTrace (prefixWord ++ tailWord_971551) baseStart_971551 baseEnd_971551 := by
    simpa [prefixWord, tailWord_971551, baseEnd_971551] using wordTrace_append hprefix tailTrace_971551
  have hstable : (prefixWord ++ tailWord_971551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971551).length < 2 ^ (prefixWord ++ tailWord_971551).sum := by decide
  have hdescent : baseEnd_971551 < baseStart_971551 := by decide
  rcases family_descends (prefixWord ++ tailWord_971551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971581 : List Nat := [1, 4, 1, 4, 2, 2, 2, 6]
def baseStart_971581 : Nat := 118140960795 + 971581 * 2 ^ 59
def prefixEnd_971581 : Nat := 4983230072969 + 3 ^ 40 * 971581 * 2
def baseEnd_971581 : Nat := 36954670205634697671799

theorem tailTrace_971581 : CollatzResearch.WordTrace tailWord_971581 prefixEnd_971581 36954670205634697671799 := by
  unfold tailWord_971581
  simp only [CollatzResearch.WordTrace]
  refine ⟨35436470293135444669322597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23624313528756963112881731 35436470293135444669322597)
  ·
    refine ⟨6644338179962895875497987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35436470293135444669322597 6644338179962895875497987)
    ·
      refine ⟨9966507269944343813246981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6644338179962895875497987 9966507269944343813246981)
      ·
        refine ⟨1868720113114564464983809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9966507269944343813246981 1868720113114564464983809)
        ·
          refine ⟨1401540084835923348737857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1868720113114564464983809 1401540084835923348737857)
          ·
            refine ⟨1051155063626942511553393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1401540084835923348737857 1051155063626942511553393)
            ·
              refine ⟨788366297720206883665045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1051155063626942511553393 788366297720206883665045)
              ·
                refine ⟨36954670205634697671799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 788366297720206883665045 36954670205634697671799)
                ·
                  rfl

theorem cell22_971581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 6].length) (baseStart_971581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_971581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_971581 prefixEnd_971581 := by exact prefixLift 971581
  have htrace : WordTrace (prefixWord ++ tailWord_971581) baseStart_971581 baseEnd_971581 := by
    simpa [prefixWord, tailWord_971581, baseEnd_971581] using wordTrace_append hprefix tailTrace_971581
  have hstable : (prefixWord ++ tailWord_971581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971581).length < 2 ^ (prefixWord ++ tailWord_971581).sum := by decide
  have hdescent : baseEnd_971581 < baseStart_971581 := by decide
  rcases family_descends (prefixWord ++ tailWord_971581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971667 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 4, 4]
def baseStart_971667 : Nat := 118140960795 + 971667 * 2 ^ 59
def prefixEnd_971667 : Nat := 4983230072969 + 3 ^ 40 * 971667 * 2
def baseEnd_971667 : Nat := 332621471408236721395927

theorem tailTrace_971667 : CollatzResearch.WordTrace tailWord_971667 prefixEnd_971667 332621471408236721395927 := by
  unfold tailWord_971667
  simp only [CollatzResearch.WordTrace]
  refine ⟨35439606970823881356953255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23626404647215920904635503 35439606970823881356953255)
  ·
    refine ⟨53159410456235822035429883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35439606970823881356953255 53159410456235822035429883)
    ·
      refine ⟨79739115684353733053144825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53159410456235822035429883 79739115684353733053144825)
      ·
        refine ⟨59804336763265299789858619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79739115684353733053144825 59804336763265299789858619)
        ·
          refine ⟨89706505144897949684787929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59804336763265299789858619 89706505144897949684787929)
          ·
            refine ⟨67279878858673462263590947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89706505144897949684787929 67279878858673462263590947)
            ·
              refine ⟨100919818288010193395386421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67279878858673462263590947 100919818288010193395386421)
              ·
                refine ⟨9461232964500955630817477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100919818288010193395386421 9461232964500955630817477)
                ·
                  refine ⟨1773981180843929180778277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9461232964500955630817477 1773981180843929180778277)
                  ·
                    refine ⟨332621471408236721395927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1773981180843929180778277 332621471408236721395927)
                    ·
                      rfl

theorem cell22_971667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 4].length) (baseStart_971667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_971667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_971667 prefixEnd_971667 := by exact prefixLift 971667
  have htrace : WordTrace (prefixWord ++ tailWord_971667) baseStart_971667 baseEnd_971667 := by
    simpa [prefixWord, tailWord_971667, baseEnd_971667] using wordTrace_append hprefix tailTrace_971667
  have hstable : (prefixWord ++ tailWord_971667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971667).length < 2 ^ (prefixWord ++ tailWord_971667).sum := by decide
  have hdescent : baseEnd_971667 < baseStart_971667 := by decide
  rcases family_descends (prefixWord ++ tailWord_971667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971716 : List Nat := [2, 3, 3, 3, 1, 1, 9]
def baseStart_971716 : Nat := 118140960795 + 971716 * 2 ^ 59
def prefixEnd_971716 : Nat := 4983230072969 + 3 ^ 40 * 971716 * 2
def baseEnd_971716 : Nat := 12319935004059886182251

theorem tailTrace_971716 : CollatzResearch.WordTrace tailWord_971716 prefixEnd_971716 12319935004059886182251 := by
  unfold tailWord_971716
  simp only [CollatzResearch.WordTrace]
  refine ⟨17720697073823181362743501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23627596098430908483658001 17720697073823181362743501)
  ·
    refine ⟨6645261402683693011028813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17720697073823181362743501 6645261402683693011028813)
    ·
      refine ⟨2491973026006384879135805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6645261402683693011028813 2491973026006384879135805)
      ·
        refine ⟨934489884752394329675927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2491973026006384879135805 934489884752394329675927)
        ·
          refine ⟨1401734827128591494513891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 934489884752394329675927 1401734827128591494513891)
          ·
            refine ⟨2102602240692887241770837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1401734827128591494513891 2102602240692887241770837)
            ·
              refine ⟨12319935004059886182251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2102602240692887241770837 12319935004059886182251)
              ·
                rfl

theorem cell22_971716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 9].length) (baseStart_971716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_971716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_971716 prefixEnd_971716 := by exact prefixLift 971716
  have htrace : WordTrace (prefixWord ++ tailWord_971716) baseStart_971716 baseEnd_971716 := by
    simpa [prefixWord, tailWord_971716, baseEnd_971716] using wordTrace_append hprefix tailTrace_971716
  have hstable : (prefixWord ++ tailWord_971716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971716).length < 2 ^ (prefixWord ++ tailWord_971716).sum := by decide
  have hdescent : baseEnd_971716 < baseStart_971716 := by decide
  rcases family_descends (prefixWord ++ tailWord_971716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971720 : List Nat := [2, 1, 3, 1, 6, 1, 1, 2, 2, 3]
def baseStart_971720 : Nat := 118140960795 + 971720 * 2 ^ 59
def prefixEnd_971720 : Nat := 4983230072969 + 3 ^ 40 * 971720 * 2
def baseEnd_971720 : Nat := 332639614391362249820765

theorem tailTrace_971720 : CollatzResearch.WordTrace tailWord_971720 prefixEnd_971720 332639614391362249820765 := by
  unfold tailWord_971720
  simp only [CollatzResearch.WordTrace]
  refine ⟨17720770019815935704316307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23627693359754580939088409 17720770019815935704316307)
  ·
    refine ⟨26581155029723903556474461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17720770019815935704316307 26581155029723903556474461)
    ·
      refine ⟨9967933136146463833677923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26581155029723903556474461 9967933136146463833677923)
      ·
        refine ⟨14951899704219695750516885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9967933136146463833677923 14951899704219695750516885)
        ·
          refine ⟨700870298635298238305479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14951899704219695750516885 700870298635298238305479)
          ·
            refine ⟨1051305447952947357458219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700870298635298238305479 1051305447952947357458219)
            ·
              refine ⟨1576958171929421036187329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1051305447952947357458219 1576958171929421036187329)
              ·
                refine ⟨1182718628947065777140497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1576958171929421036187329 1182718628947065777140497)
                ·
                  refine ⟨887038971710299332855373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1182718628947065777140497 887038971710299332855373)
                  ·
                    refine ⟨332639614391362249820765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 887038971710299332855373 332639614391362249820765)
                    ·
                      rfl

theorem cell22_971720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_971720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_971720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_971720 prefixEnd_971720 := by exact prefixLift 971720
  have htrace : WordTrace (prefixWord ++ tailWord_971720) baseStart_971720 baseEnd_971720 := by
    simpa [prefixWord, tailWord_971720, baseEnd_971720] using wordTrace_append hprefix tailTrace_971720
  have hstable : (prefixWord ++ tailWord_971720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971720).length < 2 ^ (prefixWord ++ tailWord_971720).sum := by decide
  have hdescent : baseEnd_971720 < baseStart_971720 := by decide
  rcases family_descends (prefixWord ++ tailWord_971720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971808 : List Nat := [2, 1, 1, 7, 1, 1, 1, 1, 3, 4]
def baseStart_971808 : Nat := 118140960795 + 971808 * 2 ^ 59
def prefixEnd_971808 : Nat := 4983230072969 + 3 ^ 40 * 971808 * 2
def baseEnd_971808 : Nat := 332669738589759353620495

theorem tailTrace_971808 : CollatzResearch.WordTrace tailWord_971808 prefixEnd_971808 332669738589759353620495 := by
  unfold tailWord_971808
  simp only [CollatzResearch.WordTrace]
  refine ⟨17722374831656531218918039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23629833108875374958557385 17722374831656531218918039)
  ·
    refine ⟨26583562247484796828377059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17722374831656531218918039 26583562247484796828377059)
    ·
      refine ⟨39875343371227195242565589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26583562247484796828377059 39875343371227195242565589)
      ·
        refine ⟨934578360263137388497631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 39875343371227195242565589 934578360263137388497631)
        ·
          refine ⟨1401867540394706082746447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 934578360263137388497631 1401867540394706082746447)
          ·
            refine ⟨2102801310592059124119671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1401867540394706082746447 2102801310592059124119671)
            ·
              refine ⟨3154201965888088686179507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2102801310592059124119671 3154201965888088686179507)
              ·
                refine ⟨4731302948832133029269261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3154201965888088686179507 4731302948832133029269261)
                ·
                  refine ⟨1774238605812049885975973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4731302948832133029269261 1774238605812049885975973)
                  ·
                    refine ⟨332669738589759353620495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1774238605812049885975973 332669738589759353620495)
                    ·
                      rfl

theorem cell22_971808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 3, 4].length) (baseStart_971808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_971808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_971808 prefixEnd_971808 := by exact prefixLift 971808
  have htrace : WordTrace (prefixWord ++ tailWord_971808) baseStart_971808 baseEnd_971808 := by
    simpa [prefixWord, tailWord_971808, baseEnd_971808] using wordTrace_append hprefix tailTrace_971808
  have hstable : (prefixWord ++ tailWord_971808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971808).length < 2 ^ (prefixWord ++ tailWord_971808).sum := by decide
  have hdescent : baseEnd_971808 < baseStart_971808 := by decide
  rcases family_descends (prefixWord ++ tailWord_971808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971836 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 4]
def baseStart_971836 : Nat := 118140960795 + 971836 * 2 ^ 59
def prefixEnd_971836 : Nat := 4983230072969 + 3 ^ 40 * 971836 * 2
def baseEnd_971836 : Nat := 332679323561976613920409

theorem tailTrace_971836 : CollatzResearch.WordTrace tailWord_971836 prefixEnd_971836 332679323561976613920409 := by
  unfold tailWord_971836
  simp only [CollatzResearch.WordTrace]
  refine ⟨17722885453605811609927681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23630513938141082146570241 17722885453605811609927681)
  ·
    refine ⟨13292164090204358707445761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17722885453605811609927681 13292164090204358707445761)
    ·
      refine ⟨9969123067653269030584321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13292164090204358707445761 9969123067653269030584321)
      ·
        refine ⟨7476842300739951772938241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9969123067653269030584321 7476842300739951772938241)
        ·
          refine ⟨5607631725554963829703681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7476842300739951772938241 5607631725554963829703681)
          ·
            refine ⟨4205723794166222872277761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5607631725554963829703681 4205723794166222872277761)
            ·
              refine ⟨3154292845624667154208321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4205723794166222872277761 3154292845624667154208321)
              ·
                refine ⟨2365719634218500365656241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3154292845624667154208321 2365719634218500365656241)
                ·
                  refine ⟨1774289725663875274242181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2365719634218500365656241 1774289725663875274242181)
                  ·
                    refine ⟨332679323561976613920409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1774289725663875274242181 332679323561976613920409)
                    ·
                      rfl

theorem cell22_971836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_971836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_971836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_971836 prefixEnd_971836 := by exact prefixLift 971836
  have htrace : WordTrace (prefixWord ++ tailWord_971836) baseStart_971836 baseEnd_971836 := by
    simpa [prefixWord, tailWord_971836, baseEnd_971836] using wordTrace_append hprefix tailTrace_971836
  have hstable : (prefixWord ++ tailWord_971836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971836).length < 2 ^ (prefixWord ++ tailWord_971836).sum := by decide
  have hdescent : baseEnd_971836 < baseStart_971836 := by decide
  rcases family_descends (prefixWord ++ tailWord_971836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971864 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 2, 6]
def baseStart_971864 : Nat := 118140960795 + 971864 * 2 ^ 59
def prefixEnd_971864 : Nat := 4983230072969 + 3 ^ 40 * 971864 * 2
def baseEnd_971864 : Nat := 332688908534193874220323

theorem tailTrace_971864 : CollatzResearch.WordTrace tailWord_971864 prefixEnd_971864 332688908534193874220323 := by
  unfold tailWord_971864
  simp only [CollatzResearch.WordTrace]
  refine ⟨17723396075555092000937323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23631194767406789334583097 17723396075555092000937323)
  ·
    refine ⟨26585094113332638001405985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17723396075555092000937323 26585094113332638001405985)
    ·
      refine ⟨19938820584999478501054489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26585094113332638001405985 19938820584999478501054489)
      ·
        refine ⟨14954115438749608875790867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19938820584999478501054489 14954115438749608875790867)
        ·
          refine ⟨22431173158124413313686301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14954115438749608875790867 22431173158124413313686301)
          ·
            refine ⟨8411689934296654992632363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22431173158124413313686301 8411689934296654992632363)
            ·
              refine ⟨12617534901444982488948545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8411689934296654992632363 12617534901444982488948545)
              ·
                refine ⟨9463151176083736866711409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12617534901444982488948545 9463151176083736866711409)
                ·
                  refine ⟨7097363382062802650033557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9463151176083736866711409 7097363382062802650033557)
                  ·
                    refine ⟨332688908534193874220323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7097363382062802650033557 332688908534193874220323)
                    ·
                      rfl

theorem cell22_971864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_971864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_971864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_971864 prefixEnd_971864 := by exact prefixLift 971864
  have htrace : WordTrace (prefixWord ++ tailWord_971864) baseStart_971864 baseEnd_971864 := by
    simpa [prefixWord, tailWord_971864, baseEnd_971864] using wordTrace_append hprefix tailTrace_971864
  have hstable : (prefixWord ++ tailWord_971864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971864).length < 2 ^ (prefixWord ++ tailWord_971864).sum := by decide
  have hdescent : baseEnd_971864 < baseStart_971864 := by decide
  rcases family_descends (prefixWord ++ tailWord_971864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971870 : List Nat := [4, 4, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_971870 : Nat := 118140960795 + 971870 * 2 ^ 59
def prefixEnd_971870 : Nat := 4983230072969 + 3 ^ 40 * 971870 * 2
def baseEnd_971870 : Nat := 332690962456811858570305

theorem tailTrace_971870 : CollatzResearch.WordTrace tailWord_971870 prefixEnd_971870 332690962456811858570305 := by
  unfold tailWord_971870
  simp only [CollatzResearch.WordTrace]
  refine ⟨4430876373636055878324133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23631340659392298017728709 4430876373636055878324133)
  ·
    refine ⟨830789320056760477185775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4430876373636055878324133 830789320056760477185775)
    ·
      refine ⟨1246183980085140715778663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 830789320056760477185775 1246183980085140715778663)
      ·
        refine ⟨1869275970127711073667995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1246183980085140715778663 1869275970127711073667995)
        ·
          refine ⟨2803913955191566610501993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1869275970127711073667995 2803913955191566610501993)
          ·
            refine ⟨2102935466393674957876495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2803913955191566610501993 2102935466393674957876495)
            ·
              refine ⟨3154403199590512436814743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2102935466393674957876495 3154403199590512436814743)
              ·
                refine ⟨4731604799385768655222115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3154403199590512436814743 4731604799385768655222115)
                ·
                  refine ⟨7097407199078652982833173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4731604799385768655222115 7097407199078652982833173)
                  ·
                    refine ⟨332690962456811858570305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7097407199078652982833173 332690962456811858570305)
                    ·
                      rfl

theorem cell22_971870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_971870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_971870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_971870 prefixEnd_971870 := by exact prefixLift 971870
  have htrace : WordTrace (prefixWord ++ tailWord_971870) baseStart_971870 baseEnd_971870 := by
    simpa [prefixWord, tailWord_971870, baseEnd_971870] using wordTrace_append hprefix tailTrace_971870
  have hstable : (prefixWord ++ tailWord_971870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971870).length < 2 ^ (prefixWord ++ tailWord_971870).sum := by decide
  have hdescent : baseEnd_971870 < baseStart_971870 := by decide
  rcases family_descends (prefixWord ++ tailWord_971870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971896 : List Nat := [2, 1, 2, 1, 1, 1, 7, 2, 5]
def baseStart_971896 : Nat := 118140960795 + 971896 * 2 ^ 59
def prefixEnd_971896 : Nat := 4983230072969 + 3 ^ 40 * 971896 * 2
def baseEnd_971896 : Nat := 110899954262718819140075

theorem tailTrace_971896 : CollatzResearch.WordTrace tailWord_971896 prefixEnd_971896 110899954262718819140075 := by
  unfold tailWord_971896
  simp only [CollatzResearch.WordTrace]
  refine ⟨17723979643497126733519771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23631972857996168978026361 17723979643497126733519771)
  ·
    refine ⟨26585969465245690100279657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17723979643497126733519771 26585969465245690100279657)
    ·
      refine ⟨19939477098934267575209743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26585969465245690100279657 19939477098934267575209743)
      ·
        refine ⟨29909215648401401362814615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19939477098934267575209743 29909215648401401362814615)
        ·
          refine ⟨44863823472602102044221923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29909215648401401362814615 44863823472602102044221923)
          ·
            refine ⟨67295735208903153066332885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44863823472602102044221923 67295735208903153066332885)
            ·
              refine ⟨1577243793958667649992177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 67295735208903153066332885 1577243793958667649992177)
              ·
                refine ⟨1182932845469000737494133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1577243793958667649992177 1182932845469000737494133)
                ·
                  refine ⟨110899954262718819140075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1182932845469000737494133 110899954262718819140075)
                  ·
                    rfl

theorem cell22_971896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 5].length) (baseStart_971896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_971896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_971896 prefixEnd_971896 := by exact prefixLift 971896
  have htrace : WordTrace (prefixWord ++ tailWord_971896) baseStart_971896 baseEnd_971896 := by
    simpa [prefixWord, tailWord_971896, baseEnd_971896] using wordTrace_append hprefix tailTrace_971896
  have hstable : (prefixWord ++ tailWord_971896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971896).length < 2 ^ (prefixWord ++ tailWord_971896).sum := by decide
  have hdescent : baseEnd_971896 < baseStart_971896 := by decide
  rcases family_descends (prefixWord ++ tailWord_971896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971913 : List Nat := [1, 2, 1, 1, 4, 4, 3, 1, 5]
def baseStart_971913 : Nat := 118140960795 + 971913 * 2 ^ 59
def prefixEnd_971913 : Nat := 4983230072969 + 3 ^ 40 * 971913 * 2
def baseEnd_971913 : Nat := 110901894078524693248391

theorem tailTrace_971913 : CollatzResearch.WordTrace tailWord_971913 prefixEnd_971913 110901894078524693248391 := by
  unfold tailWord_971913
  simp only [CollatzResearch.WordTrace]
  refine ⟨35448579327932665370408393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23632386218621776913605595 35448579327932665370408393)
  ·
    refine ⟨26586434495949499027806295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35448579327932665370408393 26586434495949499027806295)
    ·
      refine ⟨39879651743924248541709443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26586434495949499027806295 39879651743924248541709443)
      ·
        refine ⟨59819477615886372812564165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39879651743924248541709443 59819477615886372812564165)
        ·
          refine ⟨11216152052978694902355781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59819477615886372812564165 11216152052978694902355781)
          ·
            refine ⟨2103028509933505294191709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11216152052978694902355781 2103028509933505294191709)
            ·
              refine ⟨788635691225064485321891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2103028509933505294191709 788635691225064485321891)
              ·
                refine ⟨1182953536837596727982837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 788635691225064485321891 1182953536837596727982837)
                ·
                  refine ⟨110901894078524693248391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1182953536837596727982837 110901894078524693248391)
                  ·
                    rfl

theorem cell22_971913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 5].length) (baseStart_971913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_971913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_971913 prefixEnd_971913 := by exact prefixLift 971913
  have htrace : WordTrace (prefixWord ++ tailWord_971913) baseStart_971913 baseEnd_971913 := by
    simpa [prefixWord, tailWord_971913, baseEnd_971913] using wordTrace_append hprefix tailTrace_971913
  have hstable : (prefixWord ++ tailWord_971913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971913).length < 2 ^ (prefixWord ++ tailWord_971913).sum := by decide
  have hdescent : baseEnd_971913 < baseStart_971913 := by decide
  rcases family_descends (prefixWord ++ tailWord_971913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971934 : List Nat := [4, 3, 1, 1, 2, 3, 1, 3, 1, 3]
def baseStart_971934 : Nat := 118140960795 + 971934 * 2 ^ 59
def prefixEnd_971934 : Nat := 4983230072969 + 3 ^ 40 * 971934 * 2
def baseEnd_971934 : Nat := 332712870964737024970109

theorem tailTrace_971934 : CollatzResearch.WordTrace tailWord_971934 prefixEnd_971934 332712870964737024970109 := by
  unfold tailWord_971934
  simp only [CollatzResearch.WordTrace]
  refine ⟨4431168157607073244615357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23632896840571057304615237 4431168157607073244615357)
  ·
    refine ⟨1661688059102652466730759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4431168157607073244615357 1661688059102652466730759)
    ·
      refine ⟨2492532088653978700096139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1661688059102652466730759 2492532088653978700096139)
      ·
        refine ⟨3738798132980968050144209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2492532088653978700096139 3738798132980968050144209)
        ·
          refine ⟨2804098599735726037608157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3738798132980968050144209 2804098599735726037608157)
          ·
            refine ⟨1051536974900897264103059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2804098599735726037608157 1051536974900897264103059)
            ·
              refine ⟨1577305462351345896154589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1051536974900897264103059 1577305462351345896154589)
              ·
                refine ⟨591489548381754711057971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1577305462351345896154589 591489548381754711057971)
                ·
                  refine ⟨887234322572632066586957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 591489548381754711057971 887234322572632066586957)
                  ·
                    refine ⟨332712870964737024970109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 887234322572632066586957 332712870964737024970109)
                    ·
                      rfl

theorem cell22_971934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_971934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_971934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_971934 prefixEnd_971934 := by exact prefixLift 971934
  have htrace : WordTrace (prefixWord ++ tailWord_971934) baseStart_971934 baseEnd_971934 := by
    simpa [prefixWord, tailWord_971934, baseEnd_971934] using wordTrace_append hprefix tailTrace_971934
  have hstable : (prefixWord ++ tailWord_971934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971934).length < 2 ^ (prefixWord ++ tailWord_971934).sum := by decide
  have hdescent : baseEnd_971934 < baseStart_971934 := by decide
  rcases family_descends (prefixWord ++ tailWord_971934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971986 : List Nat := [3, 2, 2, 2, 1, 1, 1, 10]
def baseStart_971986 : Nat := 118140960795 + 971986 * 2 ^ 59
def prefixEnd_971986 : Nat := 4983230072969 + 3 ^ 40 * 971986 * 2
def baseEnd_971986 : Nat := 36970074625269580296661

theorem tailTrace_971986 : CollatzResearch.WordTrace tailWord_971986 prefixEnd_971986 36970074625269580296661 := by
  unfold tailWord_971986
  simp only [CollatzResearch.WordTrace]
  refine ⟨8862810464167049709453953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23634161237778799225210541 8862810464167049709453953)
  ·
    refine ⟨6647107848125287282090465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8862810464167049709453953 6647107848125287282090465)
    ·
      refine ⟨4985330886093965461567849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6647107848125287282090465 4985330886093965461567849)
      ·
        refine ⟨3738998164570474096175887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4985330886093965461567849 3738998164570474096175887)
        ·
          refine ⟨5608497246855711144263831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3738998164570474096175887 5608497246855711144263831)
          ·
            refine ⟨8412745870283566716395747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5608497246855711144263831 8412745870283566716395747)
            ·
              refine ⟨12619118805425350074593621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8412745870283566716395747 12619118805425350074593621)
              ·
                refine ⟨36970074625269580296661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12619118805425350074593621 36970074625269580296661)
                ·
                  rfl

theorem cell22_971986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 10].length) (baseStart_971986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_971986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_971986 prefixEnd_971986 := by exact prefixLift 971986
  have htrace : WordTrace (prefixWord ++ tailWord_971986) baseStart_971986 baseEnd_971986 := by
    simpa [prefixWord, tailWord_971986, baseEnd_971986] using wordTrace_append hprefix tailTrace_971986
  have hstable : (prefixWord ++ tailWord_971986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971986).length < 2 ^ (prefixWord ++ tailWord_971986).sum := by decide
  have hdescent : baseEnd_971986 < baseStart_971986 := by decide
  rcases family_descends (prefixWord ++ tailWord_971986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972007 : List Nat := [1, 1, 5, 3, 2, 1, 2, 2, 2, 3]
def baseStart_972007 : Nat := 118140960795 + 972007 * 2 ^ 59
def prefixEnd_972007 : Nat := 4983230072969 + 3 ^ 40 * 972007 * 2
def baseEnd_972007 : Nat := 332737860356589167894885

theorem tailTrace_972007 : CollatzResearch.WordTrace tailWord_972007 prefixEnd_972007 332737860356589167894885 := by
  unfold tailWord_972007
  simp only [CollatzResearch.WordTrace]
  refine ⟨35452007789592119424330275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23634671859728079616220183 35452007789592119424330275)
  ·
    refine ⟨53178011684388179136495413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35452007789592119424330275 53178011684388179136495413)
    ·
      refine ⟨4985438595411391794046445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53178011684388179136495413 4985438595411391794046445)
      ·
        refine ⟨1869539473279271922767417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4985438595411391794046445 1869539473279271922767417)
        ·
          refine ⟨1402154604959453942075563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1869539473279271922767417 1402154604959453942075563)
          ·
            refine ⟨2103231907439180913113345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1402154604959453942075563 2103231907439180913113345)
            ·
              refine ⟨1577423930579385684835009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2103231907439180913113345 1577423930579385684835009)
              ·
                refine ⟨1183067947934539263626257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1577423930579385684835009 1183067947934539263626257)
                ·
                  refine ⟨887300960950904447719693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1183067947934539263626257 887300960950904447719693)
                  ·
                    refine ⟨332737860356589167894885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 887300960950904447719693 332737860356589167894885)
                    ·
                      rfl

theorem cell22_972007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_972007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_972007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_972007 prefixEnd_972007 := by exact prefixLift 972007
  have htrace : WordTrace (prefixWord ++ tailWord_972007) baseStart_972007 baseEnd_972007 := by
    simpa [prefixWord, tailWord_972007, baseEnd_972007] using wordTrace_append hprefix tailTrace_972007
  have hstable : (prefixWord ++ tailWord_972007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972007).length < 2 ^ (prefixWord ++ tailWord_972007).sum := by decide
  have hdescent : baseEnd_972007 < baseStart_972007 := by decide
  rcases family_descends (prefixWord ++ tailWord_972007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972095 : List Nat := [1, 1, 2, 2, 4, 3, 2, 2, 1, 4]
def baseStart_972095 : Nat := 118140960795 + 972095 * 2 ^ 59
def prefixEnd_972095 : Nat := 4983230072969 + 3 ^ 40 * 972095 * 2
def baseEnd_972095 : Nat := 332767984554986271694615

theorem tailTrace_972095 : CollatzResearch.WordTrace tailWord_972095 prefixEnd_972095 332767984554986271694615 := by
  unfold tailWord_972095
  simp only [CollatzResearch.WordTrace]
  refine ⟨35455217413273310453533739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23636811608848873635689159 35455217413273310453533739)
  ·
    refine ⟨53182826119909965680300609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35455217413273310453533739 53182826119909965680300609)
    ·
      refine ⟨39887119589932474260225457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53182826119909965680300609 39887119589932474260225457)
      ·
        refine ⟨29915339692449355695169093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39887119589932474260225457 29915339692449355695169093)
        ·
          refine ⟨5609126192334254192844205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29915339692449355695169093 5609126192334254192844205)
          ·
            refine ⟨2103422322125345322316577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5609126192334254192844205 2103422322125345322316577)
            ·
              refine ⟨1577566741594008991737433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2103422322125345322316577 1577566741594008991737433)
              ·
                refine ⟨1183175056195506743803075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1577566741594008991737433 1183175056195506743803075)
                ·
                  refine ⟨1774762584293260115704613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1183175056195506743803075 1774762584293260115704613)
                  ·
                    refine ⟨332767984554986271694615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1774762584293260115704613 332767984554986271694615)
                    ·
                      rfl

theorem cell22_972095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 4].length) (baseStart_972095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_972095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_972095 prefixEnd_972095 := by exact prefixLift 972095
  have htrace : WordTrace (prefixWord ++ tailWord_972095) baseStart_972095 baseEnd_972095 := by
    simpa [prefixWord, tailWord_972095, baseEnd_972095] using wordTrace_append hprefix tailTrace_972095
  have hstable : (prefixWord ++ tailWord_972095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972095).length < 2 ^ (prefixWord ++ tailWord_972095).sum := by decide
  have hdescent : baseEnd_972095 < baseStart_972095 := by decide
  rcases family_descends (prefixWord ++ tailWord_972095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972121 : List Nat := [1, 2, 1, 2, 2, 2, 12]
def baseStart_972121 : Nat := 118140960795 + 972121 * 2 ^ 59
def prefixEnd_972121 : Nat := 4983230072969 + 3 ^ 40 * 972121 * 2
def baseEnd_972121 : Nat := 12325069810604847057205

theorem tailTrace_972121 : CollatzResearch.WordTrace tailWord_972121 prefixEnd_972121 12325069810604847057205 := by
  unfold tailWord_972121
  simp only [CollatzResearch.WordTrace]
  refine ⟨35456165711179116893980217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23637443807452744595986811 35456165711179116893980217)
  ·
    refine ⟨26592124283384337670485163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35456165711179116893980217 26592124283384337670485163)
    ·
      refine ⟨39888186425076506505727745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26592124283384337670485163 39888186425076506505727745)
      ·
        refine ⟨29916139818807379879295809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39888186425076506505727745 29916139818807379879295809)
        ·
          refine ⟨22437104864105534909471857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29916139818807379879295809 22437104864105534909471857)
          ·
            refine ⟨16827828648079151182103893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22437104864105534909471857 16827828648079151182103893)
            ·
              refine ⟨12325069810604847057205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 16827828648079151182103893 12325069810604847057205)
              ·
                rfl

theorem cell22_972121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 12].length) (baseStart_972121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_972121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_972121 prefixEnd_972121 := by exact prefixLift 972121
  have htrace : WordTrace (prefixWord ++ tailWord_972121) baseStart_972121 baseEnd_972121 := by
    simpa [prefixWord, tailWord_972121, baseEnd_972121] using wordTrace_append hprefix tailTrace_972121
  have hstable : (prefixWord ++ tailWord_972121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972121).length < 2 ^ (prefixWord ++ tailWord_972121).sum := by decide
  have hdescent : baseEnd_972121 < baseStart_972121 := by decide
  rcases family_descends (prefixWord ++ tailWord_972121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972178 : List Nat := [3, 2, 3, 3, 2, 1, 2, 2, 4]
def baseStart_972178 : Nat := 118140960795 + 972178 * 2 ^ 59
def prefixEnd_972178 : Nat := 4983230072969 + 3 ^ 40 * 972178 * 2
def baseEnd_972178 : Nat := 110932132383733907289787

theorem tailTrace_972178 : CollatzResearch.WordTrace tailWord_972178 prefixEnd_972178 110932132383733907289787 := by
  unfold tailWord_972178
  simp only [CollatzResearch.WordTrace]
  refine ⟨8864561167993153907201297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23638829781315077085870125 8864561167993153907201297)
  ·
    refine ⟨6648420875994865430400973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8864561167993153907201297 6648420875994865430400973)
    ·
      refine ⟨2493157828498074536400365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6648420875994865430400973 2493157828498074536400365)
      ·
        refine ⟨934934185686777951150137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2493157828498074536400365 934934185686777951150137)
        ·
          refine ⟨701200639265083463362603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 934934185686777951150137 701200639265083463362603)
          ·
            refine ⟨1051800958897625195043905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701200639265083463362603 1051800958897625195043905)
            ·
              refine ⟨788850719173218896282929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1051800958897625195043905 788850719173218896282929)
              ·
                refine ⟨591638039379914172212197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 788850719173218896282929 591638039379914172212197)
                ·
                  refine ⟨110932132383733907289787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 591638039379914172212197 110932132383733907289787)
                  ·
                    rfl

theorem cell22_972178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_972178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_972178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_972178 prefixEnd_972178 := by exact prefixLift 972178
  have htrace : WordTrace (prefixWord ++ tailWord_972178) baseStart_972178 baseEnd_972178 := by
    simpa [prefixWord, tailWord_972178, baseEnd_972178] using wordTrace_append hprefix tailTrace_972178
  have hstable : (prefixWord ++ tailWord_972178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972178).length < 2 ^ (prefixWord ++ tailWord_972178).sum := by decide
  have hdescent : baseEnd_972178 < baseStart_972178 := by decide
  rcases family_descends (prefixWord ++ tailWord_972178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972245 : List Nat := [1, 3, 2, 3, 1, 1, 4, 1, 6]
def baseStart_972245 : Nat := 118140960795 + 972245 * 2 ^ 59
def prefixEnd_972245 : Nat := 4983230072969 + 3 ^ 40 * 972245 * 2
def baseEnd_972245 : Nat := 110939777540145293481385

theorem tailTrace_972245 : CollatzResearch.WordTrace tailWord_972245 prefixEnd_972245 110939777540145293481385 := by
  unfold tailWord_972245
  simp only [CollatzResearch.WordTrace]
  refine ⟨35460688362729886071494189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23640458908486590714329459 35460688362729886071494189)
  ·
    refine ⟨13297758136023707276810321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35460688362729886071494189 13297758136023707276810321)
    ·
      refine ⟨9973318602017780457607741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13297758136023707276810321 9973318602017780457607741)
      ·
        refine ⟨3739994475756667671602903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9973318602017780457607741 3739994475756667671602903)
        ·
          refine ⟨5609991713635001507404355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3739994475756667671602903 5609991713635001507404355)
          ·
            refine ⟨8414987570452502261106533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5609991713635001507404355 8414987570452502261106533)
            ·
              refine ⟨1577810169459844173957475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8414987570452502261106533 1577810169459844173957475)
              ·
                refine ⟨2366715254189766260936213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1577810169459844173957475 2366715254189766260936213)
                ·
                  refine ⟨110939777540145293481385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2366715254189766260936213 110939777540145293481385)
                  ·
                    rfl

theorem cell22_972245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 6].length) (baseStart_972245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_972245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_972245 prefixEnd_972245 := by exact prefixLift 972245
  have htrace : WordTrace (prefixWord ++ tailWord_972245) baseStart_972245 baseEnd_972245 := by
    simpa [prefixWord, tailWord_972245, baseEnd_972245] using wordTrace_append hprefix tailTrace_972245
  have hstable : (prefixWord ++ tailWord_972245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972245).length < 2 ^ (prefixWord ++ tailWord_972245).sum := by decide
  have hdescent : baseEnd_972245 < baseStart_972245 := by decide
  rcases family_descends (prefixWord ++ tailWord_972245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972322 : List Nat := [3, 3, 1, 1, 1, 1, 2, 4, 3, 3]
def baseStart_972322 : Nat := 118140960795 + 972322 * 2 ^ 59
def prefixEnd_972322 : Nat := 4983230072969 + 3 ^ 40 * 972322 * 2
def baseEnd_972322 : Nat := 332845691294033346268919

theorem tailTrace_972322 : CollatzResearch.WordTrace tailWord_972322 prefixEnd_972322 332845691294033346268919 := by
  unfold tailWord_972322
  simp only [CollatzResearch.WordTrace]
  refine ⟨8865874195862732055511805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23642331188967285481364813 8865874195862732055511805)
  ·
    refine ⟨3324702823448524520816927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8865874195862732055511805 3324702823448524520816927)
    ·
      refine ⟨4987054235172786781225391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3324702823448524520816927 4987054235172786781225391)
      ·
        refine ⟨7480581352759180171838087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4987054235172786781225391 7480581352759180171838087)
        ·
          refine ⟨11220872029138770257757131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7480581352759180171838087 11220872029138770257757131)
          ·
            refine ⟨16831308043708155386635697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11220872029138770257757131 16831308043708155386635697)
            ·
              refine ⟨12623481032781116539976773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16831308043708155386635697 12623481032781116539976773)
              ·
                refine ⟨2366902693646459351245645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12623481032781116539976773 2366902693646459351245645)
                ·
                  refine ⟨887588510117422256717117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2366902693646459351245645 887588510117422256717117)
                  ·
                    refine ⟨332845691294033346268919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 887588510117422256717117 332845691294033346268919)
                    ·
                      rfl

theorem cell22_972322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_972322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_972322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_972322 prefixEnd_972322 := by exact prefixLift 972322
  have htrace : WordTrace (prefixWord ++ tailWord_972322) baseStart_972322 baseEnd_972322 := by
    simpa [prefixWord, tailWord_972322, baseEnd_972322] using wordTrace_append hprefix tailTrace_972322
  have hstable : (prefixWord ++ tailWord_972322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972322).length < 2 ^ (prefixWord ++ tailWord_972322).sum := by decide
  have hdescent : baseEnd_972322 < baseStart_972322 := by decide
  rcases family_descends (prefixWord ++ tailWord_972322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972474 : List Nat := [3, 1, 1, 1, 2, 4, 3, 1, 3, 3]
def baseStart_972474 : Nat := 118140960795 + 972474 * 2 ^ 59
def prefixEnd_972474 : Nat := 4983230072969 + 3 ^ 40 * 972474 * 2
def baseEnd_972474 : Nat := 332897724000355616468453

theorem tailTrace_972474 : CollatzResearch.WordTrace tailWord_972474 prefixEnd_972474 332897724000355616468453 := by
  unfold tailWord_972474
  simp only [CollatzResearch.WordTrace]
  refine ⟨8867260169725064545395119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23646027119266838787720317 8867260169725064545395119)
  ·
    refine ⟨13300890254587596818092679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8867260169725064545395119 13300890254587596818092679)
    ·
      refine ⟨19951335381881395227139019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13300890254587596818092679 19951335381881395227139019)
      ·
        refine ⟨29927003072822092840708529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19951335381881395227139019 29927003072822092840708529)
        ·
          refine ⟨22445252304616569630531397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29927003072822092840708529 22445252304616569630531397)
          ·
            refine ⟨4208484807115606805724637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22445252304616569630531397 4208484807115606805724637)
            ·
              refine ⟨1578181802668352552146739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4208484807115606805724637 1578181802668352552146739)
              ·
                refine ⟨2367272704002528828220109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1578181802668352552146739 2367272704002528828220109)
                ·
                  refine ⟨887727264000948310582541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2367272704002528828220109 887727264000948310582541)
                  ·
                    refine ⟨332897724000355616468453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 887727264000948310582541 332897724000355616468453)
                    ·
                      rfl

theorem cell22_972474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 3, 3].length) (baseStart_972474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_972474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_972474 prefixEnd_972474 := by exact prefixLift 972474
  have htrace : WordTrace (prefixWord ++ tailWord_972474) baseStart_972474 baseEnd_972474 := by
    simpa [prefixWord, tailWord_972474, baseEnd_972474] using wordTrace_append hprefix tailTrace_972474
  have hstable : (prefixWord ++ tailWord_972474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972474).length < 2 ^ (prefixWord ++ tailWord_972474).sum := by decide
  have hdescent : baseEnd_972474 < baseStart_972474 := by decide
  rcases family_descends (prefixWord ++ tailWord_972474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972487 : List Nat := [1, 1, 4, 1, 1, 1, 5, 3, 5]
def baseStart_972487 : Nat := 118140960795 + 972487 * 2 ^ 59
def prefixEnd_972487 : Nat := 4983230072969 + 3 ^ 40 * 972487 * 2
def baseEnd_972487 : Nat := 110967391388675971964471

theorem tailTrace_972487 : CollatzResearch.WordTrace tailWord_972487 prefixEnd_972487 110967391388675971964471 := by
  unfold tailWord_972487
  simp only [CollatzResearch.WordTrace]
  refine ⟨35469514827853161401803715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23646343218568774267869143 35469514827853161401803715)
  ·
    refine ⟨53204272241779742102705573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35469514827853161401803715 53204272241779742102705573)
    ·
      refine ⟨9975801045333701644257295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53204272241779742102705573 9975801045333701644257295)
      ·
        refine ⟨14963701568000552466385943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9975801045333701644257295 14963701568000552466385943)
        ·
          refine ⟨22445552352000828699578915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14963701568000552466385943 22445552352000828699578915)
          ·
            refine ⟨33668328528001243049368373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22445552352000828699578915 33668328528001243049368373)
            ·
              refine ⟨3156405799500116535878285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33668328528001243049368373 3156405799500116535878285)
              ·
                refine ⟨1183652174812543700954357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3156405799500116535878285 1183652174812543700954357)
                ·
                  refine ⟨110967391388675971964471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1183652174812543700954357 110967391388675971964471)
                  ·
                    rfl

theorem cell22_972487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 5].length) (baseStart_972487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_972487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_972487 prefixEnd_972487 := by exact prefixLift 972487
  have htrace : WordTrace (prefixWord ++ tailWord_972487) baseStart_972487 baseEnd_972487 := by
    simpa [prefixWord, tailWord_972487, baseEnd_972487] using wordTrace_append hprefix tailTrace_972487
  have hstable : (prefixWord ++ tailWord_972487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972487).length < 2 ^ (prefixWord ++ tailWord_972487).sum := by decide
  have hdescent : baseEnd_972487 < baseStart_972487 := by decide
  rcases family_descends (prefixWord ++ tailWord_972487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972525 : List Nat := [1, 5, 1, 2, 1, 4, 2, 2, 1, 3]
def baseStart_972525 : Nat := 118140960795 + 972525 * 2 ^ 59
def prefixEnd_972525 : Nat := 4983230072969 + 3 ^ 40 * 972525 * 2
def baseEnd_972525 : Nat := 332915182342608483443297

theorem tailTrace_972525 : CollatzResearch.WordTrace tailWord_972525 prefixEnd_972525 332915182342608483443297 := by
  unfold tailWord_972525
  simp only [CollatzResearch.WordTrace]
  refine ⟨35470900801715493891687029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23647267201143662594458019 35470900801715493891687029)
  ·
    refine ⟨3325396950160827552345659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35470900801715493891687029 3325396950160827552345659)
    ·
      refine ⟨4988095425241241328518489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3325396950160827552345659 4988095425241241328518489)
      ·
        refine ⟨3741071568930930996388867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4988095425241241328518489 3741071568930930996388867)
        ·
          refine ⟨5611607353396396494583301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3741071568930930996388867 5611607353396396494583301)
          ·
            refine ⟨1052176378761824342734369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5611607353396396494583301 1052176378761824342734369)
            ·
              refine ⟨789132284071368257050777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1052176378761824342734369 789132284071368257050777)
              ·
                refine ⟨591849213053526192788083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 789132284071368257050777 591849213053526192788083)
                ·
                  refine ⟨887773819580289289182125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 591849213053526192788083 887773819580289289182125)
                  ·
                    refine ⟨332915182342608483443297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 887773819580289289182125 332915182342608483443297)
                    ·
                      rfl

theorem cell22_972525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_972525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_972525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_972525 prefixEnd_972525 := by exact prefixLift 972525
  have htrace : WordTrace (prefixWord ++ tailWord_972525) baseStart_972525 baseEnd_972525 := by
    simpa [prefixWord, tailWord_972525, baseEnd_972525] using wordTrace_append hprefix tailTrace_972525
  have hstable : (prefixWord ++ tailWord_972525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972525).length < 2 ^ (prefixWord ++ tailWord_972525).sum := by decide
  have hdescent : baseEnd_972525 < baseStart_972525 := by decide
  rcases family_descends (prefixWord ++ tailWord_972525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972534 : List Nat := [5, 1, 1, 1, 1, 3, 1, 2, 3, 4]
def baseStart_972534 : Nat := 118140960795 + 972534 * 2 ^ 59
def prefixEnd_972534 : Nat := 4983230072969 + 3 ^ 40 * 972534 * 2
def baseEnd_972534 : Nat := 332918263226535459968269

theorem tailTrace_972534 : CollatzResearch.WordTrace tailWord_972534 prefixEnd_972534 332918263226535459968269 := by
  unfold tailWord_972534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2216951816167680526797791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23647486039121925619176437 2216951816167680526797791)
  ·
    refine ⟨3325427724251520790196687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2216951816167680526797791 3325427724251520790196687)
    ·
      refine ⟨4988141586377281185295031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3325427724251520790196687 4988141586377281185295031)
      ·
        refine ⟨7482212379565921777942547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4988141586377281185295031 7482212379565921777942547)
        ·
          refine ⟨11223318569348882666913821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7482212379565921777942547 11223318569348882666913821)
          ·
            refine ⟨4208744463505831000092683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11223318569348882666913821 4208744463505831000092683)
            ·
              refine ⟨6313116695258746500139025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4208744463505831000092683 6313116695258746500139025)
              ·
                refine ⟨4734837521444059875104269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6313116695258746500139025 4734837521444059875104269)
                ·
                  refine ⟨1775564070541522453164101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4734837521444059875104269 1775564070541522453164101)
                  ·
                    refine ⟨332918263226535459968269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1775564070541522453164101 332918263226535459968269)
                    ·
                      rfl

theorem cell22_972534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_972534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_972534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_972534 prefixEnd_972534 := by exact prefixLift 972534
  have htrace : WordTrace (prefixWord ++ tailWord_972534) baseStart_972534 baseEnd_972534 := by
    simpa [prefixWord, tailWord_972534, baseEnd_972534] using wordTrace_append hprefix tailTrace_972534
  have hstable : (prefixWord ++ tailWord_972534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972534).length < 2 ^ (prefixWord ++ tailWord_972534).sum := by decide
  have hdescent : baseEnd_972534 < baseStart_972534 := by decide
  rcases family_descends (prefixWord ++ tailWord_972534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972547 : List Nat := [1, 1, 1, 3, 2, 2, 3, 3, 1, 5]
def baseStart_972547 : Nat := 118140960795 + 972547 * 2 ^ 59
def prefixEnd_972547 : Nat := 4983230072969 + 3 ^ 40 * 972547 * 2
def baseEnd_972547 : Nat := 332922713392207759393229

theorem tailTrace_972547 : CollatzResearch.WordTrace tailWord_972547 prefixEnd_972547 332922713392207759393229 := by
  unfold tailWord_972547
  simp only [CollatzResearch.WordTrace]
  refine ⟨35471703207635791648987895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23647802138423861099325263 35471703207635791648987895)
  ·
    refine ⟨53207554811453687473481843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35471703207635791648987895 53207554811453687473481843)
    ·
      refine ⟨79811332217180531210222765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53207554811453687473481843 79811332217180531210222765)
      ·
        refine ⟨29929249581442699203833537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79811332217180531210222765 29929249581442699203833537)
        ·
          refine ⟨22446937186082024402875153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29929249581442699203833537 22446937186082024402875153)
          ·
            refine ⟨16835202889561518302156365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22446937186082024402875153 16835202889561518302156365)
            ·
              refine ⟨6313201083585569363308637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16835202889561518302156365 6313201083585569363308637)
              ·
                refine ⟨2367450406344588511240739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6313201083585569363308637 2367450406344588511240739)
                ·
                  refine ⟨3551175609516882766861109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2367450406344588511240739 3551175609516882766861109)
                  ·
                    refine ⟨332922713392207759393229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3551175609516882766861109 332922713392207759393229)
                    ·
                      rfl

theorem cell22_972547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 5].length) (baseStart_972547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_972547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_972547 prefixEnd_972547 := by exact prefixLift 972547
  have htrace : WordTrace (prefixWord ++ tailWord_972547) baseStart_972547 baseEnd_972547 := by
    simpa [prefixWord, tailWord_972547, baseEnd_972547] using wordTrace_append hprefix tailTrace_972547
  have hstable : (prefixWord ++ tailWord_972547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972547).length < 2 ^ (prefixWord ++ tailWord_972547).sum := by decide
  have hdescent : baseEnd_972547 < baseStart_972547 := by decide
  rcases family_descends (prefixWord ++ tailWord_972547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972577 : List Nat := [1, 2, 3, 2, 1, 4, 9]
def baseStart_972577 : Nat := 118140960795 + 972577 * 2 ^ 59
def prefixEnd_972577 : Nat := 4983230072969 + 3 ^ 40 * 972577 * 2
def baseEnd_972577 : Nat := 12330851222418432634931

theorem tailTrace_972577 : CollatzResearch.WordTrace tailWord_972577 prefixEnd_972577 12330851222418432634931 := by
  unfold tailWord_972577
  simp only [CollatzResearch.WordTrace]
  refine ⟨35472797397527106772579985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23648531598351404515053323 35472797397527106772579985)
  ·
    refine ⟨26604598048145330079434989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35472797397527106772579985 26604598048145330079434989)
    ·
      refine ⟨9976724268054498779788121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26604598048145330079434989 9976724268054498779788121)
      ·
        refine ⟨7482543201040874084841091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9976724268054498779788121 7482543201040874084841091)
        ·
          refine ⟨11223814801561311127261637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7482543201040874084841091 11223814801561311127261637)
          ·
            refine ⟨2104465275292745836361557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11223814801561311127261637 2104465275292745836361557)
            ·
              refine ⟨12330851222418432634931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2104465275292745836361557 12330851222418432634931)
              ·
                rfl

theorem cell22_972577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 9].length) (baseStart_972577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_972577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_972577 prefixEnd_972577 := by exact prefixLift 972577
  have htrace : WordTrace (prefixWord ++ tailWord_972577) baseStart_972577 baseEnd_972577 := by
    simpa [prefixWord, tailWord_972577, baseEnd_972577] using wordTrace_append hprefix tailTrace_972577
  have hstable : (prefixWord ++ tailWord_972577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972577).length < 2 ^ (prefixWord ++ tailWord_972577).sum := by decide
  have hdescent : baseEnd_972577 < baseStart_972577 := by decide
  rcases family_descends (prefixWord ++ tailWord_972577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972581 : List Nat := [1, 3, 1, 2, 3, 2, 3, 2, 2, 3]
def baseStart_972581 : Nat := 118140960795 + 972581 * 2 ^ 59
def prefixEnd_972581 : Nat := 4983230072969 + 3 ^ 40 * 972581 * 2
def baseEnd_972581 : Nat := 332934352287043004043125

theorem tailTrace_972581 : CollatzResearch.WordTrace tailWord_972581 prefixEnd_972581 332934352287043004043125 := by
  unfold tailWord_972581
  simp only [CollatzResearch.WordTrace]
  refine ⟨35472943289512615455725597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23648628859675076970483731 35472943289512615455725597)
  ·
    refine ⟨13302353733567230795897099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35472943289512615455725597 13302353733567230795897099)
    ·
      refine ⟨19953530600350846193845649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13302353733567230795897099 19953530600350846193845649)
      ·
        refine ⟨14965147950263134645384237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19953530600350846193845649 14965147950263134645384237)
        ·
          refine ⟨5611930481348675492019089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14965147950263134645384237 5611930481348675492019089)
          ·
            refine ⟨4208947861011506619014317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5611930481348675492019089 4208947861011506619014317)
            ·
              refine ⟨1578355447879314982130369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4208947861011506619014317 1578355447879314982130369)
              ·
                refine ⟨1183766585909486236597777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1578355447879314982130369 1183766585909486236597777)
                ·
                  refine ⟨887824939432114677448333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1183766585909486236597777 887824939432114677448333)
                  ·
                    refine ⟨332934352287043004043125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 887824939432114677448333 332934352287043004043125)
                    ·
                      rfl

theorem cell22_972581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 2, 3].length) (baseStart_972581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_972581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_972581 prefixEnd_972581 := by exact prefixLift 972581
  have htrace : WordTrace (prefixWord ++ tailWord_972581) baseStart_972581 baseEnd_972581 := by
    simpa [prefixWord, tailWord_972581, baseEnd_972581] using wordTrace_append hprefix tailTrace_972581
  have hstable : (prefixWord ++ tailWord_972581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972581).length < 2 ^ (prefixWord ++ tailWord_972581).sum := by decide
  have hdescent : baseEnd_972581 < baseStart_972581 := by decide
  rcases family_descends (prefixWord ++ tailWord_972581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972598 : List Nat := [5, 1, 2, 2, 1, 3, 1, 1, 1, 5]
def baseStart_972598 : Nat := 118140960795 + 972598 * 2 ^ 59
def prefixEnd_972598 : Nat := 4983230072969 + 3 ^ 40 * 972598 * 2
def baseEnd_972598 : Nat := 332940171734460626368073

theorem tailTrace_972598 : CollatzResearch.WordTrace tailWord_972598 prefixEnd_972598 332940171734460626368073 := by
  unfold tailWord_972598
  simp only [CollatzResearch.WordTrace]
  refine ⟨2217097708153189209943403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23649042220300684906062965 2217097708153189209943403)
  ·
    refine ⟨3325646562229783814915105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2217097708153189209943403 3325646562229783814915105)
    ·
      refine ⟨2494234921672337861186329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3325646562229783814915105 2494234921672337861186329)
      ·
        refine ⟨1870676191254253395889747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2494234921672337861186329 1870676191254253395889747)
        ·
          refine ⟨2806014286881380093834621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1870676191254253395889747 2806014286881380093834621)
          ·
            refine ⟨1052255357580517535187983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2806014286881380093834621 1052255357580517535187983)
            ·
              refine ⟨1578383036370776302781975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052255357580517535187983 1578383036370776302781975)
              ·
                refine ⟨2367574554556164454172963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1578383036370776302781975 2367574554556164454172963)
                ·
                  refine ⟨3551361831834246681259445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2367574554556164454172963 3551361831834246681259445)
                  ·
                    refine ⟨332940171734460626368073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3551361831834246681259445 332940171734460626368073)
                    ·
                      rfl

theorem cell22_972598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_972598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_972598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_972598 prefixEnd_972598 := by exact prefixLift 972598
  have htrace : WordTrace (prefixWord ++ tailWord_972598) baseStart_972598 baseEnd_972598 := by
    simpa [prefixWord, tailWord_972598, baseEnd_972598] using wordTrace_append hprefix tailTrace_972598
  have hstable : (prefixWord ++ tailWord_972598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972598).length < 2 ^ (prefixWord ++ tailWord_972598).sum := by decide
  have hdescent : baseEnd_972598 < baseStart_972598 := by decide
  rcases family_descends (prefixWord ++ tailWord_972598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972643 : List Nat := [1, 1, 1, 5, 4, 2, 1, 1, 3, 3]
def baseStart_972643 : Nat := 118140960795 + 972643 * 2 ^ 59
def prefixEnd_972643 : Nat := 4983230072969 + 3 ^ 40 * 972643 * 2
def baseEnd_972643 : Nat := 332955576154095508992935

theorem tailTrace_972643 : CollatzResearch.WordTrace tailWord_972643 prefixEnd_972643 332955576154095508992935 := by
  unfold tailWord_972643
  simp only [CollatzResearch.WordTrace]
  refine ⟨35475204615288000044482583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23650136410192000029655055 35475204615288000044482583)
  ·
    refine ⟨53212806922932000066723875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35475204615288000044482583 53212806922932000066723875)
    ·
      refine ⟨79819210384398000100085813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53212806922932000066723875 79819210384398000100085813)
      ·
        refine ⟨7483050973537312509383045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79819210384398000100085813 7483050973537312509383045)
        ·
          refine ⟨1403072057538246095509321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7483050973537312509383045 1403072057538246095509321)
          ·
            refine ⟨1052304043153684571631991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1403072057538246095509321 1052304043153684571631991)
            ·
              refine ⟨1578456064730526857447987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052304043153684571631991 1578456064730526857447987)
              ·
                refine ⟨2367684097095790286171981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1578456064730526857447987 2367684097095790286171981)
                ·
                  refine ⟨887881536410921357314493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2367684097095790286171981 887881536410921357314493)
                  ·
                    refine ⟨332955576154095508992935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 887881536410921357314493 332955576154095508992935)
                    ·
                      rfl

theorem cell22_972643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 3, 3].length) (baseStart_972643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_972643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_972643 prefixEnd_972643 := by exact prefixLift 972643
  have htrace : WordTrace (prefixWord ++ tailWord_972643) baseStart_972643 baseEnd_972643 := by
    simpa [prefixWord, tailWord_972643, baseEnd_972643] using wordTrace_append hprefix tailTrace_972643
  have hstable : (prefixWord ++ tailWord_972643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972643).length < 2 ^ (prefixWord ++ tailWord_972643).sum := by decide
  have hdescent : baseEnd_972643 < baseStart_972643 := by decide
  rcases family_descends (prefixWord ++ tailWord_972643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972667 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 8]
def baseStart_972667 : Nat := 118140960795 + 972667 * 2 ^ 59
def prefixEnd_972667 : Nat := 4983230072969 + 3 ^ 40 * 972667 * 2
def baseEnd_972667 : Nat := 110987930614855815464287

theorem tailTrace_972667 : CollatzResearch.WordTrace tailWord_972667 prefixEnd_972667 110987930614855815464287 := by
  unfold tailWord_972667
  simp only [CollatzResearch.WordTrace]
  refine ⟨35476079967201052143356255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23650719978134034762237503 35476079967201052143356255)
  ·
    refine ⟨53214119950801578215034383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35476079967201052143356255 53214119950801578215034383)
    ·
      refine ⟨79821179926202367322551575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53214119950801578215034383 79821179926202367322551575)
      ·
        refine ⟨119731769889303550983827363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79821179926202367322551575 119731769889303550983827363)
        ·
          refine ⟨179597654833955326475741045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119731769889303550983827363 179597654833955326475741045)
          ·
            refine ⟨16837280140683311857100723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 179597654833955326475741045 16837280140683311857100723)
            ·
              refine ⟨25255920211024967785651085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16837280140683311857100723 25255920211024967785651085)
              ·
                refine ⟨9470970079134362919619157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25255920211024967785651085 9470970079134362919619157)
                ·
                  refine ⟨110987930614855815464287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9470970079134362919619157 110987930614855815464287)
                  ·
                    rfl

theorem cell22_972667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 8].length) (baseStart_972667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_972667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_972667 prefixEnd_972667 := by exact prefixLift 972667
  have htrace : WordTrace (prefixWord ++ tailWord_972667) baseStart_972667 baseEnd_972667 := by
    simpa [prefixWord, tailWord_972667, baseEnd_972667] using wordTrace_append hprefix tailTrace_972667
  have hstable : (prefixWord ++ tailWord_972667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972667).length < 2 ^ (prefixWord ++ tailWord_972667).sum := by decide
  have hdescent : baseEnd_972667 < baseStart_972667 := by decide
  rcases family_descends (prefixWord ++ tailWord_972667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972694 : List Nat := [5, 3, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_972694 : Nat := 118140960795 + 972694 * 2 ^ 59
def prefixEnd_972694 : Nat := 4983230072969 + 3 ^ 40 * 972694 * 2
def baseEnd_972694 : Nat := 332973034496348375967779

theorem tailTrace_972694 : CollatzResearch.WordTrace tailWord_972694 prefixEnd_972694 332973034496348375967779 := by
  unfold tailWord_972694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2217316546131452234661821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23651376492068823836392757 2217316546131452234661821)
  ·
    refine ⟨831493704799294587998183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2217316546131452234661821 831493704799294587998183)
    ·
      refine ⟨1247240557198941881997275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 831493704799294587998183 1247240557198941881997275)
      ·
        refine ⟨1870860835798412822995913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1247240557198941881997275 1870860835798412822995913)
        ·
          refine ⟨1403145626848809617246935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1870860835798412822995913 1403145626848809617246935)
          ·
            refine ⟨2104718440273214425870403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1403145626848809617246935 2104718440273214425870403)
            ·
              refine ⟨3157077660409821638805605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2104718440273214425870403 3157077660409821638805605)
              ·
                refine ⟨591952061326841557276051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3157077660409821638805605 591952061326841557276051)
                ·
                  refine ⟨887928091990262335914077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 591952061326841557276051 887928091990262335914077)
                  ·
                    refine ⟨332973034496348375967779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 887928091990262335914077 332973034496348375967779)
                    ·
                      rfl

theorem cell22_972694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_972694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_972694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_972694 prefixEnd_972694 := by exact prefixLift 972694
  have htrace : WordTrace (prefixWord ++ tailWord_972694) baseStart_972694 baseEnd_972694 := by
    simpa [prefixWord, tailWord_972694, baseEnd_972694] using wordTrace_append hprefix tailTrace_972694
  have hstable : (prefixWord ++ tailWord_972694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972694).length < 2 ^ (prefixWord ++ tailWord_972694).sum := by decide
  have hdescent : baseEnd_972694 < baseStart_972694 := by decide
  rcases family_descends (prefixWord ++ tailWord_972694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972851 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 6, 3]
def baseStart_972851 : Nat := 118140960795 + 972851 * 2 ^ 59
def prefixEnd_972851 : Nat := 4983230072969 + 3 ^ 40 * 972851 * 2
def baseEnd_972851 : Nat := 333026778804852299792297

theorem tailTrace_972851 : CollatzResearch.WordTrace tailWord_972851 prefixEnd_972851 333026778804852299792297 := by
  unfold tailWord_972851
  simp only [CollatzResearch.WordTrace]
  refine ⟨35482790998534451568054407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23655193999022967712036271 35482790998534451568054407)
  ·
    refine ⟨53224186497801677352081611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35482790998534451568054407 53224186497801677352081611)
    ·
      refine ⟨79836279746702516028122417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53224186497801677352081611 79836279746702516028122417)
      ·
        refine ⟨59877209810026887021091813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79836279746702516028122417 59877209810026887021091813)
        ·
          refine ⟨11226976839380041316454715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59877209810026887021091813 11226976839380041316454715)
          ·
            refine ⟨16840465259070061974682073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11226976839380041316454715 16840465259070061974682073)
            ·
              refine ⟨12630348944302546481011555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16840465259070061974682073 12630348944302546481011555)
              ·
                refine ⟨18945523416453819721517333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12630348944302546481011555 18945523416453819721517333)
                ·
                  refine ⟨888071410146272799446125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18945523416453819721517333 888071410146272799446125)
                  ·
                    refine ⟨333026778804852299792297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 888071410146272799446125 333026778804852299792297)
                    ·
                      rfl

theorem cell22_972851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 6, 3].length) (baseStart_972851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_972851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_972851 prefixEnd_972851 := by exact prefixLift 972851
  have htrace : WordTrace (prefixWord ++ tailWord_972851) baseStart_972851 baseEnd_972851 := by
    simpa [prefixWord, tailWord_972851, baseEnd_972851] using wordTrace_append hprefix tailTrace_972851
  have hstable : (prefixWord ++ tailWord_972851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972851).length < 2 ^ (prefixWord ++ tailWord_972851).sum := by decide
  have hdescent : baseEnd_972851 < baseStart_972851 := by decide
  rcases family_descends (prefixWord ++ tailWord_972851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972864 : List Nat := [2, 1, 1, 2, 2, 14]
def baseStart_972864 : Nat := 118140960795 + 972864 * 2 ^ 59
def prefixEnd_972864 : Nat := 4983230072969 + 3 ^ 40 * 972864 * 2
def baseEnd_972864 : Nat := 4111496653957093817497

theorem tailTrace_972864 : CollatzResearch.WordTrace tailWord_972864 prefixEnd_972864 4111496653957093817497 := by
  unfold tailWord_972864
  simp only [CollatzResearch.WordTrace]
  refine ⟨17741632573743677394138823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23655510098324903192185097 17741632573743677394138823)
  ·
    refine ⟨26612448860615516091208235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17741632573743677394138823 26612448860615516091208235)
    ·
      refine ⟨39918673290923274136812353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26612448860615516091208235 39918673290923274136812353)
      ·
        refine ⟨29939004968192455602609265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39918673290923274136812353 29939004968192455602609265)
        ·
          refine ⟨22454253726144341701956949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29939004968192455602609265 22454253726144341701956949)
          ·
            refine ⟨4111496653957093817497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 22454253726144341701956949 4111496653957093817497)
            ·
              rfl

theorem cell22_972864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 14].length) (baseStart_972864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_972864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_972864 prefixEnd_972864 := by exact prefixLift 972864
  have htrace : WordTrace (prefixWord ++ tailWord_972864) baseStart_972864 baseEnd_972864 := by
    simpa [prefixWord, tailWord_972864, baseEnd_972864] using wordTrace_append hprefix tailTrace_972864
  have hstable : (prefixWord ++ tailWord_972864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972864).length < 2 ^ (prefixWord ++ tailWord_972864).sum := by decide
  have hdescent : baseEnd_972864 < baseStart_972864 := by decide
  rcases family_descends (prefixWord ++ tailWord_972864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972964 : List Nat := [2, 3, 1, 2, 4, 2, 1, 3, 1, 3]
def baseStart_972964 : Nat := 118140960795 + 972964 * 2 ^ 59
def prefixEnd_972964 : Nat := 4983230072969 + 3 ^ 40 * 972964 * 2
def baseEnd_972964 : Nat := 333065461014157671716951

theorem tailTrace_972964 : CollatzResearch.WordTrace tailWord_972964 prefixEnd_972964 333065461014157671716951 := by
  unfold tailWord_972964
  simp only [CollatzResearch.WordTrace]
  refine ⟨17743456223562535933458973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23657941631416714577945297 17743456223562535933458973)
  ·
    refine ⟨6653796083835950975047115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17743456223562535933458973 6653796083835950975047115)
    ·
      refine ⟨9980694125753926462570673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6653796083835950975047115 9980694125753926462570673)
      ·
        refine ⟨7485520594315444846928005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9980694125753926462570673 7485520594315444846928005)
        ·
          refine ⟨1403535111434145908799001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7485520594315444846928005 1403535111434145908799001)
          ·
            refine ⟨1052651333575609431599251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1403535111434145908799001 1052651333575609431599251)
            ·
              refine ⟨1578977000363414147398877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052651333575609431599251 1578977000363414147398877)
              ·
                refine ⟨592116375136280305274579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1578977000363414147398877 592116375136280305274579)
                ·
                  refine ⟨888174562704420457911869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 592116375136280305274579 888174562704420457911869)
                  ·
                    refine ⟨333065461014157671716951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 888174562704420457911869 333065461014157671716951)
                    ·
                      rfl

theorem cell22_972964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_972964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_972964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_972964 prefixEnd_972964 := by exact prefixLift 972964
  have htrace : WordTrace (prefixWord ++ tailWord_972964) baseStart_972964 baseEnd_972964 := by
    simpa [prefixWord, tailWord_972964, baseEnd_972964] using wordTrace_append hprefix tailTrace_972964
  have hstable : (prefixWord ++ tailWord_972964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972964).length < 2 ^ (prefixWord ++ tailWord_972964).sum := by decide
  have hdescent : baseEnd_972964 < baseStart_972964 := by decide
  rcases family_descends (prefixWord ++ tailWord_972964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972981 : List Nat := [1, 3, 3, 4, 1, 1, 3, 2, 1, 3]
def baseStart_972981 : Nat := 118140960795 + 972981 * 2 ^ 59
def prefixEnd_972981 : Nat := 4983230072969 + 3 ^ 40 * 972981 * 2
def baseEnd_972981 : Nat := 333071280461575294041899

theorem tailTrace_972981 : CollatzResearch.WordTrace tailWord_972981 prefixEnd_972981 333071280461575294041899 := by
  unfold tailWord_972981
  simp only [CollatzResearch.WordTrace]
  refine ⟨35487532488063483770286797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23658354992042322513524531 35487532488063483770286797)
  ·
    refine ⟨13307824683023806413857549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35487532488063483770286797 13307824683023806413857549)
    ·
      refine ⟨4990434256133927405196581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13307824683023806413857549 4990434256133927405196581)
      ·
        refine ⟨935706423025111388474359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4990434256133927405196581 935706423025111388474359)
        ·
          refine ⟨1403559634537667082711539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 935706423025111388474359 1403559634537667082711539)
          ·
            refine ⟨2105339451806500624067309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1403559634537667082711539 2105339451806500624067309)
            ·
              refine ⟨789502294427437734025241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2105339451806500624067309 789502294427437734025241)
              ·
                refine ⟨592126720820578300518931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 789502294427437734025241 592126720820578300518931)
                ·
                  refine ⟨888190081230867450778397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 592126720820578300518931 888190081230867450778397)
                  ·
                    refine ⟨333071280461575294041899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 888190081230867450778397 333071280461575294041899)
                    ·
                      rfl

theorem cell22_972981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_972981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_972981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_972981 prefixEnd_972981 := by exact prefixLift 972981
  have htrace : WordTrace (prefixWord ++ tailWord_972981) baseStart_972981 baseEnd_972981 := by
    simpa [prefixWord, tailWord_972981, baseEnd_972981] using wordTrace_append hprefix tailTrace_972981
  have hstable : (prefixWord ++ tailWord_972981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972981).length < 2 ^ (prefixWord ++ tailWord_972981).sum := by decide
  have hdescent : baseEnd_972981 < baseStart_972981 := by decide
  rcases family_descends (prefixWord ++ tailWord_972981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972994 : List Nat := [3, 5, 1, 1, 1, 1, 4, 1, 5]
def baseStart_972994 : Nat := 118140960795 + 972994 * 2 ^ 59
def prefixEnd_972994 : Nat := 4983230072969 + 3 ^ 40 * 972994 * 2
def baseEnd_972994 : Nat := 111025243542415864488953

theorem tailTrace_972994 : CollatzResearch.WordTrace tailWord_972994 prefixEnd_972994 111025243542415864488953 := by
  unfold tailWord_972994
  simp only [CollatzResearch.WordTrace]
  refine ⟨8872001659254096747627509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23658671091344257993673357 8872001659254096747627509)
  ·
    refine ⟨831750155555071570090079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8872001659254096747627509 831750155555071570090079)
    ·
      refine ⟨1247625233332607355135119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 831750155555071570090079 1247625233332607355135119)
      ·
        refine ⟨1871437849998911032702679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1247625233332607355135119 1871437849998911032702679)
        ·
          refine ⟨2807156774998366549054019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1871437849998911032702679 2807156774998366549054019)
          ·
            refine ⟨4210735162497549823581029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2807156774998366549054019 4210735162497549823581029)
            ·
              refine ⟨789512842968290591921443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4210735162497549823581029 789512842968290591921443)
              ·
                refine ⟨1184269264452435887882165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789512842968290591921443 1184269264452435887882165)
                ·
                  refine ⟨111025243542415864488953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1184269264452435887882165 111025243542415864488953)
                  ·
                    rfl

theorem cell22_972994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_972994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_972994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_972994 prefixEnd_972994 := by exact prefixLift 972994
  have htrace : WordTrace (prefixWord ++ tailWord_972994) baseStart_972994 baseEnd_972994 := by
    simpa [prefixWord, tailWord_972994, baseEnd_972994] using wordTrace_append hprefix tailTrace_972994
  have hstable : (prefixWord ++ tailWord_972994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972994).length < 2 ^ (prefixWord ++ tailWord_972994).sum := by decide
  have hdescent : baseEnd_972994 < baseStart_972994 := by decide
  rcases family_descends (prefixWord ++ tailWord_972994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973001 : List Nat := [1, 2, 1, 1, 2, 1, 1, 6, 1, 6]
def baseStart_973001 : Nat := 118140960795 + 973001 * 2 ^ 59
def prefixEnd_973001 : Nat := 4983230072969 + 3 ^ 40 * 973001 * 2
def baseEnd_973001 : Nat := 333078126870301908541837

theorem tailTrace_973001 : CollatzResearch.WordTrace tailWord_973001 prefixEnd_973001 333078126870301908541837 := by
  unfold tailWord_973001
  simp only [CollatzResearch.WordTrace]
  refine ⟨35488261947991027186014857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23658841298660684790676571 35488261947991027186014857)
  ·
    refine ⟨26616196460993270389511143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35488261947991027186014857 26616196460993270389511143)
    ·
      refine ⟨39924294691489905584266715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26616196460993270389511143 39924294691489905584266715)
      ·
        refine ⟨59886442037234858376400073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39924294691489905584266715 59886442037234858376400073)
        ·
          refine ⟨44914831527926143782300055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59886442037234858376400073 44914831527926143782300055)
          ·
            refine ⟨67372247291889215673450083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44914831527926143782300055 67372247291889215673450083)
            ·
              refine ⟨101058370937833823510175125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67372247291889215673450083 101058370937833823510175125)
              ·
                refine ⟨4737111137710960477039459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101058370937833823510175125 4737111137710960477039459)
                ·
                  refine ⟨7105666706566440715559189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4737111137710960477039459 7105666706566440715559189)
                  ·
                    refine ⟨333078126870301908541837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7105666706566440715559189 333078126870301908541837)
                    ·
                      rfl

theorem cell22_973001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 6].length) (baseStart_973001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973001 prefixEnd_973001 := by exact prefixLift 973001
  have htrace : WordTrace (prefixWord ++ tailWord_973001) baseStart_973001 baseEnd_973001 := by
    simpa [prefixWord, tailWord_973001, baseEnd_973001] using wordTrace_append hprefix tailTrace_973001
  have hstable : (prefixWord ++ tailWord_973001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973001).length < 2 ^ (prefixWord ++ tailWord_973001).sum := by decide
  have hdescent : baseEnd_973001 < baseStart_973001 := by decide
  rcases family_descends (prefixWord ++ tailWord_973001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973018 : List Nat := [3, 1, 1, 2, 2, 1, 3, 3, 2, 4]
def baseStart_973018 : Nat := 118140960795 + 973018 * 2 ^ 59
def prefixEnd_973018 : Nat := 4983230072969 + 3 ^ 40 * 973018 * 2
def baseEnd_973018 : Nat := 333083946317719530866785

theorem tailTrace_973018 : CollatzResearch.WordTrace tailWord_973018 prefixEnd_973018 333083946317719530866785 := by
  unfold tailWord_973018
  simp only [CollatzResearch.WordTrace]
  refine ⟨8872220497232359772345927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23659254659286292726255805 8872220497232359772345927)
  ·
    refine ⟨13308330745848539658518891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8872220497232359772345927 13308330745848539658518891)
    ·
      refine ⟨19962496118772809487778337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13308330745848539658518891 19962496118772809487778337)
      ·
        refine ⟨14971872089079607115833753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19962496118772809487778337 14971872089079607115833753)
        ·
          refine ⟨11228904066809705336875315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14971872089079607115833753 11228904066809705336875315)
          ·
            refine ⟨16843356100214558005312973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11228904066809705336875315 16843356100214558005312973)
            ·
              refine ⟨6316258537580459251992365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16843356100214558005312973 6316258537580459251992365)
              ·
                refine ⟨2368596951592672219497137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6316258537580459251992365 2368596951592672219497137)
                ·
                  refine ⟨1776447713694504164622853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2368596951592672219497137 1776447713694504164622853)
                  ·
                    refine ⟨333083946317719530866785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1776447713694504164622853 333083946317719530866785)
                    ·
                      rfl

theorem cell22_973018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_973018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973018 prefixEnd_973018 := by exact prefixLift 973018
  have htrace : WordTrace (prefixWord ++ tailWord_973018) baseStart_973018 baseEnd_973018 := by
    simpa [prefixWord, tailWord_973018, baseEnd_973018] using wordTrace_append hprefix tailTrace_973018
  have hstable : (prefixWord ++ tailWord_973018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973018).length < 2 ^ (prefixWord ++ tailWord_973018).sum := by decide
  have hdescent : baseEnd_973018 < baseStart_973018 := by decide
  rcases family_descends (prefixWord ++ tailWord_973018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973048 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 7, 3]
def baseStart_973048 : Nat := 118140960795 + 973048 * 2 ^ 59
def prefixEnd_973048 : Nat := 4983230072969 + 3 ^ 40 * 973048 * 2
def baseEnd_973048 : Nat := 333094215930809452616693

theorem tailTrace_973048 : CollatzResearch.WordTrace tailWord_973048 prefixEnd_973048 333094215930809452616693 := by
  unfold tailWord_973048
  simp only [CollatzResearch.WordTrace]
  refine ⟨17744988089410377106487899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23659984119213836141983865 17744988089410377106487899)
  ·
    refine ⟨26617482134115565659731849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17744988089410377106487899 26617482134115565659731849)
    ·
      refine ⟨19963111600586674244798887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26617482134115565659731849 19963111600586674244798887)
      ·
        refine ⟨29944667400880011367198331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19963111600586674244798887 29944667400880011367198331)
        ·
          refine ⟨44917001101320017050797497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29944667400880011367198331 44917001101320017050797497)
          ·
            refine ⟨33687750825990012788098123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44917001101320017050797497 33687750825990012788098123)
            ·
              refine ⟨50531626238985019182147185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33687750825990012788098123 50531626238985019182147185)
              ·
                refine ⟨37898719679238764386610389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50531626238985019182147185 37898719679238764386610389)
                ·
                  refine ⟨888251242482158540311181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 37898719679238764386610389 888251242482158540311181)
                  ·
                    refine ⟨333094215930809452616693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 888251242482158540311181 333094215930809452616693)
                    ·
                      rfl

theorem cell22_973048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 7, 3].length) (baseStart_973048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973048 prefixEnd_973048 := by exact prefixLift 973048
  have htrace : WordTrace (prefixWord ++ tailWord_973048) baseStart_973048 baseEnd_973048 := by
    simpa [prefixWord, tailWord_973048, baseEnd_973048] using wordTrace_append hprefix tailTrace_973048
  have hstable : (prefixWord ++ tailWord_973048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973048).length < 2 ^ (prefixWord ++ tailWord_973048).sum := by decide
  have hdescent : baseEnd_973048 < baseStart_973048 := by decide
  rcases family_descends (prefixWord ++ tailWord_973048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973065 : List Nat := [1, 2, 1, 1, 3, 5, 1, 2, 3, 3]
def baseStart_973065 : Nat := 118140960795 + 973065 * 2 ^ 59
def prefixEnd_973065 : Nat := 4983230072969 + 3 ^ 40 * 973065 * 2
def baseEnd_973065 : Nat := 333100035378227074941641

theorem tailTrace_973065 : CollatzResearch.WordTrace tailWord_973065 prefixEnd_973065 333100035378227074941641 := by
  unfold tailWord_973065
  simp only [CollatzResearch.WordTrace]
  refine ⟨35490596219759166116344649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23660397479839444077563099 35490596219759166116344649)
  ·
    refine ⟨26617947164819374587258487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35490596219759166116344649 26617947164819374587258487)
    ·
      refine ⟨39926920747229061880887731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26617947164819374587258487 39926920747229061880887731)
      ·
        refine ⟨59890381120843592821331597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39926920747229061880887731 59890381120843592821331597)
        ·
          refine ⟨22458892920316347307999349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59890381120843592821331597 22458892920316347307999349)
          ·
            refine ⟨2105521211279657560124939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22458892920316347307999349 2105521211279657560124939)
            ·
              refine ⟨3158281816919486340187409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2105521211279657560124939 3158281816919486340187409)
              ·
                refine ⟨2368711362689614755140557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3158281816919486340187409 2368711362689614755140557)
                ·
                  refine ⟨888266761008605533177709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2368711362689614755140557 888266761008605533177709)
                  ·
                    refine ⟨333100035378227074941641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 888266761008605533177709 333100035378227074941641)
                    ·
                      rfl

theorem cell22_973065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 3, 3].length) (baseStart_973065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973065 prefixEnd_973065 := by exact prefixLift 973065
  have htrace : WordTrace (prefixWord ++ tailWord_973065) baseStart_973065 baseEnd_973065 := by
    simpa [prefixWord, tailWord_973065, baseEnd_973065] using wordTrace_append hprefix tailTrace_973065
  have hstable : (prefixWord ++ tailWord_973065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973065).length < 2 ^ (prefixWord ++ tailWord_973065).sum := by decide
  have hdescent : baseEnd_973065 < baseStart_973065 := by decide
  rcases family_descends (prefixWord ++ tailWord_973065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973123 : List Nat := [1, 1, 1, 3, 1, 3, 4, 2, 6]
def baseStart_973123 : Nat := 118140960795 + 973123 * 2 ^ 59
def prefixEnd_973123 : Nat := 4983230072969 + 3 ^ 40 * 973123 * 2
def baseEnd_973123 : Nat := 111039963321178085663821

theorem tailTrace_973123 : CollatzResearch.WordTrace tailWord_973123 prefixEnd_973123 111039963321178085663821 := by
  unfold tailWord_973123
  simp only [CollatzResearch.WordTrace]
  refine ⟨35492711653549042021956023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23661807769032694681304015 35492711653549042021956023)
  ·
    refine ⟨53239067480323563032934035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35492711653549042021956023 53239067480323563032934035)
    ·
      refine ⟨79858601220485344549401053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53239067480323563032934035 79858601220485344549401053)
      ·
        refine ⟨29946975457682004206025395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79858601220485344549401053 29946975457682004206025395)
        ·
          refine ⟨44920463186523006309038093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29946975457682004206025395 44920463186523006309038093)
          ·
            refine ⟨16845173694946127365889285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44920463186523006309038093 16845173694946127365889285)
            ·
              refine ⟨3158470067802398881104241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16845173694946127365889285 3158470067802398881104241)
              ·
                refine ⟨2368852550851799160828181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3158470067802398881104241 2368852550851799160828181)
                ·
                  refine ⟨111039963321178085663821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2368852550851799160828181 111039963321178085663821)
                  ·
                    rfl

theorem cell22_973123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 6].length) (baseStart_973123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973123 prefixEnd_973123 := by exact prefixLift 973123
  have htrace : WordTrace (prefixWord ++ tailWord_973123) baseStart_973123 baseEnd_973123 := by
    simpa [prefixWord, tailWord_973123, baseEnd_973123] using wordTrace_append hprefix tailTrace_973123
  have hstable : (prefixWord ++ tailWord_973123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973123).length < 2 ^ (prefixWord ++ tailWord_973123).sum := by decide
  have hdescent : baseEnd_973123 < baseStart_973123 := by decide
  rcases family_descends (prefixWord ++ tailWord_973123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973150 : List Nat := [4, 4, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_973150 : Nat := 118140960795 + 973150 * 2 ^ 59
def prefixEnd_973150 : Nat := 4983230072969 + 3 ^ 40 * 973150 * 2
def baseEnd_973150 : Nat := 333129132615315186566381

theorem tailTrace_973150 : CollatzResearch.WordTrace tailWord_973150 prefixEnd_973150 333129132615315186566381 := by
  unfold tailWord_973150
  simp only [CollatzResearch.WordTrace]
  refine ⟨4436712053056403204148613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23662464282967483755459269 4436712053056403204148613)
  ·
    refine ⟨831883509948075600777865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4436712053056403204148613 831883509948075600777865)
    ·
      refine ⟨623912632461056700583399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 831883509948075600777865 623912632461056700583399)
      ·
        refine ⟨935868948691585050875099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623912632461056700583399 935868948691585050875099)
        ·
          refine ⟨1403803423037377576312649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 935868948691585050875099 1403803423037377576312649)
          ·
            refine ⟨1052852567278033182234487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1403803423037377576312649 1052852567278033182234487)
            ·
              refine ⟨1579278850917049773351731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052852567278033182234487 1579278850917049773351731)
              ·
                refine ⟨2368918276375574660027597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1579278850917049773351731 2368918276375574660027597)
                ·
                  refine ⟨888344353640840497510349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2368918276375574660027597 888344353640840497510349)
                  ·
                    refine ⟨333129132615315186566381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 888344353640840497510349 333129132615315186566381)
                    ·
                      rfl

theorem cell22_973150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_973150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973150 prefixEnd_973150 := by exact prefixLift 973150
  have htrace : WordTrace (prefixWord ++ tailWord_973150) baseStart_973150 baseEnd_973150 := by
    simpa [prefixWord, tailWord_973150, baseEnd_973150] using wordTrace_append hprefix tailTrace_973150
  have hstable : (prefixWord ++ tailWord_973150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973150).length < 2 ^ (prefixWord ++ tailWord_973150).sum := by decide
  have hdescent : baseEnd_973150 < baseStart_973150 := by decide
  rcases family_descends (prefixWord ++ tailWord_973150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973155 : List Nat := [1, 1, 1, 5, 2, 1, 1, 3, 4, 3]
def baseStart_973155 : Nat := 118140960795 + 973155 * 2 ^ 59
def prefixEnd_973155 : Nat := 4983230072969 + 3 ^ 40 * 973155 * 2
def baseEnd_973155 : Nat := 333130844217496840191365

theorem tailTrace_973155 : CollatzResearch.WordTrace tailWord_973155 prefixEnd_973155 333130844217496840191365 := by
  unfold tailWord_973155
  simp only [CollatzResearch.WordTrace]
  refine ⟨35493878789433111487120919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23662585859622074324747279 35493878789433111487120919)
  ·
    refine ⟨53240818184149667230681379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35493878789433111487120919 53240818184149667230681379)
    ·
      refine ⟨79861227276224500846022069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53240818184149667230681379 79861227276224500846022069)
      ·
        refine ⟨7486990057146046954314569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79861227276224500846022069 7486990057146046954314569)
        ·
          refine ⟨5615242542859535215735927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7486990057146046954314569 5615242542859535215735927)
          ·
            refine ⟨8422863814289302823603891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5615242542859535215735927 8422863814289302823603891)
            ·
              refine ⟨12634295721433954235405837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8422863814289302823603891 12634295721433954235405837)
              ·
                refine ⟨4737860895537732838277189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12634295721433954235405837 4737860895537732838277189)
                ·
                  refine ⟨888348917913324907176973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4737860895537732838277189 888348917913324907176973)
                  ·
                    refine ⟨333130844217496840191365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 888348917913324907176973 333130844217496840191365)
                    ·
                      rfl

theorem cell22_973155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 4, 3].length) (baseStart_973155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973155 prefixEnd_973155 := by exact prefixLift 973155
  have htrace : WordTrace (prefixWord ++ tailWord_973155) baseStart_973155 baseEnd_973155 := by
    simpa [prefixWord, tailWord_973155, baseEnd_973155] using wordTrace_append hprefix tailTrace_973155
  have hstable : (prefixWord ++ tailWord_973155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973155).length < 2 ^ (prefixWord ++ tailWord_973155).sum := by decide
  have hdescent : baseEnd_973155 < baseStart_973155 := by decide
  rcases family_descends (prefixWord ++ tailWord_973155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973168 : List Nat := [2, 1, 1, 1, 4, 3, 1, 9]
def baseStart_973168 : Nat := 118140960795 + 973168 * 2 ^ 59
def prefixEnd_973168 : Nat := 4983230072969 + 3 ^ 40 * 973168 * 2
def baseEnd_973168 : Nat := 37015032709241015512925

theorem tailTrace_973168 : CollatzResearch.WordTrace tailWord_973168 prefixEnd_973168 37015032709241015512925 := by
  unfold tailWord_973168
  simp only [CollatzResearch.WordTrace]
  refine ⟨17747176469193007353672079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23662901958924009804896105 17747176469193007353672079)
  ·
    refine ⟨26620764703789511030508119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17747176469193007353672079 26620764703789511030508119)
    ·
      refine ⟨39931147055684266545762179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26620764703789511030508119 39931147055684266545762179)
      ·
        refine ⟨59896720583526399818643269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39931147055684266545762179 59896720583526399818643269)
        ·
          refine ⟨11230635109411199965995613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59896720583526399818643269 11230635109411199965995613)
          ·
            refine ⟨4211488166029199987248355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11230635109411199965995613 4211488166029199987248355)
            ·
              refine ⟨6317232249043799980872533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4211488166029199987248355 6317232249043799980872533)
              ·
                refine ⟨37015032709241015512925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6317232249043799980872533 37015032709241015512925)
                ·
                  rfl

theorem cell22_973168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 9].length) (baseStart_973168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973168 prefixEnd_973168 := by exact prefixLift 973168
  have htrace : WordTrace (prefixWord ++ tailWord_973168) baseStart_973168 baseEnd_973168 := by
    simpa [prefixWord, tailWord_973168, baseEnd_973168] using wordTrace_append hprefix tailTrace_973168
  have hstable : (prefixWord ++ tailWord_973168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973168).length < 2 ^ (prefixWord ++ tailWord_973168).sum := by decide
  have hdescent : baseEnd_973168 < baseStart_973168 := by decide
  rcases family_descends (prefixWord ++ tailWord_973168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973185 : List Nat := [1, 2, 4, 3, 1, 1, 2, 8]
def baseStart_973185 : Nat := 118140960795 + 973185 * 2 ^ 59
def prefixEnd_973185 : Nat := 4983230072969 + 3 ^ 40 * 973185 * 2
def baseEnd_973185 : Nat := 37015679314509640215697

theorem tailTrace_973185 : CollatzResearch.WordTrace tailWord_973185 prefixEnd_973185 37015679314509640215697 := by
  unfold tailWord_973185
  simp only [CollatzResearch.WordTrace]
  refine ⟨35494972979324426610713009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23663315319549617740475339 35494972979324426610713009)
  ·
    refine ⟨26621229734493319958034757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35494972979324426610713009 26621229734493319958034757)
    ·
      refine ⟨4991480575217497492131517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26621229734493319958034757 4991480575217497492131517)
      ·
        refine ⟨1871805215706561559549319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4991480575217497492131517 1871805215706561559549319)
        ·
          refine ⟨2807707823559842339323979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1871805215706561559549319 2807707823559842339323979)
          ·
            refine ⟨4211561735339763508985969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2807707823559842339323979 4211561735339763508985969)
            ·
              refine ⟨3158671301504822631739477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4211561735339763508985969 3158671301504822631739477)
              ·
                refine ⟨37015679314509640215697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3158671301504822631739477 37015679314509640215697)
                ·
                  rfl

theorem cell22_973185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 8].length) (baseStart_973185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973185 prefixEnd_973185 := by exact prefixLift 973185
  have htrace : WordTrace (prefixWord ++ tailWord_973185) baseStart_973185 baseEnd_973185 := by
    simpa [prefixWord, tailWord_973185, baseEnd_973185] using wordTrace_append hprefix tailTrace_973185
  have hstable : (prefixWord ++ tailWord_973185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973185).length < 2 ^ (prefixWord ++ tailWord_973185).sum := by decide
  have hdescent : baseEnd_973185 < baseStart_973185 := by decide
  rcases family_descends (prefixWord ++ tailWord_973185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973187 : List Nat := [1, 1, 1, 3, 6, 1, 2, 1, 2, 4]
def baseStart_973187 : Nat := 118140960795 + 973187 * 2 ^ 59
def prefixEnd_973187 : Nat := 4983230072969 + 3 ^ 40 * 973187 * 2
def baseEnd_973187 : Nat := 333141798471459423391267

theorem tailTrace_973187 : CollatzResearch.WordTrace tailWord_973187 prefixEnd_973187 333141798471459423391267 := by
  unfold tailWord_973187
  simp only [CollatzResearch.WordTrace]
  refine ⟨35495045925317180952285815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23663363950211453968190543 35495045925317180952285815)
  ·
    refine ⟨53242568887975771428428723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35495045925317180952285815 53242568887975771428428723)
    ·
      refine ⟨79863853331963657142643085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53242568887975771428428723 79863853331963657142643085)
      ·
        refine ⟨29948944999486371428491157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79863853331963657142643085 29948944999486371428491157)
        ·
          refine ⟨1403856796850923660710523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29948944999486371428491157 1403856796850923660710523)
          ·
            refine ⟨2105785195276385491065785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1403856796850923660710523 2105785195276385491065785)
            ·
              refine ⟨1579338896457289118299339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2105785195276385491065785 1579338896457289118299339)
              ·
                refine ⟨2369008344685933677449009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1579338896457289118299339 2369008344685933677449009)
                ·
                  refine ⟨1776756258514450258086757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2369008344685933677449009 1776756258514450258086757)
                  ·
                    refine ⟨333141798471459423391267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1776756258514450258086757 333141798471459423391267)
                    ·
                      rfl

theorem cell22_973187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 4].length) (baseStart_973187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973187 prefixEnd_973187 := by exact prefixLift 973187
  have htrace : WordTrace (prefixWord ++ tailWord_973187) baseStart_973187 baseEnd_973187 := by
    simpa [prefixWord, tailWord_973187, baseEnd_973187] using wordTrace_append hprefix tailTrace_973187
  have hstable : (prefixWord ++ tailWord_973187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973187).length < 2 ^ (prefixWord ++ tailWord_973187).sum := by decide
  have hdescent : baseEnd_973187 < baseStart_973187 := by decide
  rcases family_descends (prefixWord ++ tailWord_973187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973236 : List Nat := [2, 5, 2, 2, 1, 1, 3, 6]
def baseStart_973236 : Nat := 118140960795 + 973236 * 2 ^ 59
def prefixEnd_973236 : Nat := 4983230072969 + 3 ^ 40 * 973236 * 2
def baseEnd_973236 : Nat := 37017619130315514324013

theorem tailTrace_973236 : CollatzResearch.WordTrace tailWord_973236 prefixEnd_973236 37017619130315514324013 := by
  unfold tailWord_973236
  simp only [CollatzResearch.WordTrace]
  refine ⟨17748416551069831160409781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23664555401426441547213041 17748416551069831160409781)
  ·
    refine ⟨1663914051662796671288417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17748416551069831160409781 1663914051662796671288417)
    ·
      refine ⟨1247935538747097503466313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1663914051662796671288417 1247935538747097503466313)
      ·
        refine ⟨935951654060323127599735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1247935538747097503466313 935951654060323127599735)
        ·
          refine ⟨1403927481090484691399603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 935951654060323127599735 1403927481090484691399603)
          ·
            refine ⟨2105891221635727037099405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1403927481090484691399603 2105891221635727037099405)
            ·
              refine ⟨789709208113397638912277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2105891221635727037099405 789709208113397638912277)
              ·
                refine ⟨37017619130315514324013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 789709208113397638912277 37017619130315514324013)
                ·
                  rfl

theorem cell22_973236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 6].length) (baseStart_973236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973236 prefixEnd_973236 := by exact prefixLift 973236
  have htrace : WordTrace (prefixWord ++ tailWord_973236) baseStart_973236 baseEnd_973236 := by
    simpa [prefixWord, tailWord_973236, baseEnd_973236] using wordTrace_append hprefix tailTrace_973236
  have hstable : (prefixWord ++ tailWord_973236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973236).length < 2 ^ (prefixWord ++ tailWord_973236).sum := by decide
  have hdescent : baseEnd_973236 < baseStart_973236 := by decide
  rcases family_descends (prefixWord ++ tailWord_973236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973243 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 4, 8]
def baseStart_973243 : Nat := 118140960795 + 973243 * 2 ^ 59
def prefixEnd_973243 : Nat := 4983230072969 + 3 ^ 40 * 973243 * 2
def baseEnd_973243 : Nat := 333160968415893943991095

theorem tailTrace_973243 : CollatzResearch.WordTrace tailWord_973243 prefixEnd_973243 333160968415893943991095 := by
  unfold tailWord_973243
  simp only [CollatzResearch.WordTrace]
  refine ⟨35497088413114302516324383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23664725608742868344216255 35497088413114302516324383)
  ·
    refine ⟨53245632619671453774486575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35497088413114302516324383 53245632619671453774486575)
    ·
      refine ⟨79868448929507180661729863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53245632619671453774486575 79868448929507180661729863)
      ·
        refine ⟨119802673394260770992594795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79868448929507180661729863 119802673394260770992594795)
        ·
          refine ⟨179704010091391156488892193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119802673394260770992594795 179704010091391156488892193)
          ·
            refine ⟨134778007568543367366669145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179704010091391156488892193 134778007568543367366669145)
            ·
              refine ⟨101083505676407525525001859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134778007568543367366669145 101083505676407525525001859)
              ·
                refine ⟨151625258514611288287502789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101083505676407525525001859 151625258514611288287502789)
                ·
                  refine ⟨28429735971489616553906773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151625258514611288287502789 28429735971489616553906773)
                  ·
                    refine ⟨333160968415893943991095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 28429735971489616553906773 333160968415893943991095)
                    ·
                      rfl

theorem cell22_973243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 8].length) (baseStart_973243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973243 prefixEnd_973243 := by exact prefixLift 973243
  have htrace : WordTrace (prefixWord ++ tailWord_973243) baseStart_973243 baseEnd_973243 := by
    simpa [prefixWord, tailWord_973243, baseEnd_973243] using wordTrace_append hprefix tailTrace_973243
  have hstable : (prefixWord ++ tailWord_973243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973243).length < 2 ^ (prefixWord ++ tailWord_973243).sum := by decide
  have hdescent : baseEnd_973243 < baseStart_973243 := by decide
  rcases family_descends (prefixWord ++ tailWord_973243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973294 : List Nat := [4, 1, 2, 1, 2, 3, 2, 2, 1, 4]
def baseStart_973294 : Nat := 118140960795 + 973294 * 2 ^ 59
def prefixEnd_973294 : Nat := 4983230072969 + 3 ^ 40 * 973294 * 2
def baseEnd_973294 : Nat := 333178426758146810965939

theorem tailTrace_973294 : CollatzResearch.WordTrace tailWord_973294 prefixEnd_973294 333178426758146810965939 := by
  unfold tailWord_973294
  simp only [CollatzResearch.WordTrace]
  refine ⟨4437368566991192278303867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23665965690619692150953957 4437368566991192278303867)
  ·
    refine ⟨6656052850486788417455801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4437368566991192278303867 6656052850486788417455801)
    ·
      refine ⟨4992039637865091313091851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6656052850486788417455801 4992039637865091313091851)
      ·
        refine ⟨7488059456797636969637777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4992039637865091313091851 7488059456797636969637777)
        ·
          refine ⟨5616044592598227727228333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7488059456797636969637777 5616044592598227727228333)
          ·
            refine ⟨2106016722224335397710625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5616044592598227727228333 2106016722224335397710625)
            ·
              refine ⟨1579512541668251548282969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2106016722224335397710625 1579512541668251548282969)
              ·
                refine ⟨1184634406251188661212227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1579512541668251548282969 1184634406251188661212227)
                ·
                  refine ⟨1776951609376782991818341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1184634406251188661212227 1776951609376782991818341)
                  ·
                    refine ⟨333178426758146810965939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1776951609376782991818341 333178426758146810965939)
                    ·
                      rfl

theorem cell22_973294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_973294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973294 prefixEnd_973294 := by exact prefixLift 973294
  have htrace : WordTrace (prefixWord ++ tailWord_973294) baseStart_973294 baseEnd_973294 := by
    simpa [prefixWord, tailWord_973294, baseEnd_973294] using wordTrace_append hprefix tailTrace_973294
  have hstable : (prefixWord ++ tailWord_973294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973294).length < 2 ^ (prefixWord ++ tailWord_973294).sum := by decide
  have hdescent : baseEnd_973294 < baseStart_973294 := by decide
  rcases family_descends (prefixWord ++ tailWord_973294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973305 : List Nat := [1, 2, 1, 3, 1, 2, 4, 1, 1, 6]
def baseStart_973305 : Nat := 118140960795 + 973305 * 2 ^ 59
def prefixEnd_973305 : Nat := 4983230072969 + 3 ^ 40 * 973305 * 2
def baseEnd_973305 : Nat := 333182192282946448940905

theorem tailTrace_973305 : CollatzResearch.WordTrace tailWord_973305 prefixEnd_973305 333182192282946448940905 := by
  unfold tailWord_973305
  simp only [CollatzResearch.WordTrace]
  refine ⟨35499349738889687105081369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23666233159259791403387579 35499349738889687105081369)
  ·
    refine ⟨26624512304167265328811027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35499349738889687105081369 26624512304167265328811027)
    ·
      refine ⟨39936768456250897993216541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26624512304167265328811027 39936768456250897993216541)
      ·
        refine ⟨14976288171094086747456203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39936768456250897993216541 14976288171094086747456203)
        ·
          refine ⟨22464432256641130121184305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14976288171094086747456203 22464432256641130121184305)
          ·
            refine ⟨16848324192480847590888229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22464432256641130121184305 16848324192480847590888229)
            ·
              refine ⟨3159060786090158923291543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16848324192480847590888229 3159060786090158923291543)
              ·
                refine ⟨4738591179135238384937315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3159060786090158923291543 4738591179135238384937315)
                ·
                  refine ⟨7107886768702857577405973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4738591179135238384937315 7107886768702857577405973)
                  ·
                    refine ⟨333182192282946448940905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7107886768702857577405973 333182192282946448940905)
                    ·
                      rfl

theorem cell22_973305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 6].length) (baseStart_973305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973305 prefixEnd_973305 := by exact prefixLift 973305
  have htrace : WordTrace (prefixWord ++ tailWord_973305) baseStart_973305 baseEnd_973305 := by
    simpa [prefixWord, tailWord_973305, baseEnd_973305] using wordTrace_append hprefix tailTrace_973305
  have hstable : (prefixWord ++ tailWord_973305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973305).length < 2 ^ (prefixWord ++ tailWord_973305).sum := by decide
  have hdescent : baseEnd_973305 < baseStart_973305 := by decide
  rcases family_descends (prefixWord ++ tailWord_973305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973322 : List Nat := [3, 1, 2, 2, 2, 1, 3, 2, 2, 4]
def baseStart_973322 : Nat := 118140960795 + 973322 * 2 ^ 59
def prefixEnd_973322 : Nat := 4983230072969 + 3 ^ 40 * 973322 * 2
def baseEnd_973322 : Nat := 333188011730364071265853

theorem tailTrace_973322 : CollatzResearch.WordTrace tailWord_973322 prefixEnd_973322 333188011730364071265853 := by
  unfold tailWord_973322
  simp only [CollatzResearch.WordTrace]
  refine ⟨8874992444957024752112555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23666646519885399338966813 8874992444957024752112555)
  ·
    refine ⟨13312488667435537128168833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8874992444957024752112555 13312488667435537128168833)
    ·
      refine ⟨9984366500576652846126625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13312488667435537128168833 9984366500576652846126625)
      ·
        refine ⟨7488274875432489634594969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9984366500576652846126625 7488274875432489634594969)
        ·
          refine ⟨5616206156574367225946227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7488274875432489634594969 5616206156574367225946227)
          ·
            refine ⟨8424309234861550838919341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5616206156574367225946227 8424309234861550838919341)
            ·
              refine ⟨3159115963073081564594753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8424309234861550838919341 3159115963073081564594753)
              ·
                refine ⟨2369336972304811173446065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3159115963073081564594753 2369336972304811173446065)
                ·
                  refine ⟨1777002729228608380084549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2369336972304811173446065 1777002729228608380084549)
                  ·
                    refine ⟨333188011730364071265853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1777002729228608380084549 333188011730364071265853)
                    ·
                      rfl

theorem cell22_973322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_973322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973322 prefixEnd_973322 := by exact prefixLift 973322
  have htrace : WordTrace (prefixWord ++ tailWord_973322) baseStart_973322 baseEnd_973322 := by
    simpa [prefixWord, tailWord_973322, baseEnd_973322] using wordTrace_append hprefix tailTrace_973322
  have hstable : (prefixWord ++ tailWord_973322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973322).length < 2 ^ (prefixWord ++ tailWord_973322).sum := by decide
  have hdescent : baseEnd_973322 < baseStart_973322 := by decide
  rcases family_descends (prefixWord ++ tailWord_973322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973326 : List Nat := [4, 1, 1, 2, 3, 2, 3, 2, 4]
def baseStart_973326 : Nat := 118140960795 + 973326 * 2 ^ 59
def prefixEnd_973326 : Nat := 4983230072969 + 3 ^ 40 * 973326 * 2
def baseEnd_973326 : Nat := 111063127004036464721947

theorem tailTrace_973326 : CollatzResearch.WordTrace tailWord_973326 prefixEnd_973326 111063127004036464721947 := by
  unfold tailWord_973326
  simp only [CollatzResearch.WordTrace]
  refine ⟨4437514458976700961449479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23666743781209071794397221 4437514458976700961449479)
  ·
    refine ⟨6656271688465051442174219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4437514458976700961449479 6656271688465051442174219)
    ·
      refine ⟨9984407532697577163261329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6656271688465051442174219 9984407532697577163261329)
      ·
        refine ⟨7488305649523182872445997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9984407532697577163261329 7488305649523182872445997)
        ·
          refine ⟨2808114618571193577167249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7488305649523182872445997 2808114618571193577167249)
          ·
            refine ⟨2106085963928395182875437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2808114618571193577167249 2106085963928395182875437)
            ·
              refine ⟨789782236473148193578289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2106085963928395182875437 789782236473148193578289)
              ·
                refine ⟨592336677354861145183717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 789782236473148193578289 592336677354861145183717)
                ·
                  refine ⟨111063127004036464721947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 592336677354861145183717 111063127004036464721947)
                  ·
                    rfl

theorem cell22_973326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_973326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973326 prefixEnd_973326 := by exact prefixLift 973326
  have htrace : WordTrace (prefixWord ++ tailWord_973326) baseStart_973326 baseEnd_973326 := by
    simpa [prefixWord, tailWord_973326, baseEnd_973326] using wordTrace_append hprefix tailTrace_973326
  have hstable : (prefixWord ++ tailWord_973326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973326).length < 2 ^ (prefixWord ++ tailWord_973326).sum := by decide
  have hdescent : baseEnd_973326 < baseStart_973326 := by decide
  rcases family_descends (prefixWord ++ tailWord_973326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973341 : List Nat := [1, 4, 2, 2, 1, 2, 4, 1, 2, 3]
def baseStart_973341 : Nat := 118140960795 + 973341 * 2 ^ 59
def prefixEnd_973341 : Nat := 4983230072969 + 3 ^ 40 * 973341 * 2
def baseEnd_973341 : Nat := 333194515818654355040795

theorem tailTrace_973341 : CollatzResearch.WordTrace tailWord_973341 prefixEnd_973341 333194515818654355040795 := by
  unfold tailWord_973341
  simp only [CollatzResearch.WordTrace]
  refine ⟨35500662766759265253391877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23667108511172843502261251 35500662766759265253391877)
  ·
    refine ⟨6656374268767362235010977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35500662766759265253391877 6656374268767362235010977)
    ·
      refine ⟨4992280701575521676258233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6656374268767362235010977 4992280701575521676258233)
      ·
        refine ⟨3744210526181641257193675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4992280701575521676258233 3744210526181641257193675)
        ·
          refine ⟨5616315789272461885790513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3744210526181641257193675 5616315789272461885790513)
          ·
            refine ⟨4212236841954346414342885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5616315789272461885790513 4212236841954346414342885)
            ·
              refine ⟨789794407866439952689291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4212236841954346414342885 789794407866439952689291)
              ·
                refine ⟨1184691611799659929033937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789794407866439952689291 1184691611799659929033937)
                ·
                  refine ⟨888518708849744946775453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1184691611799659929033937 888518708849744946775453)
                  ·
                    refine ⟨333194515818654355040795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 888518708849744946775453 333194515818654355040795)
                    ·
                      rfl

theorem cell22_973341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_973341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973341 prefixEnd_973341 := by exact prefixLift 973341
  have htrace : WordTrace (prefixWord ++ tailWord_973341) baseStart_973341 baseEnd_973341 := by
    simpa [prefixWord, tailWord_973341, baseEnd_973341] using wordTrace_append hprefix tailTrace_973341
  have hstable : (prefixWord ++ tailWord_973341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973341).length < 2 ^ (prefixWord ++ tailWord_973341).sum := by decide
  have hdescent : baseEnd_973341 < baseStart_973341 := by decide
  rcases family_descends (prefixWord ++ tailWord_973341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973386 : List Nat := [3, 1, 2, 1, 1, 5, 1, 4, 1, 3]
def baseStart_973386 : Nat := 118140960795 + 973386 * 2 ^ 59
def prefixEnd_973386 : Nat := 4983230072969 + 3 ^ 40 * 973386 * 2
def baseEnd_973386 : Nat := 333209920238289237665657

theorem tailTrace_973386 : CollatzResearch.WordTrace tailWord_973386 prefixEnd_973386 333209920238289237665657 := by
  unfold tailWord_973386
  simp only [CollatzResearch.WordTrace]
  refine ⟨8875576012899059484695003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23668202701064158625853341 8875576012899059484695003)
  ·
    refine ⟨13313364019348589227042505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8875576012899059484695003 13313364019348589227042505)
    ·
      refine ⟨9985023014511441920281879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13313364019348589227042505 9985023014511441920281879)
      ·
        refine ⟨14977534521767162880422819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9985023014511441920281879 14977534521767162880422819)
        ·
          refine ⟨22466301782650744320634229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14977534521767162880422819 22466301782650744320634229)
          ·
            refine ⟨2106215792123507280059459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22466301782650744320634229 2106215792123507280059459)
            ·
              refine ⟨3159323688185260920089189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2106215792123507280059459 3159323688185260920089189)
              ·
                refine ⟨592373191534736422516723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3159323688185260920089189 592373191534736422516723)
                ·
                  refine ⟨888559787302104633775085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 592373191534736422516723 888559787302104633775085)
                  ·
                    refine ⟨333209920238289237665657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 888559787302104633775085 333209920238289237665657)
                    ·
                      rfl

theorem cell22_973386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_973386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973386 prefixEnd_973386 := by exact prefixLift 973386
  have htrace : WordTrace (prefixWord ++ tailWord_973386) baseStart_973386 baseEnd_973386 := by
    simpa [prefixWord, tailWord_973386, baseEnd_973386] using wordTrace_append hprefix tailTrace_973386
  have hstable : (prefixWord ++ tailWord_973386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973386).length < 2 ^ (prefixWord ++ tailWord_973386).sum := by decide
  have hdescent : baseEnd_973386 < baseStart_973386 := by decide
  rcases family_descends (prefixWord ++ tailWord_973386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973412 : List Nat := [2, 3, 1, 1, 2, 2, 1, 3, 3, 4]
def baseStart_973412 : Nat := 118140960795 + 973412 * 2 ^ 59
def prefixEnd_973412 : Nat := 4983230072969 + 3 ^ 40 * 973412 * 2
def baseEnd_973412 : Nat := 333218820569633836515577

theorem tailTrace_973412 : CollatzResearch.WordTrace tailWord_973412 prefixEnd_973412 333218820569633836515577 := by
  unfold tailWord_973412
  simp only [CollatzResearch.WordTrace]
  refine ⟨17751626174751022189613245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23668834899668029586150993 17751626174751022189613245)
  ·
    refine ⟨6656859815531633321104967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17751626174751022189613245 6656859815531633321104967)
    ·
      refine ⟨9985289723297449981657451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6656859815531633321104967 9985289723297449981657451)
      ·
        refine ⟨14977934584946174972486177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9985289723297449981657451 14977934584946174972486177)
        ·
          refine ⟨11233450938709631229364633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14977934584946174972486177 11233450938709631229364633)
          ·
            refine ⟨8425088204032223422023475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11233450938709631229364633 8425088204032223422023475)
            ·
              refine ⟨12637632306048335133035213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8425088204032223422023475 12637632306048335133035213)
              ·
                refine ⟨4739112114768125674888205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12637632306048335133035213 4739112114768125674888205)
                ·
                  refine ⟨1777167043038047128083077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4739112114768125674888205 1777167043038047128083077)
                  ·
                    refine ⟨333218820569633836515577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1777167043038047128083077 333218820569633836515577)
                    ·
                      rfl

theorem cell22_973412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_973412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973412 prefixEnd_973412 := by exact prefixLift 973412
  have htrace : WordTrace (prefixWord ++ tailWord_973412) baseStart_973412 baseEnd_973412 := by
    simpa [prefixWord, tailWord_973412, baseEnd_973412] using wordTrace_append hprefix tailTrace_973412
  have hstable : (prefixWord ++ tailWord_973412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973412).length < 2 ^ (prefixWord ++ tailWord_973412).sum := by decide
  have hdescent : baseEnd_973412 < baseStart_973412 := by decide
  rcases family_descends (prefixWord ++ tailWord_973412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973444 : List Nat := [2, 3, 2, 1, 3, 2, 2, 1, 6]
def baseStart_973444 : Nat := 118140960795 + 973444 * 2 ^ 59
def prefixEnd_973444 : Nat := 4983230072969 + 3 ^ 40 * 973444 * 2
def baseEnd_973444 : Nat := 111076591607865473238493

theorem tailTrace_973444 : CollatzResearch.WordTrace tailWord_973444 prefixEnd_973444 111076591607865473238493 := by
  unfold tailWord_973444
  simp only [CollatzResearch.WordTrace]
  refine ⟨17752209742693056922195693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23669612990257409229594257 17752209742693056922195693)
  ·
    refine ⟨6657078653509896345823385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17752209742693056922195693 6657078653509896345823385)
    ·
      refine ⟨4992808990132422259367539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6657078653509896345823385 4992808990132422259367539)
      ·
        refine ⟨7489213485198633389051309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4992808990132422259367539 7489213485198633389051309)
        ·
          refine ⟨2808455056949487520894241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7489213485198633389051309 2808455056949487520894241)
          ·
            refine ⟨2106341292712115640670681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2808455056949487520894241 2106341292712115640670681)
            ·
              refine ⟨1579755969534086730503011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2106341292712115640670681 1579755969534086730503011)
              ·
                refine ⟨2369633954301130095754517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1579755969534086730503011 2369633954301130095754517)
                ·
                  refine ⟨111076591607865473238493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2369633954301130095754517 111076591607865473238493)
                  ·
                    rfl

theorem cell22_973444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_973444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973444 prefixEnd_973444 := by exact prefixLift 973444
  have htrace : WordTrace (prefixWord ++ tailWord_973444) baseStart_973444 baseEnd_973444 := by
    simpa [prefixWord, tailWord_973444, baseEnd_973444] using wordTrace_append hprefix tailTrace_973444
  have hstable : (prefixWord ++ tailWord_973444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973444).length < 2 ^ (prefixWord ++ tailWord_973444).sum := by decide
  have hdescent : baseEnd_973444 < baseStart_973444 := by decide
  rcases family_descends (prefixWord ++ tailWord_973444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973549 : List Nat := [1, 5, 1, 2, 1, 1, 2, 2, 2, 5]
def baseStart_973549 : Nat := 118140960795 + 973549 * 2 ^ 59
def prefixEnd_973549 : Nat := 4983230072969 + 3 ^ 40 * 973549 * 2
def baseEnd_973549 : Nat := 333265718469411145840157

theorem tailTrace_973549 : CollatzResearch.WordTrace tailWord_973549 prefixEnd_973549 333265718469411145840157 := by
  unfold tailWord_973549
  simp only [CollatzResearch.WordTrace]
  refine ⟨35508249150005716776963701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23672166100003811184642467 35508249150005716776963701)
  ·
    refine ⟨3328898357813035947840347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35508249150005716776963701 3328898357813035947840347)
    ·
      refine ⟨4993347536719553921760521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3328898357813035947840347 4993347536719553921760521)
      ·
        refine ⟨3745010652539665441320391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4993347536719553921760521 3745010652539665441320391)
        ·
          refine ⟨5617515978809498161980587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3745010652539665441320391 5617515978809498161980587)
          ·
            refine ⟨8426273968214247242970881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5617515978809498161980587 8426273968214247242970881)
            ·
              refine ⟨6319705476160685432228161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8426273968214247242970881 6319705476160685432228161)
              ·
                refine ⟨4739779107120514074171121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6319705476160685432228161 4739779107120514074171121)
                ·
                  refine ⟨3554834330340385555628341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4739779107120514074171121 3554834330340385555628341)
                  ·
                    refine ⟨333265718469411145840157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3554834330340385555628341 333265718469411145840157)
                    ·
                      rfl

theorem cell22_973549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_973549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973549 prefixEnd_973549 := by exact prefixLift 973549
  have htrace : WordTrace (prefixWord ++ tailWord_973549) baseStart_973549 baseEnd_973549 := by
    simpa [prefixWord, tailWord_973549, baseEnd_973549] using wordTrace_append hprefix tailTrace_973549
  have hstable : (prefixWord ++ tailWord_973549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973549).length < 2 ^ (prefixWord ++ tailWord_973549).sum := by decide
  have hdescent : baseEnd_973549 < baseStart_973549 := by decide
  rcases family_descends (prefixWord ++ tailWord_973549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973564 : List Nat := [2, 2, 2, 1, 3, 2, 1, 2, 3, 4]
def baseStart_973564 : Nat := 118140960795 + 973564 * 2 ^ 59
def prefixEnd_973564 : Nat := 4983230072969 + 3 ^ 40 * 973564 * 2
def baseEnd_973564 : Nat := 333270853275956106715111

theorem tailTrace_973564 : CollatzResearch.WordTrace tailWord_973564 prefixEnd_973564 333270853275956106715111 := by
  unfold tailWord_973564
  simp only [CollatzResearch.WordTrace]
  refine ⟨17754398122475687169379873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23672530829967582892506497 17754398122475687169379873)
  ·
    refine ⟨13315798591856765377034905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17754398122475687169379873 13315798591856765377034905)
    ·
      refine ⟨9986848943892574032776179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13315798591856765377034905 9986848943892574032776179)
      ·
        refine ⟨14980273415838861049164269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9986848943892574032776179 14980273415838861049164269)
        ·
          refine ⟨5617602530939572893436601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14980273415838861049164269 5617602530939572893436601)
          ·
            refine ⟨4213201898204679670077451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5617602530939572893436601 4213201898204679670077451)
            ·
              refine ⟨6319802847307019505116177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4213201898204679670077451 6319802847307019505116177)
              ·
                refine ⟨4739852135480264628837133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6319802847307019505116177 4739852135480264628837133)
                ·
                  refine ⟨1777444550805099235813925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4739852135480264628837133 1777444550805099235813925)
                  ·
                    refine ⟨333270853275956106715111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1777444550805099235813925 333270853275956106715111)
                    ·
                      rfl

theorem cell22_973564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_973564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973564 prefixEnd_973564 := by exact prefixLift 973564
  have htrace : WordTrace (prefixWord ++ tailWord_973564) baseStart_973564 baseEnd_973564 := by
    simpa [prefixWord, tailWord_973564, baseEnd_973564] using wordTrace_append hprefix tailTrace_973564
  have hstable : (prefixWord ++ tailWord_973564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973564).length < 2 ^ (prefixWord ++ tailWord_973564).sum := by decide
  have hdescent : baseEnd_973564 < baseStart_973564 := by decide
  rcases family_descends (prefixWord ++ tailWord_973564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973566 : List Nat := [4, 2, 2, 1, 2, 2, 1, 1, 2, 5]
def baseStart_973566 : Nat := 118140960795 + 973566 * 2 ^ 59
def prefixEnd_973566 : Nat := 4983230072969 + 3 ^ 40 * 973566 * 2
def baseEnd_973566 : Nat := 333271537916828768165105

theorem tailTrace_973566 : CollatzResearch.WordTrace tailWord_973566 prefixEnd_973566 333271537916828768165105 := by
  unfold tailWord_973566
  simp only [CollatzResearch.WordTrace]
  refine ⟨4438608648868016085041569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23672579460629419120221701 4438608648868016085041569)
  ·
    refine ⟨3328956486651012063781177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4438608648868016085041569 3328956486651012063781177)
    ·
      refine ⟨2496717364988259047835883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3328956486651012063781177 2496717364988259047835883)
      ·
        refine ⟨3745076047482388571753825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2496717364988259047835883 3745076047482388571753825)
        ·
          refine ⟨2808807035611791428815369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3745076047482388571753825 2808807035611791428815369)
          ·
            refine ⟨2106605276708843571611527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2808807035611791428815369 2106605276708843571611527)
            ·
              refine ⟨3159907915063265357417291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2106605276708843571611527 3159907915063265357417291)
              ·
                refine ⟨4739861872594898036125937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3159907915063265357417291 4739861872594898036125937)
                ·
                  refine ⟨3554896404446173527094453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4739861872594898036125937 3554896404446173527094453)
                  ·
                    refine ⟨333271537916828768165105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3554896404446173527094453 333271537916828768165105)
                    ·
                      rfl

theorem cell22_973566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_973566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973566 prefixEnd_973566 := by exact prefixLift 973566
  have htrace : WordTrace (prefixWord ++ tailWord_973566) baseStart_973566 baseEnd_973566 := by
    simpa [prefixWord, tailWord_973566, baseEnd_973566] using wordTrace_append hprefix tailTrace_973566
  have hstable : (prefixWord ++ tailWord_973566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973566).length < 2 ^ (prefixWord ++ tailWord_973566).sum := by decide
  have hdescent : baseEnd_973566 < baseStart_973566 := by decide
  rcases family_descends (prefixWord ++ tailWord_973566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973594 : List Nat := [3, 1, 1, 3, 2, 1, 1, 4, 1, 5]
def baseStart_973594 : Nat := 118140960795 + 973594 * 2 ^ 59
def prefixEnd_973594 : Nat := 4983230072969 + 3 ^ 40 * 973594 * 2
def baseEnd_973594 : Nat := 333281122889046028465019

theorem tailTrace_973594 : CollatzResearch.WordTrace tailWord_973594 prefixEnd_973594 333281122889046028465019 := by
  unfold tailWord_973594
  simp only [CollatzResearch.WordTrace]
  refine ⟨8877472608710672365587959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23673260289895126308234557 8877472608710672365587959)
  ·
    refine ⟨13316208913066008548381939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8877472608710672365587959 13316208913066008548381939)
    ·
      refine ⟨19974313369599012822572909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13316208913066008548381939 19974313369599012822572909)
      ·
        refine ⟨7490367513599629808464841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19974313369599012822572909 7490367513599629808464841)
        ·
          refine ⟨5617775635199722356348631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7490367513599629808464841 5617775635199722356348631)
          ·
            refine ⟨8426663452799583534522947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5617775635199722356348631 8426663452799583534522947)
            ·
              refine ⟨12639995179199375301784421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8426663452799583534522947 12639995179199375301784421)
              ·
                refine ⟨2369999096099882869084579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12639995179199375301784421 2369999096099882869084579)
                ·
                  refine ⟨3554998644149824303626869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2369999096099882869084579 3554998644149824303626869)
                  ·
                    refine ⟨333281122889046028465019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3554998644149824303626869 333281122889046028465019)
                    ·
                      rfl

theorem cell22_973594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_973594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973594 prefixEnd_973594 := by exact prefixLift 973594
  have htrace : WordTrace (prefixWord ++ tailWord_973594) baseStart_973594 baseEnd_973594 := by
    simpa [prefixWord, tailWord_973594, baseEnd_973594] using wordTrace_append hprefix tailTrace_973594
  have hstable : (prefixWord ++ tailWord_973594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973594).length < 2 ^ (prefixWord ++ tailWord_973594).sum := by decide
  have hdescent : baseEnd_973594 < baseStart_973594 := by decide
  rcases family_descends (prefixWord ++ tailWord_973594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973596 : List Nat := [2, 2, 3, 1, 1, 3, 1, 5, 4]
def baseStart_973596 : Nat := 118140960795 + 973596 * 2 ^ 59
def prefixEnd_973596 : Nat := 4983230072969 + 3 ^ 40 * 973596 * 2
def baseEnd_973596 : Nat := 111093935843306229971671

theorem tailTrace_973596 : CollatzResearch.WordTrace tailWord_973596 prefixEnd_973596 111093935843306229971671 := by
  unfold tailWord_973596
  simp only [CollatzResearch.WordTrace]
  refine ⟨17754981690417721901962321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23673308920556962535949761 17754981690417721901962321)
  ·
    refine ⟨13316236267813291426471741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17754981690417721901962321 13316236267813291426471741)
    ·
      refine ⟨4993588600429984284926903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13316236267813291426471741 4993588600429984284926903)
      ·
        refine ⟨7490382900644976427390355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4993588600429984284926903 7490382900644976427390355)
        ·
          refine ⟨11235574350967464641085533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7490382900644976427390355 11235574350967464641085533)
          ·
            refine ⟨4213340381612799240407075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11235574350967464641085533 4213340381612799240407075)
            ·
              refine ⟨6320010572419198860610613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4213340381612799240407075 6320010572419198860610613)
              ·
                refine ⟨592500991164299893182245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6320010572419198860610613 592500991164299893182245)
                ·
                  refine ⟨111093935843306229971671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 592500991164299893182245 111093935843306229971671)
                  ·
                    rfl

theorem cell22_973596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 5, 4].length) (baseStart_973596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973596 prefixEnd_973596 := by exact prefixLift 973596
  have htrace : WordTrace (prefixWord ++ tailWord_973596) baseStart_973596 baseEnd_973596 := by
    simpa [prefixWord, tailWord_973596, baseEnd_973596] using wordTrace_append hprefix tailTrace_973596
  have hstable : (prefixWord ++ tailWord_973596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973596).length < 2 ^ (prefixWord ++ tailWord_973596).sum := by decide
  have hdescent : baseEnd_973596 < baseStart_973596 := by decide
  rcases family_descends (prefixWord ++ tailWord_973596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973641 : List Nat := [1, 2, 1, 1, 2, 7, 2, 6]
def baseStart_973641 : Nat := 118140960795 + 973641 * 2 ^ 59
def prefixEnd_973641 : Nat := 4983230072969 + 3 ^ 40 * 973641 * 2
def baseEnd_973641 : Nat := 37033023549950396948875

theorem tailTrace_973641 : CollatzResearch.WordTrace tailWord_973641 prefixEnd_973641 37033023549950396948875 := by
  unfold tailWord_973641
  simp only [CollatzResearch.WordTrace]
  refine ⟨35511604665672416489312777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23674403110448277659541851 35511604665672416489312777)
  ·
    refine ⟨26633703499254312366984583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35511604665672416489312777 26633703499254312366984583)
    ·
      refine ⟨39950555248881468550476875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26633703499254312366984583 39950555248881468550476875)
      ·
        refine ⟨59925832873322202825715313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39950555248881468550476875 59925832873322202825715313)
        ·
          refine ⟨44944374654991652119286485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59925832873322202825715313 44944374654991652119286485)
          ·
            refine ⟨1053383780976366846545777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 44944374654991652119286485 1053383780976366846545777)
            ·
              refine ⟨790037835732275134909333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1053383780976366846545777 790037835732275134909333)
              ·
                refine ⟨37033023549950396948875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 790037835732275134909333 37033023549950396948875)
                ·
                  rfl

theorem cell22_973641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 6].length) (baseStart_973641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973641 prefixEnd_973641 := by exact prefixLift 973641
  have htrace : WordTrace (prefixWord ++ tailWord_973641) baseStart_973641 baseEnd_973641 := by
    simpa [prefixWord, tailWord_973641, baseEnd_973641] using wordTrace_append hprefix tailTrace_973641
  have hstable : (prefixWord ++ tailWord_973641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973641).length < 2 ^ (prefixWord ++ tailWord_973641).sum := by decide
  have hdescent : baseEnd_973641 < baseStart_973641 := by decide
  rcases family_descends (prefixWord ++ tailWord_973641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973669 : List Nat := [1, 3, 1, 3, 1, 1, 4, 1, 7]
def baseStart_973669 : Nat := 118140960795 + 973669 * 2 ^ 59
def prefixEnd_973669 : Nat := 4983230072969 + 3 ^ 40 * 973669 * 2
def baseEnd_973669 : Nat := 111102265640590277613263

theorem tailTrace_973669 : CollatzResearch.WordTrace tailWord_973669 prefixEnd_973669 111102265640590277613263 := by
  unfold tailWord_973669
  simp only [CollatzResearch.WordTrace]
  refine ⟨35512625909570977271332061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23675083939713984847554707 35512625909570977271332061)
  ·
    refine ⟨13317234716089116476749523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35512625909570977271332061 13317234716089116476749523)
    ·
      refine ⟨19975852074133674715124285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13317234716089116476749523 19975852074133674715124285)
      ·
        refine ⟨7490944527800128018171607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19975852074133674715124285 7490944527800128018171607)
        ·
          refine ⟨11236416791700192027257411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7490944527800128018171607 11236416791700192027257411)
          ·
            refine ⟨16854625187550288040886117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11236416791700192027257411 16854625187550288040886117)
            ·
              refine ⟨3160242222665679007666147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16854625187550288040886117 3160242222665679007666147)
              ·
                refine ⟨4740363333998518511499221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3160242222665679007666147 4740363333998518511499221)
                ·
                  refine ⟨111102265640590277613263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4740363333998518511499221 111102265640590277613263)
                  ·
                    rfl

theorem cell22_973669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 7].length) (baseStart_973669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973669 prefixEnd_973669 := by exact prefixLift 973669
  have htrace : WordTrace (prefixWord ++ tailWord_973669) baseStart_973669 baseEnd_973669 := by
    simpa [prefixWord, tailWord_973669, baseEnd_973669] using wordTrace_append hprefix tailTrace_973669
  have hstable : (prefixWord ++ tailWord_973669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973669).length < 2 ^ (prefixWord ++ tailWord_973669).sum := by decide
  have hdescent : baseEnd_973669 < baseStart_973669 := by decide
  rcases family_descends (prefixWord ++ tailWord_973669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973724 : List Nat := [2, 2, 3, 3, 2, 2, 2, 2, 1, 3]
def baseStart_973724 : Nat := 118140960795 + 973724 * 2 ^ 59
def prefixEnd_973724 : Nat := 4983230072969 + 3 ^ 40 * 973724 * 2
def baseEnd_973724 : Nat := 333325624545769022714621

theorem tailTrace_973724 : CollatzResearch.WordTrace tailWord_973724 prefixEnd_973724 333325624545769022714621 := by
  unfold tailWord_973724
  simp only [CollatzResearch.WordTrace]
  refine ⟨17757315962185860832292113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23676421282914481109722817 17757315962185860832292113)
  ·
    refine ⟨13317986971639395624219085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17757315962185860832292113 13317986971639395624219085)
    ·
      refine ⟨4994245114364773359082157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13317986971639395624219085 4994245114364773359082157)
      ·
        refine ⟨1872841917886790009655809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4994245114364773359082157 1872841917886790009655809)
        ·
          refine ⟨1404631438415092507241857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1872841917886790009655809 1404631438415092507241857)
          ·
            refine ⟨1053473578811319380431393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1404631438415092507241857 1053473578811319380431393)
            ·
              refine ⟨790105184108489535323545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1053473578811319380431393 790105184108489535323545)
              ·
                refine ⟨592578888081367151492659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 790105184108489535323545 592578888081367151492659)
                ·
                  refine ⟨888868332122050727238989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 592578888081367151492659 888868332122050727238989)
                  ·
                    refine ⟨333325624545769022714621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 888868332122050727238989 333325624545769022714621)
                    ·
                      rfl

theorem cell22_973724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_973724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973724 prefixEnd_973724 := by exact prefixLift 973724
  have htrace : WordTrace (prefixWord ++ tailWord_973724) baseStart_973724 baseEnd_973724 := by
    simpa [prefixWord, tailWord_973724, baseEnd_973724] using wordTrace_append hprefix tailTrace_973724
  have hstable : (prefixWord ++ tailWord_973724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973724).length < 2 ^ (prefixWord ++ tailWord_973724).sum := by decide
  have hdescent : baseEnd_973724 < baseStart_973724 := by decide
  rcases family_descends (prefixWord ++ tailWord_973724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973746 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 8, 3]
def baseStart_973746 : Nat := 118140960795 + 973746 * 2 ^ 59
def prefixEnd_973746 : Nat := 4983230072969 + 3 ^ 40 * 973746 * 2
def baseEnd_973746 : Nat := 333333155595368298664553

theorem tailTrace_973746 : CollatzResearch.WordTrace tailWord_973746 prefixEnd_973746 333333155595368298664553 := by
  unfold tailWord_973746
  simp only [CollatzResearch.WordTrace]
  refine ⟨8878858582573004855471273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23676956220194679614590061 8878858582573004855471273)
  ·
    refine ⟨6659143936929753641603455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8878858582573004855471273 6659143936929753641603455)
    ·
      refine ⟨9988715905394630462405183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6659143936929753641603455 9988715905394630462405183)
      ·
        refine ⟨14983073858091945693607775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9988715905394630462405183 14983073858091945693607775)
        ·
          refine ⟨22474610787137918540411663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14983073858091945693607775 22474610787137918540411663)
          ·
            refine ⟨33711916180706877810617495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22474610787137918540411663 33711916180706877810617495)
            ·
              refine ⟨50567874271060316715926243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33711916180706877810617495 50567874271060316715926243)
              ·
                refine ⟨75851811406590475073889365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50567874271060316715926243 75851811406590475073889365)
                ·
                  refine ⟨888888414920982129772141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 75851811406590475073889365 888888414920982129772141)
                  ·
                    refine ⟨333333155595368298664553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 888888414920982129772141 333333155595368298664553)
                    ·
                      rfl

theorem cell22_973746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_973746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973746 prefixEnd_973746 := by exact prefixLift 973746
  have htrace : WordTrace (prefixWord ++ tailWord_973746) baseStart_973746 baseEnd_973746 := by
    simpa [prefixWord, tailWord_973746, baseEnd_973746] using wordTrace_append hprefix tailTrace_973746
  have hstable : (prefixWord ++ tailWord_973746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973746).length < 2 ^ (prefixWord ++ tailWord_973746).sum := by decide
  have hdescent : baseEnd_973746 < baseStart_973746 := by decide
  rcases family_descends (prefixWord ++ tailWord_973746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973748 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 8]
def baseStart_973748 : Nat := 118140960795 + 973748 * 2 ^ 59
def prefixEnd_973748 : Nat := 4983230072969 + 3 ^ 40 * 973748 * 2
def baseEnd_973748 : Nat := 111111280078746986704849

theorem tailTrace_973748 : CollatzResearch.WordTrace tailWord_973748 prefixEnd_973748 111111280078746986704849 := by
  unfold tailWord_973748
  simp only [CollatzResearch.WordTrace]
  refine ⟨17757753638142386881728949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23677004850856515842305265 17757753638142386881728949)
  ·
    refine ⟨1664789403575848770162089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17757753638142386881728949 1664789403575848770162089)
    ·
      refine ⟨1248592052681886577621567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1664789403575848770162089 1248592052681886577621567)
      ·
        refine ⟨1872888079022829866432351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1248592052681886577621567 1872888079022829866432351)
        ·
          refine ⟨2809332118534244799648527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1872888079022829866432351 2809332118534244799648527)
          ·
            refine ⟨4213998177801367199472791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2809332118534244799648527 4213998177801367199472791)
            ·
              refine ⟨6320997266702050799209187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4213998177801367199472791 6320997266702050799209187)
              ·
                refine ⟨9481495900053076198813781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6320997266702050799209187 9481495900053076198813781)
                ·
                  refine ⟨111111280078746986704849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9481495900053076198813781 111111280078746986704849)
                  ·
                    rfl

theorem cell22_973748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_973748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973748 prefixEnd_973748 := by exact prefixLift 973748
  have htrace : WordTrace (prefixWord ++ tailWord_973748) baseStart_973748 baseEnd_973748 := by
    simpa [prefixWord, tailWord_973748, baseEnd_973748] using wordTrace_append hprefix tailTrace_973748
  have hstable : (prefixWord ++ tailWord_973748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973748).length < 2 ^ (prefixWord ++ tailWord_973748).sum := by decide
  have hdescent : baseEnd_973748 < baseStart_973748 := by decide
  rcases family_descends (prefixWord ++ tailWord_973748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973780 : List Nat := [2, 4, 1, 2, 1, 2, 3, 2, 2, 3]
def baseStart_973780 : Nat := 118140960795 + 973780 * 2 ^ 59
def prefixEnd_973780 : Nat := 4983230072969 + 3 ^ 40 * 973780 * 2
def baseEnd_973780 : Nat := 333344794490203543314449

theorem tailTrace_973780 : CollatzResearch.WordTrace tailWord_973780 prefixEnd_973780 333344794490203543314449 := by
  unfold tailWord_973780
  simp only [CollatzResearch.WordTrace]
  refine ⟨17758337206084421614311397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23677782941445895485748529 17758337206084421614311397)
  ·
    refine ⟨3329688226140829052683387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17758337206084421614311397 3329688226140829052683387)
    ·
      refine ⟨4994532339211243579025081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3329688226140829052683387 4994532339211243579025081)
      ·
        refine ⟨3745899254408432684268811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4994532339211243579025081 3745899254408432684268811)
        ·
          refine ⟨5618848881612649026403217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3745899254408432684268811 5618848881612649026403217)
          ·
            refine ⟨4214136661209486769802413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5618848881612649026403217 4214136661209486769802413)
            ·
              refine ⟨1580301247953557538675905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4214136661209486769802413 1580301247953557538675905)
              ·
                refine ⟨1185225935965168154006929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1580301247953557538675905 1185225935965168154006929)
                ·
                  refine ⟨888919451973876115505197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1185225935965168154006929 888919451973876115505197)
                  ·
                    refine ⟨333344794490203543314449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 888919451973876115505197 333344794490203543314449)
                    ·
                      rfl

theorem cell22_973780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_973780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973780 prefixEnd_973780 := by exact prefixLift 973780
  have htrace : WordTrace (prefixWord ++ tailWord_973780) baseStart_973780 baseEnd_973780 := by
    simpa [prefixWord, tailWord_973780, baseEnd_973780] using wordTrace_append hprefix tailTrace_973780
  have hstable : (prefixWord ++ tailWord_973780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973780).length < 2 ^ (prefixWord ++ tailWord_973780).sum := by decide
  have hdescent : baseEnd_973780 < baseStart_973780 := by decide
  rcases family_descends (prefixWord ++ tailWord_973780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973797 : List Nat := [1, 3, 1, 6, 2, 1, 1, 1, 1, 5]
def baseStart_973797 : Nat := 118140960795 + 973797 * 2 ^ 59
def prefixEnd_973797 : Nat := 4983230072969 + 3 ^ 40 * 973797 * 2
def baseEnd_973797 : Nat := 333350613937621165639397

theorem tailTrace_973797 : CollatzResearch.WordTrace tailWord_973797 prefixEnd_973797 333350613937621165639397 := by
  unfold tailWord_973797
  simp only [CollatzResearch.WordTrace]
  refine ⟨35517294453107255131991645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23678196302071503421327763 35517294453107255131991645)
  ·
    refine ⟨13318985419915220674496867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35517294453107255131991645 13318985419915220674496867)
    ·
      refine ⟨19978478129872831011745301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13318985419915220674496867 19978478129872831011745301)
      ·
        refine ⟨936491162337788953675561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19978478129872831011745301 936491162337788953675561)
        ·
          refine ⟨702368371753341715256671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 936491162337788953675561 702368371753341715256671)
          ·
            refine ⟨1053552557630012572885007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702368371753341715256671 1053552557630012572885007)
            ·
              refine ⟨1580328836445018859327511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1053552557630012572885007 1580328836445018859327511)
              ·
                refine ⟨2370493254667528288991267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1580328836445018859327511 2370493254667528288991267)
                ·
                  refine ⟨3555739882001292433486901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2370493254667528288991267 3555739882001292433486901)
                  ·
                    refine ⟨333350613937621165639397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3555739882001292433486901 333350613937621165639397)
                    ·
                      rfl

theorem cell22_973797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 1, 5].length) (baseStart_973797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973797 prefixEnd_973797 := by exact prefixLift 973797
  have htrace : WordTrace (prefixWord ++ tailWord_973797) baseStart_973797 baseEnd_973797 := by
    simpa [prefixWord, tailWord_973797, baseEnd_973797] using wordTrace_append hprefix tailTrace_973797
  have hstable : (prefixWord ++ tailWord_973797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973797).length < 2 ^ (prefixWord ++ tailWord_973797).sum := by decide
  have hdescent : baseEnd_973797 < baseStart_973797 := by decide
  rcases family_descends (prefixWord ++ tailWord_973797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973855 : List Nat := [1, 1, 2, 4, 1, 5, 2, 1, 5]
def baseStart_973855 : Nat := 118140960795 + 973855 * 2 ^ 59
def prefixEnd_973855 : Nat := 4983230072969 + 3 ^ 40 * 973855 * 2
def baseEnd_973855 : Nat := 111123489507642782563073

theorem tailTrace_973855 : CollatzResearch.WordTrace tailWord_973855 prefixEnd_973855 111123489507642782563073 := by
  unfold tailWord_973855
  simp only [CollatzResearch.WordTrace]
  refine ⟨35519409886897131037603019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23679606591264754025068679 35519409886897131037603019)
  ·
    refine ⟨53279114830345696556404529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35519409886897131037603019 53279114830345696556404529)
    ·
      refine ⟨39959336122759272417303397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53279114830345696556404529 39959336122759272417303397)
      ·
        refine ⟨7492375523017363578244387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39959336122759272417303397 7492375523017363578244387)
        ·
          refine ⟨11238563284526045367366581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7492375523017363578244387 11238563284526045367366581)
          ·
            refine ⟨1053615307924316753190617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11238563284526045367366581 1053615307924316753190617)
            ·
              refine ⟨790211480943237564892963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1053615307924316753190617 790211480943237564892963)
              ·
                refine ⟨1185317221414856347339445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790211480943237564892963 1185317221414856347339445)
                ·
                  refine ⟨111123489507642782563073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1185317221414856347339445 111123489507642782563073)
                  ·
                    rfl

theorem cell22_973855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 5].length) (baseStart_973855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973855 prefixEnd_973855 := by exact prefixLift 973855
  have htrace : WordTrace (prefixWord ++ tailWord_973855) baseStart_973855 baseEnd_973855 := by
    simpa [prefixWord, tailWord_973855, baseEnd_973855] using wordTrace_append hprefix tailTrace_973855
  have hstable : (prefixWord ++ tailWord_973855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973855).length < 2 ^ (prefixWord ++ tailWord_973855).sum := by decide
  have hdescent : baseEnd_973855 < baseStart_973855 := by decide
  rcases family_descends (prefixWord ++ tailWord_973855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973898 : List Nat := [3, 1, 2, 1, 1, 2, 2, 3, 4, 3]
def baseStart_973898 : Nat := 118140960795 + 973898 * 2 ^ 59
def prefixEnd_973898 : Nat := 4983230072969 + 3 ^ 40 * 973898 * 2
def baseEnd_973898 : Nat := 333385188301690568864087

theorem tailTrace_973898 : CollatzResearch.WordTrace tailWord_973898 prefixEnd_973898 333385188301690568864087 := by
  unfold tailWord_973898
  simp only [CollatzResearch.WordTrace]
  refine ⟨8880244556435337345354587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23680652150494232920945565 8880244556435337345354587)
  ·
    refine ⟨13320366834653006018031881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8880244556435337345354587 13320366834653006018031881)
    ·
      refine ⟨9990275125989754513523911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13320366834653006018031881 9990275125989754513523911)
      ·
        refine ⟨14985412688984631770285867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9990275125989754513523911 14985412688984631770285867)
        ·
          refine ⟨22478119033476947655428801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14985412688984631770285867 22478119033476947655428801)
          ·
            refine ⟨16858589275107710741571601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22478119033476947655428801 16858589275107710741571601)
            ·
              refine ⟨12643941956330783056178701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16858589275107710741571601 12643941956330783056178701)
              ·
                refine ⟨4741478233624043646067013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12643941956330783056178701 4741478233624043646067013)
                ·
                  refine ⟨889027168804508183637565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4741478233624043646067013 889027168804508183637565)
                  ·
                    refine ⟨333385188301690568864087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 889027168804508183637565 333385188301690568864087)
                    ·
                      rfl

theorem cell22_973898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_973898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973898 prefixEnd_973898 := by exact prefixLift 973898
  have htrace : WordTrace (prefixWord ++ tailWord_973898) baseStart_973898 baseEnd_973898 := by
    simpa [prefixWord, tailWord_973898, baseEnd_973898] using wordTrace_append hprefix tailTrace_973898
  have hstable : (prefixWord ++ tailWord_973898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973898).length < 2 ^ (prefixWord ++ tailWord_973898).sum := by decide
  have hdescent : baseEnd_973898 < baseStart_973898 := by decide
  rcases family_descends (prefixWord ++ tailWord_973898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973930 : List Nat := [3, 1, 3, 2, 2, 1, 3, 1, 2, 4]
def baseStart_973930 : Nat := 118140960795 + 973930 * 2 ^ 59
def prefixEnd_973930 : Nat := 4983230072969 + 3 ^ 40 * 973930 * 2
def baseEnd_973930 : Nat := 333396142555653152063989

theorem tailTrace_973930 : CollatzResearch.WordTrace tailWord_973930 prefixEnd_973930 333396142555653152063989 := by
  unfold tailWord_973930
  simp only [CollatzResearch.WordTrace]
  refine ⟨8880536340406354711645811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23681430241083612564388829 8880536340406354711645811)
  ·
    refine ⟨13320804510609532067468717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8880536340406354711645811 13320804510609532067468717)
    ·
      refine ⟨4995301691478574525300769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13320804510609532067468717 4995301691478574525300769)
      ·
        refine ⟨3746476268608930893975577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4995301691478574525300769 3746476268608930893975577)
        ·
          refine ⟨2809857201456698170481683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3746476268608930893975577 2809857201456698170481683)
          ·
            refine ⟨4214785802185047255722525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2809857201456698170481683 4214785802185047255722525)
            ·
              refine ⟨1580544675819392720895947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4214785802185047255722525 1580544675819392720895947)
              ·
                refine ⟨2370817013729089081343921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1580544675819392720895947 2370817013729089081343921)
                ·
                  refine ⟨1778112760296816811007941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2370817013729089081343921 1778112760296816811007941)
                  ·
                    refine ⟨333396142555653152063989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1778112760296816811007941 333396142555653152063989)
                    ·
                      rfl

theorem cell22_973930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_973930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973930 prefixEnd_973930 := by exact prefixLift 973930
  have htrace : WordTrace (prefixWord ++ tailWord_973930) baseStart_973930 baseEnd_973930 := by
    simpa [prefixWord, tailWord_973930, baseEnd_973930] using wordTrace_append hprefix tailTrace_973930
  have hstable : (prefixWord ++ tailWord_973930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973930).length < 2 ^ (prefixWord ++ tailWord_973930).sum := by decide
  have hdescent : baseEnd_973930 < baseStart_973930 := by decide
  rcases family_descends (prefixWord ++ tailWord_973930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973943 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 5, 3]
def baseStart_973943 : Nat := 118140960795 + 973943 * 2 ^ 59
def prefixEnd_973943 : Nat := 4983230072969 + 3 ^ 40 * 973943 * 2
def baseEnd_973943 : Nat := 333400592721325451488949

theorem tailTrace_973943 : CollatzResearch.WordTrace tailWord_973943 prefixEnd_973943 333400592721325451488949 := by
  unfold tailWord_973943
  simp only [CollatzResearch.WordTrace]
  refine ⟨35522619510578322066806483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23681746340385548044537655 35522619510578322066806483)
  ·
    refine ⟨53283929265867483100209725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35522619510578322066806483 53283929265867483100209725)
    ·
      refine ⟨19981473474700306162578647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53283929265867483100209725 19981473474700306162578647)
      ·
        refine ⟨29972210212050459243867971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19981473474700306162578647 29972210212050459243867971)
        ·
          refine ⟨44958315318075688865801957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29972210212050459243867971 44958315318075688865801957)
          ·
            refine ⟨8429684122139191662337867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44958315318075688865801957 8429684122139191662337867)
            ·
              refine ⟨12644526183208787493506801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8429684122139191662337867 12644526183208787493506801)
              ·
                refine ⟨9483394637406590620130101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12644526183208787493506801 9483394637406590620130101)
                ·
                  refine ⟨889068247256867870637197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9483394637406590620130101 889068247256867870637197)
                  ·
                    refine ⟨333400592721325451488949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 889068247256867870637197 333400592721325451488949)
                    ·
                      rfl

theorem cell22_973943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 5, 3].length) (baseStart_973943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_973943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_973943 prefixEnd_973943 := by exact prefixLift 973943
  have htrace : WordTrace (prefixWord ++ tailWord_973943) baseStart_973943 baseEnd_973943 := by
    simpa [prefixWord, tailWord_973943, baseEnd_973943] using wordTrace_append hprefix tailTrace_973943
  have hstable : (prefixWord ++ tailWord_973943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973943).length < 2 ^ (prefixWord ++ tailWord_973943).sum := by decide
  have hdescent : baseEnd_973943 < baseStart_973943 := by decide
  rcases family_descends (prefixWord ++ tailWord_973943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974033 : List Nat := [1, 2, 2, 1, 2, 2, 1, 5, 1, 5]
def baseStart_974033 : Nat := 118140960795 + 974033 * 2 ^ 59
def prefixEnd_974033 : Nat := 4983230072969 + 3 ^ 40 * 974033 * 2
def baseEnd_974033 : Nat := 333431401560595216738673

theorem tailTrace_974033 : CollatzResearch.WordTrace tailWord_974033 prefixEnd_974033 333431401560595216738673 := by
  unfold tailWord_974033
  simp only [CollatzResearch.WordTrace]
  refine ⟨35525902080252267437582753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23683934720168178291721835 35525902080252267437582753)
  ·
    refine ⟨26644426560189200578187065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35525902080252267437582753 26644426560189200578187065)
    ·
      refine ⟨19983319920141900433640299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26644426560189200578187065 19983319920141900433640299)
      ·
        refine ⟨29974979880212850650460449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19983319920141900433640299 29974979880212850650460449)
        ·
          refine ⟨22481234910159637987845337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29974979880212850650460449 22481234910159637987845337)
          ·
            refine ⟨16860926182619728490884003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22481234910159637987845337 16860926182619728490884003)
            ·
              refine ⟨25291389273929592736326005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16860926182619728490884003 25291389273929592736326005)
              ·
                refine ⟨2371067744430899319030563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25291389273929592736326005 2371067744430899319030563)
                ·
                  refine ⟨3556601616646348978545845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2371067744430899319030563 3556601616646348978545845)
                  ·
                    refine ⟨333431401560595216738673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3556601616646348978545845 333431401560595216738673)
                    ·
                      rfl

theorem cell22_974033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_974033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_974033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_974033 prefixEnd_974033 := by exact prefixLift 974033
  have htrace : WordTrace (prefixWord ++ tailWord_974033) baseStart_974033 baseEnd_974033 := by
    simpa [prefixWord, tailWord_974033, baseEnd_974033] using wordTrace_append hprefix tailTrace_974033
  have hstable : (prefixWord ++ tailWord_974033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974033).length < 2 ^ (prefixWord ++ tailWord_974033).sum := by decide
  have hdescent : baseEnd_974033 < baseStart_974033 := by decide
  rcases family_descends (prefixWord ++ tailWord_974033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974037 : List Nat := [1, 3, 2, 4, 1, 1, 3, 2, 1, 4]
def baseStart_974037 : Nat := 118140960795 + 974037 * 2 ^ 59
def prefixEnd_974037 : Nat := 4983230072969 + 3 ^ 40 * 974037 * 2
def baseEnd_974037 : Nat := 333432770842340539638661

theorem tailTrace_974037 : CollatzResearch.WordTrace tailWord_974037 prefixEnd_974037 333432770842340539638661 := by
  unfold tailWord_974037
  simp only [CollatzResearch.WordTrace]
  refine ⟨35526047972237776120728365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23684031981491850747152243 35526047972237776120728365)
  ·
    refine ⟨13322267989589166045273137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35526047972237776120728365 13322267989589166045273137)
    ·
      refine ⟨9991700992191874533954853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13322267989589166045273137 9991700992191874533954853)
      ·
        refine ⟨1873443936035976475116535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9991700992191874533954853 1873443936035976475116535)
        ·
          refine ⟨2810165904053964712674803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1873443936035976475116535 2810165904053964712674803)
          ·
            refine ⟨4215248856080947069012205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2810165904053964712674803 4215248856080947069012205)
            ·
              refine ⟨1580718321030355150879577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4215248856080947069012205 1580718321030355150879577)
              ·
                refine ⟨1185538740772766363159683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1580718321030355150879577 1185538740772766363159683)
                ·
                  refine ⟨1778308111159149544739525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1185538740772766363159683 1778308111159149544739525)
                  ·
                    refine ⟨333432770842340539638661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1778308111159149544739525 333432770842340539638661)
                    ·
                      rfl

theorem cell22_974037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_974037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_974037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_974037 prefixEnd_974037 := by exact prefixLift 974037
  have htrace : WordTrace (prefixWord ++ tailWord_974037) baseStart_974037 baseEnd_974037 := by
    simpa [prefixWord, tailWord_974037, baseEnd_974037] using wordTrace_append hprefix tailTrace_974037
  have hstable : (prefixWord ++ tailWord_974037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974037).length < 2 ^ (prefixWord ++ tailWord_974037).sum := by decide
  have hdescent : baseEnd_974037 < baseStart_974037 := by decide
  rcases family_descends (prefixWord ++ tailWord_974037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974063 : List Nat := [1, 1, 2, 1, 7, 10]
def baseStart_974063 : Nat := 118140960795 + 974063 * 2 ^ 59
def prefixEnd_974063 : Nat := 4983230072969 + 3 ^ 40 * 974063 * 2
def baseEnd_974063 : Nat := 4116563841650433808501

theorem tailTrace_974063 : CollatzResearch.WordTrace tailWord_974063 prefixEnd_974063 4116563841650433808501 := by
  unfold tailWord_974063
  simp only [CollatzResearch.WordTrace]
  refine ⟨35526996270143582561174843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23684664180095721707449895 35526996270143582561174843)
  ·
    refine ⟨53290494405215373841762265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35526996270143582561174843 53290494405215373841762265)
    ·
      refine ⟨39967870803911530381321699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53290494405215373841762265 39967870803911530381321699)
      ·
        refine ⟨59951806205867295571982549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39967870803911530381321699 59951806205867295571982549)
        ·
          refine ⟨1405120457950014739968341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 59951806205867295571982549 1405120457950014739968341)
          ·
            refine ⟨4116563841650433808501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1405120457950014739968341 4116563841650433808501)
            ·
              rfl

theorem cell22_974063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 10].length) (baseStart_974063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_974063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_974063 prefixEnd_974063 := by exact prefixLift 974063
  have htrace : WordTrace (prefixWord ++ tailWord_974063) baseStart_974063 baseEnd_974063 := by
    simpa [prefixWord, tailWord_974063, baseEnd_974063] using wordTrace_append hprefix tailTrace_974063
  have hstable : (prefixWord ++ tailWord_974063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974063).length < 2 ^ (prefixWord ++ tailWord_974063).sum := by decide
  have hdescent : baseEnd_974063 < baseStart_974063 := by decide
  rcases family_descends (prefixWord ++ tailWord_974063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974067 : List Nat := [1, 1, 1, 2, 2, 6, 2, 2, 2, 3]
def baseStart_974067 : Nat := 118140960795 + 974067 * 2 ^ 59
def prefixEnd_974067 : Nat := 4983230072969 + 3 ^ 40 * 974067 * 2
def baseEnd_974067 : Nat := 333443040455430461388569

theorem tailTrace_974067 : CollatzResearch.WordTrace tailWord_974067 prefixEnd_974067 333443040455430461388569 := by
  unfold tailWord_974067
  simp only [CollatzResearch.WordTrace]
  refine ⟨35527142162129091244320455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23684761441419394162880303 35527142162129091244320455)
  ·
    refine ⟨53290713243193636866480683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35527142162129091244320455 53290713243193636866480683)
    ·
      refine ⟨79936069864790455299721025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53290713243193636866480683 79936069864790455299721025)
      ·
        refine ⟨59952052398592841474790769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79936069864790455299721025 59952052398592841474790769)
        ·
          refine ⟨44964039298944631106093077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59952052398592841474790769 44964039298944631106093077)
          ·
            refine ⟨2107689342138029583098113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44964039298944631106093077 2107689342138029583098113)
            ·
              refine ⟨1580767006603522187323585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2107689342138029583098113 1580767006603522187323585)
              ·
                refine ⟨1185575254952641640492689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1580767006603522187323585 1185575254952641640492689)
                ·
                  refine ⟨889181441214481230369517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1185575254952641640492689 889181441214481230369517)
                  ·
                    refine ⟨333443040455430461388569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 889181441214481230369517 333443040455430461388569)
                    ·
                      rfl

theorem cell22_974067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 2, 3].length) (baseStart_974067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_974067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_974067 prefixEnd_974067 := by exact prefixLift 974067
  have htrace : WordTrace (prefixWord ++ tailWord_974067) baseStart_974067 baseEnd_974067 := by
    simpa [prefixWord, tailWord_974067, baseEnd_974067] using wordTrace_append hprefix tailTrace_974067
  have hstable : (prefixWord ++ tailWord_974067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974067).length < 2 ^ (prefixWord ++ tailWord_974067).sum := by decide
  have hdescent : baseEnd_974067 < baseStart_974067 := by decide
  rcases family_descends (prefixWord ++ tailWord_974067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974129 : List Nat := [1, 2, 2, 3, 3, 1, 2, 4, 1, 3]
def baseStart_974129 : Nat := 118140960795 + 974129 * 2 ^ 59
def prefixEnd_974129 : Nat := 4983230072969 + 3 ^ 40 * 974129 * 2
def baseEnd_974129 : Nat := 333464264322482966338379

theorem tailTrace_974129 : CollatzResearch.WordTrace tailWord_974129 prefixEnd_974129 333464264322482966338379 := by
  unfold tailWord_974129
  simp only [CollatzResearch.WordTrace]
  refine ⟨35529403487904475833077441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23686268991936317222051627 35529403487904475833077441)
  ·
    refine ⟨26647052615928356874808081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35529403487904475833077441 26647052615928356874808081)
    ·
      refine ⟨19985289461946267656106061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26647052615928356874808081 19985289461946267656106061)
      ·
        refine ⟨7494483548229850371039773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19985289461946267656106061 7494483548229850371039773)
        ·
          refine ⟨2810431330586193889139915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7494483548229850371039773 2810431330586193889139915)
          ·
            refine ⟨4215646995879290833709873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2810431330586193889139915 4215646995879290833709873)
            ·
              refine ⟨3161735246909468125282405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4215646995879290833709873 3161735246909468125282405)
              ·
                refine ⟨592825358795525273490451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3161735246909468125282405 592825358795525273490451)
                ·
                  refine ⟨889238038193287910235677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 592825358795525273490451 889238038193287910235677)
                  ·
                    refine ⟨333464264322482966338379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 889238038193287910235677 333464264322482966338379)
                    ·
                      rfl

theorem cell22_974129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 4, 1, 3].length) (baseStart_974129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_974129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_974129 prefixEnd_974129 := by exact prefixLift 974129
  have htrace : WordTrace (prefixWord ++ tailWord_974129) baseStart_974129 baseEnd_974129 := by
    simpa [prefixWord, tailWord_974129, baseEnd_974129] using wordTrace_append hprefix tailTrace_974129
  have hstable : (prefixWord ++ tailWord_974129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974129).length < 2 ^ (prefixWord ++ tailWord_974129).sum := by decide
  have hdescent : baseEnd_974129 < baseStart_974129 := by decide
  rcases family_descends (prefixWord ++ tailWord_974129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974140 : List Nat := [2, 2, 2, 2, 1, 3, 2, 1, 2, 5]
def baseStart_974140 : Nat := 118140960795 + 974140 * 2 ^ 59
def prefixEnd_974140 : Nat := 4983230072969 + 3 ^ 40 * 974140 * 2
def baseEnd_974140 : Nat := 333468029847282604313345

theorem tailTrace_974140 : CollatzResearch.WordTrace tailWord_974140 prefixEnd_974140 333468029847282604313345 := by
  unfold tailWord_974140
  simp only [CollatzResearch.WordTrace]
  refine ⟨17764902345432312355863937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23686536460576416474485249 17764902345432312355863937)
  ·
    refine ⟨13323676759074234266897953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17764902345432312355863937 13323676759074234266897953)
    ·
      refine ⟨9992757569305675700173465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13323676759074234266897953 9992757569305675700173465)
      ·
        refine ⟨7494568176979256775130099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9992757569305675700173465 7494568176979256775130099)
        ·
          refine ⟨11241852265468885162695149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7494568176979256775130099 11241852265468885162695149)
          ·
            refine ⟨4215694599550831936010681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11241852265468885162695149 4215694599550831936010681)
            ·
              refine ⟨3161770949663123952008011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4215694599550831936010681 3161770949663123952008011)
              ·
                refine ⟨4742656424494685928012017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3161770949663123952008011 4742656424494685928012017)
                ·
                  refine ⟨3556992318371014446009013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4742656424494685928012017 3556992318371014446009013)
                  ·
                    refine ⟨333468029847282604313345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3556992318371014446009013 333468029847282604313345)
                    ·
                      rfl

theorem cell22_974140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_974140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_974140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_974140 prefixEnd_974140 := by exact prefixLift 974140
  have htrace : WordTrace (prefixWord ++ tailWord_974140) baseStart_974140 baseEnd_974140 := by
    simpa [prefixWord, tailWord_974140, baseEnd_974140] using wordTrace_append hprefix tailTrace_974140
  have hstable : (prefixWord ++ tailWord_974140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974140).length < 2 ^ (prefixWord ++ tailWord_974140).sum := by decide
  have hdescent : baseEnd_974140 < baseStart_974140 := by decide
  rcases family_descends (prefixWord ++ tailWord_974140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974202 : List Nat := [3, 1, 1, 1, 1, 1, 2, 7, 2, 3]
def baseStart_974202 : Nat := 118140960795 + 974202 * 2 ^ 59
def prefixEnd_974202 : Nat := 4983230072969 + 3 ^ 40 * 974202 * 2
def baseEnd_974202 : Nat := 333489253714335109263155

theorem tailTrace_974202 : CollatzResearch.WordTrace tailWord_974202 prefixEnd_974202 333489253714335109263155 := by
  unfold tailWord_974202
  simp only [CollatzResearch.WordTrace]
  refine ⟨8883016504160002325121215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23688044011093339533656573 8883016504160002325121215)
  ·
    refine ⟨13324524756240003487681823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8883016504160002325121215 13324524756240003487681823)
    ·
      refine ⟨19986787134360005231522735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13324524756240003487681823 19986787134360005231522735)
      ·
        refine ⟨29980180701540007847284103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19986787134360005231522735 29980180701540007847284103)
        ·
          refine ⟨44970271052310011770926155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29980180701540007847284103 44970271052310011770926155)
          ·
            refine ⟨67455406578465017656389233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44970271052310011770926155 67455406578465017656389233)
            ·
              refine ⟨50591554933848763242291925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67455406578465017656389233 50591554933848763242291925)
              ·
                refine ⟨1185739568762080388491217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 50591554933848763242291925 1185739568762080388491217)
                ·
                  refine ⟨889304676571560291368413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1185739568762080388491217 889304676571560291368413)
                  ·
                    refine ⟨333489253714335109263155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 889304676571560291368413 333489253714335109263155)
                    ·
                      rfl

theorem cell22_974202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 2, 3].length) (baseStart_974202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_974202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_974202 prefixEnd_974202 := by exact prefixLift 974202
  have htrace : WordTrace (prefixWord ++ tailWord_974202) baseStart_974202 baseEnd_974202 := by
    simpa [prefixWord, tailWord_974202, baseEnd_974202] using wordTrace_append hprefix tailTrace_974202
  have hstable : (prefixWord ++ tailWord_974202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974202).length < 2 ^ (prefixWord ++ tailWord_974202).sum := by decide
  have hdescent : baseEnd_974202 < baseStart_974202 := by decide
  rcases family_descends (prefixWord ++ tailWord_974202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974206 : List Nat := [4, 2, 3, 2, 1, 1, 1, 1, 3, 4]
def baseStart_974206 : Nat := 118140960795 + 974206 * 2 ^ 59
def prefixEnd_974206 : Nat := 4983230072969 + 3 ^ 40 * 974206 * 2
def baseEnd_974206 : Nat := 333490622996080432163143

theorem tailTrace_974206 : CollatzResearch.WordTrace tailWord_974206 prefixEnd_974206 333490622996080432163143 := by
  unfold tailWord_974206
  simp only [CollatzResearch.WordTrace]
  refine ⟨4441526488578189747953809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23688141272417011989086981 4441526488578189747953809)
  ·
    refine ⟨3331144866433642310965357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4441526488578189747953809 3331144866433642310965357)
    ·
      refine ⟨1249179324912615866612009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3331144866433642310965357 1249179324912615866612009)
      ·
        refine ⟨936884493684461899959007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1249179324912615866612009 936884493684461899959007)
        ·
          refine ⟨1405326740526692849938511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 936884493684461899959007 1405326740526692849938511)
          ·
            refine ⟨2107990110790039274907767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1405326740526692849938511 2107990110790039274907767)
            ·
              refine ⟨3161985166185058912361651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2107990110790039274907767 3161985166185058912361651)
              ·
                refine ⟨4742977749277588368542477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3161985166185058912361651 4742977749277588368542477)
                ·
                  refine ⟨1778616655979095638203429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4742977749277588368542477 1778616655979095638203429)
                  ·
                    refine ⟨333490622996080432163143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1778616655979095638203429 333490622996080432163143)
                    ·
                      rfl

theorem cell22_974206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_974206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_974206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_974206 prefixEnd_974206 := by exact prefixLift 974206
  have htrace : WordTrace (prefixWord ++ tailWord_974206) baseStart_974206 baseEnd_974206 := by
    simpa [prefixWord, tailWord_974206, baseEnd_974206] using wordTrace_append hprefix tailTrace_974206
  have hstable : (prefixWord ++ tailWord_974206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974206).length < 2 ^ (prefixWord ++ tailWord_974206).sum := by decide
  have hdescent : baseEnd_974206 < baseStart_974206 := by decide
  rcases family_descends (prefixWord ++ tailWord_974206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974215 : List Nat := [1, 1, 4, 2, 2, 2, 2, 8]
def baseStart_974215 : Nat := 118140960795 + 974215 * 2 ^ 59
def prefixEnd_974215 : Nat := 4983230072969 + 3 ^ 40 * 974215 * 2
def baseEnd_974215 : Nat := 37054855986667489854235

theorem tailTrace_974215 : CollatzResearch.WordTrace tailWord_974215 prefixEnd_974215 37054855986667489854235 := by
  unfold tailWord_974215
  simp only [CollatzResearch.WordTrace]
  refine ⟨35532540165592912520708099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23688360110395275013805399 35532540165592912520708099)
  ·
    refine ⟨53298810248389368781062149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35532540165592912520708099 53298810248389368781062149)
    ·
      refine ⟨9993526921573006646449153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53298810248389368781062149 9993526921573006646449153)
      ·
        refine ⟨7495145191179754984836865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9993526921573006646449153 7495145191179754984836865)
        ·
          refine ⟨5621358893384816238627649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7495145191179754984836865 5621358893384816238627649)
          ·
            refine ⟨4216019170038612178970737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5621358893384816238627649 4216019170038612178970737)
            ·
              refine ⟨3162014377528959134228053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4216019170038612178970737 3162014377528959134228053)
              ·
                refine ⟨37054855986667489854235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3162014377528959134228053 37054855986667489854235)
                ·
                  rfl

theorem cell22_974215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 8].length) (baseStart_974215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_974215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_974215 prefixEnd_974215 := by exact prefixLift 974215
  have htrace : WordTrace (prefixWord ++ tailWord_974215) baseStart_974215 baseEnd_974215 := by
    simpa [prefixWord, tailWord_974215, baseEnd_974215] using wordTrace_append hprefix tailTrace_974215
  have hstable : (prefixWord ++ tailWord_974215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974215).length < 2 ^ (prefixWord ++ tailWord_974215).sum := by decide
  have hdescent : baseEnd_974215 < baseStart_974215 := by decide
  rcases family_descends (prefixWord ++ tailWord_974215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974232 : List Nat := [2, 1, 2, 5, 3, 9]
def baseStart_974232 : Nat := 118140960795 + 974232 * 2 ^ 59
def prefixEnd_974232 : Nat := 4983230072969 + 3 ^ 40 * 974232 * 2
def baseEnd_974232 : Nat := 4117278065770679395223

theorem tailTrace_974232 : CollatzResearch.WordTrace tailWord_974232 prefixEnd_974232 4117278065770679395223 := by
  unfold tailWord_974232
  simp only [CollatzResearch.WordTrace]
  refine ⟨17766580103265662212038475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23688773471020882949384633 17766580103265662212038475)
  ·
    refine ⟨26649870154898493318057713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17766580103265662212038475 26649870154898493318057713)
    ·
      refine ⟨19987402616173869988543285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26649870154898493318057713 19987402616173869988543285)
      ·
        refine ⟨1873818995266300311425933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19987402616173869988543285 1873818995266300311425933)
        ·
          refine ⟨702682123224862616784725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1873818995266300311425933 702682123224862616784725)
          ·
            refine ⟨4117278065770679395223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 702682123224862616784725 4117278065770679395223)
            ·
              rfl

theorem cell22_974232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 9].length) (baseStart_974232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_974232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_974232 prefixEnd_974232 := by exact prefixLift 974232
  have htrace : WordTrace (prefixWord ++ tailWord_974232) baseStart_974232 baseEnd_974232 := by
    simpa [prefixWord, tailWord_974232, baseEnd_974232] using wordTrace_append hprefix tailTrace_974232
  have hstable : (prefixWord ++ tailWord_974232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974232).length < 2 ^ (prefixWord ++ tailWord_974232).sum := by decide
  have hdescent : baseEnd_974232 < baseStart_974232 := by decide
  rcases family_descends (prefixWord ++ tailWord_974232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974274 : List Nat := [3, 5, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_974274 : Nat := 118140960795 + 974274 * 2 ^ 59
def prefixEnd_974274 : Nat := 4983230072969 + 3 ^ 40 * 974274 * 2
def baseEnd_974274 : Nat := 333513900785750921462935

theorem tailTrace_974274 : CollatzResearch.WordTrace tailWord_974274 prefixEnd_974274 333513900785750921462935 := by
  unfold tailWord_974274
  simp only [CollatzResearch.WordTrace]
  refine ⟨8883673018094791399276469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23689794714919443731403917 8883673018094791399276469)
  ·
    refine ⟨832844345446386693682169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8883673018094791399276469 832844345446386693682169)
    ·
      refine ⟨624633259084790020261627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 832844345446386693682169 624633259084790020261627)
      ·
        refine ⟨936949888627185030392441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624633259084790020261627 936949888627185030392441)
        ·
          refine ⟨702712416470388772794331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 936949888627185030392441 702712416470388772794331)
          ·
            refine ⟨1054068624705583159191497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702712416470388772794331 1054068624705583159191497)
            ·
              refine ⟨790551468529187369393623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1054068624705583159191497 790551468529187369393623)
              ·
                refine ⟨1185827202793781054090435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790551468529187369393623 1185827202793781054090435)
                ·
                  refine ⟨1778740804190671581135653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1185827202793781054090435 1778740804190671581135653)
                  ·
                    refine ⟨333513900785750921462935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1778740804190671581135653 333513900785750921462935)
                    ·
                      rfl

theorem cell22_974274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_974274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_974274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_974274 prefixEnd_974274 := by exact prefixLift 974274
  have htrace : WordTrace (prefixWord ++ tailWord_974274) baseStart_974274 baseEnd_974274 := by
    simpa [prefixWord, tailWord_974274, baseEnd_974274] using wordTrace_append hprefix tailTrace_974274
  have hstable : (prefixWord ++ tailWord_974274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974274).length < 2 ^ (prefixWord ++ tailWord_974274).sum := by decide
  have hdescent : baseEnd_974274 < baseStart_974274 := by decide
  rcases family_descends (prefixWord ++ tailWord_974274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974294 : List Nat := [5, 2, 1, 1, 1, 3, 1, 1, 7]
def baseStart_974294 : Nat := 118140960795 + 974294 * 2 ^ 59
def prefixEnd_974294 : Nat := 4983230072969 + 3 ^ 40 * 974294 * 2
def baseEnd_974294 : Nat := 111173582398159178654291

theorem tailTrace_974294 : CollatzResearch.WordTrace tailWord_974294 prefixEnd_974294 111173582398159178654291 := by
  unfold tailWord_974294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2220963845769169313302121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23690281021537806008555957 2220963845769169313302121)
  ·
    refine ⟨1665722884326876984976591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2220963845769169313302121 1665722884326876984976591)
    ·
      refine ⟨2498584326490315477464887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1665722884326876984976591 2498584326490315477464887)
      ·
        refine ⟨3747876489735473216197331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2498584326490315477464887 3747876489735473216197331)
        ·
          refine ⟨5621814734603209824295997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3747876489735473216197331 5621814734603209824295997)
          ·
            refine ⟨2108180525476203684110999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5621814734603209824295997 2108180525476203684110999)
            ·
              refine ⟨3162270788214305526166499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2108180525476203684110999 3162270788214305526166499)
              ·
                refine ⟨4743406182321458289249749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3162270788214305526166499 4743406182321458289249749)
                ·
                  refine ⟨111173582398159178654291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4743406182321458289249749 111173582398159178654291)
                  ·
                    rfl

theorem cell22_974294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_974294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_974294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_974294 prefixEnd_974294 := by exact prefixLift 974294
  have htrace : WordTrace (prefixWord ++ tailWord_974294) baseStart_974294 baseEnd_974294 := by
    simpa [prefixWord, tailWord_974294, baseEnd_974294] using wordTrace_append hprefix tailTrace_974294
  have hstable : (prefixWord ++ tailWord_974294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974294).length < 2 ^ (prefixWord ++ tailWord_974294).sum := by decide
  have hdescent : baseEnd_974294 < baseStart_974294 := by decide
  rcases family_descends (prefixWord ++ tailWord_974294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974371 : List Nat := [1, 1, 1, 4, 5, 1, 1, 3, 2, 3]
def baseStart_974371 : Nat := 118140960795 + 974371 * 2 ^ 59
def prefixEnd_974371 : Nat := 4983230072969 + 3 ^ 40 * 974371 * 2
def baseEnd_974371 : Nat := 333547105868075001787637

theorem tailTrace_974371 : CollatzResearch.WordTrace tailWord_974371 prefixEnd_974371 333547105868075001787637 := by
  unfold tailWord_974371
  simp only [CollatzResearch.WordTrace]
  refine ⟨35538229953027751163386967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23692153302018500775591311 35538229953027751163386967)
  ·
    refine ⟨53307344929541626745080451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35538229953027751163386967 53307344929541626745080451)
    ·
      refine ⟨79961017394312440117620677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53307344929541626745080451 79961017394312440117620677)
      ·
        refine ⟨14992690761433582522053877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79961017394312440117620677 14992690761433582522053877)
        ·
          refine ⟨1405564758884398361442551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14992690761433582522053877 1405564758884398361442551)
          ·
            refine ⟨2108347138326597542163827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1405564758884398361442551 2108347138326597542163827)
            ·
              refine ⟨3162520707489896313245741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2108347138326597542163827 3162520707489896313245741)
              ·
                refine ⟨1185945265308711117467153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3162520707489896313245741 1185945265308711117467153)
                ·
                  refine ⟨889458948981533338100365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1185945265308711117467153 889458948981533338100365)
                  ·
                    refine ⟨333547105868075001787637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 889458948981533338100365 333547105868075001787637)
                    ·
                      rfl

theorem cell22_974371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 2, 3].length) (baseStart_974371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_974371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_974371 prefixEnd_974371 := by exact prefixLift 974371
  have htrace : WordTrace (prefixWord ++ tailWord_974371) baseStart_974371 baseEnd_974371 := by
    simpa [prefixWord, tailWord_974371, baseEnd_974371] using wordTrace_append hprefix tailTrace_974371
  have hstable : (prefixWord ++ tailWord_974371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974371).length < 2 ^ (prefixWord ++ tailWord_974371).sum := by decide
  have hdescent : baseEnd_974371 < baseStart_974371 := by decide
  rcases family_descends (prefixWord ++ tailWord_974371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974416 : List Nat := [2, 1, 1, 1, 1, 3, 5, 4, 1, 3]
def baseStart_974416 : Nat := 118140960795 + 974416 * 2 ^ 59
def prefixEnd_974416 : Nat := 4983230072969 + 3 ^ 40 * 974416 * 2
def baseEnd_974416 : Nat := 333562510287709884412499

theorem tailTrace_974416 : CollatzResearch.WordTrace tailWord_974416 prefixEnd_974416 333562510287709884412499 := by
  unfold tailWord_974416
  simp only [CollatzResearch.WordTrace]
  refine ⟨17769935618932361924387551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23693247491909815899183401 17769935618932361924387551)
  ·
    refine ⟨26654903428398542886581327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17769935618932361924387551 26654903428398542886581327)
    ·
      refine ⟨39982355142597814329871991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26654903428398542886581327 39982355142597814329871991)
      ·
        refine ⟨59973532713896721494807987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39982355142597814329871991 59973532713896721494807987)
        ·
          refine ⟨89960299070845082242211981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59973532713896721494807987 89960299070845082242211981)
          ·
            refine ⟨33735112151566905840829493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89960299070845082242211981 33735112151566905840829493)
            ·
              refine ⟨3162666764209397422577765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33735112151566905840829493 3162666764209397422577765)
              ·
                refine ⟨593000018289262016733331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3162666764209397422577765 593000018289262016733331)
                ·
                  refine ⟨889500027433893025099997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 593000018289262016733331 889500027433893025099997)
                  ·
                    refine ⟨333562510287709884412499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 889500027433893025099997 333562510287709884412499)
                    ·
                      rfl

theorem cell22_974416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 4, 1, 3].length) (baseStart_974416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_974416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_974416 prefixEnd_974416 := by exact prefixLift 974416
  have htrace : WordTrace (prefixWord ++ tailWord_974416) baseStart_974416 baseEnd_974416 := by
    simpa [prefixWord, tailWord_974416, baseEnd_974416] using wordTrace_append hprefix tailTrace_974416
  have hstable : (prefixWord ++ tailWord_974416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974416).length < 2 ^ (prefixWord ++ tailWord_974416).sum := by decide
  have hdescent : baseEnd_974416 < baseStart_974416 := by decide
  rcases family_descends (prefixWord ++ tailWord_974416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974457 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 8]
def baseStart_974457 : Nat := 118140960795 + 974457 * 2 ^ 59
def prefixEnd_974457 : Nat := 4983230072969 + 3 ^ 40 * 974457 * 2
def baseEnd_974457 : Nat := 111192181808533148045791

theorem tailTrace_974457 : CollatzResearch.WordTrace tailWord_974457 prefixEnd_974457 111192181808533148045791 := by
  unfold tailWord_974457
  simp only [CollatzResearch.WordTrace]
  refine ⟨35541366630716187851017625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23694244420477458567345083 35541366630716187851017625)
  ·
    refine ⟨26656024973037140888263219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35541366630716187851017625 26656024973037140888263219)
    ·
      refine ⟨39984037459555711332394829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26656024973037140888263219 39984037459555711332394829)
      ·
        refine ⟨14994014047333391749648061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39984037459555711332394829 14994014047333391749648061)
        ·
          refine ⟨5622755267750021906118023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14994014047333391749648061 5622755267750021906118023)
          ·
            refine ⟨8434132901625032859177035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5622755267750021906118023 8434132901625032859177035)
            ·
              refine ⟨12651199352437549288765553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8434132901625032859177035 12651199352437549288765553)
              ·
                refine ⟨9488399514328161966574165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12651199352437549288765553 9488399514328161966574165)
                ·
                  refine ⟨111192181808533148045791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9488399514328161966574165 111192181808533148045791)
                  ·
                    rfl

theorem cell22_974457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 8].length) (baseStart_974457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_974457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_974457 prefixEnd_974457 := by exact prefixLift 974457
  have htrace : WordTrace (prefixWord ++ tailWord_974457) baseStart_974457 baseEnd_974457 := by
    simpa [prefixWord, tailWord_974457, baseEnd_974457] using wordTrace_append hprefix tailTrace_974457
  have hstable : (prefixWord ++ tailWord_974457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974457).length < 2 ^ (prefixWord ++ tailWord_974457).sum := by decide
  have hdescent : baseEnd_974457 < baseStart_974457 := by decide
  rcases family_descends (prefixWord ++ tailWord_974457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974459 : List Nat := [1, 1, 1, 1, 1, 4, 5, 3, 1, 4]
def baseStart_974459 : Nat := 118140960795 + 974459 * 2 ^ 59
def prefixEnd_974459 : Nat := 4983230072969 + 3 ^ 40 * 974459 * 2
def baseEnd_974459 : Nat := 333577230066472105587367

theorem tailTrace_974459 : CollatzResearch.WordTrace tailWord_974459 prefixEnd_974459 333577230066472105587367 := by
  unfold tailWord_974459
  simp only [CollatzResearch.WordTrace]
  refine ⟨35541439576708942192590431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23694293051139294795060287 35541439576708942192590431)
  ·
    refine ⟨53312159365063413288885647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35541439576708942192590431 53312159365063413288885647)
    ·
      refine ⟨79968239047595119933328471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53312159365063413288885647 79968239047595119933328471)
      ·
        refine ⟨119952358571392679899992707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79968239047595119933328471 119952358571392679899992707)
        ·
          refine ⟨179928537857089019849989061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119952358571392679899992707 179928537857089019849989061)
          ·
            refine ⟨33736600848204191221872949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179928537857089019849989061 33736600848204191221872949)
            ·
              refine ⟨3162806329519142927050589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33736600848204191221872949 3162806329519142927050589)
              ·
                refine ⟨1186052373569678597643971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3162806329519142927050589 1186052373569678597643971)
                ·
                  refine ⟨1779078560354517896465957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1186052373569678597643971 1779078560354517896465957)
                  ·
                    refine ⟨333577230066472105587367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1779078560354517896465957 333577230066472105587367)
                    ·
                      rfl

theorem cell22_974459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 4].length) (baseStart_974459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_974459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_974459 prefixEnd_974459 := by exact prefixLift 974459
  have htrace : WordTrace (prefixWord ++ tailWord_974459) baseStart_974459 baseEnd_974459 := by
    simpa [prefixWord, tailWord_974459, baseEnd_974459] using wordTrace_append hprefix tailTrace_974459
  have hstable : (prefixWord ++ tailWord_974459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974459).length < 2 ^ (prefixWord ++ tailWord_974459).sum := by decide
  have hdescent : baseEnd_974459 < baseStart_974459 := by decide
  rcases family_descends (prefixWord ++ tailWord_974459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974474 : List Nat := [3, 1, 2, 3, 2, 1, 1, 3, 6]
def baseStart_974474 : Nat := 118140960795 + 974474 * 2 ^ 59
def prefixEnd_974474 : Nat := 4983230072969 + 3 ^ 40 * 974474 * 2
def baseEnd_974474 : Nat := 111194121624339022154107

theorem tailTrace_974474 : CollatzResearch.WordTrace tailWord_974474 prefixEnd_974474 111194121624339022154107 := by
  unfold tailWord_974474
  simp only [CollatzResearch.WordTrace]
  refine ⟨8885496667913649938596619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23694657781103066502924317 8885496667913649938596619)
  ·
    refine ⟨13328245001870474907894929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8885496667913649938596619 13328245001870474907894929)
    ·
      refine ⟨9996183751402856180921197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13328245001870474907894929 9996183751402856180921197)
      ·
        refine ⟨3748568906776071067845449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9996183751402856180921197 3748568906776071067845449)
        ·
          refine ⟨2811426680082053300884087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3748568906776071067845449 2811426680082053300884087)
          ·
            refine ⟨4217140020123079951326131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2811426680082053300884087 4217140020123079951326131)
            ·
              refine ⟨6325710030184619926989197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4217140020123079951326131 6325710030184619926989197)
              ·
                refine ⟨2372141261319232472620949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6325710030184619926989197 2372141261319232472620949)
                ·
                  refine ⟨111194121624339022154107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2372141261319232472620949 111194121624339022154107)
                  ·
                    rfl

theorem cell22_974474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 6].length) (baseStart_974474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_974474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_974474 prefixEnd_974474 := by exact prefixLift 974474
  have htrace : WordTrace (prefixWord ++ tailWord_974474) baseStart_974474 baseEnd_974474 := by
    simpa [prefixWord, tailWord_974474, baseEnd_974474] using wordTrace_append hprefix tailTrace_974474
  have hstable : (prefixWord ++ tailWord_974474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974474).length < 2 ^ (prefixWord ++ tailWord_974474).sum := by decide
  have hdescent : baseEnd_974474 < baseStart_974474 := by decide
  rcases family_descends (prefixWord ++ tailWord_974474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974519 : List Nat := [1, 1, 3, 1, 5, 3, 8]
def baseStart_974519 : Nat := 118140960795 + 974519 * 2 ^ 59
def prefixEnd_974519 : Nat := 4983230072969 + 3 ^ 40 * 974519 * 2
def baseEnd_974519 : Nat := 12355472936764887003229

theorem tailTrace_974519 : CollatzResearch.WordTrace tailWord_974519 prefixEnd_974519 12355472936764887003229 := by
  unfold tailWord_974519
  simp only [CollatzResearch.WordTrace]
  refine ⟨35543627956491572439774611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23695751970994381626516407 35543627956491572439774611)
  ·
    refine ⟨53315441934737358659661917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35543627956491572439774611 53315441934737358659661917)
    ·
      refine ⟨19993290725526509497373219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53315441934737358659661917 19993290725526509497373219)
      ·
        refine ⟨29989936088289764246059829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19993290725526509497373219 29989936088289764246059829)
        ·
          refine ⟨2811556508277165398068109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29989936088289764246059829 2811556508277165398068109)
          ·
            refine ⟨1054333690603937024275541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2811556508277165398068109 1054333690603937024275541)
            ·
              refine ⟨12355472936764887003229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1054333690603937024275541 12355472936764887003229)
              ·
                rfl

theorem cell22_974519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 8].length) (baseStart_974519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_974519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_974519 prefixEnd_974519 := by exact prefixLift 974519
  have htrace : WordTrace (prefixWord ++ tailWord_974519) baseStart_974519 baseEnd_974519 := by
    simpa [prefixWord, tailWord_974519, baseEnd_974519] using wordTrace_append hprefix tailTrace_974519
  have hstable : (prefixWord ++ tailWord_974519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974519).length < 2 ^ (prefixWord ++ tailWord_974519).sum := by decide
  have hdescent : baseEnd_974519 < baseStart_974519 := by decide
  rcases family_descends (prefixWord ++ tailWord_974519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974596 : List Nat := [2, 3, 2, 2, 1, 3, 1, 1, 2, 5]
def baseStart_974596 : Nat := 118140960795 + 974596 * 2 ^ 59
def prefixEnd_974596 : Nat := 4983230072969 + 3 ^ 40 * 974596 * 2
def baseEnd_974596 : Nat := 333624127966249414911947

theorem tailTrace_974596 : CollatzResearch.WordTrace tailWord_974596 prefixEnd_974596 333624127966249414911947 := by
  unfold tailWord_974596
  simp only [CollatzResearch.WordTrace]
  refine ⟨17773218188606307295163821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23697624251475076393551761 17773218188606307295163821)
  ·
    refine ⟨6664956820727365235686433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17773218188606307295163821 6664956820727365235686433)
    ·
      refine ⟨4998717615545523926764825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6664956820727365235686433 4998717615545523926764825)
      ·
        refine ⟨3749038211659142945073619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4998717615545523926764825 3749038211659142945073619)
        ·
          refine ⟨5623557317488714417610429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3749038211659142945073619 5623557317488714417610429)
          ·
            refine ⟨2108833994058267906603911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5623557317488714417610429 2108833994058267906603911)
            ·
              refine ⟨3163250991087401859905867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2108833994058267906603911 3163250991087401859905867)
              ·
                refine ⟨4744876486631102789858801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3163250991087401859905867 4744876486631102789858801)
                ·
                  refine ⟨3558657364973327092394101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4744876486631102789858801 3558657364973327092394101)
                  ·
                    refine ⟨333624127966249414911947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3558657364973327092394101 333624127966249414911947)
                    ·
                      rfl

theorem cell22_974596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_974596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_974596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_974596 prefixEnd_974596 := by exact prefixLift 974596
  have htrace : WordTrace (prefixWord ++ tailWord_974596) baseStart_974596 baseEnd_974596 := by
    simpa [prefixWord, tailWord_974596, baseEnd_974596] using wordTrace_append hprefix tailTrace_974596
  have hstable : (prefixWord ++ tailWord_974596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974596).length < 2 ^ (prefixWord ++ tailWord_974596).sum := by decide
  have hdescent : baseEnd_974596 < baseStart_974596 := by decide
  rcases family_descends (prefixWord ++ tailWord_974596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974628 : List Nat := [2, 3, 1, 3, 2, 2, 1, 3, 1, 4]
def baseStart_974628 : Nat := 118140960795 + 974628 * 2 ^ 59
def prefixEnd_974628 : Nat := 4983230072969 + 3 ^ 40 * 974628 * 2
def baseEnd_974628 : Nat := 333635082220211998111849

theorem tailTrace_974628 : CollatzResearch.WordTrace tailWord_974628 prefixEnd_974628 333635082220211998111849 := by
  unfold tailWord_974628
  simp only [CollatzResearch.WordTrace]
  refine ⟨17773801756548342027746269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23698402342064456036995025 17773801756548342027746269)
  ·
    refine ⟨6665175658705628260404851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17773801756548342027746269 6665175658705628260404851)
    ·
      refine ⟨9997763488058442390607277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6665175658705628260404851 9997763488058442390607277)
      ·
        refine ⟨3749161308021915896477729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9997763488058442390607277 3749161308021915896477729)
        ·
          refine ⟨2811870981016436922358297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3749161308021915896477729 2811870981016436922358297)
          ·
            refine ⟨2108903235762327691768723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2811870981016436922358297 2108903235762327691768723)
            ·
              refine ⟨3163354853643491537653085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2108903235762327691768723 3163354853643491537653085)
              ·
                refine ⟨1186258070116309326619907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3163354853643491537653085 1186258070116309326619907)
                ·
                  refine ⟨1779387105174463989929861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1186258070116309326619907 1779387105174463989929861)
                  ·
                    refine ⟨333635082220211998111849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1779387105174463989929861 333635082220211998111849)
                    ·
                      rfl

theorem cell22_974628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_974628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_974628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_974628 prefixEnd_974628 := by exact prefixLift 974628
  have htrace : WordTrace (prefixWord ++ tailWord_974628) baseStart_974628 baseEnd_974628 := by
    simpa [prefixWord, tailWord_974628, baseEnd_974628] using wordTrace_append hprefix tailTrace_974628
  have hstable : (prefixWord ++ tailWord_974628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974628).length < 2 ^ (prefixWord ++ tailWord_974628).sum := by decide
  have hdescent : baseEnd_974628 < baseStart_974628 := by decide
  rcases family_descends (prefixWord ++ tailWord_974628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974662 : List Nat := [6, 1, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_974662 : Nat := 118140960795 + 974662 * 2 ^ 59
def prefixEnd_974662 : Nat := 4983230072969 + 3 ^ 40 * 974662 * 2
def baseEnd_974662 : Nat := 333646721115047242761745

theorem tailTrace_974662 : CollatzResearch.WordTrace tailWord_974662 prefixEnd_974662 333646721115047242761745 := by
  unfold tailWord_974662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1110901362342922120694695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23699229063315671908153493 1110901362342922120694695)
  ·
    refine ⟨1666352043514383181042043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1110901362342922120694695 1666352043514383181042043)
    ·
      refine ⟨2499528065271574771563065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1666352043514383181042043 2499528065271574771563065)
      ·
        refine ⟨1874646048953681078672299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2499528065271574771563065 1874646048953681078672299)
        ·
          refine ⟨2811969073430521618008449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1874646048953681078672299 2811969073430521618008449)
          ·
            refine ⟨2108976805072891213506337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2811969073430521618008449 2108976805072891213506337)
            ·
              refine ⟨1581732603804668410129753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2108976805072891213506337 1581732603804668410129753)
              ·
                refine ⟨1186299452853501307597315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1581732603804668410129753 1186299452853501307597315)
                ·
                  refine ⟨1779449179280251961395973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1186299452853501307597315 1779449179280251961395973)
                  ·
                    refine ⟨333646721115047242761745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1779449179280251961395973 333646721115047242761745)
                    ·
                      rfl

theorem cell22_974662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_974662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_974662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_974662 prefixEnd_974662 := by exact prefixLift 974662
  have htrace : WordTrace (prefixWord ++ tailWord_974662) baseStart_974662 baseEnd_974662 := by
    simpa [prefixWord, tailWord_974662, baseEnd_974662] using wordTrace_append hprefix tailTrace_974662
  have hstable : (prefixWord ++ tailWord_974662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974662).length < 2 ^ (prefixWord ++ tailWord_974662).sum := by decide
  have hdescent : baseEnd_974662 < baseStart_974662 := by decide
  rcases family_descends (prefixWord ++ tailWord_974662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974810 : List Nat := [3, 1, 1, 2, 5, 1, 1, 1, 4, 3]
def baseStart_974810 : Nat := 118140960795 + 974810 * 2 ^ 59
def prefixEnd_974810 : Nat := 4983230072969 + 3 ^ 40 * 974810 * 2
def baseEnd_974810 : Nat := 333697384539624190061291

theorem tailTrace_974810 : CollatzResearch.WordTrace tailWord_974810 prefixEnd_974810 333697384539624190061291 := by
  unfold tailWord_974810
  simp only [CollatzResearch.WordTrace]
  refine ⟨8888560399609332284654471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23702827732291552759078589 8888560399609332284654471)
  ·
    refine ⟨13332840599413998426981707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8888560399609332284654471 13332840599413998426981707)
    ·
      refine ⟨19999260899120997640472561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13332840599413998426981707 19999260899120997640472561)
      ·
        refine ⟨14999445674340748230354421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19999260899120997640472561 14999445674340748230354421)
        ·
          refine ⟨1406198031969445146595727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14999445674340748230354421 1406198031969445146595727)
          ·
            refine ⟨2109297047954167719893591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1406198031969445146595727 2109297047954167719893591)
            ·
              refine ⟨3163945571931251579840387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2109297047954167719893591 3163945571931251579840387)
              ·
                refine ⟨4745918357896877369760581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3163945571931251579840387 4745918357896877369760581)
                ·
                  refine ⟨889859692105664506830109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4745918357896877369760581 889859692105664506830109)
                  ·
                    refine ⟨333697384539624190061291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 889859692105664506830109 333697384539624190061291)
                    ·
                      rfl

theorem cell22_974810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 4, 3].length) (baseStart_974810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_974810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_974810 prefixEnd_974810 := by exact prefixLift 974810
  have htrace : WordTrace (prefixWord ++ tailWord_974810) baseStart_974810 baseEnd_974810 := by
    simpa [prefixWord, tailWord_974810, baseEnd_974810] using wordTrace_append hprefix tailTrace_974810
  have hstable : (prefixWord ++ tailWord_974810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974810).length < 2 ^ (prefixWord ++ tailWord_974810).sum := by decide
  have hdescent : baseEnd_974810 < baseStart_974810 := by decide
  rcases family_descends (prefixWord ++ tailWord_974810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974885 : List Nat := [1, 3, 1, 2, 2, 3, 4, 1, 5]
def baseStart_974885 : Nat := 118140960795 + 974885 * 2 ^ 59
def prefixEnd_974885 : Nat := 4983230072969 + 3 ^ 40 * 974885 * 2
def baseEnd_974885 : Nat := 111241019524116331478687

theorem tailTrace_974885 : CollatzResearch.WordTrace tailWord_974885 prefixEnd_974885 111241019524116331478687 := by
  unfold tailWord_974885
  simp only [CollatzResearch.WordTrace]
  refine ⟨35556977073165616947598109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23704651382110411298398739 35556977073165616947598109)
  ·
    refine ⟨13333866402437106355349291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35556977073165616947598109 13333866402437106355349291)
    ·
      refine ⟨20000799603655659533023937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13333866402437106355349291 20000799603655659533023937)
      ·
        refine ⟨15000599702741744649767953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20000799603655659533023937 15000599702741744649767953)
        ·
          refine ⟨11250449777056308487325965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15000599702741744649767953 11250449777056308487325965)
          ·
            refine ⟨4218918666396115682747237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11250449777056308487325965 4218918666396115682747237)
            ·
              refine ⟨791047249949271690515107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4218918666396115682747237 791047249949271690515107)
              ·
                refine ⟨1186570874923907535772661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 791047249949271690515107 1186570874923907535772661)
                ·
                  refine ⟨111241019524116331478687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1186570874923907535772661 111241019524116331478687)
                  ·
                    rfl

theorem cell22_974885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 5].length) (baseStart_974885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_974885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_974885 prefixEnd_974885 := by exact prefixLift 974885
  have htrace : WordTrace (prefixWord ++ tailWord_974885) baseStart_974885 baseEnd_974885 := by
    simpa [prefixWord, tailWord_974885, baseEnd_974885] using wordTrace_append hprefix tailTrace_974885
  have hstable : (prefixWord ++ tailWord_974885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974885).length < 2 ^ (prefixWord ++ tailWord_974885).sum := by decide
  have hdescent : baseEnd_974885 < baseStart_974885 := by decide
  rcases family_descends (prefixWord ++ tailWord_974885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974960 : List Nat := [2, 1, 1, 1, 5, 2, 3, 1, 2, 4]
def baseStart_974960 : Nat := 118140960795 + 974960 * 2 ^ 59
def prefixEnd_974960 : Nat := 4983230072969 + 3 ^ 40 * 974960 * 2
def baseEnd_974960 : Nat := 333748732605073798810831

theorem tailTrace_974960 : CollatzResearch.WordTrace tailWord_974960 prefixEnd_974960 333748732605073798810831 := by
  unfold tailWord_974960
  simp only [CollatzResearch.WordTrace]
  refine ⟨17779856273946952378289167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23706475031929269837718889 17779856273946952378289167)
  ·
    refine ⟨26669784410920428567433751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17779856273946952378289167 26669784410920428567433751)
    ·
      refine ⟨40004676616380642851150627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26669784410920428567433751 40004676616380642851150627)
      ·
        refine ⟨60007014924570964276725941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40004676616380642851150627 60007014924570964276725941)
        ·
          refine ⟨5625657649178527900943057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60007014924570964276725941 5625657649178527900943057)
          ·
            refine ⟨4219243236883895925707293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5625657649178527900943057 4219243236883895925707293)
            ·
              refine ⟨1582216213831460972140235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4219243236883895925707293 1582216213831460972140235)
              ·
                refine ⟨2373324320747191458210353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1582216213831460972140235 2373324320747191458210353)
                ·
                  refine ⟨1779993240560393593657765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2373324320747191458210353 1779993240560393593657765)
                  ·
                    refine ⟨333748732605073798810831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1779993240560393593657765 333748732605073798810831)
                    ·
                      rfl

theorem cell22_974960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 2, 4].length) (baseStart_974960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_974960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_974960 prefixEnd_974960 := by exact prefixLift 974960
  have htrace : WordTrace (prefixWord ++ tailWord_974960) baseStart_974960 baseEnd_974960 := by
    simpa [prefixWord, tailWord_974960, baseEnd_974960] using wordTrace_append hprefix tailTrace_974960
  have hstable : (prefixWord ++ tailWord_974960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974960).length < 2 ^ (prefixWord ++ tailWord_974960).sum := by decide
  have hdescent : baseEnd_974960 < baseStart_974960 := by decide
  rcases family_descends (prefixWord ++ tailWord_974960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974996 : List Nat := [2, 4, 2, 3, 2, 1, 1, 1, 1, 5]
def baseStart_974996 : Nat := 118140960795 + 974996 * 2 ^ 59
def prefixEnd_974996 : Nat := 4983230072969 + 3 ^ 40 * 974996 * 2
def baseEnd_974996 : Nat := 333761056140781704910721

theorem tailTrace_974996 : CollatzResearch.WordTrace tailWord_974996 prefixEnd_974996 333761056140781704910721 := by
  unfold tailWord_974996
  simp only [CollatzResearch.WordTrace]
  refine ⟨17780512787881741452444421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23707350383842321936592561 17780512787881741452444421)
  ·
    refine ⟨3333846147727826522333329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17780512787881741452444421 3333846147727826522333329)
    ·
      refine ⟨2500384610795869891749997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3333846147727826522333329 2500384610795869891749997)
      ·
        refine ⟨937644229048451209406249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2500384610795869891749997 937644229048451209406249)
        ·
          refine ⟨703233171786338407054687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 937644229048451209406249 703233171786338407054687)
          ·
            refine ⟨1054849757679507610582031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703233171786338407054687 1054849757679507610582031)
            ·
              refine ⟨1582274636519261415873047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1054849757679507610582031 1582274636519261415873047)
              ·
                refine ⟨2373411954778892123809571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1582274636519261415873047 2373411954778892123809571)
                ·
                  refine ⟨3560117932168338185714357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2373411954778892123809571 3560117932168338185714357)
                  ·
                    refine ⟨333761056140781704910721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3560117932168338185714357 333761056140781704910721)
                    ·
                      rfl

theorem cell22_974996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_974996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_974996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_974996 prefixEnd_974996 := by exact prefixLift 974996
  have htrace : WordTrace (prefixWord ++ tailWord_974996) baseStart_974996 baseEnd_974996 := by
    simpa [prefixWord, tailWord_974996, baseEnd_974996] using wordTrace_append hprefix tailTrace_974996
  have hstable : (prefixWord ++ tailWord_974996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974996).length < 2 ^ (prefixWord ++ tailWord_974996).sum := by decide
  have hdescent : baseEnd_974996 < baseStart_974996 := by decide
  rcases family_descends (prefixWord ++ tailWord_974996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975007 : List Nat := [1, 1, 2, 6, 1, 1, 2, 2, 3, 3]
def baseStart_975007 : Nat := 118140960795 + 975007 * 2 ^ 59
def prefixEnd_975007 : Nat := 4983230072969 + 3 ^ 40 * 975007 * 2
def baseEnd_975007 : Nat := 333764821665581342885687

theorem tailTrace_975007 : CollatzResearch.WordTrace tailWord_975007 prefixEnd_975007 333764821665581342885687 := by
  unfold tailWord_975007
  simp only [CollatzResearch.WordTrace]
  refine ⟨35561426778723631783539275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23707617852482421189026183 35561426778723631783539275)
  ·
    refine ⟨53342140168085447675308913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35561426778723631783539275 53342140168085447675308913)
    ·
      refine ⟨40006605126064085756481685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53342140168085447675308913 40006605126064085756481685)
      ·
        refine ⟨1875309615284254019835079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40006605126064085756481685 1875309615284254019835079)
        ·
          refine ⟨2812964422926381029752619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1875309615284254019835079 2812964422926381029752619)
          ·
            refine ⟨4219446634389571544628929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2812964422926381029752619 4219446634389571544628929)
            ·
              refine ⟨3164584975792178658471697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4219446634389571544628929 3164584975792178658471697)
              ·
                refine ⟨2373438731844133993853773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3164584975792178658471697 2373438731844133993853773)
                ·
                  refine ⟨890039524441550247695165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2373438731844133993853773 890039524441550247695165)
                  ·
                    refine ⟨333764821665581342885687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 890039524441550247695165 333764821665581342885687)
                    ·
                      rfl

theorem cell22_975007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 3, 3].length) (baseStart_975007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975007 prefixEnd_975007 := by exact prefixLift 975007
  have htrace : WordTrace (prefixWord ++ tailWord_975007) baseStart_975007 baseEnd_975007 := by
    simpa [prefixWord, tailWord_975007, baseEnd_975007] using wordTrace_append hprefix tailTrace_975007
  have hstable : (prefixWord ++ tailWord_975007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975007).length < 2 ^ (prefixWord ++ tailWord_975007).sum := by decide
  have hdescent : baseEnd_975007 < baseStart_975007 := by decide
  rcases family_descends (prefixWord ++ tailWord_975007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975041 : List Nat := [1, 2, 6, 1, 2, 2, 1, 1, 3, 3]
def baseStart_975041 : Nat := 118140960795 + 975041 * 2 ^ 59
def prefixEnd_975041 : Nat := 4983230072969 + 3 ^ 40 * 975041 * 2
def baseEnd_975041 : Nat := 333776460560416587535583

theorem tailTrace_975041 : CollatzResearch.WordTrace tailWord_975041 prefixEnd_975041 333776460560416587535583 := by
  unfold tailWord_975041
  simp only [CollatzResearch.WordTrace]
  refine ⟨35562666860600455590276977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23708444573733637060184651 35562666860600455590276977)
  ·
    refine ⟨26672000145450341692707733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35562666860600455590276977 26672000145450341692707733)
    ·
      refine ⟨1250250006817984766845675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26672000145450341692707733 1250250006817984766845675)
      ·
        refine ⟨1875375010226977150268513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1250250006817984766845675 1875375010226977150268513)
        ·
          refine ⟨1406531257670232862701385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1875375010226977150268513 1406531257670232862701385)
          ·
            refine ⟨1054898443252674647026039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1406531257670232862701385 1054898443252674647026039)
            ·
              refine ⟨1582347664879011970539059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1054898443252674647026039 1582347664879011970539059)
              ·
                refine ⟨2373521497318517955808589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1582347664879011970539059 2373521497318517955808589)
                ·
                  refine ⟨890070561494444233428221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2373521497318517955808589 890070561494444233428221)
                  ·
                    refine ⟨333776460560416587535583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 890070561494444233428221 333776460560416587535583)
                    ·
                      rfl

theorem cell22_975041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_975041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975041 prefixEnd_975041 := by exact prefixLift 975041
  have htrace : WordTrace (prefixWord ++ tailWord_975041) baseStart_975041 baseEnd_975041 := by
    simpa [prefixWord, tailWord_975041, baseEnd_975041] using wordTrace_append hprefix tailTrace_975041
  have hstable : (prefixWord ++ tailWord_975041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975041).length < 2 ^ (prefixWord ++ tailWord_975041).sum := by decide
  have hdescent : baseEnd_975041 < baseStart_975041 := by decide
  rcases family_descends (prefixWord ++ tailWord_975041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975050 : List Nat := [3, 1, 2, 1, 3, 1, 2, 2, 3, 4]
def baseStart_975050 : Nat := 118140960795 + 975050 * 2 ^ 59
def prefixEnd_975050 : Nat := 4983230072969 + 3 ^ 40 * 975050 * 2
def baseEnd_975050 : Nat := 333779541444343564060555

theorem tailTrace_975050 : CollatzResearch.WordTrace tailWord_975050 prefixEnd_975050 333779541444343564060555 := by
  unfold tailWord_975050
  simp only [CollatzResearch.WordTrace]
  refine ⟨8890748779391962531838651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23708663411711900084903069 8890748779391962531838651)
  ·
    refine ⟨13336123169087943797757977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8890748779391962531838651 13336123169087943797757977)
    ·
      refine ⟨10002092376815957848318483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13336123169087943797757977 10002092376815957848318483)
      ·
        refine ⟨15003138565223936772477725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10002092376815957848318483 15003138565223936772477725)
        ·
          refine ⟨5626176961958976289679147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15003138565223936772477725 5626176961958976289679147)
          ·
            refine ⟨8439265442938464434518721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5626176961958976289679147 8439265442938464434518721)
            ·
              refine ⟨6329449082203848325889041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8439265442938464434518721 6329449082203848325889041)
              ·
                refine ⟨4747086811652886244416781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6329449082203848325889041 4747086811652886244416781)
                ·
                  refine ⟨1780157554369832341656293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4747086811652886244416781 1780157554369832341656293)
                  ·
                    refine ⟨333779541444343564060555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1780157554369832341656293 333779541444343564060555)
                    ·
                      rfl

theorem cell22_975050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_975050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975050 prefixEnd_975050 := by exact prefixLift 975050
  have htrace : WordTrace (prefixWord ++ tailWord_975050) baseStart_975050 baseEnd_975050 := by
    simpa [prefixWord, tailWord_975050, baseEnd_975050] using wordTrace_append hprefix tailTrace_975050
  have hstable : (prefixWord ++ tailWord_975050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975050).length < 2 ^ (prefixWord ++ tailWord_975050).sum := by decide
  have hdescent : baseEnd_975050 < baseStart_975050 := by decide
  rcases family_descends (prefixWord ++ tailWord_975050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975054 : List Nat := [4, 1, 1, 1, 4, 3, 2, 1, 5]
def baseStart_975054 : Nat := 118140960795 + 975054 * 2 ^ 59
def prefixEnd_975054 : Nat := 4983230072969 + 3 ^ 40 * 975054 * 2
def baseEnd_975054 : Nat := 111260303575362962320181

theorem tailTrace_975054 : CollatzResearch.WordTrace tailWord_975054 prefixEnd_975054 111260303575362962320181 := by
  unfold tailWord_975054
  simp only [CollatzResearch.WordTrace]
  refine ⟨4445392626194169851312527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23708760673035572540333477 4445392626194169851312527)
  ·
    refine ⟨6668088939291254776968791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4445392626194169851312527 6668088939291254776968791)
    ·
      refine ⟨10002133408936882165453187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6668088939291254776968791 10002133408936882165453187)
      ·
        refine ⟨15003200113405323248179781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10002133408936882165453187 15003200113405323248179781)
        ·
          refine ⟨2813100021263498109033709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15003200113405323248179781 2813100021263498109033709)
          ·
            refine ⟨1054912507973811790887641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2813100021263498109033709 1054912507973811790887641)
            ·
              refine ⟨791184380980358843165731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1054912507973811790887641 791184380980358843165731)
              ·
                refine ⟨1186776571470538264748597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 791184380980358843165731 1186776571470538264748597)
                ·
                  refine ⟨111260303575362962320181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1186776571470538264748597 111260303575362962320181)
                  ·
                    rfl

theorem cell22_975054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_975054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975054 prefixEnd_975054 := by exact prefixLift 975054
  have htrace : WordTrace (prefixWord ++ tailWord_975054) baseStart_975054 baseEnd_975054 := by
    simpa [prefixWord, tailWord_975054, baseEnd_975054] using wordTrace_append hprefix tailTrace_975054
  have hstable : (prefixWord ++ tailWord_975054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975054).length < 2 ^ (prefixWord ++ tailWord_975054).sum := by decide
  have hdescent : baseEnd_975054 < baseStart_975054 := by decide
  rcases family_descends (prefixWord ++ tailWord_975054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975080 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 3, 5]
def baseStart_975080 : Nat := 118140960795 + 975080 * 2 ^ 59
def prefixEnd_975080 : Nat := 4983230072969 + 3 ^ 40 * 975080 * 2
def baseEnd_975080 : Nat := 333789811057433485810463

theorem tailTrace_975080 : CollatzResearch.WordTrace tailWord_975080 prefixEnd_975080 333789811057433485810463 := by
  unfold tailWord_975080
  simp only [CollatzResearch.WordTrace]
  refine ⟨17782044653729582625473347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23709392871639443500631129 17782044653729582625473347)
  ·
    refine ⟨26673066980594373938210021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17782044653729582625473347 26673066980594373938210021)
    ·
      refine ⟨5001200058861445113414379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26673066980594373938210021 5001200058861445113414379)
      ·
        refine ⟨7501800088292167670121569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5001200058861445113414379 7501800088292167670121569)
        ·
          refine ⟨5626350066219125752591177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7501800088292167670121569 5626350066219125752591177)
          ·
            refine ⟨4219762549664344314443383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5626350066219125752591177 4219762549664344314443383)
            ·
              refine ⟨6329643824496516471665075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4219762549664344314443383 6329643824496516471665075)
              ·
                refine ⟨9494465736744774707497613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6329643824496516471665075 9494465736744774707497613)
                ·
                  refine ⟨3560424651279290515311605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9494465736744774707497613 3560424651279290515311605)
                  ·
                    refine ⟨333789811057433485810463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3560424651279290515311605 333789811057433485810463)
                    ·
                      rfl

theorem cell22_975080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_975080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975080 prefixEnd_975080 := by exact prefixLift 975080
  have htrace : WordTrace (prefixWord ++ tailWord_975080) baseStart_975080 baseEnd_975080 := by
    simpa [prefixWord, tailWord_975080, baseEnd_975080] using wordTrace_append hprefix tailTrace_975080
  have hstable : (prefixWord ++ tailWord_975080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975080).length < 2 ^ (prefixWord ++ tailWord_975080).sum := by decide
  have hdescent : baseEnd_975080 < baseStart_975080 := by decide
  rcases family_descends (prefixWord ++ tailWord_975080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975082 : List Nat := [3, 1, 3, 1, 1, 2, 2, 5, 4]
def baseStart_975082 : Nat := 118140960795 + 975082 * 2 ^ 59
def prefixEnd_975082 : Nat := 4983230072969 + 3 ^ 40 * 975082 * 2
def baseEnd_975082 : Nat := 111263498566102049086819

theorem tailTrace_975082 : CollatzResearch.WordTrace tailWord_975082 prefixEnd_975082 111263498566102049086819 := by
  unfold tailWord_975082
  simp only [CollatzResearch.WordTrace]
  refine ⟨8891040563362979898129875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23709441502301279728346333 8891040563362979898129875)
  ·
    refine ⟨13336560845044469847194813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8891040563362979898129875 13336560845044469847194813)
    ·
      refine ⟨5001210316891676192698055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13336560845044469847194813 5001210316891676192698055)
      ·
        refine ⟨7501815475337514289047083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5001210316891676192698055 7501815475337514289047083)
        ·
          refine ⟨11252723213006271433570625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7501815475337514289047083 11252723213006271433570625)
          ·
            refine ⟨8439542409754703575177969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11252723213006271433570625 8439542409754703575177969)
            ·
              refine ⟨6329656807316027681383477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8439542409754703575177969 6329656807316027681383477)
              ·
                refine ⟨593405325685877595129701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6329656807316027681383477 593405325685877595129701)
                ·
                  refine ⟨111263498566102049086819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 593405325685877595129701 111263498566102049086819)
                  ·
                    rfl

theorem cell22_975082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 5, 4].length) (baseStart_975082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975082 prefixEnd_975082 := by exact prefixLift 975082
  have htrace : WordTrace (prefixWord ++ tailWord_975082) baseStart_975082 baseEnd_975082 := by
    simpa [prefixWord, tailWord_975082, baseEnd_975082] using wordTrace_append hprefix tailTrace_975082
  have hstable : (prefixWord ++ tailWord_975082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975082).length < 2 ^ (prefixWord ++ tailWord_975082).sum := by decide
  have hdescent : baseEnd_975082 < baseStart_975082 := by decide
  rcases family_descends (prefixWord ++ tailWord_975082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975093 : List Nat := [1, 3, 18]
def baseStart_975093 : Nat := 118140960795 + 975093 * 2 ^ 59
def prefixEnd_975093 : Nat := 4983230072969 + 3 ^ 40 * 975093 * 2
def baseEnd_975093 : Nat := 152626548341612156029

theorem tailTrace_975093 : CollatzResearch.WordTrace tailWord_975093 prefixEnd_975093 152626548341612156029 := by
  unfold tailWord_975093
  simp only [CollatzResearch.WordTrace]
  refine ⟨35564563456412068471169933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23709708970941378980779955 35564563456412068471169933)
  ·
    refine ⟨13336711296154525676688725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35564563456412068471169933 13336711296154525676688725)
    ·
      refine ⟨152626548341612156029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 18 13336711296154525676688725 152626548341612156029)
      ·
        rfl

theorem cell22_975093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 18].length) (baseStart_975093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975093 prefixEnd_975093 := by exact prefixLift 975093
  have htrace : WordTrace (prefixWord ++ tailWord_975093) baseStart_975093 baseEnd_975093 := by
    simpa [prefixWord, tailWord_975093, baseEnd_975093] using wordTrace_append hprefix tailTrace_975093
  have hstable : (prefixWord ++ tailWord_975093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975093).length < 2 ^ (prefixWord ++ tailWord_975093).sum := by decide
  have hdescent : baseEnd_975093 < baseStart_975093 := by decide
  rcases family_descends (prefixWord ++ tailWord_975093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975127 : List Nat := [1, 1, 3, 4, 1, 3, 3, 6]
def baseStart_975127 : Nat := 118140960795 + 975127 * 2 ^ 59
def prefixEnd_975127 : Nat := 4983230072969 + 3 ^ 40 * 975127 * 2
def baseEnd_975127 : Nat := 37089544457549003320591

theorem tailTrace_975127 : CollatzResearch.WordTrace tailWord_975127 prefixEnd_975127 37089544457549003320591 := by
  unfold tailWord_975127
  simp only [CollatzResearch.WordTrace]
  refine ⟨35565803538288892277907635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23710535692192594851938423 35565803538288892277907635)
  ·
    refine ⟨53348705307433338416861453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35565803538288892277907635 53348705307433338416861453)
    ·
      refine ⟨20005764490287501906323045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53348705307433338416861453 20005764490287501906323045)
      ·
        refine ⟨3751080841928906607435571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20005764490287501906323045 3751080841928906607435571)
        ·
          refine ⟨5626621262893359911153357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3751080841928906607435571 5626621262893359911153357)
          ·
            refine ⟨2109982973585009966682509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5626621262893359911153357 2109982973585009966682509)
            ·
              refine ⟨791243615094378737505941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2109982973585009966682509 791243615094378737505941)
              ·
                refine ⟨37089544457549003320591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 791243615094378737505941 37089544457549003320591)
                ·
                  rfl

theorem cell22_975127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 6].length) (baseStart_975127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975127 prefixEnd_975127 := by exact prefixLift 975127
  have htrace : WordTrace (prefixWord ++ tailWord_975127) baseStart_975127 baseEnd_975127 := by
    simpa [prefixWord, tailWord_975127, baseEnd_975127] using wordTrace_append hprefix tailTrace_975127
  have hstable : (prefixWord ++ tailWord_975127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975127).length < 2 ^ (prefixWord ++ tailWord_975127).sum := by decide
  have hdescent : baseEnd_975127 < baseStart_975127 := by decide
  rcases family_descends (prefixWord ++ tailWord_975127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975155 : List Nat := [1, 1, 1, 2, 5, 1, 3, 1, 7]
def baseStart_975155 : Nat := 118140960795 + 975155 * 2 ^ 59
def prefixEnd_975155 : Nat := 4983230072969 + 3 ^ 40 * 975155 * 2
def baseEnd_975155 : Nat := 111271828363386096728411

theorem tailTrace_975155 : CollatzResearch.WordTrace tailWord_975155 prefixEnd_975155 111271828363386096728411 := by
  unfold tailWord_975155
  simp only [CollatzResearch.WordTrace]
  refine ⟨35566824782187453059926919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23711216521458302039951279 35566824782187453059926919)
  ·
    refine ⟨53350237173281179589890379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35566824782187453059926919 53350237173281179589890379)
    ·
      refine ⟨80025355759921769384835569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53350237173281179589890379 80025355759921769384835569)
      ·
        refine ⟨60019016819941327038626677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80025355759921769384835569 60019016819941327038626677)
        ·
          refine ⟨5626782826869499409871251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60019016819941327038626677 5626782826869499409871251)
          ·
            refine ⟨8440174240304249114806877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5626782826869499409871251 8440174240304249114806877)
            ·
              refine ⟨3165065340114093418052579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8440174240304249114806877 3165065340114093418052579)
              ·
                refine ⟨4747598010171140127078869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3165065340114093418052579 4747598010171140127078869)
                ·
                  refine ⟨111271828363386096728411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4747598010171140127078869 111271828363386096728411)
                  ·
                    rfl

theorem cell22_975155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 7].length) (baseStart_975155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975155 prefixEnd_975155 := by exact prefixLift 975155
  have htrace : WordTrace (prefixWord ++ tailWord_975155) baseStart_975155 baseEnd_975155 := by
    simpa [prefixWord, tailWord_975155, baseEnd_975155] using wordTrace_append hprefix tailTrace_975155
  have hstable : (prefixWord ++ tailWord_975155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975155).length < 2 ^ (prefixWord ++ tailWord_975155).sum := by decide
  have hdescent : baseEnd_975155 < baseStart_975155 := by decide
  rcases family_descends (prefixWord ++ tailWord_975155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975215 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 5, 5]
def baseStart_975215 : Nat := 118140960795 + 975215 * 2 ^ 59
def prefixEnd_975215 : Nat := 4983230072969 + 3 ^ 40 * 975215 * 2
def baseEnd_975215 : Nat := 333836024316338133685049

theorem tailTrace_975215 : CollatzResearch.WordTrace tailWord_975215 prefixEnd_975215 333836024316338133685049 := by
  unfold tailWord_975215
  simp only [CollatzResearch.WordTrace]
  refine ⟨35569013161970083307111099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23712675441313388871407399 35569013161970083307111099)
  ·
    refine ⟨53353519742955124960666649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35569013161970083307111099 53353519742955124960666649)
    ·
      refine ⟨40015139807216343720499987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53353519742955124960666649 40015139807216343720499987)
      ·
        refine ⟨60022709710824515580749981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40015139807216343720499987 60022709710824515580749981)
        ·
          refine ⟨22508516141559193342781243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60022709710824515580749981 22508516141559193342781243)
          ·
            refine ⟨33762774212338790014171865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22508516141559193342781243 33762774212338790014171865)
            ·
              refine ⟨25322080659254092510628899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33762774212338790014171865 25322080659254092510628899)
              ·
                refine ⟨37983120988881138765943349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25322080659254092510628899 37983120988881138765943349)
                ·
                  refine ⟨3560917592707606759307189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37983120988881138765943349 3560917592707606759307189)
                  ·
                    refine ⟨333836024316338133685049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3560917592707606759307189 333836024316338133685049)
                    ·
                      rfl

theorem cell22_975215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 5].length) (baseStart_975215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975215 prefixEnd_975215 := by exact prefixLift 975215
  have htrace : WordTrace (prefixWord ++ tailWord_975215) baseStart_975215 baseEnd_975215 := by
    simpa [prefixWord, tailWord_975215, baseEnd_975215] using wordTrace_append hprefix tailTrace_975215
  have hstable : (prefixWord ++ tailWord_975215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975215).length < 2 ^ (prefixWord ++ tailWord_975215).sum := by decide
  have hdescent : baseEnd_975215 < baseStart_975215 := by decide
  rcases family_descends (prefixWord ++ tailWord_975215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975266 : List Nat := [3, 3, 1, 2, 1, 1, 4, 2, 2, 3]
def baseStart_975266 : Nat := 118140960795 + 975266 * 2 ^ 59
def prefixEnd_975266 : Nat := 4983230072969 + 3 ^ 40 * 975266 * 2
def baseEnd_975266 : Nat := 333853482658591000659893

theorem tailTrace_975266 : CollatzResearch.WordTrace tailWord_975266 prefixEnd_975266 333853482658591000659893 := by
  unfold tailWord_975266
  simp only [CollatzResearch.WordTrace]
  refine ⟨8892718321196329754304413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23713915523190212678145101 8892718321196329754304413)
  ·
    refine ⟨3334769370448623657864155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8892718321196329754304413 3334769370448623657864155)
    ·
      refine ⟨5002154055672935486796233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3334769370448623657864155 5002154055672935486796233)
      ·
        refine ⟨3751615541754701615097175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5002154055672935486796233 3751615541754701615097175)
        ·
          refine ⟨5627423312632052422645763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3751615541754701615097175 5627423312632052422645763)
          ·
            refine ⟨8441134968948078633968645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5627423312632052422645763 8441134968948078633968645)
            ·
              refine ⟨1582712806677764743869121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8441134968948078633968645 1582712806677764743869121)
              ·
                refine ⟨1187034605008323557901841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1582712806677764743869121 1187034605008323557901841)
                ·
                  refine ⟨890275953756242668426381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1187034605008323557901841 890275953756242668426381)
                  ·
                    refine ⟨333853482658591000659893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 890275953756242668426381 333853482658591000659893)
                    ·
                      rfl

theorem cell22_975266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_975266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975266 prefixEnd_975266 := by exact prefixLift 975266
  have htrace : WordTrace (prefixWord ++ tailWord_975266) baseStart_975266 baseEnd_975266 := by
    simpa [prefixWord, tailWord_975266, baseEnd_975266] using wordTrace_append hprefix tailTrace_975266
  have hstable : (prefixWord ++ tailWord_975266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975266).length < 2 ^ (prefixWord ++ tailWord_975266).sum := by decide
  have hdescent : baseEnd_975266 < baseStart_975266 := by decide
  rcases family_descends (prefixWord ++ tailWord_975266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975294 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 5, 3]
def baseStart_975294 : Nat := 118140960795 + 975294 * 2 ^ 59
def prefixEnd_975294 : Nat := 4983230072969 + 3 ^ 40 * 975294 * 2
def baseEnd_975294 : Nat := 333863067630808260959807

theorem tailTrace_975294 : CollatzResearch.WordTrace tailWord_975294 prefixEnd_975294 333863067630808260959807 := by
  unfold tailWord_975294
  simp only [CollatzResearch.WordTrace]
  refine ⟨4446486816085484974904617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23714596352455919866157957 4446486816085484974904617)
  ·
    refine ⟨3334865112064113731178463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4446486816085484974904617 3334865112064113731178463)
    ·
      refine ⟨5002297668096170596767695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3334865112064113731178463 5002297668096170596767695)
      ·
        refine ⟨7503446502144255895151543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5002297668096170596767695 7503446502144255895151543)
        ·
          refine ⟨11255169753216383842727315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7503446502144255895151543 11255169753216383842727315)
          ·
            refine ⟨16882754629824575764090973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11255169753216383842727315 16882754629824575764090973)
            ·
              refine ⟨6331032986184215911534115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16882754629824575764090973 6331032986184215911534115)
              ·
                refine ⟨9496549479276323867301173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6331032986184215911534115 9496549479276323867301173)
                ·
                  refine ⟨890301513682155362559485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9496549479276323867301173 890301513682155362559485)
                  ·
                    refine ⟨333863067630808260959807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 890301513682155362559485 333863067630808260959807)
                    ·
                      rfl

theorem cell22_975294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_975294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975294 prefixEnd_975294 := by exact prefixLift 975294
  have htrace : WordTrace (prefixWord ++ tailWord_975294) baseStart_975294 baseEnd_975294 := by
    simpa [prefixWord, tailWord_975294, baseEnd_975294] using wordTrace_append hprefix tailTrace_975294
  have hstable : (prefixWord ++ tailWord_975294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975294).length < 2 ^ (prefixWord ++ tailWord_975294).sum := by decide
  have hdescent : baseEnd_975294 < baseStart_975294 := by decide
  rcases family_descends (prefixWord ++ tailWord_975294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975322 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 4, 5]
def baseStart_975322 : Nat := 118140960795 + 975322 * 2 ^ 59
def prefixEnd_975322 : Nat := 4983230072969 + 3 ^ 40 * 975322 * 2
def baseEnd_975322 : Nat := 333872652603025521259721

theorem tailTrace_975322 : CollatzResearch.WordTrace tailWord_975322 prefixEnd_975322 333872652603025521259721 := by
  unfold tailWord_975322
  simp only [CollatzResearch.WordTrace]
  refine ⟨8893228943145610145314055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23715277181721627054170813 8893228943145610145314055)
  ·
    refine ⟨13339843414718415217971083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8893228943145610145314055 13339843414718415217971083)
    ·
      refine ⟨20009765122077622826956625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13339843414718415217971083 20009765122077622826956625)
      ·
        refine ⟨15007323841558217120217469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20009765122077622826956625 15007323841558217120217469)
        ·
          refine ⟨5627746440584331420081551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15007323841558217120217469 5627746440584331420081551)
          ·
            refine ⟨8441619660876497130122327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5627746440584331420081551 8441619660876497130122327)
            ·
              refine ⟨12662429491314745695183491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8441619660876497130122327 12662429491314745695183491)
              ·
                refine ⟨18993644236972118542775237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12662429491314745695183491 18993644236972118542775237)
                ·
                  refine ⟨3561308294432272226770357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18993644236972118542775237 3561308294432272226770357)
                  ·
                    refine ⟨333872652603025521259721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3561308294432272226770357 333872652603025521259721)
                    ·
                      rfl

theorem cell22_975322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_975322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975322 prefixEnd_975322 := by exact prefixLift 975322
  have htrace : WordTrace (prefixWord ++ tailWord_975322) baseStart_975322 baseEnd_975322 := by
    simpa [prefixWord, tailWord_975322, baseEnd_975322] using wordTrace_append hprefix tailTrace_975322
  have hstable : (prefixWord ++ tailWord_975322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975322).length < 2 ^ (prefixWord ++ tailWord_975322).sum := by decide
  have hdescent : baseEnd_975322 < baseStart_975322 := by decide
  rcases family_descends (prefixWord ++ tailWord_975322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975337 : List Nat := [1, 2, 1, 1, 1, 2, 1, 6, 3, 4]
def baseStart_975337 : Nat := 118140960795 + 975337 * 2 ^ 59
def prefixEnd_975337 : Nat := 4983230072969 + 3 ^ 40 * 975337 * 2
def baseEnd_975337 : Nat := 333877787409570482134675

theorem tailTrace_975337 : CollatzResearch.WordTrace tailWord_975337 prefixEnd_975337 333877787409570482134675 := by
  unfold tailWord_975337
  simp only [CollatzResearch.WordTrace]
  refine ⟨35573462867528098143052265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23715641911685398762034843 35573462867528098143052265)
  ·
    refine ⟨26680097150646073607289199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35573462867528098143052265 26680097150646073607289199)
    ·
      refine ⟨40020145725969110410933799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26680097150646073607289199 40020145725969110410933799)
      ·
        refine ⟨60030218588953665616400699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40020145725969110410933799 60030218588953665616400699)
        ·
          refine ⟨90045327883430498424601049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60030218588953665616400699 90045327883430498424601049)
          ·
            refine ⟨67533995912572873818450787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90045327883430498424601049 67533995912572873818450787)
            ·
              refine ⟨101300993868859310727676181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67533995912572873818450787 101300993868859310727676181)
              ·
                refine ⟨4748484087602780190359821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101300993868859310727676181 4748484087602780190359821)
                ·
                  refine ⟨1780681532851042571384933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4748484087602780190359821 1780681532851042571384933)
                  ·
                    refine ⟨333877787409570482134675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1780681532851042571384933 333877787409570482134675)
                    ·
                      rfl

theorem cell22_975337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 4].length) (baseStart_975337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975337 prefixEnd_975337 := by exact prefixLift 975337
  have htrace : WordTrace (prefixWord ++ tailWord_975337) baseStart_975337 baseEnd_975337 := by
    simpa [prefixWord, tailWord_975337, baseEnd_975337] using wordTrace_append hprefix tailTrace_975337
  have hstable : (prefixWord ++ tailWord_975337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975337).length < 2 ^ (prefixWord ++ tailWord_975337).sum := by decide
  have hdescent : baseEnd_975337 < baseStart_975337 := by decide
  rcases family_descends (prefixWord ++ tailWord_975337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975352 : List Nat := [2, 1, 2, 1, 1, 4, 1, 4, 6]
def baseStart_975352 : Nat := 118140960795 + 975352 * 2 ^ 59
def prefixEnd_975352 : Nat := 4983230072969 + 3 ^ 40 * 975352 * 2
def baseEnd_975352 : Nat := 111294307405371814336543

theorem tailTrace_975352 : CollatzResearch.WordTrace tailWord_975352 prefixEnd_975352 111294307405371814336543 := by
  unfold tailWord_975352
  simp only [CollatzResearch.WordTrace]
  refine ⟨17787004981236877852424155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23716006641649170469898873 17787004981236877852424155)
  ·
    refine ⟨26680507471855316778636233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17787004981236877852424155 26680507471855316778636233)
    ·
      refine ⟨20010380603891487583977175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26680507471855316778636233 20010380603891487583977175)
      ·
        refine ⟨30015570905837231375965763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20010380603891487583977175 30015570905837231375965763)
        ·
          refine ⟨45023356358755847063948645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30015570905837231375965763 45023356358755847063948645)
          ·
            refine ⟨8441879317266721324490371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45023356358755847063948645 8441879317266721324490371)
            ·
              refine ⟨12662818975900081986735557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8441879317266721324490371 12662818975900081986735557)
              ·
                refine ⟨2374278557981265372512917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12662818975900081986735557 2374278557981265372512917)
                ·
                  refine ⟨111294307405371814336543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2374278557981265372512917 111294307405371814336543)
                  ·
                    rfl

theorem cell22_975352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 6].length) (baseStart_975352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975352 prefixEnd_975352 := by exact prefixLift 975352
  have htrace : WordTrace (prefixWord ++ tailWord_975352) baseStart_975352 baseEnd_975352 := by
    simpa [prefixWord, tailWord_975352, baseEnd_975352] using wordTrace_append hprefix tailTrace_975352
  have hstable : (prefixWord ++ tailWord_975352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975352).length < 2 ^ (prefixWord ++ tailWord_975352).sum := by decide
  have hdescent : baseEnd_975352 < baseStart_975352 := by decide
  rcases family_descends (prefixWord ++ tailWord_975352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975362 : List Nat := [3, 4, 1, 2, 2, 2, 1, 3, 1, 3]
def baseStart_975362 : Nat := 118140960795 + 975362 * 2 ^ 59
def prefixEnd_975362 : Nat := 4983230072969 + 3 ^ 40 * 975362 * 2
def baseEnd_975362 : Nat := 333886345420478750259599

theorem tailTrace_975362 : CollatzResearch.WordTrace tailWord_975362 prefixEnd_975362 333886345420478750259599 := by
  unfold tailWord_975362
  simp only [CollatzResearch.WordTrace]
  refine ⟨8893593673109381853178085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23716249794958351608474893 8893593673109381853178085)
  ·
    refine ⟨1667548813708009097470891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8893593673109381853178085 1667548813708009097470891)
    ·
      refine ⟨2501323220562013646206337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1667548813708009097470891 2501323220562013646206337)
      ·
        refine ⟨1875992415421510234654753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2501323220562013646206337 1875992415421510234654753)
        ·
          refine ⟨1406994311566132675991065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1875992415421510234654753 1406994311566132675991065)
          ·
            refine ⟨1055245733674599506993299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1406994311566132675991065 1055245733674599506993299)
            ·
              refine ⟨1582868600511899260489949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1055245733674599506993299 1582868600511899260489949)
              ·
                refine ⟨593575725191962222683731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1582868600511899260489949 593575725191962222683731)
                ·
                  refine ⟨890363587787943334025597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 593575725191962222683731 890363587787943334025597)
                  ·
                    refine ⟨333886345420478750259599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 890363587787943334025597 333886345420478750259599)
                    ·
                      rfl

theorem cell22_975362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_975362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975362 prefixEnd_975362 := by exact prefixLift 975362
  have htrace : WordTrace (prefixWord ++ tailWord_975362) baseStart_975362 baseEnd_975362 := by
    simpa [prefixWord, tailWord_975362, baseEnd_975362] using wordTrace_append hprefix tailTrace_975362
  have hstable : (prefixWord ++ tailWord_975362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975362).length < 2 ^ (prefixWord ++ tailWord_975362).sum := by decide
  have hdescent : baseEnd_975362 < baseStart_975362 := by decide
  rcases family_descends (prefixWord ++ tailWord_975362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975369 : List Nat := [1, 2, 1, 1, 3, 1, 2, 7, 4]
def baseStart_975369 : Nat := 118140960795 + 975369 * 2 ^ 59
def prefixEnd_975369 : Nat := 4983230072969 + 3 ^ 40 * 975369 * 2
def baseEnd_975369 : Nat := 111296247221177688444859

theorem tailTrace_975369 : CollatzResearch.WordTrace tailWord_975369 prefixEnd_975369 111296247221177688444859 := by
  unfold tailWord_975369
  simp only [CollatzResearch.WordTrace]
  refine ⟨35574630003412167608217161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23716420002274778405478107 35574630003412167608217161)
  ·
    refine ⟨26680972502559125706162871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35574630003412167608217161 26680972502559125706162871)
    ·
      refine ⟨40021458753838688559244307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26680972502559125706162871 40021458753838688559244307)
      ·
        refine ⟨60032188130758032838866461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40021458753838688559244307 60032188130758032838866461)
        ·
          refine ⟨22512070549034262314574923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60032188130758032838866461 22512070549034262314574923)
          ·
            refine ⟨33768105823551393471862385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22512070549034262314574923 33768105823551393471862385)
            ·
              refine ⟨25326079367663545103896789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33768105823551393471862385 25326079367663545103896789)
              ·
                refine ⟨593579985179614338372581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 25326079367663545103896789 593579985179614338372581)
                ·
                  refine ⟨111296247221177688444859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 593579985179614338372581 111296247221177688444859)
                  ·
                    rfl

theorem cell22_975369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 7, 4].length) (baseStart_975369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975369 prefixEnd_975369 := by exact prefixLift 975369
  have htrace : WordTrace (prefixWord ++ tailWord_975369) baseStart_975369 baseEnd_975369 := by
    simpa [prefixWord, tailWord_975369, baseEnd_975369] using wordTrace_append hprefix tailTrace_975369
  have hstable : (prefixWord ++ tailWord_975369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975369).length < 2 ^ (prefixWord ++ tailWord_975369).sum := by decide
  have hdescent : baseEnd_975369 < baseStart_975369 := by decide
  rcases family_descends (prefixWord ++ tailWord_975369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975397 : List Nat := [1, 3, 1, 2, 2, 1, 3, 9]
def baseStart_975397 : Nat := 118140960795 + 975397 * 2 ^ 59
def prefixEnd_975397 : Nat := 4983230072969 + 3 ^ 40 * 975397 * 2
def baseEnd_975397 : Nat := 37099814070638925070499

theorem tailTrace_975397 : CollatzResearch.WordTrace tailWord_975397 prefixEnd_975397 37099814070638925070499 := by
  unfold tailWord_975397
  simp only [CollatzResearch.WordTrace]
  refine ⟨35575651247310728390236445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23717100831540485593490963 35575651247310728390236445)
  ·
    refine ⟨13340869217741523146338667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35575651247310728390236445 13340869217741523146338667)
    ·
      refine ⟨20011303826612284719508001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13340869217741523146338667 20011303826612284719508001)
      ·
        refine ⟨15008477869959213539631001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20011303826612284719508001 15008477869959213539631001)
        ·
          refine ⟨11256358402469410154723251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15008477869959213539631001 11256358402469410154723251)
          ·
            refine ⟨16884537603704115232084877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11256358402469410154723251 16884537603704115232084877)
            ·
              refine ⟨6331701601389043212031829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16884537603704115232084877 6331701601389043212031829)
              ·
                refine ⟨37099814070638925070499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6331701601389043212031829 37099814070638925070499)
                ·
                  rfl

theorem cell22_975397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 9].length) (baseStart_975397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975397 prefixEnd_975397 := by exact prefixLift 975397
  have htrace : WordTrace (prefixWord ++ tailWord_975397) baseStart_975397 baseEnd_975397 := by
    simpa [prefixWord, tailWord_975397, baseEnd_975397] using wordTrace_append hprefix tailTrace_975397
  have hstable : (prefixWord ++ tailWord_975397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975397).length < 2 ^ (prefixWord ++ tailWord_975397).sum := by decide
  have hdescent : baseEnd_975397 < baseStart_975397 := by decide
  rcases family_descends (prefixWord ++ tailWord_975397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975405 : List Nat := [1, 5, 4, 1, 1, 1, 1, 1, 3, 4]
def baseStart_975405 : Nat := 118140960795 + 975405 * 2 ^ 59
def prefixEnd_975405 : Nat := 4983230072969 + 3 ^ 40 * 975405 * 2
def baseEnd_975405 : Nat := 333901065199240971434467

theorem tailTrace_975405 : CollatzResearch.WordTrace tailWord_975405 prefixEnd_975405 333901065199240971434467 := by
  unfold tailWord_975405
  simp only [CollatzResearch.WordTrace]
  refine ⟨35575943031281745756527669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23717295354187830504351779 35575943031281745756527669)
  ·
    refine ⟨3335244659182663664674469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35575943031281745756527669 3335244659182663664674469)
    ·
      refine ⟨625358373596749437126463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3335244659182663664674469 625358373596749437126463)
      ·
        refine ⟨938037560395124155689695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625358373596749437126463 938037560395124155689695)
        ·
          refine ⟨1407056340592686233534543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 938037560395124155689695 1407056340592686233534543)
          ·
            refine ⟨2110584510889029350301815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1407056340592686233534543 2110584510889029350301815)
            ·
              refine ⟨3165876766333544025452723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2110584510889029350301815 3165876766333544025452723)
              ·
                refine ⟨4748815149500316038179085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3165876766333544025452723 4748815149500316038179085)
                ·
                  refine ⟨1780805681062618514317157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4748815149500316038179085 1780805681062618514317157)
                  ·
                    refine ⟨333901065199240971434467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1780805681062618514317157 333901065199240971434467)
                    ·
                      rfl

theorem cell22_975405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_975405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975405 prefixEnd_975405 := by exact prefixLift 975405
  have htrace : WordTrace (prefixWord ++ tailWord_975405) baseStart_975405 baseEnd_975405 := by
    simpa [prefixWord, tailWord_975405, baseEnd_975405] using wordTrace_append hprefix tailTrace_975405
  have hstable : (prefixWord ++ tailWord_975405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975405).length < 2 ^ (prefixWord ++ tailWord_975405).sum := by decide
  have hdescent : baseEnd_975405 < baseStart_975405 := by decide
  rcases family_descends (prefixWord ++ tailWord_975405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975427 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 4, 6]
def baseStart_975427 : Nat := 118140960795 + 975427 * 2 ^ 59
def prefixEnd_975427 : Nat := 4983230072969 + 3 ^ 40 * 975427 * 2
def baseEnd_975427 : Nat := 333908596248840247384399

theorem tailTrace_975427 : CollatzResearch.WordTrace tailWord_975427 prefixEnd_975427 333908596248840247384399 := by
  unfold tailWord_975427
  simp only [CollatzResearch.WordTrace]
  refine ⟨35576745437202043513828535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23717830291468029009219023 35576745437202043513828535)
  ·
    refine ⟨53365118155803065270742803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35576745437202043513828535 53365118155803065270742803)
    ·
      refine ⟨80047677233704597906114205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53365118155803065270742803 80047677233704597906114205)
      ·
        refine ⟨30017878962639224214792827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80047677233704597906114205 30017878962639224214792827)
        ·
          refine ⟨45026818443958836322189241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30017878962639224214792827 45026818443958836322189241)
          ·
            refine ⟨33770113832969127241641931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45026818443958836322189241 33770113832969127241641931)
            ·
              refine ⟨50655170749453690862462897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33770113832969127241641931 50655170749453690862462897)
              ·
                refine ⟨37991378062090268146847173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50655170749453690862462897 37991378062090268146847173)
                ·
                  refine ⟨7123383386641925277533845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37991378062090268146847173 7123383386641925277533845)
                  ·
                    refine ⟨333908596248840247384399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7123383386641925277533845 333908596248840247384399)
                    ·
                      rfl

theorem cell22_975427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 6].length) (baseStart_975427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975427 prefixEnd_975427 := by exact prefixLift 975427
  have htrace : WordTrace (prefixWord ++ tailWord_975427) baseStart_975427 baseEnd_975427 := by
    simpa [prefixWord, tailWord_975427, baseEnd_975427] using wordTrace_append hprefix tailTrace_975427
  have hstable : (prefixWord ++ tailWord_975427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975427).length < 2 ^ (prefixWord ++ tailWord_975427).sum := by decide
  have hdescent : baseEnd_975427 < baseStart_975427 := by decide
  rcases family_descends (prefixWord ++ tailWord_975427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975444 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 2, 6]
def baseStart_975444 : Nat := 118140960795 + 975444 * 2 ^ 59
def prefixEnd_975444 : Nat := 4983230072969 + 3 ^ 40 * 975444 * 2
def baseEnd_975444 : Nat := 333914415696257869709347

theorem tailTrace_975444 : CollatzResearch.WordTrace tailWord_975444 prefixEnd_975444 333914415696257869709347 := by
  unfold tailWord_975444
  simp only [CollatzResearch.WordTrace]
  refine ⟨17788682739070227708598693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23718243652093636944798257 17788682739070227708598693)
  ·
    refine ⟨3335378013575667695362255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17788682739070227708598693 3335378013575667695362255)
    ·
      refine ⟨5003067020363501543043383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3335378013575667695362255 5003067020363501543043383)
      ·
        refine ⟨7504600530545252314565075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5003067020363501543043383 7504600530545252314565075)
        ·
          refine ⟨11256900795817878471847613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7504600530545252314565075 11256900795817878471847613)
          ·
            refine ⟨4221337798431704426942855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11256900795817878471847613 4221337798431704426942855)
            ·
              refine ⟨6332006697647556640414283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4221337798431704426942855 6332006697647556640414283)
              ·
                refine ⟨9498010046471334960621425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6332006697647556640414283 9498010046471334960621425)
                ·
                  refine ⟨7123507534853501220466069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9498010046471334960621425 7123507534853501220466069)
                  ·
                    refine ⟨333914415696257869709347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7123507534853501220466069 333914415696257869709347)
                    ·
                      rfl

theorem cell22_975444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_975444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975444 prefixEnd_975444 := by exact prefixLift 975444
  have htrace : WordTrace (prefixWord ++ tailWord_975444) baseStart_975444 baseEnd_975444 := by
    simpa [prefixWord, tailWord_975444, baseEnd_975444] using wordTrace_append hprefix tailTrace_975444
  have hstable : (prefixWord ++ tailWord_975444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975444).length < 2 ^ (prefixWord ++ tailWord_975444).sum := by decide
  have hdescent : baseEnd_975444 < baseStart_975444 := by decide
  rcases family_descends (prefixWord ++ tailWord_975444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975459 : List Nat := [1, 1, 1, 5, 1, 2, 1, 5, 5]
def baseStart_975459 : Nat := 118140960795 + 975459 * 2 ^ 59
def prefixEnd_975459 : Nat := 4983230072969 + 3 ^ 40 * 975459 * 2
def baseEnd_975459 : Nat := 111306516834267610194767

theorem tailTrace_975459 : CollatzResearch.WordTrace tailWord_975459 prefixEnd_975459 111306516834267610194767 := by
  unfold tailWord_975459
  simp only [CollatzResearch.WordTrace]
  refine ⟨35577912573086112978993431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23718608382057408652662287 35577912573086112978993431)
  ·
    refine ⟨53366868859629169468490147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35577912573086112978993431 53366868859629169468490147)
    ·
      refine ⟨80050303289443754202735221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53366868859629169468490147 80050303289443754202735221)
      ·
        refine ⟨7504715933385351956506427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80050303289443754202735221 7504715933385351956506427)
        ·
          refine ⟨11257073900078027934759641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7504715933385351956506427 11257073900078027934759641)
          ·
            refine ⟨8442805425058520951069731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11257073900078027934759641 8442805425058520951069731)
            ·
              refine ⟨12664208137587781426604597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8442805425058520951069731 12664208137587781426604597)
              ·
                refine ⟨1187269512898854508744181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12664208137587781426604597 1187269512898854508744181)
                ·
                  refine ⟨111306516834267610194767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1187269512898854508744181 111306516834267610194767)
                  ·
                    rfl

theorem cell22_975459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 5].length) (baseStart_975459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975459 prefixEnd_975459 := by exact prefixLift 975459
  have htrace : WordTrace (prefixWord ++ tailWord_975459) baseStart_975459 baseEnd_975459 := by
    simpa [prefixWord, tailWord_975459, baseEnd_975459] using wordTrace_append hprefix tailTrace_975459
  have hstable : (prefixWord ++ tailWord_975459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975459).length < 2 ^ (prefixWord ++ tailWord_975459).sum := by decide
  have hdescent : baseEnd_975459 < baseStart_975459 := by decide
  rcases family_descends (prefixWord ++ tailWord_975459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975549 : List Nat := [1, 4, 1, 2, 1, 3, 10]
def baseStart_975549 : Nat := 118140960795 + 975549 * 2 ^ 59
def prefixEnd_975549 : Nat := 4983230072969 + 3 ^ 40 * 975549 * 2
def baseEnd_975549 : Nat := 12368531827484170216075

theorem tailTrace_975549 : CollatzResearch.WordTrace tailWord_975549 prefixEnd_975549 12368531827484170216075 := by
  unfold tailWord_975549
  simp only [CollatzResearch.WordTrace]
  refine ⟨35581195142760058349769701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23720796761840038899846467 35581195142760058349769701)
  ·
    refine ⟨6671474089267510940581819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35581195142760058349769701 6671474089267510940581819)
    ·
      refine ⟨10007211133901266410872729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6671474089267510940581819 10007211133901266410872729)
      ·
        refine ⟨7505408350425949808154547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10007211133901266410872729 7505408350425949808154547)
        ·
          refine ⟨11258112525638924712231821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7505408350425949808154547 11258112525638924712231821)
          ·
            refine ⟨4221792197114596767086933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11258112525638924712231821 4221792197114596767086933)
            ·
              refine ⟨12368531827484170216075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4221792197114596767086933 12368531827484170216075)
              ·
                rfl

theorem cell22_975549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 10].length) (baseStart_975549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975549 prefixEnd_975549 := by exact prefixLift 975549
  have htrace : WordTrace (prefixWord ++ tailWord_975549) baseStart_975549 baseEnd_975549 := by
    simpa [prefixWord, tailWord_975549, baseEnd_975549] using wordTrace_append hprefix tailTrace_975549
  have hstable : (prefixWord ++ tailWord_975549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975549).length < 2 ^ (prefixWord ++ tailWord_975549).sum := by decide
  have hdescent : baseEnd_975549 < baseStart_975549 := by decide
  rcases family_descends (prefixWord ++ tailWord_975549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975551 : List Nat := [1, 1, 2, 2, 2, 5, 1, 2, 2, 4]
def baseStart_975551 : Nat := 118140960795 + 975551 * 2 ^ 59
def prefixEnd_975551 : Nat := 4983230072969 + 3 ^ 40 * 975551 * 2
def baseEnd_975551 : Nat := 333951043982945257284019

theorem tailTrace_975551 : CollatzResearch.WordTrace tailWord_975551 prefixEnd_975551 333951043982945257284019 := by
  unfold tailWord_975551
  simp only [CollatzResearch.WordTrace]
  refine ⟨35581268088752812691342507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23720845392501875127561671 35581268088752812691342507)
  ·
    refine ⟨53371902133129219037013761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35581268088752812691342507 53371902133129219037013761)
    ·
      refine ⟨40028926599846914277760321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53371902133129219037013761 40028926599846914277760321)
      ·
        refine ⟨30021694949885185708320241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40028926599846914277760321 30021694949885185708320241)
        ·
          refine ⟨22516271212413889281240181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30021694949885185708320241 22516271212413889281240181)
          ·
            refine ⟨2110900426163802120116267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22516271212413889281240181 2110900426163802120116267)
            ·
              refine ⟨3166350639245703180174401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2110900426163802120116267 3166350639245703180174401)
              ·
                refine ⟨2374762979434277385130801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3166350639245703180174401 2374762979434277385130801)
                ·
                  refine ⟨1781072234575708038848101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2374762979434277385130801 1781072234575708038848101)
                  ·
                    refine ⟨333951043982945257284019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1781072234575708038848101 333951043982945257284019)
                    ·
                      rfl

theorem cell22_975551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 4].length) (baseStart_975551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975551 prefixEnd_975551 := by exact prefixLift 975551
  have htrace : WordTrace (prefixWord ++ tailWord_975551) baseStart_975551 baseEnd_975551 := by
    simpa [prefixWord, tailWord_975551, baseEnd_975551] using wordTrace_append hprefix tailTrace_975551
  have hstable : (prefixWord ++ tailWord_975551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975551).length < 2 ^ (prefixWord ++ tailWord_975551).sum := by decide
  have hdescent : baseEnd_975551 < baseStart_975551 := by decide
  rcases family_descends (prefixWord ++ tailWord_975551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975566 : List Nat := [4, 1, 1, 1, 3, 3, 2, 7]
def baseStart_975566 : Nat := 118140960795 + 975566 * 2 ^ 59
def prefixEnd_975566 : Nat := 4983230072969 + 3 ^ 40 * 975566 * 2
def baseEnd_975566 : Nat := 37106242087721135350997

theorem tailTrace_975566 : CollatzResearch.WordTrace tailWord_975566 prefixEnd_975566 37106242087721135350997 := by
  unfold tailWord_975566
  simp only [CollatzResearch.WordTrace]
  refine ⟨4447726897962308781642319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23721210122465646835425701 4447726897962308781642319)
  ·
    refine ⟨6671590346943463172463479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4447726897962308781642319 6671590346943463172463479)
    ·
      refine ⟨10007385520415194758695219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6671590346943463172463479 10007385520415194758695219)
      ·
        refine ⟨15011078280622792138042829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10007385520415194758695219 15011078280622792138042829)
        ·
          refine ⟨5629154355233547051766061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15011078280622792138042829 5629154355233547051766061)
          ·
            refine ⟨2110932883212580144412273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5629154355233547051766061 2110932883212580144412273)
            ·
              refine ⟨1583199662409435108309205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2110932883212580144412273 1583199662409435108309205)
              ·
                refine ⟨37106242087721135350997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1583199662409435108309205 37106242087721135350997)
                ·
                  rfl

theorem cell22_975566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 7].length) (baseStart_975566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975566 prefixEnd_975566 := by exact prefixLift 975566
  have htrace : WordTrace (prefixWord ++ tailWord_975566) baseStart_975566 baseEnd_975566 := by
    simpa [prefixWord, tailWord_975566, baseEnd_975566] using wordTrace_append hprefix tailTrace_975566
  have hstable : (prefixWord ++ tailWord_975566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975566).length < 2 ^ (prefixWord ++ tailWord_975566).sum := by decide
  have hdescent : baseEnd_975566 < baseStart_975566 := by decide
  rcases family_descends (prefixWord ++ tailWord_975566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975570 : List Nat := [3, 2, 2, 2, 3, 1, 1, 3, 2, 3]
def baseStart_975570 : Nat := 118140960795 + 975570 * 2 ^ 59
def prefixEnd_975570 : Nat := 4983230072969 + 3 ^ 40 * 975570 * 2
def baseEnd_975570 : Nat := 333957548071235541058961

theorem tailTrace_975570 : CollatzResearch.WordTrace tailWord_975570 prefixEnd_975570 333957548071235541058961 := by
  unfold tailWord_975570
  simp only [CollatzResearch.WordTrace]
  refine ⟨8895490268920994734071041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23721307383789319290856109 8895490268920994734071041)
  ·
    refine ⟨6671617701690746050553281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8895490268920994734071041 6671617701690746050553281)
    ·
      refine ⟨5003713276268059537914961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6671617701690746050553281 5003713276268059537914961)
      ·
        refine ⟨3752784957201044653436221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5003713276268059537914961 3752784957201044653436221)
        ·
          refine ⟨1407294358950391745038583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3752784957201044653436221 1407294358950391745038583)
          ·
            refine ⟨2110941538425587617557875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1407294358950391745038583 2110941538425587617557875)
            ·
              refine ⟨3166412307638381426336813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2110941538425587617557875 3166412307638381426336813)
              ·
                refine ⟨1187404615364393034876305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3166412307638381426336813 1187404615364393034876305)
                ·
                  refine ⟨890553461523294776157229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1187404615364393034876305 890553461523294776157229)
                  ·
                    refine ⟨333957548071235541058961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 890553461523294776157229 333957548071235541058961)
                    ·
                      rfl

theorem cell22_975570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_975570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975570 prefixEnd_975570 := by exact prefixLift 975570
  have htrace : WordTrace (prefixWord ++ tailWord_975570) baseStart_975570 baseEnd_975570 := by
    simpa [prefixWord, tailWord_975570, baseEnd_975570] using wordTrace_append hprefix tailTrace_975570
  have hstable : (prefixWord ++ tailWord_975570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975570).length < 2 ^ (prefixWord ++ tailWord_975570).sum := by decide
  have hdescent : baseEnd_975570 < baseStart_975570 := by decide
  rcases family_descends (prefixWord ++ tailWord_975570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975604 : List Nat := [2, 6, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_975604 : Nat := 118140960795 + 975604 * 2 ^ 59
def prefixEnd_975604 : Nat := 4983230072969 + 3 ^ 40 * 975604 * 2
def baseEnd_975604 : Nat := 333969186966070785708857

theorem tailTrace_975604 : CollatzResearch.WordTrace tailWord_975604 prefixEnd_975604 333969186966070785708857 := by
  unfold tailWord_975604
  simp only [CollatzResearch.WordTrace]
  refine ⟨17791600578780401371510933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23722134105040535162014577 17791600578780401371510933)
  ·
    refine ⟨833981277130331314289575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17791600578780401371510933 833981277130331314289575)
    ·
      refine ⟨1250971915695496971434363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 833981277130331314289575 1250971915695496971434363)
      ·
        refine ⟨1876457873543245457151545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1250971915695496971434363 1876457873543245457151545)
        ·
          refine ⟨1407343405157434092863659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1876457873543245457151545 1407343405157434092863659)
          ·
            refine ⟨2111015107736151139295489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1407343405157434092863659 2111015107736151139295489)
            ·
              refine ⟨1583261330802113354471617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2111015107736151139295489 1583261330802113354471617)
              ·
                refine ⟨1187445998101585015853713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1583261330802113354471617 1187445998101585015853713)
                ·
                  refine ⟨890584498576188761890285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1187445998101585015853713 890584498576188761890285)
                  ·
                    refine ⟨333969186966070785708857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 890584498576188761890285 333969186966070785708857)
                    ·
                      rfl

theorem cell22_975604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_975604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975604 prefixEnd_975604 := by exact prefixLift 975604
  have htrace : WordTrace (prefixWord ++ tailWord_975604) baseStart_975604 baseEnd_975604 := by
    simpa [prefixWord, tailWord_975604, baseEnd_975604] using wordTrace_append hprefix tailTrace_975604
  have hstable : (prefixWord ++ tailWord_975604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975604).length < 2 ^ (prefixWord ++ tailWord_975604).sum := by decide
  have hdescent : baseEnd_975604 < baseStart_975604 := by decide
  rcases family_descends (prefixWord ++ tailWord_975604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975609 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 3, 7]
def baseStart_975609 : Nat := 118140960795 + 975609 * 2 ^ 59
def prefixEnd_975609 : Nat := 4983230072969 + 3 ^ 40 * 975609 * 2
def baseEnd_975609 : Nat := 333970898568252439333841

theorem tailTrace_975609 : CollatzResearch.WordTrace tailWord_975609 prefixEnd_975609 333970898568252439333841 := by
  unfold tailWord_975609
  simp only [CollatzResearch.WordTrace]
  refine ⟨35583383522542688596953881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23722255681695125731302587 35583383522542688596953881)
  ·
    refine ⟨26687537641907016447715411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35583383522542688596953881 26687537641907016447715411)
    ·
      refine ⟨40031306462860524671573117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26687537641907016447715411 40031306462860524671573117)
      ·
        refine ⟨15011739923572696751839919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40031306462860524671573117 15011739923572696751839919)
        ·
          refine ⟨22517609885359045127759879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15011739923572696751839919 22517609885359045127759879)
          ·
            refine ⟨33776414828038567691639819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22517609885359045127759879 33776414828038567691639819)
            ·
              refine ⟨50664622242057851537459729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33776414828038567691639819 50664622242057851537459729)
              ·
                refine ⟨37998466681543388653094797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50664622242057851537459729 37998466681543388653094797)
                ·
                  refine ⟨14249425005578770744910549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37998466681543388653094797 14249425005578770744910549)
                  ·
                    refine ⟨333970898568252439333841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14249425005578770744910549 333970898568252439333841)
                    ·
                      rfl

theorem cell22_975609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 7].length) (baseStart_975609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975609 prefixEnd_975609 := by exact prefixLift 975609
  have htrace : WordTrace (prefixWord ++ tailWord_975609) baseStart_975609 baseEnd_975609 := by
    simpa [prefixWord, tailWord_975609, baseEnd_975609] using wordTrace_append hprefix tailTrace_975609
  have hstable : (prefixWord ++ tailWord_975609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975609).length < 2 ^ (prefixWord ++ tailWord_975609).sum := by decide
  have hdescent : baseEnd_975609 < baseStart_975609 := by decide
  rcases family_descends (prefixWord ++ tailWord_975609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975626 : List Nat := [3, 1, 2, 2, 1, 2, 3, 1, 2, 5]
def baseStart_975626 : Nat := 118140960795 + 975626 * 2 ^ 59
def prefixEnd_975626 : Nat := 4983230072969 + 3 ^ 40 * 975626 * 2
def baseEnd_975626 : Nat := 333976718015670061658789

theorem tailTrace_975626 : CollatzResearch.WordTrace tailWord_975626 prefixEnd_975626 333976718015670061658789 := by
  unfold tailWord_975626
  simp only [CollatzResearch.WordTrace]
  refine ⟨8896000890870275125080683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23722669042320733666881821 8896000890870275125080683)
  ·
    refine ⟨13344001336305412687621025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8896000890870275125080683 13344001336305412687621025)
    ·
      refine ⟨10008001002229059515715769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13344001336305412687621025 10008001002229059515715769)
      ·
        refine ⟨7506000751671794636786827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10008001002229059515715769 7506000751671794636786827)
        ·
          refine ⟨11259001127507691955180241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7506000751671794636786827 11259001127507691955180241)
          ·
            refine ⟨8444250845630768966385181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11259001127507691955180241 8444250845630768966385181)
            ·
              refine ⟨3166594067111538362394443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8444250845630768966385181 3166594067111538362394443)
              ·
                refine ⟨4749891100667307543591665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3166594067111538362394443 4749891100667307543591665)
                ·
                  refine ⟨3562418325500480657693749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4749891100667307543591665 3562418325500480657693749)
                  ·
                    refine ⟨333976718015670061658789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3562418325500480657693749 333976718015670061658789)
                    ·
                      rfl

theorem cell22_975626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_975626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975626 prefixEnd_975626 := by exact prefixLift 975626
  have htrace : WordTrace (prefixWord ++ tailWord_975626) baseStart_975626 baseEnd_975626 := by
    simpa [prefixWord, tailWord_975626, baseEnd_975626] using wordTrace_append hprefix tailTrace_975626
  have hstable : (prefixWord ++ tailWord_975626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975626).length < 2 ^ (prefixWord ++ tailWord_975626).sum := by decide
  have hdescent : baseEnd_975626 < baseStart_975626 := by decide
  rcases family_descends (prefixWord ++ tailWord_975626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975656 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 8]
def baseStart_975656 : Nat := 118140960795 + 975656 * 2 ^ 59
def prefixEnd_975656 : Nat := 4983230072969 + 3 ^ 40 * 975656 * 2
def baseEnd_975656 : Nat := 111328995876253327802899

theorem tailTrace_975656 : CollatzResearch.WordTrace tailWord_975656 prefixEnd_975656 111328995876253327802899 := by
  unfold tailWord_975656
  simp only [CollatzResearch.WordTrace]
  refine ⟨17792548876686207811957411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23723398502248277082609881 17792548876686207811957411)
  ·
    refine ⟨26688823315029311717936117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17792548876686207811957411 26688823315029311717936117)
    ·
      refine ⟨2502077185783997973556511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26688823315029311717936117 2502077185783997973556511)
      ·
        refine ⟨3753115778675996960334767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2502077185783997973556511 3753115778675996960334767)
        ·
          refine ⟨5629673668013995440502151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3753115778675996960334767 5629673668013995440502151)
          ·
            refine ⟨8444510502020993160753227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5629673668013995440502151 8444510502020993160753227)
            ·
              refine ⟨12666765753031489741129841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8444510502020993160753227 12666765753031489741129841)
              ·
                refine ⟨9500074314773617305847381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12666765753031489741129841 9500074314773617305847381)
                ·
                  refine ⟨111328995876253327802899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9500074314773617305847381 111328995876253327802899)
                  ·
                    rfl

theorem cell22_975656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 8].length) (baseStart_975656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975656 prefixEnd_975656 := by exact prefixLift 975656
  have htrace : WordTrace (prefixWord ++ tailWord_975656) baseStart_975656 baseEnd_975656 := by
    simpa [prefixWord, tailWord_975656, baseEnd_975656] using wordTrace_append hprefix tailTrace_975656
  have hstable : (prefixWord ++ tailWord_975656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975656).length < 2 ^ (prefixWord ++ tailWord_975656).sum := by decide
  have hdescent : baseEnd_975656 < baseStart_975656 := by decide
  rcases family_descends (prefixWord ++ tailWord_975656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975701 : List Nat := [1, 3, 2, 2, 2, 1, 3, 8]
def baseStart_975701 : Nat := 118140960795 + 975701 * 2 ^ 59
def prefixEnd_975701 : Nat := 4983230072969 + 3 ^ 40 * 975701 * 2
def baseEnd_975701 : Nat := 37111376894266096225951

theorem tailTrace_975701 : CollatzResearch.WordTrace tailWord_975701 prefixEnd_975701 37111376894266096225951 := by
  unfold tailWord_975701
  simp only [CollatzResearch.WordTrace]
  refine ⟨35586739038209388309302957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23724492692139592206201971 35586739038209388309302957)
  ·
    refine ⟨13345027139328520615988609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35586739038209388309302957 13345027139328520615988609)
    ·
      refine ⟨10008770354496390461991457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13345027139328520615988609 10008770354496390461991457)
      ·
        refine ⟨7506577765872292846493593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10008770354496390461991457 7506577765872292846493593)
        ·
          refine ⟨5629933324404219634870195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7506577765872292846493593 5629933324404219634870195)
          ·
            refine ⟨8444899986606329452305293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5629933324404219634870195 8444899986606329452305293)
            ·
              refine ⟨3166837494977373544614485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8444899986606329452305293 3166837494977373544614485)
              ·
                refine ⟨37111376894266096225951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3166837494977373544614485 37111376894266096225951)
                ·
                  rfl

theorem cell22_975701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 8].length) (baseStart_975701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975701 prefixEnd_975701 := by exact prefixLift 975701
  have htrace : WordTrace (prefixWord ++ tailWord_975701) baseStart_975701 baseEnd_975701 := by
    simpa [prefixWord, tailWord_975701, baseEnd_975701] using wordTrace_append hprefix tailTrace_975701
  have hstable : (prefixWord ++ tailWord_975701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975701).length < 2 ^ (prefixWord ++ tailWord_975701).sum := by decide
  have hdescent : baseEnd_975701 < baseStart_975701 := by decide
  rcases family_descends (prefixWord ++ tailWord_975701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975761 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 4, 5]
def baseStart_975761 : Nat := 118140960795 + 975761 * 2 ^ 59
def prefixEnd_975761 : Nat := 4983230072969 + 3 ^ 40 * 975761 * 2
def baseEnd_975761 : Nat := 334022931274574709533375

theorem tailTrace_975761 : CollatzResearch.WordTrace tailWord_975761 prefixEnd_975761 334022931274574709533375 := by
  unfold tailWord_975761
  simp only [CollatzResearch.WordTrace]
  refine ⟨35588927417992018556487137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23725951611994679037658091 35588927417992018556487137)
  ·
    refine ⟨26691695563494013917365353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35588927417992018556487137 26691695563494013917365353)
    ·
      refine ⟨20018771672620510438024015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26691695563494013917365353 20018771672620510438024015)
      ·
        refine ⟨30028157508930765657036023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20018771672620510438024015 30028157508930765657036023)
        ·
          refine ⟨45042236263396148485554035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30028157508930765657036023 45042236263396148485554035)
          ·
            refine ⟨67563354395094222728331053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45042236263396148485554035 67563354395094222728331053)
            ·
              refine ⟨25336257898160333523124145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67563354395094222728331053 25336257898160333523124145)
              ·
                refine ⟨19002193423620250142343109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25336257898160333523124145 19002193423620250142343109)
                ·
                  refine ⟨3562911266928796901689333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19002193423620250142343109 3562911266928796901689333)
                  ·
                    refine ⟨334022931274574709533375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3562911266928796901689333 334022931274574709533375)
                    ·
                      rfl

theorem cell22_975761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_975761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975761 prefixEnd_975761 := by exact prefixLift 975761
  have htrace : WordTrace (prefixWord ++ tailWord_975761) baseStart_975761 baseEnd_975761 := by
    simpa [prefixWord, tailWord_975761, baseEnd_975761] using wordTrace_append hprefix tailTrace_975761
  have hstable : (prefixWord ++ tailWord_975761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975761).length < 2 ^ (prefixWord ++ tailWord_975761).sum := by decide
  have hdescent : baseEnd_975761 < baseStart_975761 := by decide
  rcases family_descends (prefixWord ++ tailWord_975761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975808 : List Nat := [2, 1, 1, 2, 3, 4, 1, 2, 6]
def baseStart_975808 : Nat := 118140960795 + 975808 * 2 ^ 59
def prefixEnd_975808 : Nat := 4983230072969 + 3 ^ 40 * 975808 * 2
def baseEnd_975808 : Nat := 111346340111694084536077

theorem tailTrace_975808 : CollatzResearch.WordTrace tailWord_975808 prefixEnd_975808 111346340111694084536077 := by
  unfold tailWord_975808
  simp only [CollatzResearch.WordTrace]
  refine ⟨17795320824410872791724039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23727094432547830388965385 17795320824410872791724039)
  ·
    refine ⟨26692981236616309187586059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17795320824410872791724039 26692981236616309187586059)
    ·
      refine ⟨40039471854924463781379089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26692981236616309187586059 40039471854924463781379089)
      ·
        refine ⟨30029603891193347836034317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40039471854924463781379089 30029603891193347836034317)
        ·
          refine ⟨11261101459197505438512869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30029603891193347836034317 11261101459197505438512869)
          ·
            refine ⟨2111456523599532269721163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11261101459197505438512869 2111456523599532269721163)
            ·
              refine ⟨3167184785399298404581745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2111456523599532269721163 3167184785399298404581745)
              ·
                refine ⟨2375388589049473803436309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3167184785399298404581745 2375388589049473803436309)
                ·
                  refine ⟨111346340111694084536077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2375388589049473803436309 111346340111694084536077)
                  ·
                    rfl

theorem cell22_975808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 6].length) (baseStart_975808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975808 prefixEnd_975808 := by exact prefixLift 975808
  have htrace : WordTrace (prefixWord ++ tailWord_975808) baseStart_975808 baseEnd_975808 := by
    simpa [prefixWord, tailWord_975808, baseEnd_975808] using wordTrace_append hprefix tailTrace_975808
  have hstable : (prefixWord ++ tailWord_975808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975808).length < 2 ^ (prefixWord ++ tailWord_975808).sum := by decide
  have hdescent : baseEnd_975808 < baseStart_975808 := by decide
  rcases family_descends (prefixWord ++ tailWord_975808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975823 : List Nat := [1, 1, 2, 1, 1, 6, 2, 2, 1, 5]
def baseStart_975823 : Nat := 118140960795 + 975823 * 2 ^ 59
def prefixEnd_975823 : Nat := 4983230072969 + 3 ^ 40 * 975823 * 2
def baseEnd_975823 : Nat := 334044155141627214483185

theorem tailTrace_975823 : CollatzResearch.WordTrace tailWord_975823 prefixEnd_975823 334044155141627214483185 := by
  unfold tailWord_975823
  simp only [CollatzResearch.WordTrace]
  refine ⟨35591188743767403145244123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23727459162511602096829415 35591188743767403145244123)
  ·
    refine ⟨53386783115651104717866185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35591188743767403145244123 53386783115651104717866185)
    ·
      refine ⟨40040087336738328538399639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53386783115651104717866185 40040087336738328538399639)
      ·
        refine ⟨60060131005107492807599459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40040087336738328538399639 60060131005107492807599459)
        ·
          refine ⟨90090196507661239211399189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60060131005107492807599459 90090196507661239211399189)
          ·
            refine ⟨4222977961296620588034337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90090196507661239211399189 4222977961296620588034337)
            ·
              refine ⟨3167233470972465441025753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4222977961296620588034337 3167233470972465441025753)
              ·
                refine ⟨2375425103229349080769315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3167233470972465441025753 2375425103229349080769315)
                ·
                  refine ⟨3563137654844023621153973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2375425103229349080769315 3563137654844023621153973)
                  ·
                    refine ⟨334044155141627214483185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3563137654844023621153973 334044155141627214483185)
                    ·
                      rfl

theorem cell22_975823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 5].length) (baseStart_975823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975823 prefixEnd_975823 := by exact prefixLift 975823
  have htrace : WordTrace (prefixWord ++ tailWord_975823) baseStart_975823 baseEnd_975823 := by
    simpa [prefixWord, tailWord_975823, baseEnd_975823] using wordTrace_append hprefix tailTrace_975823
  have hstable : (prefixWord ++ tailWord_975823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975823).length < 2 ^ (prefixWord ++ tailWord_975823).sum := by decide
  have hdescent : baseEnd_975823 < baseStart_975823 := by decide
  rcases family_descends (prefixWord ++ tailWord_975823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975825 : List Nat := [1, 2, 2, 1, 2, 1, 6, 3, 4]
def baseStart_975825 : Nat := 118140960795 + 975825 * 2 ^ 59
def prefixEnd_975825 : Nat := 4983230072969 + 3 ^ 40 * 975825 * 2
def baseEnd_975825 : Nat := 111348279927499958644393

theorem tailTrace_975825 : CollatzResearch.WordTrace tailWord_975825 prefixEnd_975825 111348279927499958644393 := by
  unfold tailWord_975825
  simp only [CollatzResearch.WordTrace]
  refine ⟨35591261689760157486816929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23727507793173438324544619 35591261689760157486816929)
  ·
    refine ⟨26693446267320118115112697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35591261689760157486816929 26693446267320118115112697)
    ·
      refine ⟨20020084700490088586334523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26693446267320118115112697 20020084700490088586334523)
      ·
        refine ⟨30030127050735132879501785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20020084700490088586334523 30030127050735132879501785)
        ·
          refine ⟨22522595288051349659626339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30030127050735132879501785 22522595288051349659626339)
          ·
            refine ⟨33783892932077024489439509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22522595288051349659626339 33783892932077024489439509)
            ·
              refine ⟨1583619981191110522942477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33783892932077024489439509 1583619981191110522942477)
              ·
                refine ⟨593857492946666446103429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1583619981191110522942477 593857492946666446103429)
                ·
                  refine ⟨111348279927499958644393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 593857492946666446103429 111348279927499958644393)
                  ·
                    rfl

theorem cell22_975825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 3, 4].length) (baseStart_975825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975825 prefixEnd_975825 := by exact prefixLift 975825
  have htrace : WordTrace (prefixWord ++ tailWord_975825) baseStart_975825 baseEnd_975825 := by
    simpa [prefixWord, tailWord_975825, baseEnd_975825] using wordTrace_append hprefix tailTrace_975825
  have hstable : (prefixWord ++ tailWord_975825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975825).length < 2 ^ (prefixWord ++ tailWord_975825).sum := by decide
  have hdescent : baseEnd_975825 < baseStart_975825 := by decide
  rcases family_descends (prefixWord ++ tailWord_975825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975842 : List Nat := [3, 3, 3, 1, 1, 2, 2, 1, 6]
def baseStart_975842 : Nat := 118140960795 + 975842 * 2 ^ 59
def prefixEnd_975842 : Nat := 4983230072969 + 3 ^ 40 * 975842 * 2
def baseEnd_975842 : Nat := 111350219743305832752709

theorem tailTrace_975842 : CollatzResearch.WordTrace tailWord_975842 prefixEnd_975842 111350219743305832752709 := by
  unfold tailWord_975842
  simp only [CollatzResearch.WordTrace]
  refine ⟨8897970432674642347546445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23727921153799046260123853 8897970432674642347546445)
  ·
    refine ⟨3336738912252990880329917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8897970432674642347546445 3336738912252990880329917)
    ·
      refine ⟨1251277092094871580123719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3336738912252990880329917 1251277092094871580123719)
      ·
        refine ⟨1876915638142307370185579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1251277092094871580123719 1876915638142307370185579)
        ·
          refine ⟨2815373457213461055278369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1876915638142307370185579 2815373457213461055278369)
          ·
            refine ⟨2111530092910095791458777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2815373457213461055278369 2111530092910095791458777)
            ·
              refine ⟨1583647569682571843594083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2111530092910095791458777 1583647569682571843594083)
              ·
                refine ⟨2375471354523857765391125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1583647569682571843594083 2375471354523857765391125)
                ·
                  refine ⟨111350219743305832752709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2375471354523857765391125 111350219743305832752709)
                  ·
                    rfl

theorem cell22_975842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_975842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975842 prefixEnd_975842 := by exact prefixLift 975842
  have htrace : WordTrace (prefixWord ++ tailWord_975842) baseStart_975842 baseEnd_975842 := by
    simpa [prefixWord, tailWord_975842, baseEnd_975842] using wordTrace_append hprefix tailTrace_975842
  have hstable : (prefixWord ++ tailWord_975842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975842).length < 2 ^ (prefixWord ++ tailWord_975842).sum := by decide
  have hdescent : baseEnd_975842 < baseStart_975842 := by decide
  rcases family_descends (prefixWord ++ tailWord_975842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975898 : List Nat := [3, 1, 1, 3, 1, 2, 1, 3, 7]
def baseStart_975898 : Nat := 118140960795 + 975898 * 2 ^ 59
def prefixEnd_975898 : Nat := 4983230072969 + 3 ^ 40 * 975898 * 2
def baseEnd_975898 : Nat := 111356609724784006285985

theorem tailTrace_975898 : CollatzResearch.WordTrace tailWord_975898 prefixEnd_975898 111356609724784006285985 := by
  unfold tailWord_975898
  simp only [CollatzResearch.WordTrace]
  refine ⟨8898481054623922738556087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23729282812330460636149565 8898481054623922738556087)
  ·
    refine ⟨13347721581935884107834131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8898481054623922738556087 13347721581935884107834131)
    ·
      refine ⟨20021582372903826161751197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13347721581935884107834131 20021582372903826161751197)
      ·
        refine ⟨7508093389838934810656699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20021582372903826161751197 7508093389838934810656699)
        ·
          refine ⟨11262140084758402215985049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7508093389838934810656699 11262140084758402215985049)
          ·
            refine ⟨8446605063568801661988787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11262140084758402215985049 8446605063568801661988787)
            ·
              refine ⟨12669907595353202492983181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8446605063568801661988787 12669907595353202492983181)
              ·
                refine ⟨4751215348257450934868693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12669907595353202492983181 4751215348257450934868693)
                ·
                  refine ⟨111356609724784006285985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4751215348257450934868693 111356609724784006285985)
                  ·
                    rfl

theorem cell22_975898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 7].length) (baseStart_975898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975898 prefixEnd_975898 := by exact prefixLift 975898
  have htrace : WordTrace (prefixWord ++ tailWord_975898) baseStart_975898 baseEnd_975898 := by
    simpa [prefixWord, tailWord_975898, baseEnd_975898] using wordTrace_append hprefix tailTrace_975898
  have hstable : (prefixWord ++ tailWord_975898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975898).length < 2 ^ (prefixWord ++ tailWord_975898).sum := by decide
  have hdescent : baseEnd_975898 < baseStart_975898 := by decide
  rcases family_descends (prefixWord ++ tailWord_975898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975975 : List Nat := [1, 1, 5, 1, 1, 3, 1, 3, 1, 5]
def baseStart_975975 : Nat := 118140960795 + 975975 * 2 ^ 59
def prefixEnd_975975 : Nat := 4983230072969 + 3 ^ 40 * 975975 * 2
def baseEnd_975975 : Nat := 334096187847949484682719

theorem tailTrace_975975 : CollatzResearch.WordTrace tailWord_975975 prefixEnd_975975 334096187847949484682719 := by
  unfold tailWord_975975
  simp only [CollatzResearch.WordTrace]
  refine ⟨35596732639216733104777379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23731155092811155403184919 35596732639216733104777379)
  ·
    refine ⟨53395098958825099657166069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35596732639216733104777379 53395098958825099657166069)
    ·
      refine ⟨5005790527389853092859319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53395098958825099657166069 5005790527389853092859319)
      ·
        refine ⟨7508685791084779639288979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5005790527389853092859319 7508685791084779639288979)
        ·
          refine ⟨11263028686627169458933469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7508685791084779639288979 11263028686627169458933469)
          ·
            refine ⟨4223635757485188547100051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11263028686627169458933469 4223635757485188547100051)
            ·
              refine ⟨6335453636227782820650077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4223635757485188547100051 6335453636227782820650077)
              ·
                refine ⟨2375795113585418557743779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6335453636227782820650077 2375795113585418557743779)
                ·
                  refine ⟨3563692670378127836615669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2375795113585418557743779 3563692670378127836615669)
                  ·
                    refine ⟨334096187847949484682719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3563692670378127836615669 334096187847949484682719)
                    ·
                      rfl

theorem cell22_975975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_975975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_975975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_975975 prefixEnd_975975 := by exact prefixLift 975975
  have htrace : WordTrace (prefixWord ++ tailWord_975975) baseStart_975975 baseEnd_975975 := by
    simpa [prefixWord, tailWord_975975, baseEnd_975975] using wordTrace_append hprefix tailTrace_975975
  have hstable : (prefixWord ++ tailWord_975975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975975).length < 2 ^ (prefixWord ++ tailWord_975975).sum := by decide
  have hdescent : baseEnd_975975 < baseStart_975975 := by decide
  rcases family_descends (prefixWord ++ tailWord_975975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976005 : List Nat := [1, 3, 1, 1, 6, 1, 9]
def baseStart_976005 : Nat := 118140960795 + 976005 * 2 ^ 59
def prefixEnd_976005 : Nat := 4983230072969 + 3 ^ 40 * 976005 * 2
def baseEnd_976005 : Nat := 12374313239297755793801

theorem tailTrace_976005 : CollatzResearch.WordTrace tailWord_976005 prefixEnd_976005 12374313239297755793801 := by
  unfold tailWord_976005
  simp only [CollatzResearch.WordTrace]
  refine ⟨35597826829108048228369469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23731884552738698818912979 35597826829108048228369469)
  ·
    refine ⟨13349185060915518085638551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35597826829108048228369469 13349185060915518085638551)
    ·
      refine ⟨20023777591373277128457827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13349185060915518085638551 20023777591373277128457827)
      ·
        refine ⟨30035666387059915692686741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20023777591373277128457827 30035666387059915692686741)
        ·
          refine ⟨1407921861893433548094691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30035666387059915692686741 1407921861893433548094691)
          ·
            refine ⟨2111882792840150322142037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1407921861893433548094691 2111882792840150322142037)
            ·
              refine ⟨12374313239297755793801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2111882792840150322142037 12374313239297755793801)
              ·
                rfl

theorem cell22_976005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 9].length) (baseStart_976005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976005 prefixEnd_976005 := by exact prefixLift 976005
  have htrace : WordTrace (prefixWord ++ tailWord_976005) baseStart_976005 baseEnd_976005 := by
    simpa [prefixWord, tailWord_976005, baseEnd_976005] using wordTrace_append hprefix tailTrace_976005
  have hstable : (prefixWord ++ tailWord_976005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976005).length < 2 ^ (prefixWord ++ tailWord_976005).sum := by decide
  have hdescent : baseEnd_976005 < baseStart_976005 := by decide
  rcases family_descends (prefixWord ++ tailWord_976005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976009 : List Nat := [1, 2, 1, 1, 4, 5, 1, 2, 2, 3]
def baseStart_976009 : Nat := 118140960795 + 976009 * 2 ^ 59
def prefixEnd_976009 : Nat := 4983230072969 + 3 ^ 40 * 976009 * 2
def baseEnd_976009 : Nat := 334107826742784729332615

theorem tailTrace_976009 : CollatzResearch.WordTrace tailWord_976009 prefixEnd_976009 334107826742784729332615 := by
  unfold tailWord_976009
  simp only [CollatzResearch.WordTrace]
  refine ⟨35597972721093556911515081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23731981814062371274343387 35597972721093556911515081)
  ·
    refine ⟨26698479540820167683636311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35597972721093556911515081 26698479540820167683636311)
    ·
      refine ⟨40047719311230251525454467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26698479540820167683636311 40047719311230251525454467)
      ·
        refine ⟨60071578966845377288181701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40047719311230251525454467 60071578966845377288181701)
        ·
          refine ⟨11263421056283508241534069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60071578966845377288181701 11263421056283508241534069)
          ·
            refine ⟨1055945724026578897643819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11263421056283508241534069 1055945724026578897643819)
            ·
              refine ⟨1583918586039868346465729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1055945724026578897643819 1583918586039868346465729)
              ·
                refine ⟨1187938939529901259849297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1583918586039868346465729 1187938939529901259849297)
                ·
                  refine ⟨890954204647425944886973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1187938939529901259849297 890954204647425944886973)
                  ·
                    refine ⟨334107826742784729332615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 890954204647425944886973 334107826742784729332615)
                    ·
                      rfl

theorem cell22_976009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 2, 3].length) (baseStart_976009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976009 prefixEnd_976009 := by exact prefixLift 976009
  have htrace : WordTrace (prefixWord ++ tailWord_976009) baseStart_976009 baseEnd_976009 := by
    simpa [prefixWord, tailWord_976009, baseEnd_976009] using wordTrace_append hprefix tailTrace_976009
  have hstable : (prefixWord ++ tailWord_976009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976009).length < 2 ^ (prefixWord ++ tailWord_976009).sum := by decide
  have hdescent : baseEnd_976009 < baseStart_976009 := by decide
  rcases family_descends (prefixWord ++ tailWord_976009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976026 : List Nat := [3, 1, 1, 5, 1, 2, 3, 1, 2, 3]
def baseStart_976026 : Nat := 118140960795 + 976026 * 2 ^ 59
def prefixEnd_976026 : Nat := 4983230072969 + 3 ^ 40 * 976026 * 2
def baseEnd_976026 : Nat := 334113646190202351657563

theorem tailTrace_976026 : CollatzResearch.WordTrace tailWord_976026 prefixEnd_976026 334113646190202351657563 := by
  unfold tailWord_976026
  simp only [CollatzResearch.WordTrace]
  refine ⟨8899648190507992203720983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23732395174687979209922621 8899648190507992203720983)
  ·
    refine ⟨13349472285761988305581475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8899648190507992203720983 13349472285761988305581475)
    ·
      refine ⟨20024208428642982458372213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13349472285761988305581475 20024208428642982458372213)
      ·
        refine ⟨1877269540185279605472395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20024208428642982458372213 1877269540185279605472395)
        ·
          refine ⟨2815904310277919408208593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1877269540185279605472395 2815904310277919408208593)
          ·
            refine ⟨2111928232708439556156445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2815904310277919408208593 2111928232708439556156445)
            ·
              refine ⟨791973087265664833558667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2111928232708439556156445 791973087265664833558667)
              ·
                refine ⟨1187959630898497250338001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 791973087265664833558667 1187959630898497250338001)
                ·
                  refine ⟨890969723173872937753501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1187959630898497250338001 890969723173872937753501)
                  ·
                    refine ⟨334113646190202351657563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 890969723173872937753501 334113646190202351657563)
                    ·
                      rfl

theorem cell22_976026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 2, 3].length) (baseStart_976026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976026 prefixEnd_976026 := by exact prefixLift 976026
  have htrace : WordTrace (prefixWord ++ tailWord_976026) baseStart_976026 baseEnd_976026 := by
    simpa [prefixWord, tailWord_976026, baseEnd_976026] using wordTrace_append hprefix tailTrace_976026
  have hstable : (prefixWord ++ tailWord_976026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976026).length < 2 ^ (prefixWord ++ tailWord_976026).sum := by decide
  have hdescent : baseEnd_976026 < baseStart_976026 := by decide
  rcases family_descends (prefixWord ++ tailWord_976026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976037 : List Nat := [1, 3, 1, 2, 1, 4, 2, 2, 3, 3]
def baseStart_976037 : Nat := 118140960795 + 976037 * 2 ^ 59
def prefixEnd_976037 : Nat := 4983230072969 + 3 ^ 40 * 976037 * 2
def baseEnd_976037 : Nat := 334117411715001989632529

theorem tailTrace_976037 : CollatzResearch.WordTrace tailWord_976037 prefixEnd_976037 334117411715001989632529 := by
  unfold tailWord_976037
  simp only [CollatzResearch.WordTrace]
  refine ⟨35598993964992117693534365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23732662643328078462356243 35598993964992117693534365)
  ·
    refine ⟨13349622736872044135075387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35598993964992117693534365 13349622736872044135075387)
    ·
      refine ⟨20024434105308066202613081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13349622736872044135075387 20024434105308066202613081)
      ·
        refine ⟨15018325578981049651959811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20024434105308066202613081 15018325578981049651959811)
        ·
          refine ⟨22527488368471574477939717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15018325578981049651959811 22527488368471574477939717)
          ·
            refine ⟨4223904069088420214613697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22527488368471574477939717 4223904069088420214613697)
            ·
              refine ⟨3167928051816315160960273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4223904069088420214613697 3167928051816315160960273)
              ·
                refine ⟨2375946038862236370720205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3167928051816315160960273 2375946038862236370720205)
                ·
                  refine ⟨890979764573338639020077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2375946038862236370720205 890979764573338639020077)
                  ·
                    refine ⟨334117411715001989632529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 890979764573338639020077 334117411715001989632529)
                    ·
                      rfl

theorem cell22_976037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 3, 3].length) (baseStart_976037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976037 prefixEnd_976037 := by exact prefixLift 976037
  have htrace : WordTrace (prefixWord ++ tailWord_976037) baseStart_976037 baseEnd_976037 := by
    simpa [prefixWord, tailWord_976037, baseEnd_976037] using wordTrace_append hprefix tailTrace_976037
  have hstable : (prefixWord ++ tailWord_976037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976037).length < 2 ^ (prefixWord ++ tailWord_976037).sum := by decide
  have hdescent : baseEnd_976037 < baseStart_976037 := by decide
  rcases family_descends (prefixWord ++ tailWord_976037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976039 : List Nat := [1, 1, 6, 2, 1, 3, 2, 6]
def baseStart_976039 : Nat := 118140960795 + 976039 * 2 ^ 59
def prefixEnd_976039 : Nat := 4983230072969 + 3 ^ 40 * 976039 * 2
def baseEnd_976039 : Nat := 37124232928430516786947

theorem tailTrace_976039 : CollatzResearch.WordTrace tailWord_976039 prefixEnd_976039 37124232928430516786947 := by
  unfold tailWord_976039
  simp only [CollatzResearch.WordTrace]
  refine ⟨35599066910984872035107171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23732711273989914690071447 35599066910984872035107171)
  ·
    refine ⟨53398600366477308052660757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35599066910984872035107171 53398600366477308052660757)
    ·
      refine ⟨2503059392178623814968473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53398600366477308052660757 2503059392178623814968473)
      ·
        refine ⟨1877294544133967861226355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2503059392178623814968473 1877294544133967861226355)
        ·
          refine ⟨2815941816200951791839533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1877294544133967861226355 2815941816200951791839533)
          ·
            refine ⟨1055978181075356921939825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2815941816200951791839533 1055978181075356921939825)
            ·
              refine ⟨791983635806517691454869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1055978181075356921939825 791983635806517691454869)
              ·
                refine ⟨37124232928430516786947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 791983635806517691454869 37124232928430516786947)
                ·
                  rfl

theorem cell22_976039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 6].length) (baseStart_976039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976039 prefixEnd_976039 := by exact prefixLift 976039
  have htrace : WordTrace (prefixWord ++ tailWord_976039) baseStart_976039 baseEnd_976039 := by
    simpa [prefixWord, tailWord_976039, baseEnd_976039] using wordTrace_append hprefix tailTrace_976039
  have hstable : (prefixWord ++ tailWord_976039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976039).length < 2 ^ (prefixWord ++ tailWord_976039).sum := by decide
  have hdescent : baseEnd_976039 < baseStart_976039 := by decide
  rcases family_descends (prefixWord ++ tailWord_976039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976050 : List Nat := [3, 2, 1, 1, 1, 4, 1, 2, 7]
def baseStart_976050 : Nat := 118140960795 + 976050 * 2 ^ 59
def prefixEnd_976050 : Nat := 4983230072969 + 3 ^ 40 * 976050 * 2
def baseEnd_976050 : Nat := 111373953960224763019163

theorem tailTrace_976050 : CollatzResearch.WordTrace tailWord_976050 prefixEnd_976050 111373953960224763019163 := by
  unfold tailWord_976050
  simp only [CollatzResearch.WordTrace]
  refine ⟨8899867028486255228439401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23732978742630013942505069 8899867028486255228439401)
  ·
    refine ⟨6674900271364691421329551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8899867028486255228439401 6674900271364691421329551)
    ·
      refine ⟨10012350407047037131994327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6674900271364691421329551 10012350407047037131994327)
      ·
        refine ⟨15018525610570555697991491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10012350407047037131994327 15018525610570555697991491)
        ·
          refine ⟨22527788415855833546987237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15018525610570555697991491 22527788415855833546987237)
          ·
            refine ⟨4223960327972968790060107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22527788415855833546987237 4223960327972968790060107)
            ·
              refine ⟨6335940491959453185090161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4223960327972968790060107 6335940491959453185090161)
              ·
                refine ⟨4751955368969589888817621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6335940491959453185090161 4751955368969589888817621)
                ·
                  refine ⟨111373953960224763019163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4751955368969589888817621 111373953960224763019163)
                  ·
                    rfl

theorem cell22_976050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_976050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976050 prefixEnd_976050 := by exact prefixLift 976050
  have htrace : WordTrace (prefixWord ++ tailWord_976050) baseStart_976050 baseEnd_976050 := by
    simpa [prefixWord, tailWord_976050, baseEnd_976050] using wordTrace_append hprefix tailTrace_976050
  have hstable : (prefixWord ++ tailWord_976050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976050).length < 2 ^ (prefixWord ++ tailWord_976050).sum := by decide
  have hdescent : baseEnd_976050 < baseStart_976050 := by decide
  rcases family_descends (prefixWord ++ tailWord_976050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976077 : List Nat := [1, 6, 2, 2, 2, 1, 2, 1, 2, 3]
def baseStart_976077 : Nat := 118140960795 + 976077 * 2 ^ 59
def prefixEnd_976077 : Nat := 4983230072969 + 3 ^ 40 * 976077 * 2
def baseEnd_976077 : Nat := 334131104532455218632407

theorem tailTrace_976077 : CollatzResearch.WordTrace tailWord_976077 prefixEnd_976077 334131104532455218632407 := by
  unfold tailWord_976077
  simp only [CollatzResearch.WordTrace]
  refine ⟨35600452884847204524990485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23733635256564803016660323 35600452884847204524990485)
  ·
    refine ⟨1668771228977212712108929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35600452884847204524990485 1668771228977212712108929)
    ·
      refine ⟨1251578421732909534081697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1668771228977212712108929 1251578421732909534081697)
      ·
        refine ⟨938683816299682150561273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1251578421732909534081697 938683816299682150561273)
        ·
          refine ⟨704012862224761612920955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 938683816299682150561273 704012862224761612920955)
          ·
            refine ⟨1056019293337142419381433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704012862224761612920955 1056019293337142419381433)
            ·
              refine ⟨792014470002856814536075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1056019293337142419381433 792014470002856814536075)
              ·
                refine ⟨1188021705004285221804113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 792014470002856814536075 1188021705004285221804113)
                ·
                  refine ⟨891016278753213916353085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1188021705004285221804113 891016278753213916353085)
                  ·
                    refine ⟨334131104532455218632407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 891016278753213916353085 334131104532455218632407)
                    ·
                      rfl

theorem cell22_976077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_976077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976077 prefixEnd_976077 := by exact prefixLift 976077
  have htrace : WordTrace (prefixWord ++ tailWord_976077) baseStart_976077 baseEnd_976077 := by
    simpa [prefixWord, tailWord_976077, baseEnd_976077] using wordTrace_append hprefix tailTrace_976077
  have hstable : (prefixWord ++ tailWord_976077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976077).length < 2 ^ (prefixWord ++ tailWord_976077).sum := by decide
  have hdescent : baseEnd_976077 < baseStart_976077 := by decide
  rcases family_descends (prefixWord ++ tailWord_976077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976095 : List Nat := [1, 1, 2, 3, 2, 1, 2, 4, 6]
def baseStart_976095 : Nat := 118140960795 + 976095 * 2 ^ 59
def prefixEnd_976095 : Nat := 4983230072969 + 3 ^ 40 * 976095 * 2
def baseEnd_976095 : Nat := 111379088766769723894117

theorem tailTrace_976095 : CollatzResearch.WordTrace tailWord_976095 prefixEnd_976095 111379088766769723894117 := by
  unfold tailWord_976095
  simp only [CollatzResearch.WordTrace]
  refine ⟨35601109398781993599145739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23734072932521329066097159 35601109398781993599145739)
  ·
    refine ⟨53401664098172990398718609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35601109398781993599145739 53401664098172990398718609)
    ·
      refine ⟨40051248073629742799038957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53401664098172990398718609 40051248073629742799038957)
      ·
        refine ⟨15019218027611153549639609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40051248073629742799038957 15019218027611153549639609)
        ·
          refine ⟨11264413520708365162229707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15019218027611153549639609 11264413520708365162229707)
          ·
            refine ⟨16896620281062547743344561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11264413520708365162229707 16896620281062547743344561)
            ·
              refine ⟨12672465210796910807508421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16896620281062547743344561 12672465210796910807508421)
              ·
                refine ⟨2376087227024420776407829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12672465210796910807508421 2376087227024420776407829)
                ·
                  refine ⟨111379088766769723894117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2376087227024420776407829 111379088766769723894117)
                  ·
                    rfl

theorem cell22_976095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 6].length) (baseStart_976095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976095 prefixEnd_976095 := by exact prefixLift 976095
  have htrace : WordTrace (prefixWord ++ tailWord_976095) baseStart_976095 baseEnd_976095 := by
    simpa [prefixWord, tailWord_976095, baseEnd_976095] using wordTrace_append hprefix tailTrace_976095
  have hstable : (prefixWord ++ tailWord_976095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976095).length < 2 ^ (prefixWord ++ tailWord_976095).sum := by decide
  have hdescent : baseEnd_976095 < baseStart_976095 := by decide
  rcases family_descends (prefixWord ++ tailWord_976095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976097 : List Nat := [1, 2, 3, 1, 3, 3, 1, 1, 3, 4]
def baseStart_976097 : Nat := 118140960795 + 976097 * 2 ^ 59
def prefixEnd_976097 : Nat := 4983230072969 + 3 ^ 40 * 976097 * 2
def baseEnd_976097 : Nat := 334137950941181833132345

theorem tailTrace_976097 : CollatzResearch.WordTrace tailWord_976097 prefixEnd_976097 334137950941181833132345 := by
  unfold tailWord_976097
  simp only [CollatzResearch.WordTrace]
  refine ⟨35601182344774747940718545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23734121563183165293812363 35601182344774747940718545)
  ·
    refine ⟨26700886758581060955538909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35601182344774747940718545 26700886758581060955538909)
    ·
      refine ⟨10012832534467897858327091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26700886758581060955538909 10012832534467897858327091)
      ·
        refine ⟨15019248801701846787490637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10012832534467897858327091 15019248801701846787490637)
        ·
          refine ⟨5632218300638192545308989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15019248801701846787490637 5632218300638192545308989)
          ·
            refine ⟨2112081862739322204490871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5632218300638192545308989 2112081862739322204490871)
            ·
              refine ⟨3168122794108983306736307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2112081862739322204490871 3168122794108983306736307)
              ·
                refine ⟨4752184191163474960104461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3168122794108983306736307 4752184191163474960104461)
                ·
                  refine ⟨1782069071686303110039173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4752184191163474960104461 1782069071686303110039173)
                  ·
                    refine ⟨334137950941181833132345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1782069071686303110039173 334137950941181833132345)
                    ·
                      rfl

theorem cell22_976097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_976097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976097 prefixEnd_976097 := by exact prefixLift 976097
  have htrace : WordTrace (prefixWord ++ tailWord_976097) baseStart_976097 baseEnd_976097 := by
    simpa [prefixWord, tailWord_976097, baseEnd_976097] using wordTrace_append hprefix tailTrace_976097
  have hstable : (prefixWord ++ tailWord_976097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976097).length < 2 ^ (prefixWord ++ tailWord_976097).sum := by decide
  have hdescent : baseEnd_976097 < baseStart_976097 := by decide
  rcases family_descends (prefixWord ++ tailWord_976097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976125 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 5, 6]
def baseStart_976125 : Nat := 118140960795 + 976125 * 2 ^ 59
def prefixEnd_976125 : Nat := 4983230072969 + 3 ^ 40 * 976125 * 2
def baseEnd_976125 : Nat := 334147535913399093432259

theorem tailTrace_976125 : CollatzResearch.WordTrace tailWord_976125 prefixEnd_976125 334147535913399093432259 := by
  unfold tailWord_976125
  simp only [CollatzResearch.WordTrace]
  refine ⟨35602203588673308722737829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23734802392448872481825219 35602203588673308722737829)
  ·
    refine ⟨6675413172876245385513343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35602203588673308722737829 6675413172876245385513343)
    ·
      refine ⟨10013119759314368078270015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6675413172876245385513343 10013119759314368078270015)
      ·
        refine ⟨15019679638971552117405023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10013119759314368078270015 15019679638971552117405023)
        ·
          refine ⟨22529519458457328176107535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15019679638971552117405023 22529519458457328176107535)
          ·
            refine ⟨33794279187685992264161303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22529519458457328176107535 33794279187685992264161303)
            ·
              refine ⟨50691418781528988396241955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33794279187685992264161303 50691418781528988396241955)
              ·
                refine ⟨76037128172293482594362933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50691418781528988396241955 76037128172293482594362933)
                ·
                  refine ⟨7128480766152513993221525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76037128172293482594362933 7128480766152513993221525)
                  ·
                    refine ⟨334147535913399093432259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7128480766152513993221525 334147535913399093432259)
                    ·
                      rfl

theorem cell22_976125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_976125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976125 prefixEnd_976125 := by exact prefixLift 976125
  have htrace : WordTrace (prefixWord ++ tailWord_976125) baseStart_976125 baseEnd_976125 := by
    simpa [prefixWord, tailWord_976125, baseEnd_976125] using wordTrace_append hprefix tailTrace_976125
  have hstable : (prefixWord ++ tailWord_976125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976125).length < 2 ^ (prefixWord ++ tailWord_976125).sum := by decide
  have hdescent : baseEnd_976125 < baseStart_976125 := by decide
  rcases family_descends (prefixWord ++ tailWord_976125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976129 : List Nat := [1, 2, 4, 1, 1, 4, 1, 4, 4]
def baseStart_976129 : Nat := 118140960795 + 976129 * 2 ^ 59
def prefixEnd_976129 : Nat := 4983230072969 + 3 ^ 40 * 976129 * 2
def baseEnd_976129 : Nat := 111382968398381472110749

theorem tailTrace_976129 : CollatzResearch.WordTrace tailWord_976129 prefixEnd_976129 111382968398381472110749 := by
  unfold tailWord_976129
  simp only [CollatzResearch.WordTrace]
  refine ⟨35602349480658817405883441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23734899653772544937255627 35602349480658817405883441)
  ·
    refine ⟨26701762110494113054412581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35602349480658817405883441 26701762110494113054412581)
    ·
      refine ⟨5006580395717646197702359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26701762110494113054412581 5006580395717646197702359)
      ·
        refine ⟨7509870593576469296553539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5006580395717646197702359 7509870593576469296553539)
        ·
          refine ⟨11264805890364703944830309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7509870593576469296553539 11264805890364703944830309)
          ·
            refine ⟨2112151104443381989655683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11264805890364703944830309 2112151104443381989655683)
            ·
              refine ⟨3168226656665072984483525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2112151104443381989655683 3168226656665072984483525)
              ·
                refine ⟨594042498124701184590661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3168226656665072984483525 594042498124701184590661)
                ·
                  refine ⟨111382968398381472110749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 594042498124701184590661 111382968398381472110749)
                  ·
                    rfl

theorem cell22_976129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 4, 4].length) (baseStart_976129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976129 prefixEnd_976129 := by exact prefixLift 976129
  have htrace : WordTrace (prefixWord ++ tailWord_976129) baseStart_976129 baseEnd_976129 := by
    simpa [prefixWord, tailWord_976129, baseEnd_976129] using wordTrace_append hprefix tailTrace_976129
  have hstable : (prefixWord ++ tailWord_976129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976129).length < 2 ^ (prefixWord ++ tailWord_976129).sum := by decide
  have hdescent : baseEnd_976129 < baseStart_976129 := by decide
  rcases family_descends (prefixWord ++ tailWord_976129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976146 : List Nat := [3, 2, 4, 2, 1, 1, 1, 2, 6]
def baseStart_976146 : Nat := 118140960795 + 976146 * 2 ^ 59
def prefixEnd_976146 : Nat := 4983230072969 + 3 ^ 40 * 976146 * 2
def baseEnd_976146 : Nat := 111384908214187346219065

theorem tailTrace_976146 : CollatzResearch.WordTrace tailWord_976146 prefixEnd_976146 111384908214187346219065 := by
  unfold tailWord_976146
  simp only [CollatzResearch.WordTrace]
  refine ⟨8900742380399307327313073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23735313014398152872834861 8900742380399307327313073)
  ·
    refine ⟨6675556785299480495484805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8900742380399307327313073 6675556785299480495484805)
    ·
      refine ⟨1251666897243652592903401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6675556785299480495484805 1251666897243652592903401)
      ·
        refine ⟨938750172932739444677551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1251666897243652592903401 938750172932739444677551)
        ·
          refine ⟨1408125259399109167016327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 938750172932739444677551 1408125259399109167016327)
          ·
            refine ⟨2112187889098663750524491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1408125259399109167016327 2112187889098663750524491)
            ·
              refine ⟨3168281833647995625786737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2112187889098663750524491 3168281833647995625786737)
              ·
                refine ⟨2376211375235996719340053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3168281833647995625786737 2376211375235996719340053)
                ·
                  refine ⟨111384908214187346219065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2376211375235996719340053 111384908214187346219065)
                  ·
                    rfl

theorem cell22_976146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_976146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976146 prefixEnd_976146 := by exact prefixLift 976146
  have htrace : WordTrace (prefixWord ++ tailWord_976146) baseStart_976146 baseEnd_976146 := by
    simpa [prefixWord, tailWord_976146, baseEnd_976146] using wordTrace_append hprefix tailTrace_976146
  have hstable : (prefixWord ++ tailWord_976146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976146).length < 2 ^ (prefixWord ++ tailWord_976146).sum := by decide
  have hdescent : baseEnd_976146 < baseStart_976146 := by decide
  rcases family_descends (prefixWord ++ tailWord_976146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976172 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 7, 3]
def baseStart_976172 : Nat := 118140960795 + 976172 * 2 ^ 59
def prefixEnd_976172 : Nat := 4983230072969 + 3 ^ 40 * 976172 * 2
def baseEnd_976172 : Nat := 334163624973906637507115

theorem tailTrace_976172 : CollatzResearch.WordTrace tailWord_976172 prefixEnd_976172 334163624973906637507115 := by
  unfold tailWord_976172
  simp only [CollatzResearch.WordTrace]
  refine ⟨17801958909751517874849385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23735945213002023833132513 17801958909751517874849385)
  ·
    refine ⟨13351469182313638406137039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17801958909751517874849385 13351469182313638406137039)
    ·
      refine ⟨20027203773470457609205559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13351469182313638406137039 20027203773470457609205559)
      ·
        refine ⟨30040805660205686413808339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20027203773470457609205559 30040805660205686413808339)
        ·
          refine ⟨45061208490308529620712509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30040805660205686413808339 45061208490308529620712509)
          ·
            refine ⟨16897953183865698607767191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45061208490308529620712509 16897953183865698607767191)
            ·
              refine ⟨25346929775798547911650787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16897953183865698607767191 25346929775798547911650787)
              ·
                refine ⟨38020394663697821867476181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25346929775798547911650787 38020394663697821867476181)
                ·
                  refine ⟨891102999930417700018973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 38020394663697821867476181 891102999930417700018973)
                  ·
                    refine ⟨334163624973906637507115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 891102999930417700018973 334163624973906637507115)
                    ·
                      rfl

theorem cell22_976172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 3].length) (baseStart_976172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976172 prefixEnd_976172 := by exact prefixLift 976172
  have htrace : WordTrace (prefixWord ++ tailWord_976172) baseStart_976172 baseEnd_976172 := by
    simpa [prefixWord, tailWord_976172, baseEnd_976172] using wordTrace_append hprefix tailTrace_976172
  have hstable : (prefixWord ++ tailWord_976172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976172).length < 2 ^ (prefixWord ++ tailWord_976172).sum := by decide
  have hdescent : baseEnd_976172 < baseStart_976172 := by decide
  rcases family_descends (prefixWord ++ tailWord_976172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976202 : List Nat := [3, 1, 2, 1, 1, 1, 1, 7, 5]
def baseStart_976202 : Nat := 118140960795 + 976202 * 2 ^ 59
def prefixEnd_976202 : Nat := 4983230072969 + 3 ^ 40 * 976202 * 2
def baseEnd_976202 : Nat := 111391298195665519752341

theorem tailTrace_976202 : CollatzResearch.WordTrace tailWord_976202 prefixEnd_976202 111391298195665519752341 := by
  unfold tailWord_976202
  simp only [CollatzResearch.WordTrace]
  refine ⟨8901253002348587718322715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23736674672929567248860573 8901253002348587718322715)
  ·
    refine ⟨13351879503522881577484073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8901253002348587718322715 13351879503522881577484073)
    ·
      refine ⟨10013909627642161183113055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13351879503522881577484073 10013909627642161183113055)
      ·
        refine ⟨15020864441463241774669583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10013909627642161183113055 15020864441463241774669583)
        ·
          refine ⟨22531296662194862662004375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15020864441463241774669583 22531296662194862662004375)
          ·
            refine ⟨33796944993292293993006563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22531296662194862662004375 33796944993292293993006563)
            ·
              refine ⟨50695417489938440989509845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33796944993292293993006563 50695417489938440989509845)
              ·
                refine ⟨1188173847420432210691637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 50695417489938440989509845 1188173847420432210691637)
                ·
                  refine ⟨111391298195665519752341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1188173847420432210691637 111391298195665519752341)
                  ·
                    rfl

theorem cell22_976202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 5].length) (baseStart_976202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976202 prefixEnd_976202 := by exact prefixLift 976202
  have htrace : WordTrace (prefixWord ++ tailWord_976202) baseStart_976202 baseEnd_976202 := by
    simpa [prefixWord, tailWord_976202, baseEnd_976202] using wordTrace_append hprefix tailTrace_976202
  have hstable : (prefixWord ++ tailWord_976202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976202).length < 2 ^ (prefixWord ++ tailWord_976202).sum := by decide
  have hdescent : baseEnd_976202 < baseStart_976202 := by decide
  rcases family_descends (prefixWord ++ tailWord_976202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976214 : List Nat := [5, 2, 3, 1, 2, 1, 1, 3, 4]
def baseStart_976214 : Nat := 118140960795 + 976214 * 2 ^ 59
def prefixEnd_976214 : Nat := 4983230072969 + 3 ^ 40 * 976214 * 2
def baseEnd_976214 : Nat := 111392667477410842652329

theorem tailTrace_976214 : CollatzResearch.WordTrace tailWord_976214 prefixEnd_976214 111392667477410842652329 := by
  unfold tailWord_976214
  simp only [CollatzResearch.WordTrace]
  refine ⟨2225340605334429807670481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23736966456900584615151797 2225340605334429807670481)
  ·
    refine ⟨1669005454000822355752861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2225340605334429807670481 1669005454000822355752861)
    ·
      refine ⟨625877045250308383407323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1669005454000822355752861 625877045250308383407323)
      ·
        refine ⟨938815567875462575110985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625877045250308383407323 938815567875462575110985)
        ·
          refine ⟨704111675906596931333239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 938815567875462575110985 704111675906596931333239)
          ·
            refine ⟨1056167513859895396999859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704111675906596931333239 1056167513859895396999859)
            ·
              refine ⟨1584251270789843095499789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1056167513859895396999859 1584251270789843095499789)
              ·
                refine ⟨594094226546191160812421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1584251270789843095499789 594094226546191160812421)
                ·
                  refine ⟨111392667477410842652329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 594094226546191160812421 111392667477410842652329)
                  ·
                    rfl

theorem cell22_976214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_976214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976214 prefixEnd_976214 := by exact prefixLift 976214
  have htrace : WordTrace (prefixWord ++ tailWord_976214) baseStart_976214 baseEnd_976214 := by
    simpa [prefixWord, tailWord_976214, baseEnd_976214] using wordTrace_append hprefix tailTrace_976214
  have hstable : (prefixWord ++ tailWord_976214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976214).length < 2 ^ (prefixWord ++ tailWord_976214).sum := by decide
  have hdescent : baseEnd_976214 < baseStart_976214 := by decide
  rcases family_descends (prefixWord ++ tailWord_976214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976277 : List Nat := [1, 3, 2, 1, 1, 2, 2, 3, 1, 6]
def baseStart_976277 : Nat := 118140960795 + 976277 * 2 ^ 59
def prefixEnd_976277 : Nat := 4983230072969 + 3 ^ 40 * 976277 * 2
def baseEnd_976277 : Nat := 334199568619721363631793

theorem tailTrace_976277 : CollatzResearch.WordTrace tailWord_976277 prefixEnd_976277 334199568619721363631793 := by
  unfold tailWord_976277
  simp only [CollatzResearch.WordTrace]
  refine ⟨35607747484122638682271085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23738498322748425788180723 35607747484122638682271085)
  ·
    refine ⟨13352905306545989505851657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35607747484122638682271085 13352905306545989505851657)
    ·
      refine ⟨10014678979909492129388743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13352905306545989505851657 10014678979909492129388743)
      ·
        refine ⟨15022018469864238194083115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10014678979909492129388743 15022018469864238194083115)
        ·
          refine ⟨22533027704796357291124673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15022018469864238194083115 22533027704796357291124673)
          ·
            refine ⟨16899770778597267968343505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22533027704796357291124673 16899770778597267968343505)
            ·
              refine ⟨12674828083947950976257629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16899770778597267968343505 12674828083947950976257629)
              ·
                refine ⟨4753060531480481616096611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12674828083947950976257629 4753060531480481616096611)
                ·
                  refine ⟨7129590797220722424144917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4753060531480481616096611 7129590797220722424144917)
                  ·
                    refine ⟨334199568619721363631793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7129590797220722424144917 334199568619721363631793)
                    ·
                      rfl

theorem cell22_976277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_976277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976277 prefixEnd_976277 := by exact prefixLift 976277
  have htrace : WordTrace (prefixWord ++ tailWord_976277) baseStart_976277 baseEnd_976277 := by
    simpa [prefixWord, tailWord_976277, baseEnd_976277] using wordTrace_append hprefix tailTrace_976277
  have hstable : (prefixWord ++ tailWord_976277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976277).length < 2 ^ (prefixWord ++ tailWord_976277).sum := by decide
  have hdescent : baseEnd_976277 < baseStart_976277 := by decide
  rcases family_descends (prefixWord ++ tailWord_976277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976309 : List Nat := [1, 3, 3, 2, 2, 1, 3, 7]
def baseStart_976309 : Nat := 118140960795 + 976309 * 2 ^ 59
def prefixEnd_976309 : Nat := 4983230072969 + 3 ^ 40 * 976309 * 2
def baseEnd_976309 : Nat := 37134502541520438536855

theorem tailTrace_976309 : CollatzResearch.WordTrace tailWord_976309 prefixEnd_976309 37134502541520438536855 := by
  unfold tailWord_976309
  simp only [CollatzResearch.WordTrace]
  refine ⟨35608914620006708147435981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23739276413337805431623987 35608914620006708147435981)
  ·
    refine ⟨13353342982502515555288493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35608914620006708147435981 13353342982502515555288493)
    ·
      refine ⟨5007503618438443333233185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13353342982502515555288493 5007503618438443333233185)
      ·
        refine ⟨3755627713828832499924889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5007503618438443333233185 3755627713828832499924889)
        ·
          refine ⟨2816720785371624374943667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3755627713828832499924889 2816720785371624374943667)
          ·
            refine ⟨4225081178057436562415501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2816720785371624374943667 4225081178057436562415501)
            ·
              refine ⟨1584405441771538710905813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4225081178057436562415501 1584405441771538710905813)
              ·
                refine ⟨37134502541520438536855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1584405441771538710905813 37134502541520438536855)
                ·
                  rfl

theorem cell22_976309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 7].length) (baseStart_976309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976309 prefixEnd_976309 := by exact prefixLift 976309
  have htrace : WordTrace (prefixWord ++ tailWord_976309) baseStart_976309 baseEnd_976309 := by
    simpa [prefixWord, tailWord_976309, baseEnd_976309] using wordTrace_append hprefix tailTrace_976309
  have hstable : (prefixWord ++ tailWord_976309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976309).length < 2 ^ (prefixWord ++ tailWord_976309).sum := by decide
  have hdescent : baseEnd_976309 < baseStart_976309 := by decide
  rcases family_descends (prefixWord ++ tailWord_976309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976369 : List Nat := [1, 2, 2, 2, 3, 2, 2, 1, 2, 5]
def baseStart_976369 : Nat := 118140960795 + 976369 * 2 ^ 59
def prefixEnd_976369 : Nat := 4983230072969 + 3 ^ 40 * 976369 * 2
def baseEnd_976369 : Nat := 334231062099863790331511

theorem tailTrace_976369 : CollatzResearch.WordTrace tailWord_976369 prefixEnd_976369 334231062099863790331511 := by
  unfold tailWord_976369
  simp only [CollatzResearch.WordTrace]
  refine ⟨35611102999789338394620161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23740735333192892263080107 35611102999789338394620161)
  ·
    refine ⟨26708327249842003795965121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35611102999789338394620161 26708327249842003795965121)
    ·
      refine ⟨20031245437381502846973841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26708327249842003795965121 20031245437381502846973841)
      ·
        refine ⟨15023434078036127135230381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20031245437381502846973841 15023434078036127135230381)
        ·
          refine ⟨5633787779263547675711393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15023434078036127135230381 5633787779263547675711393)
          ·
            refine ⟨4225340834447660756783545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5633787779263547675711393 4225340834447660756783545)
            ·
              refine ⟨3169005625835745567587659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4225340834447660756783545 3169005625835745567587659)
              ·
                refine ⟨4753508438753618351381489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3169005625835745567587659 4753508438753618351381489)
                ·
                  refine ⟨3565131329065213763536117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4753508438753618351381489 3565131329065213763536117)
                  ·
                    refine ⟨334231062099863790331511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3565131329065213763536117 334231062099863790331511)
                    ·
                      rfl

theorem cell22_976369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_976369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976369 prefixEnd_976369 := by exact prefixLift 976369
  have htrace : WordTrace (prefixWord ++ tailWord_976369) baseStart_976369 baseEnd_976369 := by
    simpa [prefixWord, tailWord_976369, baseEnd_976369] using wordTrace_append hprefix tailTrace_976369
  have hstable : (prefixWord ++ tailWord_976369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976369).length < 2 ^ (prefixWord ++ tailWord_976369).sum := by decide
  have hdescent : baseEnd_976369 < baseStart_976369 := by decide
  rcases family_descends (prefixWord ++ tailWord_976369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976416 : List Nat := [2, 1, 1, 6, 1, 1, 3, 1, 6]
def baseStart_976416 : Nat := 118140960795 + 976416 * 2 ^ 59
def prefixEnd_976416 : Nat := 4983230072969 + 3 ^ 40 * 976416 * 2
def baseEnd_976416 : Nat := 111415717053457111468789

theorem tailTrace_976416 : CollatzResearch.WordTrace tailWord_976416 prefixEnd_976416 111415717053457111468789 := by
  unfold tailWord_976416
  simp only [CollatzResearch.WordTrace]
  refine ⟨17806408615309532710790551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23741878153746043614387401 17806408615309532710790551)
  ·
    refine ⟨26709612922964299066185827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17806408615309532710790551 26709612922964299066185827)
    ·
      refine ⟨40064419384446448599278741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26709612922964299066185827 40064419384446448599278741)
      ·
        refine ⟨1878019658645927278091191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40064419384446448599278741 1878019658645927278091191)
        ·
          refine ⟨2817029487968890917136787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1878019658645927278091191 2817029487968890917136787)
          ·
            refine ⟨4225544231953336375705181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2817029487968890917136787 4225544231953336375705181)
            ·
              refine ⟨1584579086982501140889443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4225544231953336375705181 1584579086982501140889443)
              ·
                refine ⟨2376868630473751711334165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1584579086982501140889443 2376868630473751711334165)
                ·
                  refine ⟨111415717053457111468789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2376868630473751711334165 111415717053457111468789)
                  ·
                    rfl

theorem cell22_976416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 6].length) (baseStart_976416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976416 prefixEnd_976416 := by exact prefixLift 976416
  have htrace : WordTrace (prefixWord ++ tailWord_976416) baseStart_976416 baseEnd_976416 := by
    simpa [prefixWord, tailWord_976416, baseEnd_976416] using wordTrace_append hprefix tailTrace_976416
  have hstable : (prefixWord ++ tailWord_976416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976416).length < 2 ^ (prefixWord ++ tailWord_976416).sum := by decide
  have hdescent : baseEnd_976416 < baseStart_976416 := by decide
  rcases family_descends (prefixWord ++ tailWord_976416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976461 : List Nat := [1, 6, 1, 1, 3, 10]
def baseStart_976461 : Nat := 118140960795 + 976461 * 2 ^ 59
def prefixEnd_976461 : Nat := 4983230072969 + 3 ^ 40 * 976461 * 2
def baseEnd_976461 : Nat := 4126698217037113790509

theorem tailTrace_976461 : CollatzResearch.WordTrace tailWord_976461 prefixEnd_976461 4126698217037113790509 := by
  unfold tailWord_976461
  simp only [CollatzResearch.WordTrace]
  refine ⟨35614458515456038106969237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23742972343637358737979491 35614458515456038106969237)
  ·
    refine ⟨1669427742912001786264183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35614458515456038106969237 1669427742912001786264183)
    ·
      refine ⟨2504141614368002679396275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1669427742912001786264183 2504141614368002679396275)
      ·
        refine ⟨3756212421552004019094413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2504141614368002679396275 3756212421552004019094413)
        ·
          refine ⟨1408579658082001507160405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3756212421552004019094413 1408579658082001507160405)
          ·
            refine ⟨4126698217037113790509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1408579658082001507160405 4126698217037113790509)
            ·
              rfl

theorem cell22_976461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 10].length) (baseStart_976461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976461 prefixEnd_976461 := by exact prefixLift 976461
  have htrace : WordTrace (prefixWord ++ tailWord_976461) baseStart_976461 baseEnd_976461 := by
    simpa [prefixWord, tailWord_976461, baseEnd_976461] using wordTrace_append hprefix tailTrace_976461
  have hstable : (prefixWord ++ tailWord_976461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976461).length < 2 ^ (prefixWord ++ tailWord_976461).sum := by decide
  have hdescent : baseEnd_976461 < baseStart_976461 := by decide
  rcases family_descends (prefixWord ++ tailWord_976461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976504 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 6, 5]
def baseStart_976504 : Nat := 118140960795 + 976504 * 2 ^ 59
def prefixEnd_976504 : Nat := 4983230072969 + 3 ^ 40 * 976504 * 2
def baseEnd_976504 : Nat := 334277275358768438206097

theorem tailTrace_976504 : CollatzResearch.WordTrace tailWord_976504 prefixEnd_976504 334277275358768438206097 := by
  unfold tailWord_976504
  simp only [CollatzResearch.WordTrace]
  refine ⟨17808013427150128225392283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23744017902866837633856377 17808013427150128225392283)
  ·
    refine ⟨26712020140725192338088425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17808013427150128225392283 26712020140725192338088425)
    ·
      refine ⟨20034015105543894253566319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26712020140725192338088425 20034015105543894253566319)
      ·
        refine ⟨30051022658315841380349479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20034015105543894253566319 30051022658315841380349479)
        ·
          refine ⟨45076533987473762070524219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30051022658315841380349479 45076533987473762070524219)
          ·
            refine ⟨67614800981210643105786329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45076533987473762070524219 67614800981210643105786329)
            ·
              refine ⟨50711100735907982329339747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67614800981210643105786329 50711100735907982329339747)
              ·
                refine ⟨76066651103861973494009621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50711100735907982329339747 76066651103861973494009621)
                ·
                  refine ⟨3565624270493530007531701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76066651103861973494009621 3565624270493530007531701)
                  ·
                    refine ⟨334277275358768438206097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3565624270493530007531701 334277275358768438206097)
                    ·
                      rfl

theorem cell22_976504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_976504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976504 prefixEnd_976504 := by exact prefixLift 976504
  have htrace : WordTrace (prefixWord ++ tailWord_976504) baseStart_976504 baseEnd_976504 := by
    simpa [prefixWord, tailWord_976504, baseEnd_976504] using wordTrace_append hprefix tailTrace_976504
  have hstable : (prefixWord ++ tailWord_976504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976504).length < 2 ^ (prefixWord ++ tailWord_976504).sum := by decide
  have hdescent : baseEnd_976504 < baseStart_976504 := by decide
  rcases family_descends (prefixWord ++ tailWord_976504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976540 : List Nat := [2, 2, 3, 2, 3, 1, 3, 1, 5]
def baseStart_976540 : Nat := 118140960795 + 976540 * 2 ^ 59
def prefixEnd_976540 : Nat := 4983230072969 + 3 ^ 40 * 976540 * 2
def baseEnd_976540 : Nat := 111429866298158781435329

theorem tailTrace_976540 : CollatzResearch.WordTrace tailWord_976540 prefixEnd_976540 111429866298158781435329 := by
  unfold tailWord_976540
  simp only [CollatzResearch.WordTrace]
  refine ⟨17808669941084917299547537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23744893254779889732730049 17808669941084917299547537)
  ·
    refine ⟨13356502455813687974660653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17808669941084917299547537 13356502455813687974660653)
    ·
      refine ⟨5008688420930132990497745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13356502455813687974660653 5008688420930132990497745)
      ·
        refine ⟨3756516315697599742873309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5008688420930132990497745 3756516315697599742873309)
        ·
          refine ⟨1408693618386599903577491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3756516315697599742873309 1408693618386599903577491)
          ·
            refine ⟨2113040427579899855366237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1408693618386599903577491 2113040427579899855366237)
            ·
              refine ⟨792390160342462445762339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2113040427579899855366237 792390160342462445762339)
              ·
                refine ⟨1188585240513693668643509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 792390160342462445762339 1188585240513693668643509)
                ·
                  refine ⟨111429866298158781435329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1188585240513693668643509 111429866298158781435329)
                  ·
                    rfl

theorem cell22_976540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 5].length) (baseStart_976540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976540 prefixEnd_976540 := by exact prefixLift 976540
  have htrace : WordTrace (prefixWord ++ tailWord_976540) baseStart_976540 baseEnd_976540 := by
    simpa [prefixWord, tailWord_976540, baseEnd_976540] using wordTrace_append hprefix tailTrace_976540
  have hstable : (prefixWord ++ tailWord_976540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976540).length < 2 ^ (prefixWord ++ tailWord_976540).sum := by decide
  have hdescent : baseEnd_976540 < baseStart_976540 := by decide
  rcases family_descends (prefixWord ++ tailWord_976540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976578 : List Nat := [3, 5, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_976578 : Nat := 118140960795 + 976578 * 2 ^ 59
def prefixEnd_976578 : Nat := 4983230072969 + 3 ^ 40 * 976578 * 2
def baseEnd_976578 : Nat := 334302607071056911855871

theorem tailTrace_976578 : CollatzResearch.WordTrace tailWord_976578 prefixEnd_976578 334302607071056911855871 := by
  unfold tailWord_976578
  simp only [CollatzResearch.WordTrace]
  refine ⟨8904681464008041772244597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23745817237354778059318925 8904681464008041772244597)
  ·
    refine ⟨834813887250753916147931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8904681464008041772244597 834813887250753916147931)
    ·
      refine ⟨1252220830876130874221897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 834813887250753916147931 1252220830876130874221897)
      ·
        refine ⟨939165623157098155666423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1252220830876130874221897 939165623157098155666423)
        ·
          refine ⟨1408748434735647233499635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939165623157098155666423 1408748434735647233499635)
          ·
            refine ⟨2113122652103470850249453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1408748434735647233499635 2113122652103470850249453)
            ·
              refine ⟨792420994538801568843545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2113122652103470850249453 792420994538801568843545)
              ·
                refine ⟨594315745904101176632659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 792420994538801568843545 594315745904101176632659)
                ·
                  refine ⟨891473618856151764948989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 594315745904101176632659 891473618856151764948989)
                  ·
                    refine ⟨334302607071056911855871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 891473618856151764948989 334302607071056911855871)
                    ·
                      rfl

theorem cell22_976578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_976578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976578 prefixEnd_976578 := by exact prefixLift 976578
  have htrace : WordTrace (prefixWord ++ tailWord_976578) baseStart_976578 baseEnd_976578 := by
    simpa [prefixWord, tailWord_976578, baseEnd_976578] using wordTrace_append hprefix tailTrace_976578
  have hstable : (prefixWord ++ tailWord_976578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976578).length < 2 ^ (prefixWord ++ tailWord_976578).sum := by decide
  have hdescent : baseEnd_976578 < baseStart_976578 := by decide
  rcases family_descends (prefixWord ++ tailWord_976578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976581 : List Nat := [1, 3, 1, 1, 1, 1, 2, 6, 2, 4]
def baseStart_976581 : Nat := 118140960795 + 976581 * 2 ^ 59
def prefixEnd_976581 : Nat := 4983230072969 + 3 ^ 40 * 976581 * 2
def baseEnd_976581 : Nat := 334303634032365904030861

theorem tailTrace_976581 : CollatzResearch.WordTrace tailWord_976581 prefixEnd_976581 334303634032365904030861 := by
  unfold tailWord_976581
  simp only [CollatzResearch.WordTrace]
  refine ⟨35618835275021298601337597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23745890183347532400891731 35618835275021298601337597)
  ·
    refine ⟨13357063228132986975501599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35618835275021298601337597 13357063228132986975501599)
    ·
      refine ⟨20035594842199480463252399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13357063228132986975501599 20035594842199480463252399)
      ·
        refine ⟨30053392263299220694878599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20035594842199480463252399 30053392263299220694878599)
        ·
          refine ⟨45080088394948831042317899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30053392263299220694878599 45080088394948831042317899)
          ·
            refine ⟨67620132592423246563476849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45080088394948831042317899 67620132592423246563476849)
            ·
              refine ⟨50715099444317434922607637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67620132592423246563476849 50715099444317434922607637)
              ·
                refine ⟨2377270286452379761997233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50715099444317434922607637 2377270286452379761997233)
                ·
                  refine ⟨1782952714839284821497925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2377270286452379761997233 1782952714839284821497925)
                  ·
                    refine ⟨334303634032365904030861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1782952714839284821497925 334303634032365904030861)
                    ·
                      rfl

theorem cell22_976581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_976581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976581 prefixEnd_976581 := by exact prefixLift 976581
  have htrace : WordTrace (prefixWord ++ tailWord_976581) baseStart_976581 baseEnd_976581 := by
    simpa [prefixWord, tailWord_976581, baseEnd_976581] using wordTrace_append hprefix tailTrace_976581
  have hstable : (prefixWord ++ tailWord_976581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976581).length < 2 ^ (prefixWord ++ tailWord_976581).sum := by decide
  have hdescent : baseEnd_976581 < baseStart_976581 := by decide
  rcases family_descends (prefixWord ++ tailWord_976581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976583 : List Nat := [1, 1, 4, 1, 1, 1, 4, 4, 2, 3]
def baseStart_976583 : Nat := 118140960795 + 976583 * 2 ^ 59
def prefixEnd_976583 : Nat := 4983230072969 + 3 ^ 40 * 976583 * 2
def baseEnd_976583 : Nat := 334304318673238565480855

theorem tailTrace_976583 : CollatzResearch.WordTrace tailWord_976583 prefixEnd_976583 334304318673238565480855 := by
  unfold tailWord_976583
  simp only [CollatzResearch.WordTrace]
  refine ⟨35618908221014052942910403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23745938814009368628606935 35618908221014052942910403)
  ·
    refine ⟨53428362331521079414365605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35618908221014052942910403 53428362331521079414365605)
    ·
      refine ⟨10017817937160202390193551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53428362331521079414365605 10017817937160202390193551)
      ·
        refine ⟨15026726905740303585290327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10017817937160202390193551 15026726905740303585290327)
        ·
          refine ⟨22540090358610455377935491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15026726905740303585290327 22540090358610455377935491)
          ·
            refine ⟨33810135537915683066903237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22540090358610455377935491 33810135537915683066903237)
            ·
              refine ⟨6339400413359190575044357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33810135537915683066903237 6339400413359190575044357)
              ·
                refine ⟨1188637577504848232820817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6339400413359190575044357 1188637577504848232820817)
                ·
                  refine ⟨891478183128636174615613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1188637577504848232820817 891478183128636174615613)
                  ·
                    refine ⟨334304318673238565480855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 891478183128636174615613 334304318673238565480855)
                    ·
                      rfl

theorem cell22_976583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_976583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976583 prefixEnd_976583 := by exact prefixLift 976583
  have htrace : WordTrace (prefixWord ++ tailWord_976583) baseStart_976583 baseEnd_976583 := by
    simpa [prefixWord, tailWord_976583, baseEnd_976583] using wordTrace_append hprefix tailTrace_976583
  have hstable : (prefixWord ++ tailWord_976583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976583).length < 2 ^ (prefixWord ++ tailWord_976583).sum := by decide
  have hdescent : baseEnd_976583 < baseStart_976583 := by decide
  rcases family_descends (prefixWord ++ tailWord_976583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976604 : List Nat := [2, 2, 5, 1, 3, 1, 1, 2, 1, 4]
def baseStart_976604 : Nat := 118140960795 + 976604 * 2 ^ 59
def prefixEnd_976604 : Nat := 4983230072969 + 3 ^ 40 * 976604 * 2
def baseEnd_976604 : Nat := 334311507402401510705791

theorem tailTrace_976604 : CollatzResearch.WordTrace tailWord_976604 prefixEnd_976604 334311507402401510705791 := by
  unfold tailWord_976604
  simp only [CollatzResearch.WordTrace]
  refine ⟨17809837076968986764712433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23746449435958649019616577 17809837076968986764712433)
  ·
    refine ⟨13357377807726740073534325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17809837076968986764712433 13357377807726740073534325)
    ·
      refine ⟨1252254169474381881893843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13357377807726740073534325 1252254169474381881893843)
      ·
        refine ⟨1878381254211572822840765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1252254169474381881893843 1878381254211572822840765)
        ·
          refine ⟨704392970329339808565287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1878381254211572822840765 704392970329339808565287)
          ·
            refine ⟨1056589455494009712847931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704392970329339808565287 1056589455494009712847931)
            ·
              refine ⟨1584884183241014569271897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1056589455494009712847931 1584884183241014569271897)
              ·
                refine ⟨1188663137430760926953923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1584884183241014569271897 1188663137430760926953923)
                ·
                  refine ⟨1782994706146141390430885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1188663137430760926953923 1782994706146141390430885)
                  ·
                    refine ⟨334311507402401510705791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1782994706146141390430885 334311507402401510705791)
                    ·
                      rfl

theorem cell22_976604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_976604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976604 prefixEnd_976604 := by exact prefixLift 976604
  have htrace : WordTrace (prefixWord ++ tailWord_976604) baseStart_976604 baseEnd_976604 := by
    simpa [prefixWord, tailWord_976604, baseEnd_976604] using wordTrace_append hprefix tailTrace_976604
  have hstable : (prefixWord ++ tailWord_976604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976604).length < 2 ^ (prefixWord ++ tailWord_976604).sum := by decide
  have hdescent : baseEnd_976604 < baseStart_976604 := by decide
  rcases family_descends (prefixWord ++ tailWord_976604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976641 : List Nat := [1, 2, 4, 1, 1, 1, 2, 3, 7]
def baseStart_976641 : Nat := 118140960795 + 976641 * 2 ^ 59
def prefixEnd_976641 : Nat := 4983230072969 + 3 ^ 40 * 976641 * 2
def baseEnd_976641 : Nat := 111441391086181915843559

theorem tailTrace_976641 : CollatzResearch.WordTrace tailWord_976641 prefixEnd_976641 111441391086181915843559 := by
  unfold tailWord_976641
  simp only [CollatzResearch.WordTrace]
  refine ⟨35621023654803928848521777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23747349103202619232347851 35621023654803928848521777)
  ·
    refine ⟨26715767741102946636391333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35621023654803928848521777 26715767741102946636391333)
    ·
      refine ⟨5009206451456802494323375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26715767741102946636391333 5009206451456802494323375)
      ·
        refine ⟨7513809677185203741485063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5009206451456802494323375 7513809677185203741485063)
        ·
          refine ⟨11270714515777805612227595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7513809677185203741485063 11270714515777805612227595)
          ·
            refine ⟨16906071773666708418341393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11270714515777805612227595 16906071773666708418341393)
            ·
              refine ⟨12679553830250031313756045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16906071773666708418341393 12679553830250031313756045)
              ·
                refine ⟨4754832686343761742658517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12679553830250031313756045 4754832686343761742658517)
                ·
                  refine ⟨111441391086181915843559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4754832686343761742658517 111441391086181915843559)
                  ·
                    rfl

theorem cell22_976641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 7].length) (baseStart_976641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976641 prefixEnd_976641 := by exact prefixLift 976641
  have htrace : WordTrace (prefixWord ++ tailWord_976641) baseStart_976641 baseEnd_976641 := by
    simpa [prefixWord, tailWord_976641, baseEnd_976641] using wordTrace_append hprefix tailTrace_976641
  have hstable : (prefixWord ++ tailWord_976641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976641).length < 2 ^ (prefixWord ++ tailWord_976641).sum := by decide
  have hdescent : baseEnd_976641 < baseStart_976641 := by decide
  rcases family_descends (prefixWord ++ tailWord_976641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976692 : List Nat := [2, 5, 1, 1, 2, 3, 1, 2, 5]
def baseStart_976692 : Nat := 118140960795 + 976692 * 2 ^ 59
def prefixEnd_976692 : Nat := 4983230072969 + 3 ^ 40 * 976692 * 2
def baseEnd_976692 : Nat := 111447210533599538168507

theorem tailTrace_976692 : CollatzResearch.WordTrace tailWord_976692 prefixEnd_976692 111447210533599538168507 := by
  unfold tailWord_976692
  simp only [CollatzResearch.WordTrace]
  refine ⟨17811441888809582279314165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23748589185079443039085553 17811441888809582279314165)
  ·
    refine ⟨1669822677075898338685703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17811441888809582279314165 1669822677075898338685703)
    ·
      refine ⟨2504734015613847508028555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1669822677075898338685703 2504734015613847508028555)
      ·
        refine ⟨3757101023420771262042833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2504734015613847508028555 3757101023420771262042833)
        ·
          refine ⟨2817825767565578446532125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3757101023420771262042833 2817825767565578446532125)
          ·
            refine ⟨1056684662837091917449547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2817825767565578446532125 1056684662837091917449547)
            ·
              refine ⟨1585026994255637876174321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1056684662837091917449547 1585026994255637876174321)
              ·
                refine ⟨1188770245691728407130741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1585026994255637876174321 1188770245691728407130741)
                ·
                  refine ⟨111447210533599538168507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1188770245691728407130741 111447210533599538168507)
                  ·
                    rfl

theorem cell22_976692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_976692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976692 prefixEnd_976692 := by exact prefixLift 976692
  have htrace : WordTrace (prefixWord ++ tailWord_976692) baseStart_976692 baseEnd_976692 := by
    simpa [prefixWord, tailWord_976692, baseEnd_976692] using wordTrace_append hprefix tailTrace_976692
  have hstable : (prefixWord ++ tailWord_976692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976692).length < 2 ^ (prefixWord ++ tailWord_976692).sum := by decide
  have hdescent : baseEnd_976692 < baseStart_976692 := by decide
  rcases family_descends (prefixWord ++ tailWord_976692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976748 : List Nat := [2, 2, 1, 1, 4, 4, 8]
def baseStart_976748 : Nat := 118140960795 + 976748 * 2 ^ 59
def prefixEnd_976748 : Nat := 4983230072969 + 3 ^ 40 * 976748 * 2
def baseEnd_976748 : Nat := 12383733390564190189087

theorem tailTrace_976748 : CollatzResearch.WordTrace tailWord_976748 prefixEnd_976748 12383733390564190189087 := by
  unfold tailWord_976748
  simp only [CollatzResearch.WordTrace]
  refine ⟨17812463132708143061333449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23749950843610857415111265 17812463132708143061333449)
  ·
    refine ⟨13359347349531107296000087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17812463132708143061333449 13359347349531107296000087)
    ·
      refine ⟨20039021024296660944000131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13359347349531107296000087 20039021024296660944000131)
      ·
        refine ⟨30058531536444991416000197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20039021024296660944000131 30058531536444991416000197)
        ·
          refine ⟨5635974663083435890500037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30058531536444991416000197 5635974663083435890500037)
          ·
            refine ⟨1056745249328144229468757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5635974663083435890500037 1056745249328144229468757)
            ·
              refine ⟨12383733390564190189087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1056745249328144229468757 12383733390564190189087)
              ·
                rfl

theorem cell22_976748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 8].length) (baseStart_976748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976748 prefixEnd_976748 := by exact prefixLift 976748
  have htrace : WordTrace (prefixWord ++ tailWord_976748) baseStart_976748 baseEnd_976748 := by
    simpa [prefixWord, tailWord_976748, baseEnd_976748] using wordTrace_append hprefix tailTrace_976748
  have hstable : (prefixWord ++ tailWord_976748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976748).length < 2 ^ (prefixWord ++ tailWord_976748).sum := by decide
  have hdescent : baseEnd_976748 < baseStart_976748 := by decide
  rcases family_descends (prefixWord ++ tailWord_976748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976750 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 4, 4]
def baseStart_976750 : Nat := 118140960795 + 976750 * 2 ^ 59
def prefixEnd_976750 : Nat := 4983230072969 + 3 ^ 40 * 976750 * 2
def baseEnd_976750 : Nat := 334361486186105796555343

theorem tailTrace_976750 : CollatzResearch.WordTrace tailWord_976750 prefixEnd_976750 334361486186105796555343 := by
  unfold tailWord_976750
  simp only [CollatzResearch.WordTrace]
  refine ⟨4453124901426130058029963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23749999474272693642826469 4453124901426130058029963)
  ·
    refine ⟨6679687352139195087044945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4453124901426130058029963 6679687352139195087044945)
    ·
      refine ⟨5009765514104396315283709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6679687352139195087044945 5009765514104396315283709)
      ·
        refine ⟨1878662067789148618231391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5009765514104396315283709 1878662067789148618231391)
        ·
          refine ⟨2817993101683722927347087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1878662067789148618231391 2817993101683722927347087)
          ·
            refine ⟨4226989652525584391020631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2817993101683722927347087 4226989652525584391020631)
            ·
              refine ⟨6340484478788376586530947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4226989652525584391020631 6340484478788376586530947)
              ·
                refine ⟨9510726718182564879796421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6340484478788376586530947 9510726718182564879796421)
                ·
                  refine ⟨1783261259659230914961829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9510726718182564879796421 1783261259659230914961829)
                  ·
                    refine ⟨334361486186105796555343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1783261259659230914961829 334361486186105796555343)
                    ·
                      rfl

theorem cell22_976750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_976750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976750 prefixEnd_976750 := by exact prefixLift 976750
  have htrace : WordTrace (prefixWord ++ tailWord_976750) baseStart_976750 baseEnd_976750 := by
    simpa [prefixWord, tailWord_976750, baseEnd_976750] using wordTrace_append hprefix tailTrace_976750
  have hstable : (prefixWord ++ tailWord_976750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976750).length < 2 ^ (prefixWord ++ tailWord_976750).sum := by decide
  have hdescent : baseEnd_976750 < baseStart_976750 := by decide
  rcases family_descends (prefixWord ++ tailWord_976750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976769 : List Nat := [1, 2, 4, 4, 1, 1, 1, 3, 2, 3]
def baseStart_976769 : Nat := 118140960795 + 976769 * 2 ^ 59
def prefixEnd_976769 : Nat := 4983230072969 + 3 ^ 40 * 976769 * 2
def baseEnd_976769 : Nat := 334367990274396080330285

theorem tailTrace_976769 : CollatzResearch.WordTrace tailWord_976769 prefixEnd_976769 334367990274396080330285 := by
  unfold tailWord_976769
  simp only [CollatzResearch.WordTrace]
  refine ⟨35625692198340206709181361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23750461465560137806120907 35625692198340206709181361)
  ·
    refine ⟨26719269148755155031886021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35625692198340206709181361 26719269148755155031886021)
    ·
      refine ⟨5009862965391591568478629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26719269148755155031886021 5009862965391591568478629)
      ·
        refine ⟨939349306010923419089743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5009862965391591568478629 939349306010923419089743)
        ·
          refine ⟨1409023959016385128634615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939349306010923419089743 1409023959016385128634615)
          ·
            refine ⟨2113535938524577692951923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409023959016385128634615 2113535938524577692951923)
            ·
              refine ⟨3170303907786866539427885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2113535938524577692951923 3170303907786866539427885)
              ·
                refine ⟨1188863965420074952285457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3170303907786866539427885 1188863965420074952285457)
                ·
                  refine ⟨891647974065056214214093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1188863965420074952285457 891647974065056214214093)
                  ·
                    refine ⟨334367990274396080330285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 891647974065056214214093 334367990274396080330285)
                    ·
                      rfl

theorem cell22_976769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_976769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976769 prefixEnd_976769 := by exact prefixLift 976769
  have htrace : WordTrace (prefixWord ++ tailWord_976769) baseStart_976769 baseEnd_976769 := by
    simpa [prefixWord, tailWord_976769, baseEnd_976769] using wordTrace_append hprefix tailTrace_976769
  have hstable : (prefixWord ++ tailWord_976769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976769).length < 2 ^ (prefixWord ++ tailWord_976769).sum := by decide
  have hdescent : baseEnd_976769 < baseStart_976769 := by decide
  rcases family_descends (prefixWord ++ tailWord_976769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976840 : List Nat := [2, 1, 3, 1, 4, 1, 2, 1, 3, 4]
def baseStart_976840 : Nat := 118140960795 + 976840 * 2 ^ 59
def prefixEnd_976840 : Nat := 4983230072969 + 3 ^ 40 * 976840 * 2
def baseEnd_976840 : Nat := 334392295025375561805067

theorem tailTrace_976840 : CollatzResearch.WordTrace tailWord_976840 prefixEnd_976840 334392295025375561805067 := by
  unfold tailWord_976840
  simp only [CollatzResearch.WordTrace]
  refine ⟨17814140890541492917507987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23752187854055323890010649 17814140890541492917507987)
  ·
    refine ⟨26721211335812239376261981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17814140890541492917507987 26721211335812239376261981)
    ·
      refine ⟨10020454250929589766098243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26721211335812239376261981 10020454250929589766098243)
      ·
        refine ⟨15030681376394384649147365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10020454250929589766098243 15030681376394384649147365)
        ·
          refine ⟨2818252758073947121715131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15030681376394384649147365 2818252758073947121715131)
          ·
            refine ⟨4227379137110920682572697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2818252758073947121715131 4227379137110920682572697)
            ·
              refine ⟨3170534352833190511929523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4227379137110920682572697 3170534352833190511929523)
              ·
                refine ⟨4755801529249785767894285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3170534352833190511929523 4755801529249785767894285)
                ·
                  refine ⟨1783425573468669662960357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4755801529249785767894285 1783425573468669662960357)
                  ·
                    refine ⟨334392295025375561805067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1783425573468669662960357 334392295025375561805067)
                    ·
                      rfl

theorem cell22_976840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_976840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976840 prefixEnd_976840 := by exact prefixLift 976840
  have htrace : WordTrace (prefixWord ++ tailWord_976840) baseStart_976840 baseEnd_976840 := by
    simpa [prefixWord, tailWord_976840, baseEnd_976840] using wordTrace_append hprefix tailTrace_976840
  have hstable : (prefixWord ++ tailWord_976840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976840).length < 2 ^ (prefixWord ++ tailWord_976840).sum := by decide
  have hdescent : baseEnd_976840 < baseStart_976840 := by decide
  rcases family_descends (prefixWord ++ tailWord_976840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976857 : List Nat := [1, 2, 1, 2, 6, 1, 1, 3, 1, 4]
def baseStart_976857 : Nat := 118140960795 + 976857 * 2 ^ 59
def prefixEnd_976857 : Nat := 4983230072969 + 3 ^ 40 * 976857 * 2
def baseEnd_976857 : Nat := 334398114472793184130015

theorem tailTrace_976857 : CollatzResearch.WordTrace tailWord_976857 prefixEnd_976857 334398114472793184130015 := by
  unfold tailWord_976857
  simp only [CollatzResearch.WordTrace]
  refine ⟨35628901822021397738384825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23752601214680931825589883 35628901822021397738384825)
  ·
    refine ⟨26721676366516048303788619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35628901822021397738384825 26721676366516048303788619)
    ·
      refine ⟨40082514549774072455682929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26721676366516048303788619 40082514549774072455682929)
      ·
        refine ⟨30061885912330554341762197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40082514549774072455682929 30061885912330554341762197)
        ·
          refine ⟨1409150902140494734770103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30061885912330554341762197 1409150902140494734770103)
          ·
            refine ⟨2113726353210742102155155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409150902140494734770103 2113726353210742102155155)
            ·
              refine ⟨3170589529816113153232733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2113726353210742102155155 3170589529816113153232733)
              ·
                refine ⟨1188971073681042432462275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3170589529816113153232733 1188971073681042432462275)
                ·
                  refine ⟨1783456610521563648693413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1188971073681042432462275 1783456610521563648693413)
                  ·
                    refine ⟨334398114472793184130015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1783456610521563648693413 334398114472793184130015)
                    ·
                      rfl

theorem cell22_976857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 4].length) (baseStart_976857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976857 prefixEnd_976857 := by exact prefixLift 976857
  have htrace : WordTrace (prefixWord ++ tailWord_976857) baseStart_976857 baseEnd_976857 := by
    simpa [prefixWord, tailWord_976857, baseEnd_976857] using wordTrace_append hprefix tailTrace_976857
  have hstable : (prefixWord ++ tailWord_976857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976857).length < 2 ^ (prefixWord ++ tailWord_976857).sum := by decide
  have hdescent : baseEnd_976857 < baseStart_976857 := by decide
  rcases family_descends (prefixWord ++ tailWord_976857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976906 : List Nat := [3, 1, 2, 2, 5, 1, 1, 3, 4]
def baseStart_976906 : Nat := 118140960795 + 976906 * 2 ^ 59
def prefixEnd_976906 : Nat := 4983230072969 + 3 ^ 40 * 976906 * 2
def baseEnd_976906 : Nat := 111471629391391129884955

theorem tailTrace_976906 : CollatzResearch.WordTrace tailWord_976906 prefixEnd_976906 111471629391391129884955 := by
  unfold tailWord_976906
  simp only [CollatzResearch.WordTrace]
  refine ⟨8907672249710969776729643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23753792665895919404612381 8907672249710969776729643)
  ·
    refine ⟨13361508374566454665094465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8907672249710969776729643 13361508374566454665094465)
    ·
      refine ⟨10021131280924840998820849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13361508374566454665094465 10021131280924840998820849)
      ·
        refine ⟨7515848460693630749115637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10021131280924840998820849 7515848460693630749115637)
        ·
          refine ⟨704610793190027882729591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7515848460693630749115637 704610793190027882729591)
          ·
            refine ⟨1056916189785041824094387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704610793190027882729591 1056916189785041824094387)
            ·
              refine ⟨1585374284677562736141581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1056916189785041824094387 1585374284677562736141581)
              ·
                refine ⟨594515356754086026053093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1585374284677562736141581 594515356754086026053093)
                ·
                  refine ⟨111471629391391129884955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 594515356754086026053093 111471629391391129884955)
                  ·
                    rfl

theorem cell22_976906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 3, 4].length) (baseStart_976906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976906 prefixEnd_976906 := by exact prefixLift 976906
  have htrace : WordTrace (prefixWord ++ tailWord_976906) baseStart_976906 baseEnd_976906 := by
    simpa [prefixWord, tailWord_976906, baseEnd_976906] using wordTrace_append hprefix tailTrace_976906
  have hstable : (prefixWord ++ tailWord_976906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976906).length < 2 ^ (prefixWord ++ tailWord_976906).sum := by decide
  have hdescent : baseEnd_976906 < baseStart_976906 := by decide
  rcases family_descends (prefixWord ++ tailWord_976906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976913 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 3, 8]
def baseStart_976913 : Nat := 118140960795 + 976913 * 2 ^ 59
def prefixEnd_976913 : Nat := 4983230072969 + 3 ^ 40 * 976913 * 2
def baseEnd_976913 : Nat := 334417284417227704729843

theorem tailTrace_976913 : CollatzResearch.WordTrace tailWord_976913 prefixEnd_976913 334417284417227704729843 := by
  unfold tailWord_976913
  simp only [CollatzResearch.WordTrace]
  refine ⟨35630944309818519302423393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23753962873212346201615595 35630944309818519302423393)
  ·
    refine ⟨26723208232363889476817545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35630944309818519302423393 26723208232363889476817545)
    ·
      refine ⟨20042406174272917107613159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26723208232363889476817545 20042406174272917107613159)
      ·
        refine ⟨30063609261409375661419739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20042406174272917107613159 30063609261409375661419739)
        ·
          refine ⟨45095413892114063492129609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30063609261409375661419739 45095413892114063492129609)
          ·
            refine ⟨33821560419085547619097207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45095413892114063492129609 33821560419085547619097207)
            ·
              refine ⟨50732340628628321428645811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33821560419085547619097207 50732340628628321428645811)
              ·
                refine ⟨76098510942942482142968717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50732340628628321428645811 76098510942942482142968717)
                ·
                  refine ⟨28536941603603430803613269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76098510942942482142968717 28536941603603430803613269)
                  ·
                    refine ⟨334417284417227704729843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 28536941603603430803613269 334417284417227704729843)
                    ·
                      rfl

theorem cell22_976913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_976913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976913 prefixEnd_976913 := by exact prefixLift 976913
  have htrace : WordTrace (prefixWord ++ tailWord_976913) baseStart_976913 baseEnd_976913 := by
    simpa [prefixWord, tailWord_976913, baseEnd_976913] using wordTrace_append hprefix tailTrace_976913
  have hstable : (prefixWord ++ tailWord_976913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976913).length < 2 ^ (prefixWord ++ tailWord_976913).sum := by decide
  have hdescent : baseEnd_976913 < baseStart_976913 := by decide
  rcases family_descends (prefixWord ++ tailWord_976913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976915 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 5, 3]
def baseStart_976915 : Nat := 118140960795 + 976915 * 2 ^ 59
def prefixEnd_976915 : Nat := 4983230072969 + 3 ^ 40 * 976915 * 2
def baseEnd_976915 : Nat := 334417969058100366179837

theorem tailTrace_976915 : CollatzResearch.WordTrace tailWord_976915 prefixEnd_976915 334417969058100366179837 := by
  unfold tailWord_976915
  simp only [CollatzResearch.WordTrace]
  refine ⟨35631017255811273643996199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23754011503874182429330799 35631017255811273643996199)
  ·
    refine ⟨53446525883716910465994299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35631017255811273643996199 53446525883716910465994299)
    ·
      refine ⟨80169788825575365698991449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53446525883716910465994299 80169788825575365698991449)
      ·
        refine ⟨60127341619181524274243587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80169788825575365698991449 60127341619181524274243587)
        ·
          refine ⟨90191012428772286411365381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60127341619181524274243587 90191012428772286411365381)
          ·
            refine ⟨16910814830394803702131009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90191012428772286411365381 16910814830394803702131009)
            ·
              refine ⟨12683111122796102776598257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16910814830394803702131009 12683111122796102776598257)
              ·
                refine ⟨9512333342097077082448693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12683111122796102776598257 9512333342097077082448693)
                ·
                  refine ⟨891781250821600976479565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9512333342097077082448693 891781250821600976479565)
                  ·
                    refine ⟨334417969058100366179837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 891781250821600976479565 334417969058100366179837)
                    ·
                      rfl

theorem cell22_976915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 5, 3].length) (baseStart_976915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976915 prefixEnd_976915 := by exact prefixLift 976915
  have htrace : WordTrace (prefixWord ++ tailWord_976915) baseStart_976915 baseEnd_976915 := by
    simpa [prefixWord, tailWord_976915, baseEnd_976915] using wordTrace_append hprefix tailTrace_976915
  have hstable : (prefixWord ++ tailWord_976915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976915).length < 2 ^ (prefixWord ++ tailWord_976915).sum := by decide
  have hdescent : baseEnd_976915 < baseStart_976915 := by decide
  rcases family_descends (prefixWord ++ tailWord_976915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976917 : List Nat := [1, 3, 2, 1, 6, 1, 8]
def baseStart_976917 : Nat := 118140960795 + 976917 * 2 ^ 59
def prefixEnd_976917 : Nat := 4983230072969 + 3 ^ 40 * 976917 * 2
def baseEnd_976917 : Nat := 12385876062924926949253

theorem tailTrace_976917 : CollatzResearch.WordTrace tailWord_976917 prefixEnd_976917 12385876062924926949253 := by
  unfold tailWord_976917
  simp only [CollatzResearch.WordTrace]
  refine ⟨35631090201804027985569005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23754060134536018657046003 35631090201804027985569005)
  ·
    refine ⟨13361658825676510494588377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35631090201804027985569005 13361658825676510494588377)
    ·
      refine ⟨10021244119257382870941283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13361658825676510494588377 10021244119257382870941283)
      ·
        refine ⟨15031866178886074306411925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10021244119257382870941283 15031866178886074306411925)
        ·
          refine ⟨704618727135284733113059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15031866178886074306411925 704618727135284733113059)
          ·
            refine ⟨1056928090702927099669589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704618727135284733113059 1056928090702927099669589)
            ·
              refine ⟨12385876062924926949253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1056928090702927099669589 12385876062924926949253)
              ·
                rfl

theorem cell22_976917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 8].length) (baseStart_976917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976917 prefixEnd_976917 := by exact prefixLift 976917
  have htrace : WordTrace (prefixWord ++ tailWord_976917) baseStart_976917 baseEnd_976917 := by
    simpa [prefixWord, tailWord_976917, baseEnd_976917] using wordTrace_append hprefix tailTrace_976917
  have hstable : (prefixWord ++ tailWord_976917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976917).length < 2 ^ (prefixWord ++ tailWord_976917).sum := by decide
  have hdescent : baseEnd_976917 < baseStart_976917 := by decide
  rcases family_descends (prefixWord ++ tailWord_976917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976930 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 2, 6]
def baseStart_976930 : Nat := 118140960795 + 976930 * 2 ^ 59
def prefixEnd_976930 : Nat := 4983230072969 + 3 ^ 40 * 976930 * 2
def baseEnd_976930 : Nat := 334423103864645327054791

theorem tailTrace_976930 : CollatzResearch.WordTrace tailWord_976930 prefixEnd_976930 334423103864645327054791 := by
  unfold tailWord_976930
  simp only [CollatzResearch.WordTrace]
  refine ⟨8907891087689232801448061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23754376233837954137194829 8907891087689232801448061)
  ·
    refine ⟨3340459157883462300543023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8907891087689232801448061 3340459157883462300543023)
    ·
      refine ⟨5010688736825193450814535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3340459157883462300543023 5010688736825193450814535)
      ·
        refine ⟨7516033105237790176221803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5010688736825193450814535 7516033105237790176221803)
        ·
          refine ⟨11274049657856685264332705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7516033105237790176221803 11274049657856685264332705)
          ·
            refine ⟨8455537243392513948249529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11274049657856685264332705 8455537243392513948249529)
            ·
              refine ⟨6341652932544385461187147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8455537243392513948249529 6341652932544385461187147)
              ·
                refine ⟨9512479398816578191780721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6341652932544385461187147 9512479398816578191780721)
                ·
                  refine ⟨7134359549112433643835541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9512479398816578191780721 7134359549112433643835541)
                  ·
                    refine ⟨334423103864645327054791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7134359549112433643835541 334423103864645327054791)
                    ·
                      rfl

theorem cell22_976930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_976930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976930 prefixEnd_976930 := by exact prefixLift 976930
  have htrace : WordTrace (prefixWord ++ tailWord_976930) baseStart_976930 baseEnd_976930 := by
    simpa [prefixWord, tailWord_976930, baseEnd_976930] using wordTrace_append hprefix tailTrace_976930
  have hstable : (prefixWord ++ tailWord_976930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976930).length < 2 ^ (prefixWord ++ tailWord_976930).sum := by decide
  have hdescent : baseEnd_976930 < baseStart_976930 := by decide
  rcases family_descends (prefixWord ++ tailWord_976930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976994 : List Nat := [3, 3, 2, 2, 2, 1, 1, 1, 2, 5]
def baseStart_976994 : Nat := 118140960795 + 976994 * 2 ^ 59
def prefixEnd_976994 : Nat := 4983230072969 + 3 ^ 40 * 976994 * 2
def baseEnd_976994 : Nat := 334445012372570493454595

theorem tailTrace_976994 : CollatzResearch.WordTrace tailWord_976994 prefixEnd_976994 334445012372570493454595 := by
  unfold tailWord_976994
  simp only [CollatzResearch.WordTrace]
  refine ⟨8908474655631267534030509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23755932415016713424081357 8908474655631267534030509)
  ·
    refine ⟨3340677995861725325261441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8908474655631267534030509 3340677995861725325261441)
    ·
      refine ⟨2505508496896293993946081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3340677995861725325261441 2505508496896293993946081)
      ·
        refine ⟨1879131372672220495459561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2505508496896293993946081 1879131372672220495459561)
        ·
          refine ⟨1409348529504165371594671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1879131372672220495459561 1409348529504165371594671)
          ·
            refine ⟨2114022794256248057392007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409348529504165371594671 2114022794256248057392007)
            ·
              refine ⟨3171034191384372086088011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2114022794256248057392007 3171034191384372086088011)
              ·
                refine ⟨4756551287076558129132017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3171034191384372086088011 4756551287076558129132017)
                ·
                  refine ⟨3567413465307418596849013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4756551287076558129132017 3567413465307418596849013)
                  ·
                    refine ⟨334445012372570493454595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3567413465307418596849013 334445012372570493454595)
                    ·
                      rfl

theorem cell22_976994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_976994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_976994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_976994 prefixEnd_976994 := by exact prefixLift 976994
  have htrace : WordTrace (prefixWord ++ tailWord_976994) baseStart_976994 baseEnd_976994 := by
    simpa [prefixWord, tailWord_976994, baseEnd_976994] using wordTrace_append hprefix tailTrace_976994
  have hstable : (prefixWord ++ tailWord_976994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976994).length < 2 ^ (prefixWord ++ tailWord_976994).sum := by decide
  have hdescent : baseEnd_976994 < baseStart_976994 := by decide
  rcases family_descends (prefixWord ++ tailWord_976994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977056 : List Nat := [2, 1, 1, 4, 2, 3, 3, 1, 2, 3]
def baseStart_977056 : Nat := 118140960795 + 977056 * 2 ^ 59
def prefixEnd_977056 : Nat := 4983230072969 + 3 ^ 40 * 977056 * 2
def baseEnd_977056 : Nat := 334466236239622998404405

theorem tailTrace_977056 : CollatzResearch.WordTrace tailWord_977056 prefixEnd_977056 334466236239622998404405 := by
  unfold tailWord_977056
  simp only [CollatzResearch.WordTrace]
  refine ⟨17818079974150227362439511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23757439965533636483252681 17818079974150227362439511)
  ·
    refine ⟨26727119961225341043659267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17818079974150227362439511 26727119961225341043659267)
    ·
      refine ⟨40090679941838011565488901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26727119961225341043659267 40090679941838011565488901)
      ·
        refine ⟨7517002489094627168529169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40090679941838011565488901 7517002489094627168529169)
        ·
          refine ⟨5637751866820970376396877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7517002489094627168529169 5637751866820970376396877)
          ·
            refine ⟨2114156950057863891148829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5637751866820970376396877 2114156950057863891148829)
            ·
              refine ⟨792808856271698959180811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2114156950057863891148829 792808856271698959180811)
              ·
                refine ⟨1189213284407548438771217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 792808856271698959180811 1189213284407548438771217)
                ·
                  refine ⟨891909963305661329078413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1189213284407548438771217 891909963305661329078413)
                  ·
                    refine ⟨334466236239622998404405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 891909963305661329078413 334466236239622998404405)
                    ·
                      rfl

theorem cell22_977056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 2, 3].length) (baseStart_977056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_977056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_977056 prefixEnd_977056 := by exact prefixLift 977056
  have htrace : WordTrace (prefixWord ++ tailWord_977056) baseStart_977056 baseEnd_977056 := by
    simpa [prefixWord, tailWord_977056, baseEnd_977056] using wordTrace_append hprefix tailTrace_977056
  have hstable : (prefixWord ++ tailWord_977056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977056).length < 2 ^ (prefixWord ++ tailWord_977056).sum := by decide
  have hdescent : baseEnd_977056 < baseStart_977056 := by decide
  rcases family_descends (prefixWord ++ tailWord_977056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977069 : List Nat := [1, 5, 2, 1, 2, 1, 4, 6]
def baseStart_977069 : Nat := 118140960795 + 977069 * 2 ^ 59
def prefixEnd_977069 : Nat := 4983230072969 + 3 ^ 40 * 977069 * 2
def baseEnd_977069 : Nat := 37163409600588366425485

theorem tailTrace_977069 : CollatzResearch.WordTrace tailWord_977069 prefixEnd_977069 37163409600588366425485 := by
  unfold tailWord_977069
  simp only [CollatzResearch.WordTrace]
  refine ⟨35636634097253357945102261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23757756064835571963401507 35636634097253357945102261)
  ·
    refine ⟨3340934446617502307353337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35636634097253357945102261 3340934446617502307353337)
    ·
      refine ⟨2505700834963126730515003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3340934446617502307353337 2505700834963126730515003)
      ·
        refine ⟨3758551252444690095772505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2505700834963126730515003 3758551252444690095772505)
        ·
          refine ⟨2818913439333517571829379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3758551252444690095772505 2818913439333517571829379)
          ·
            refine ⟨4228370159000276357744069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2818913439333517571829379 4228370159000276357744069)
            ·
              refine ⟨792819404812551817077013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4228370159000276357744069 792819404812551817077013)
              ·
                refine ⟨37163409600588366425485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 792819404812551817077013 37163409600588366425485)
                ·
                  rfl

theorem cell22_977069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 6].length) (baseStart_977069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_977069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_977069 prefixEnd_977069 := by exact prefixLift 977069
  have htrace : WordTrace (prefixWord ++ tailWord_977069) baseStart_977069 baseEnd_977069 := by
    simpa [prefixWord, tailWord_977069, baseEnd_977069] using wordTrace_append hprefix tailTrace_977069
  have hstable : (prefixWord ++ tailWord_977069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977069).length < 2 ^ (prefixWord ++ tailWord_977069).sum := by decide
  have hdescent : baseEnd_977069 < baseStart_977069 := by decide
  rcases family_descends (prefixWord ++ tailWord_977069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977080 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 9]
def baseStart_977080 : Nat := 118140960795 + 977080 * 2 ^ 59
def prefixEnd_977080 : Nat := 4983230072969 + 3 ^ 40 * 977080 * 2
def baseEnd_977080 : Nat := 111491483976698311934777

theorem tailTrace_977080 : CollatzResearch.WordTrace tailWord_977080 prefixEnd_977080 111491483976698311934777 := by
  unfold tailWord_977080
  simp only [CollatzResearch.WordTrace]
  refine ⟨17818517650106753411876347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23758023533475671215835129 17818517650106753411876347)
  ·
    refine ⟨26727776475160130117814521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17818517650106753411876347 26727776475160130117814521)
    ·
      refine ⟨20045832356370097588360891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26727776475160130117814521 20045832356370097588360891)
      ·
        refine ⟨30068748534555146382541337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20045832356370097588360891 30068748534555146382541337)
        ·
          refine ⟨22551561400916359786906003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30068748534555146382541337 22551561400916359786906003)
          ·
            refine ⟨33827342101374539680359005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22551561400916359786906003 33827342101374539680359005)
            ·
              refine ⟨12685253288015452380134627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33827342101374539680359005 12685253288015452380134627)
              ·
                refine ⟨19027879932023178570201941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12685253288015452380134627 19027879932023178570201941)
                ·
                  refine ⟨111491483976698311934777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19027879932023178570201941 111491483976698311934777)
                  ·
                    rfl

theorem cell22_977080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 9].length) (baseStart_977080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_977080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_977080 prefixEnd_977080 := by exact prefixLift 977080
  have htrace : WordTrace (prefixWord ++ tailWord_977080) baseStart_977080 baseEnd_977080 := by
    simpa [prefixWord, tailWord_977080, baseEnd_977080] using wordTrace_append hprefix tailTrace_977080
  have hstable : (prefixWord ++ tailWord_977080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977080).length < 2 ^ (prefixWord ++ tailWord_977080).sum := by decide
  have hdescent : baseEnd_977080 < baseStart_977080 := by decide
  rcases family_descends (prefixWord ++ tailWord_977080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977114 : List Nat := [3, 1, 1, 2, 2, 1, 6, 1, 5]
def baseStart_977114 : Nat := 118140960795 + 977114 * 2 ^ 59
def prefixEnd_977114 : Nat := 4983230072969 + 3 ^ 40 * 977114 * 2
def baseEnd_977114 : Nat := 111495363608310060151409

theorem tailTrace_977114 : CollatzResearch.WordTrace tailWord_977114 prefixEnd_977114 111495363608310060151409 := by
  unfold tailWord_977114
  simp only [CollatzResearch.WordTrace]
  refine ⟨8909568845522582657622599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23758850254726887086993597 8909568845522582657622599)
  ·
    refine ⟨13364353268283873986433899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8909568845522582657622599 13364353268283873986433899)
    ·
      refine ⟨20046529902425810979650849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13364353268283873986433899 20046529902425810979650849)
      ·
        refine ⟨15034897426819358234738137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20046529902425810979650849 15034897426819358234738137)
        ·
          refine ⟨11276173070114518676053603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15034897426819358234738137 11276173070114518676053603)
          ·
            refine ⟨16914259605171778014080405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11276173070114518676053603 16914259605171778014080405)
            ·
              refine ⟨792855918992427094410019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16914259605171778014080405 792855918992427094410019)
              ·
                refine ⟨1189283878488640641615029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 792855918992427094410019 1189283878488640641615029)
                ·
                  refine ⟨111495363608310060151409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1189283878488640641615029 111495363608310060151409)
                  ·
                    rfl

theorem cell22_977114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 5].length) (baseStart_977114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_977114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_977114 prefixEnd_977114 := by exact prefixLift 977114
  have htrace : WordTrace (prefixWord ++ tailWord_977114) baseStart_977114 baseEnd_977114 := by
    simpa [prefixWord, tailWord_977114, baseEnd_977114] using wordTrace_append hprefix tailTrace_977114
  have hstable : (prefixWord ++ tailWord_977114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977114).length < 2 ^ (prefixWord ++ tailWord_977114).sum := by decide
  have hdescent : baseEnd_977114 < baseStart_977114 := by decide
  rcases family_descends (prefixWord ++ tailWord_977114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
